#include "transition.h"

#include <map>
#include <algorithm>

#include "dtg_manager.h"
#include "dtg_node.h"
#include "property_space.h"
#include "../formula.h"
#include "../parser_utils.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

///#define ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
///#define ENABLE_MYPOP_SAS_TRANSITION_DEBUG

namespace MyPOP {

namespace SAS_Plus {

bool CompareBalancedPropertySet::operator()(const BalancedPropertySet& lhs, const BalancedPropertySet& rhs) const
{
	if (lhs.property_space_ < rhs.property_space_)
		return true;
	
	if (lhs.property_space_ == rhs.property_space_ && lhs.invariable_domain_ < rhs.invariable_domain_)
		return true;
	
	return false;
}
	
BalancedPropertySet::BalancedPropertySet(const PropertySpace& property_space, const std::vector<const Object*>* invariable_domain)
	: property_space_(&property_space), invariable_domain_(invariable_domain)
{
	
}

void BalancedPropertySet::removeProperty(const BoundedAtom& fact)
{
	if (std::find(properties_deleted_.begin(), properties_deleted_.end(), &fact) == properties_deleted_.end())
	{
		properties_deleted_.push_back(&fact);
	}
}

void BalancedPropertySet::addProperty(const BoundedAtom& fact)
{
	if (std::find(properties_added_.begin(), properties_added_.end(), &fact) == properties_added_.end())
	{
		properties_added_.push_back(&fact);
	}
}

const std::vector<const BoundedAtom*>& BalancedPropertySet::getAddedProperties() const
{
	return properties_added_;
}
	
const std::vector<const BoundedAtom*>& BalancedPropertySet::getRemovedProperties() const
{
	return properties_deleted_;
}

void BalancedPropertySet::removeAddedProperty(const BoundedAtom& fact)
{
	for (std::vector<const BoundedAtom*>::reverse_iterator ri = properties_added_.rbegin(); ri != properties_added_.rend(); ri++)
	{
		if (&fact == *ri)
		{
			properties_added_.erase(ri.base() - 1);
		}
	}
	//std::remove(properties_added_.begin(), properties_added_.end(), &fact);
}
	
void BalancedPropertySet::removeRemovedProperty(const BoundedAtom& fact)
{
	for (std::vector<const BoundedAtom*>::reverse_iterator ri = properties_deleted_.rbegin(); ri != properties_deleted_.rend(); ri++)
	{
		if (&fact == *ri)
		{
			properties_deleted_.erase(ri.base() - 1);
		}
	}
	//std::remove(properties_deleted_.begin(), properties_deleted_.end(), &fact);
}


Transition* Transition::createTransition(const Action& action, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
{
	if (&to_node.getDTG() != &from_node.getDTG())
	{
		std::cout << "[Transition::createTransition] FATAL ERROR! The nodes are not part of the same DTG!" << std::endl;
		assert(false);
	}

	Bindings& bindings = from_node.getDTG().getBindings();

	// Create the transition's action. We initiate the action by linking its precondition and effects
	// to this node and to_node respectively. This way we can force bindings on these nodes.
	StepID action_step_id = bindings.createVariableDomains(action);
	StepPtr action_step(new Step(action_step_id, action));
	
	// If a DTG node does not contain a node with a valid invariable index, we use the createSimpleTransition. This method should not
	// exist, but it works for now so it is on the TODO list to be merged with the createTransition method.
	bool contains_invariables = false;
	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		if (from_node.getIndex(**ci) != NO_INVARIABLE_INDEX)
		{
			contains_invariables = true;
			break;
		}
	}
	
	Transition* transition = NULL;
	
	if (contains_invariables)
	{
		transition = Transition::createTransition(action_step, from_node, to_node, initial_facts);
	}
	else
	{
		transition = Transition::createSimpleTransition(action_step, from_node, to_node, initial_facts);
	}
	
	if (transition == NULL)
	{
		for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ci++)
		{
			bindings.removeBindings(action_step_id, **ci);
		}
	}
	return transition;
}

Transition* Transition::createSimpleTransition(const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
{
	std::cout << std::endl << std::endl;
	std::cout << "[Transition::createSimpleTransition] NEW TRANSITION!!!!" << std::endl;
	std::cout << "From: " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), action_step->getStepId());
	std::cout << std::endl;

	if (&to_node.getDTG() != &from_node.getDTG())
	{
		std::cout << "[Transition::createSimpleTransition] FATAL ERROR! The nodes are not part of the same DTG!" << std::endl;
		assert(false);
	}

	Bindings& bindings = from_node.getDTG().getBindings();

	/**
	 * First of all we check which facts are removed and which facts are added between the DTGs.
	 * Compare the from and to nodes, store all the facts which are added, removed and those which stay the same. This information is used to
	 * determine which variable is the invariable one and if the transitions is executable in the first place.
	 * The rules we apply are as follows:
	 * 1) If a fact is present in the from node but not in the to node, the action must delete the missing fact.
	 * 2) If a fact is added in the to node, the action must add the added fact.
	 * 3) If a fact is present in both nodes, the action must either have deleted and added the fact or not touched at all.
	 * 4) The action should either remove or add something.
	 * If any of these rules are broken, the action cannot be applied.
	 */

	/**
	 * Store per property state a pair of: removed properties and added properties.
	 */
	std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > > property_space_balanced_sets;

	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* from_fact = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = from_fact->getProperties().begin(); ci != from_fact->getProperties().end(); ci++)
		{
			// Check if the property space this from_fact belongs to has already been created.
			//const PropertySpace& from_fact_property_space = from_fact->getProperty()->getPropertyState().getPropertySpace();
			const PropertySpace& from_fact_property_space = (*ci)->getPropertyState().getPropertySpace();
			std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::iterator property_space_i = property_space_balanced_sets.find(&from_fact_property_space);
			std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > add_remove_list;
			if (property_space_i == property_space_balanced_sets.end())
			{
				std::vector<const BoundedAtom*>* add_list = new std::vector<const BoundedAtom*>();
				std::vector<const BoundedAtom*>* removal_list = new std::vector<const BoundedAtom*>();
				add_remove_list = std::make_pair(add_list, removal_list);
				property_space_balanced_sets[&from_fact_property_space] = add_remove_list;
			}
			else
			{
				add_remove_list = (*property_space_i).second;
			}
			
			assert (from_node.getIndex(*from_fact) == NO_INVARIABLE_INDEX);
			
			/**
			* Determine if this fact has been removed (i.e. is not part of the to_node). If the fact has not been removed it is marked as
			* persistent. This can later be undone if we find that the fact is removed and later added by the given action.
			*/
			for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* to_fact = *ci;
				
				assert (to_node.getIndex(*to_fact) == NO_INVARIABLE_INDEX);

				// If the same fact appears in the to node we assume it is not deleted and thus is persistent. The next block of code
				// determines if this is really the case or if the action deletes and adds this fact.
				if (from_node.getIndex(*from_fact) == to_node.getIndex(*to_fact) &&
					to_fact->getAtom().isNegative() == from_fact->getAtom().isNegative() &&
					bindings.canUnify(from_fact->getAtom(), from_fact->getId(), to_fact->getAtom(), to_fact->getId()))
				{
					assert (false);
				}
			}

			add_remove_list.second->push_back(from_fact);
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* to_fact = *ci;
		
//		if (to_fact->getProperty() == NULL)
//			continue;

		for (std::vector<const Property*>::const_iterator ci = to_fact->getProperties().begin(); ci != to_fact->getProperties().end(); ci++)
		{
			// Check if the property space this to_fact belongs to has already been created.
			//const PropertySpace& to_fact_property_space = to_fact->getProperty()->getPropertyState().getPropertySpace();
			const PropertySpace& to_fact_property_space = (*ci)->getPropertyState().getPropertySpace();
			std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::iterator property_space_i = property_space_balanced_sets.find(&to_fact_property_space);
			std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > add_remove_list;
			if (property_space_i == property_space_balanced_sets.end())
			{
				std::vector<const BoundedAtom*>* add_list = new std::vector<const BoundedAtom*>();
				std::vector<const BoundedAtom*>* removal_list = new std::vector<const BoundedAtom*>();
				add_remove_list = std::make_pair(add_list, removal_list);
				property_space_balanced_sets[&to_fact_property_space] = add_remove_list;
			}
			else
			{
				add_remove_list = (*property_space_i).second;
			}
			
			bool is_added = true;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* from_fact = *ci;

				// Check if the fact in the to node is added or was already present.
				if (to_node.getIndex(*to_fact) == from_node.getIndex(*from_fact) &&
					to_fact->getAtom().isNegative() == from_fact->getAtom().isNegative() &&
					bindings.canUnify(to_fact->getAtom(), to_fact->getId(), from_fact->getAtom(), from_fact->getId()))
				{
					is_added = false;
					break;
				}
			}
			
			if (is_added)
			{
				add_remove_list.first->push_back(to_fact);
			}
		}
	}

	/**
	 * Make sure all the added and deleted facts are accounted for.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> >* precondition_mapping_to_from_node = new std::vector<std::pair<const Atom*, InvariableIndex> >(); // Pair of precondition and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> >* add_effects_mapping_to_to_node = new std::vector<std::pair<const Atom*, InvariableIndex> >();    // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> >* remove_effects_mapping_to_to_node = new std::vector<std::pair<const Atom*, InvariableIndex> >(); // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> >* persistent_preconditions = new std::vector<std::pair<const Atom*, InvariableIndex> >(); // Pair of precondition and invariable index.
	
	std::vector<std::pair<const Atom*, const BoundedAtom*> >* add_effects_to_to_node_bindings = new std::vector<std::pair<const Atom*, const BoundedAtom*> >();
	std::vector<std::pair<const Atom*, const BoundedAtom*> >* precondition_to_from_node_bindings = new std::vector<std::pair<const Atom*, const BoundedAtom*> >();
	
	StepID action_step_id = action_step->getStepId();
	const Action& action = action_step->getAction();
	
	const std::vector<const Atom*>& effects = action_step->getAction().getEffects();
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &action.getPrecondition());

	for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
///		const PropertySpace* property_space = (*ci).first;
		const std::vector<const BoundedAtom*>* added_facts = (*ci).second.first;
		const std::vector<const BoundedAtom*>* removed_facts = (*ci).second.second;
		
		if (added_facts->empty() || removed_facts->empty())
		{
			continue;
		}
//		std::cout << " ****************************** " << std::endl;
/*		std::cout << "Check all added and removed facts are accounted for: " << std::endl;
		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts->begin(); ci != added_facts->end(); ci++)
		{
			std::cout << "+ ";
			(*ci)->print(std::cout, bindings);
			std::cout << std::endl;
		}
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts->begin(); ci != removed_facts->end(); ci++)
		{
			std::cout << "- ";
			(*ci)->print(std::cout, bindings);
			std::cout << std::endl;
		}
*/
		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts->begin(); ci != added_facts->end(); ci++)
		{
			const BoundedAtom* added_fact = *ci;
			bool is_added = false;
			
//			std::cout << " =++> Make sure the added fact: ";
//			added_fact->print(std::cout, bindings);
//			std::cout << "is accounted for..." << std::endl;
			
			// Make sure an effect actually added this fact.
			for (std::vector<const Atom*>::const_iterator ci = effects.begin();  ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
				
				if (effect->isNegative() == added_fact->getAtom().isNegative() &&
				    bindings.canUnify(*effect, action_step_id, added_fact->getAtom(), added_fact->getId()))
				{
//					std::cout << "It's added by: ";
//					effect->print(std::cout, bindings, action_step_id);
//					std::cout << std::endl;
					is_added = true;
					add_effects_mapping_to_to_node->push_back(std::make_pair(effect, to_node.getIndex(*added_fact)));
					add_effects_to_to_node_bindings->push_back(std::make_pair(effect, added_fact));
					break;
				}
			}
			
			if (!is_added)
			{
//				std::cout << "The effect: ";
//				added_fact->print(std::cout, bindings);
//				std::cout << " is not accounted for..." << std::endl;
				return NULL;
			}
		}
		
//		std::cout << "Make sure all delete facts are accounted for!" << std::endl;
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts->begin(); ci != removed_facts->end(); ci++)
		{
			const BoundedAtom* removed_fact = *ci;
			bool is_a_precondition = false;
			bool is_removed = false;
			
			if (removed_fact->getAtom().isNegative())
			{
//				std::cout << " =++> The removed fact ";
//				removed_fact->print(std::cout, bindings);
//				std::cout << " is negative so doesn't need to be accounted for." << std::endl;
				continue;
			}
			
//			std::cout << " =++> Make sure the removed fact: ";
//			removed_fact->print(std::cout, bindings);
//			std::cout << "is accounted for..." << std::endl;
			
			// Make sure an effect actually added this fact.
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin();  ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				
				if (precondition->isNegative() == removed_fact->getAtom().isNegative() &&
				    bindings.canUnify(*precondition, action_step_id, removed_fact->getAtom(), removed_fact->getId()))
				{
//					std::cout << "It's removed by: ";
//					precondition->print(std::cout, bindings, action_step_id);
//					std::cout << std::endl;
					precondition_mapping_to_from_node->push_back(std::make_pair(precondition, from_node.getIndex(*removed_fact)));
					precondition_to_from_node_bindings->push_back(std::make_pair(precondition, removed_fact));
					is_a_precondition = true;
					break;
				}
			}
			
			if (!is_a_precondition)
			{
//				std::cout << "The removed precondition: ";
//				removed_fact->print(std::cout, bindings);
//				std::cout << " is not accounted for..." << std::endl;
				return NULL;
			}
			
			for (std::vector<const Atom*>::const_iterator ci = effects.begin();  ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
				
				if (effect->isNegative() != removed_fact->getAtom().isNegative() &&
				    bindings.canUnify(*effect, action_step_id, removed_fact->getAtom(), removed_fact->getId()))
				{
//					std::cout << "It's removed by: ";
//					effect->print(std::cout, bindings, action_step_id);
//					std::cout << std::endl;
					remove_effects_mapping_to_to_node->push_back(std::make_pair(effect, from_node.getIndex(*removed_fact)));
					is_removed = true;
					break;
				}
			}
			
			if (!is_removed)
			{
//				std::cout << "The precondition is not removed: ";
//				removed_fact->print(std::cout, bindings);
//				std::cout << " is not accounted for..." << std::endl;
				return NULL;
			}
		}
	}
	
	/**
	 * Start making the actual bindings!
	 */
//	std::cout << "[Transition::createTransition] Unify the effects!" << std::endl;
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = add_effects_to_to_node_bindings->begin(); ci != add_effects_to_to_node_bindings->end(); ci++)
	{
		const Atom* added_effect = (*ci).first;
		const BoundedAtom* to_node_atom = (*ci).second;
		
		if (!bindings.unify(*added_effect, action_step_id, to_node_atom->getAtom(), to_node_atom->getId()))
		{
//			std::cout << "[Transition::createTransition] Could not perform the actual bindings on effects!" << std::endl;
//			to_node_atom->print(std::cout, bindings);
//			std::cout << " couldn't bind with: ";
//			added_effect->print(std::cout, bindings, new_action_step_id);
//			std::cout << std::endl;
			return NULL;
		}
	}
	
//	std::cout << "[Transition::createTransition] Unify the preconditions!" << std::endl;
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = precondition_to_from_node_bindings->begin(); ci != precondition_to_from_node_bindings->end(); ci++)
	{
		const Atom* precondition = (*ci).first;
		const BoundedAtom* from_node_atom = (*ci).second;
		
		if (!bindings.unify(*precondition, action_step_id, from_node_atom->getAtom(), from_node_atom->getId()))
		{
//			std::cout << "[Transition::createTransition] Could not perform the actual bindings on preconditions!" << std::endl;
//			from_node_atom->print(std::cout, bindings);
//			std::cout << " couldn't bind with: ";
//			precondition->print(std::cout, bindings, new_action_step_id);
//			std::cout << std::endl;
			return NULL;
		}
	}
	
	std::vector<std::pair<const Atom*, InvariableIndex> >* all_precondition_mappings = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		all_precondition_mappings->push_back(std::make_pair(precondition, NO_INVARIABLE_INDEX));
	}
	
/*
	std::cout << "Success!" << std::endl;
	std::cout << "Created a transition from " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	new_action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), new_action_step->getStepId());
	std::cout << std::endl;
*/
	std::map<const PropertySpace*, const Variable*>* property_space_action_invariables = new std::map<const PropertySpace*, const Variable*>();
	
	return new Transition(action_step, from_node, to_node, *precondition_mapping_to_from_node, *add_effects_mapping_to_to_node, *remove_effects_mapping_to_to_node, *persistent_preconditions, *property_space_action_invariables, *all_precondition_mappings);
}

Transition* Transition::createTransition(const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << std::endl << std::endl;
	std::cout << "[Transition::createTransition] NEW TRANSITION!!!!" << std::endl;
	std::cout << "From: " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), action_step->getStepId());
	std::cout << std::endl;
#endif
	
	if (&to_node.getDTG() != &from_node.getDTG())
	{
		std::cout << "[Transition::createTransition] FATAL ERROR! The nodes are not part of the same DTG!" << std::endl;
		assert(false);
	}

	Bindings& bindings = from_node.getDTG().getBindings();

	/**
	 * First of all we check which facts are removed and which facts are added between the DTGs.
	 * Compare the from and to nodes, store all the facts which are added, removed and those which stay the same. This information is used to
	 * determine which variable is the invariable one and if the transitions is executable in the first place.
	 * The rules we apply are as follows:
	 * 1) If a fact is present in the from node but not in the to node, the action must delete the missing fact.
	 * 2) If a fact is added in the to node, the action must add the added fact.
	 * 3) If a fact is present in both nodes, the action must either have deleted and added the fact or not touched at all.
	 * 4) The action should either remove or add something.
	 * If any of these rules are broken, the action cannot be applied.
	 */

	/**
	 * Store per property state a pair of: removed properties and added properties.
	 * TODO: For recursive structures (Blocksworld / Depots) - store a per instance balanced set.
	 */
	std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*> property_space_balanced_sets;
	
	/**
	 * Persistent facts appear in both the start and end node and are not affected by the transition. They are stored 
	 * as <from_node, to_node>.
	 */
	std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> > persistent_facts;

	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* from_fact = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = from_fact->getProperties().begin(); ci != from_fact->getProperties().end(); ci++)
		{
			// Check if the property space this from_fact belongs to has already been created.
			const Property* from_fact_property = *ci;
			const PropertySpace& from_fact_property_space = from_fact_property->getPropertyState().getPropertySpace();

			BalancedPropertySet* balanced_property_set = NULL;
			
			std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::iterator property_space_i = property_space_balanced_sets.find(std::make_pair(&from_fact_property_space, static_cast<const std::vector<const Object*>*>(NULL)));
			
			if (property_space_i == property_space_balanced_sets.end())
			{
				const std::vector<const Object*>* invariable_objects = NULL;
//				if (from_fact_property->getIndex() != NO_INVARIABLE_INDEX)
//				{
//					invariable_objects = from_fact->getAtom().getTerms()[from_fact_property->getIndex()].getDomain(from_fact->getId(), bindings);
//				}
				
				balanced_property_set = new BalancedPropertySet(from_fact_property_space, invariable_objects);

				property_space_balanced_sets[std::make_pair(&from_fact_property_space, static_cast<const std::vector<const Object*>*>(NULL))] = balanced_property_set;
			}
			else
			{
				balanced_property_set = (*property_space_i).second;
			}

			/**
			 * Determine if this fact has been removed (i.e. is not part of the to_node). If the fact has not been removed it is marked as
			 * persistent. This can later be undone if we find that the fact is removed and later added by the given action.
			 */
			bool is_removed = true;
			for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* to_fact = *ci;
				
				// Check if there is a property in the to_fact which overlaps with that of the from fact.
				for (std::vector<const Property*>::const_iterator ci = to_fact->getProperties().begin(); ci != to_fact->getProperties().end(); ci++)
				{
					// Check if the property space this from_fact belongs to has already been created.
					const Property* to_fact_property = *ci;

					// If the same fact appears in the to node we assume it is not deleted and thus is persistent. The next block of code
					// determines if this is really the case or if the action deletes and adds this fact.
					if (*from_fact_property == *to_fact_property &&
						to_fact->getAtom().isNegative() == from_fact->getAtom().isNegative() &&
						bindings.areEquivalent(from_fact->getAtom(), from_fact->getId(), to_fact->getAtom(), to_fact->getId()))
					{
						is_removed = false;
						persistent_facts.push_back(std::make_pair(from_fact, to_fact));
						
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << "Potential persistent fact set: ";
						from_fact->print(std::cout, bindings);
						std::cout << " - ";
						to_fact->print(std::cout ,bindings);
						std::cout << "." << std::endl;
#endif
					}
				}
			}

			if (is_removed)
			{
				balanced_property_set->removeProperty(*from_fact);
			}
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* to_fact = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = to_fact->getProperties().begin(); ci != to_fact->getProperties().end(); ci++)
		{
			// Check if the property space this to_fact belongs to has already been created.
			const Property* to_fact_property = *ci;
			const PropertySpace& to_fact_property_space = to_fact_property->getPropertyState().getPropertySpace();
			
			BalancedPropertySet* balanced_property_set = NULL;
			std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::iterator property_space_i = property_space_balanced_sets.find(std::make_pair(&to_fact_property_space, static_cast<const std::vector<const Object*>*>(NULL)));
			
			if (property_space_i == property_space_balanced_sets.end())
			{
				const std::vector<const Object*>* invariable_objects = NULL;
//				if (from_fact_property->getIndex() != NO_INVARIABLE_INDEX)
//				{
//					invariable_objects = from_fact->getAtom().getTerms()[from_fact_property->getIndex()].getDomain(from_fact->getId(), bindings);
//				}
				
				balanced_property_set = new BalancedPropertySet(to_fact_property_space, invariable_objects);
				property_space_balanced_sets[std::make_pair(&to_fact_property_space, static_cast<const std::vector<const Object*>*>(NULL))] = balanced_property_set;
			}
			else
			{
				balanced_property_set = (*property_space_i).second;
			}

			bool is_added = true;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* from_fact = *ci;
				
				for (std::vector<const Property*>::const_iterator ci = from_fact->getProperties().begin(); ci != from_fact->getProperties().end(); ci++)
				{
					const Property* from_fact_property = *ci;
					// Check if the fact in the to node is added or was already present.
					if (*to_fact_property == *from_fact_property &&
						to_fact->getAtom().isNegative() == from_fact->getAtom().isNegative() &&
						bindings.areEquivalent(to_fact->getAtom(), to_fact->getId(), from_fact->getAtom(), from_fact->getId()))
					{
						is_added = false;
						break;
					}
				}
				
				if (!is_added) break;
			}
			
			if (is_added)
			{
				balanced_property_set->addProperty(*to_fact);
//				add_remove_list.first->push_back(to_fact);
			}
		}
	}

	StepID action_step_id = action_step->getStepId();
	const Action& action = action_step->getAction();
	
	const std::vector<const Atom*>& effects = action_step->getAction().getEffects();
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &action.getPrecondition());

	// Check the facts that are persistent due to the fact that they are removed and added by this action. These are 
	// not found by the previous analysis because we only compare the index of the invariable and check if the variable 
	// domains overlap. An action is invalid if it does not interact with the nodes at all, so an action which adds and 
	// removes the same fact, e.g. drive-truck removes (at ?truck ?location) and adds (at ?truck ?location). Based on the 
	// previous analysis we conclude that the action does not interact, but we might discover that the action adds and 
	// removes a similar fact and does interact with the nodes.
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::reverse_iterator persistent_ci = persistent_facts.rbegin(); persistent_ci != persistent_facts.rend(); persistent_ci++)
	{
		const BoundedAtom* from_persistent_atom = (*persistent_ci).first;
		const BoundedAtom* to_persistent_atom = (*persistent_ci).second;
		bool is_added = false;
		bool is_deleted = false;
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Validate persistent fact: ";
		from_persistent_atom->print(std::cout, bindings);
		std::cout << std::endl;
#endif
		
		// Check if the transitions removes this fact.
		for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
		{
			const Atom* effect = *ci;

//			std::cout << " v.s. effect: ";
//			effect->print(std::cout, bindings, action_step_id);
//			std::cout << std::endl;

			if (effect->isNegative() == to_persistent_atom->getAtom().isNegative() && 
				bindings.canUnify(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()))
			{
//				std::cout << "Is added!" << std::endl;
				is_added = true;
			}

			if (bindings.affects(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()))
			{
//				std::cout << "Is deleted!" << std::endl;
				is_deleted = true;
			}
		}

		if (is_added && is_deleted)
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "Invallid persistent fact!" << std::endl;
#endif

			for (std::vector<const Property*>::const_iterator ci = to_persistent_atom->getProperties().begin(); ci != to_persistent_atom->getProperties().end(); ci++)
			{
				const PropertySpace& property_space = (*ci)->getPropertyState().getPropertySpace();
				std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::iterator i = property_space_balanced_sets.find(std::make_pair(&property_space, static_cast<const std::vector<const Object*>*>(NULL)));
				
				assert (i != property_space_balanced_sets.end());
				
				(*i).second->addProperty(*to_persistent_atom);
				(*i).second->removeProperty(*from_persistent_atom);
			}
			
			for (std::vector<const Property*>::const_iterator ci = from_persistent_atom->getProperties().begin(); ci != from_persistent_atom->getProperties().end(); ci++)
			{
				const PropertySpace& property_space = (*ci)->getPropertyState().getPropertySpace();
				std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::iterator i = property_space_balanced_sets.find(std::make_pair(&property_space, static_cast<const std::vector<const Object*>*>(NULL)));
				
				assert (i != property_space_balanced_sets.end());
				
				(*i).second->addProperty(*to_persistent_atom);
				(*i).second->removeProperty(*from_persistent_atom);
			}

			persistent_facts.erase(persistent_ci.base() - 1);
			break;
		}
	}
	
	/**
	 * Remove all facts from the add / remove sets if they are reported to be persistent!
	 * TODO: Not a nice way of doing things, but works for now :).
	 */
	std::vector<std::pair<const PropertySpace*, const std::vector<const Object*>* > > to_remove;
	for (std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		BalancedPropertySet* balanced_property_set = (*ci).second;
		std::pair<const PropertySpace*, const std::vector<const Object*>* > key = (*ci).first;
		
		for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
		{
			balanced_property_set->removeAddedProperty(*(*ci).second);
			balanced_property_set->removeRemovedProperty(*(*ci).first);
		}
		
		if (balanced_property_set->getAddedProperties().empty() && balanced_property_set->getRemovedProperties().empty())
		{
			to_remove.push_back(key);
		}
	}
	
	for (std::vector<std::pair<const PropertySpace*, const std::vector<const Object*>* > >::const_iterator ci = to_remove.begin(); ci != to_remove.end(); ci++)
	{
		property_space_balanced_sets.erase(*ci);
	}
	
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	for (std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		
		std::cout << "Add / Remove sets: " << (*ci).first.first << std::endl;
		BalancedPropertySet* balanced_property_set = (*ci).second;
		
		for (std::vector<const BoundedAtom*>::const_iterator ci = balanced_property_set->getAddedProperties().begin(); ci != balanced_property_set->getAddedProperties().end(); ci++)
		{
			const BoundedAtom* add_atom = *ci;
			
			std::cout << "+ ";
			add_atom->print(std::cout, bindings);
			std::cout << std::endl;
		}
		
		for (std::vector<const BoundedAtom*>::const_iterator ci = balanced_property_set->getRemovedProperties().begin(); ci != balanced_property_set->getRemovedProperties().end(); ci++)
		{
			const BoundedAtom* add_atom = *ci;
			
			std::cout << "- ";
			add_atom->print(std::cout, bindings);
			std::cout << std::endl;
		}
	}


	std::cout << "Persistent facts: " << std::endl;
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
	{
		const BoundedAtom* from_bounded_atom = (*ci).first;
		const BoundedAtom* to_bounded_atom = (*ci).second;
		
		std::cout << "= ";
		from_bounded_atom->print(std::cout, bindings);
		std::cout << " --- ";
		to_bounded_atom->print(std::cout, bindings);
		std::cout << std::endl;
	}
#endif

	/**
	 * Determine for each property space which action variable is invariable.
	 */
	std::map<const PropertySpace*, const std::vector<const Object*>*> property_space_invariables;
	std::map<const PropertySpace*, const Variable*>* property_space_action_invariables = new std::map<const PropertySpace*, const Variable*>();
	
	for (std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		// Only consider property spaces which get removed and added, if a fact is only added or removed it's an optional precondition.
		const PropertySpace* property_space = (*ci).first.first;
		
		BalancedPropertySet* balanced_property_set = (*ci).second;
		
		const std::vector<const BoundedAtom*>& added_facts = balanced_property_set->getAddedProperties();
		const std::vector<const BoundedAtom*>& removed_facts = balanced_property_set->getRemovedProperties();
		
		if (added_facts.empty() || removed_facts.empty())
		{
			continue;
		}
		
		std::set<const std::vector<const Object*>*> action_invariables;
		std::map<const std::vector<const Object*>*, const Variable*> action_invariable_variable;
		
		// Initialize by making all action variables possible invariables.
		for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ci++)
		{
			const std::vector<const Object*>& objects = (*ci)->getDomain(action_step_id, bindings);
			action_invariables.insert(&objects);
			action_invariable_variable[&objects] = *ci;
		}
		
		/**
		 * Go over all the preconditions and effects and determine the invariable.
		 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Find invariable for all added facts." << std::endl;
#endif
		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts.begin(); ci != added_facts.end(); ci++)
		{
			const BoundedAtom* added_fact = *ci;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "- For ";
			added_fact->print(std::cout, bindings);
			std::cout << std::endl;
#endif
			
			std::set<const std::vector<const Object*>*> possible_add_invariables;
			
			for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
				
				if (effect->isNegative() == added_fact->getAtom().isNegative() &&
				    bindings.canUnify(*effect, action_step_id, added_fact->getAtom(), added_fact->getId()))
				{
					// Go over all the properties attached to the to_node and note down all invariables as possibles.
					for (std::vector<const Property*>::const_iterator ci = added_fact->getProperties().begin(); ci != added_fact->getProperties().end(); ci++)
					{
						const Property* property = *ci;
						if (property->getIndex() == NO_INVARIABLE_INDEX)
							continue;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << "Possible invariable: ";
						effect->print(std::cout, bindings, action_step_id);
						std::cout << "(" << property->getIndex() << ")" << std::endl;
#endif
						possible_add_invariables.insert(&effect->getTerms()[property->getIndex()]->getDomain(action_step_id, bindings));
					}
				}
			}
			
			// Prune the possible range.
			std::set<const std::vector<const Object*>*> tmp_set;
			std::set_intersection(possible_add_invariables.begin(), possible_add_invariables.end(), action_invariables.begin(), action_invariables.end(), std::inserter(tmp_set, tmp_set.begin()));
			
			action_invariables.clear();
			action_invariables.insert(tmp_set.begin(), tmp_set.end());
		}
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Find invariable for all removed facts." << std::endl;
#endif
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts.begin(); ci != removed_facts.end(); ci++)
		{
			const BoundedAtom* removed_fact = *ci;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "- For ";
			removed_fact->print(std::cout, bindings);
			std::cout << std::endl;
#endif
			
			std::set<const std::vector<const Object*>*> possible_remove_invariables;
			
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				
				if (bindings.canUnify(*precondition, action_step_id, removed_fact->getAtom(), removed_fact->getId()))
				{
					// Go over all the properties attached to the to_node and note down all invariables as possibles.
					for (std::vector<const Property*>::const_iterator ci = removed_fact->getProperties().begin(); ci != removed_fact->getProperties().end(); ci++)
					{
						const Property* property = *ci;
						if (property->getIndex() == NO_INVARIABLE_INDEX)
							continue;

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << "Possible invariable: ";
						precondition->print(std::cout, bindings, action_step_id);
						std::cout << "(" << property->getIndex() << ")" << std::endl;
#endif

						possible_remove_invariables.insert(&precondition->getTerms()[property->getIndex()]->getDomain(action_step_id, bindings));
					}
				}
			}
			
			// Prune the possible range.
			std::set<const std::vector<const Object*>*> tmp_set;
			std::set_intersection(possible_remove_invariables.begin(), possible_remove_invariables.end(), action_invariables.begin(), action_invariables.end(), std::inserter(tmp_set, tmp_set.begin()));
			
			action_invariables.clear();
			action_invariables.insert(tmp_set.begin(), tmp_set.end());
		}
		
		if (action_invariables.size() == 1)
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "Invariable action variable: {";
#endif
			const std::vector<const Object*>* invariable_domain = *action_invariables.begin();
			const Variable* invariable_action_variable = action_invariable_variable[invariable_domain];
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			for (std::vector<const Object*>::const_iterator ci = invariable_domain->begin(); ci != invariable_domain->end(); ci++)
			{
				std::cout << **ci;
				if (ci + 1 != invariable_domain->end())
				{
					std::cout << ", ";
				}
			}
			std::cout << "}" << std::endl;

			std::cout << "(" << action.getPredicate() << " ";
			for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ci++)
			{
				const Variable* variable = *ci;
				
				const std::vector<const Object*>& variable_domain = variable->getDomain(action_step_id, bindings);
				if (&variable_domain == invariable_domain)
				{
					std::cout << "*";
				}
				std::cout << variable->getName();
				
				if (ci + 1 != action.getVariables().end())
				{
					std::cout << " ";
				}
			}
			std::cout << ")" << std::endl;
#endif
			property_space_invariables[property_space] = invariable_domain;
			(*property_space_action_invariables)[property_space] = invariable_action_variable;
		}
		else if (action_invariables.size() == 0)
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "No invariable action variable found!" << std::endl;
#endif
			return NULL;
		}
		else
		{
			std::cout << "Multiple action invariables found!" << std::endl;
			assert (false);
			return NULL;
		}
	}
	
	if (property_space_invariables.size() == 0)
	{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Found no invariables, so this transition is not possible" << std::endl;
#endif
		return NULL;
	}

	/**
	 * Now that we know the invariables, make sure none of the persistent nodes are added or removed.
	 */
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::reverse_iterator persistent_ci = persistent_facts.rbegin(); persistent_ci != persistent_facts.rend(); persistent_ci++)
	{
		const BoundedAtom* to_persistent_atom = (*persistent_ci).second;
		
		for (std::vector<const Property*>::const_iterator ci = to_persistent_atom->getProperties().begin(); ci != to_persistent_atom->getProperties().end(); ci++)
		{
			const Property* property = *ci;
			const std::vector<const Object*>* invariable_term = property_space_invariables[&property->getPropertyState().getPropertySpace()];
			
			// Check if the transitions removes this fact.
			for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
	//			std::cout << " v.s. effect: ";
	//			effect->print(std::cout, bindings, action_step_id);
	//			std::cout << std::endl;

				if (effect->isNegative() == to_persistent_atom->getAtom().isNegative() && 
					bindings.canUnify(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()) &&
					&effect->getTerms()[property->getIndex()]->getDomain(action_step_id, bindings) == invariable_term)
				{
	//				std::cout << "Is added!" << std::endl;
	#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "A persistent is added but not removed. This is invalid!" << std::endl;
	#endif
					return NULL;
				}

				if (bindings.affects(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()) &&
					&effect->getTerms()[property->getIndex()]->getDomain(action_step_id, bindings) == invariable_term)
				{
	//				std::cout << "Is deleted!" << std::endl;
	#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "Removed but not added. This is invalid!" << std::endl;
	#endif
					return NULL;
				}
			}
		}
	}
	
	/**
	 * After we have found all the invariable of each property space, check there are no mutex preconditions or effects.
	 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Check mutex relationships..." << std::endl;
#endif

	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
		{
			const Property* bounded_atom_property = *ci;
			const PropertySpace& property_space = bounded_atom_property->getPropertyState().getPropertySpace();
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " * Checking preconditions against the from node atom * ";
			bounded_atom->print(std::cout, bindings);
			std::cout << std::endl;
#endif

			const std::vector<const Object*>* invariable_term = property_space_invariables[&property_space];
			if (invariable_term == NULL)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Could not find the invariable term of ";
				bounded_atom->print(std::cout, bindings);
				std::cout << "[" << bounded_atom_property->getIndex() << "]" << std::endl;
#endif
				continue;
			}

			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << " * * Precondition: ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << std::endl;
#endif
				
				// Make sure the precondition is linked to the invariable.
				const Term* invariable_precondition_term = NULL;
				for (std::map<const PropertySpace*, const std::vector<const Object*>*>::const_iterator ci = property_space_invariables.begin(); ci != property_space_invariables.end(); ci++)
				{
					const std::vector<const Object*>* domain = (*ci).second;
					for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
					{
						const Term* term = *ci;
						if (&term->getDomain(action_step_id, bindings) == domain)
						{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << " * * * The term: ";
							term->print(std::cout, bindings, action_step_id);
							std::cout << " is invariable!" << std::endl;
#endif

#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
							if (invariable_precondition_term != NULL)
							{
								assert (term == invariable_precondition_term);
							}
#endif
							invariable_precondition_term = term;

#ifndef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
							break;
#endif
						}
					}

#ifndef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
					if (invariable_precondition_term != NULL) break;
#endif
				}
				
				if (invariable_precondition_term == NULL)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "Precondition is not relevant, continue!" << std::endl;
#endif
					continue;
				}

				for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
				{
					const PropertyState* property_state = *ci;
					
					for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
					{
						const Property* property = *ci;
						
						if (precondition->getPredicate().getName() == property->getPredicate().getName() &&
							precondition->getPredicate().getArity() == property->getPredicate().getArity())
						{
							InvariableIndex invariable_index = property->getIndex();
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << "Compare if ";
							precondition->print(std::cout, bindings, action_step_id);
							std::cout << "(" << invariable_index << ") is the same as ";
							bounded_atom->print(std::cout, bindings);
							std::cout << "(" << bounded_atom_property->getIndex() << ")" << std::endl;
#endif
							
							if (precondition->getTerms()[invariable_index] != invariable_precondition_term)
							{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
								std::cout << "Invariables don't match, move on!" << std::endl;
#endif
								continue;
							}
							
							if (precondition->getTerms()[invariable_index]->canUnify(action_step_id, *bounded_atom->getAtom().getTerms()[bounded_atom_property->getIndex()], bounded_atom->getId(), bindings))
							{
								if (bounded_atom->isMutexWith(*precondition, action_step_id, bindings, invariable_index))
								{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
									std::cout << "The precondition ";
									precondition->print(std::cout, bindings, action_step_id);
									std::cout << " is mutex with the from fact ";
									bounded_atom->print(std::cout, bindings);
									std::cout << "." << std::endl;
#endif
									return NULL;
								}
							}
						}
					}
				}
			}
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
		{
			const Property* bounded_atom_property = *ci;
			const PropertySpace& bounded_atom_property_space = (*ci)->getPropertyState().getPropertySpace();
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " * Check effects against the to node: ";
			bounded_atom->print(std::cout, bindings);
			std::cout << std::endl;
#endif

			const std::vector<const Object*>* invariable_term = property_space_invariables[&bounded_atom_property_space];
			if (invariable_term == NULL)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << " * * Could not find the invariable term of ";
				bounded_atom->print(std::cout, bindings);
				std::cout << "[" << to_node.getIndex(*bounded_atom) << "]" << std::endl;
#endif
				continue;
			}

			for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << " * * Effect: ";
				effect->print(std::cout, bindings, action_step_id);
				std::cout << std::endl;
#endif

				// Make sure the precondition is linked to the invariable.
				const Term* invariable_effect_term = NULL;
				for (std::map<const PropertySpace*, const std::vector<const Object*>*>::const_iterator ci = property_space_invariables.begin(); ci != property_space_invariables.end(); ci++)
				{
					const std::vector<const Object*>* domain = (*ci).second;
					for (std::vector<const Term*>::const_iterator ci = effect->getTerms().begin(); ci != effect->getTerms().end(); ci++)
					{
						const Term* term = *ci;
						if (&term->getDomain(action_step_id, bindings) == domain)
						{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << " * * * The term: ";
							term->print(std::cout, bindings, action_step_id);
							std::cout << " is invariable!" << std::endl;
#endif

#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
							if (invariable_effect_term != NULL)
							{
								assert (invariable_effect_term == term);
							}
#endif
							invariable_effect_term = term;

#ifndef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
							break;
#endif
						}
					}
#ifndef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
					if (invariable_effect_term != NULL) break;
#endif
				}
				
				if (invariable_effect_term == NULL)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << " * * Effect is not relevant, continue!" << std::endl;
#endif
					continue;
				}
				
				for (std::vector<const PropertyState*>::const_iterator ci = bounded_atom_property_space.getPropertyStates().begin(); ci != bounded_atom_property_space.getPropertyStates().end(); ci++)
				{
					const PropertyState* property_state = *ci;
					
					for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
					{
						const Property* property = *ci;
						
						if (effect->getPredicate().getName() == property->getPredicate().getName() &&
							effect->getPredicate().getArity() == property->getPredicate().getArity())
						{
							InvariableIndex invariable_index = property->getIndex();
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << " * * * Compare if ";
							effect->print(std::cout, bindings, action_step_id);
							std::cout << "(" << invariable_index << ") is the same as ";
							bounded_atom->print(std::cout, bindings);
							std::cout << "(" << bounded_atom_property->getIndex() << ")" << std::endl;
#endif
							
							if (effect->getTerms()[invariable_index] != invariable_effect_term)
							{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
								std::cout << " * * * * Invariables don't match, move on!" << std::endl;
#endif
								continue;
							}
							
							if (effect->getTerms()[invariable_index]->canUnify(action_step_id, *bounded_atom->getAtom().getTerms()[bounded_atom_property->getIndex()], bounded_atom->getId(), bindings))
							{
								if (effect->isNegative() == bounded_atom->getAtom().isNegative() &&
									bounded_atom->isMutexWith(*effect, action_step_id, bindings, invariable_index))
								{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
									std::cout << " * * * * The effect ";
									effect->print(std::cout, bindings, action_step_id);
									std::cout << " is mutex with the to fact ";
									bounded_atom->print(std::cout, bindings);
									std::cout << "." << std::endl;
#endif
									return NULL;
								}
							}
						}
					}
				}
			}
		}
	}
	
	/**
	 * Make sure all the added and deleted facts are accounted for.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> >* precondition_mapping_to_from_node = new std::vector<std::pair<const Atom*, InvariableIndex> >(); // Pair of precondition and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> >* add_effects_mapping_to_to_node = new std::vector<std::pair<const Atom*, InvariableIndex> >();    // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> >* remove_effects_mapping_to_to_node = new std::vector<std::pair<const Atom*, InvariableIndex> >(); // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> >* persistent_preconditions = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	
	std::vector<std::pair<const Atom*, const BoundedAtom*> >* add_effects_to_to_node_bindings = new std::vector<std::pair<const Atom*, const BoundedAtom*> >();
	std::vector<std::pair<const Atom*, const BoundedAtom*> >* precondition_to_from_node_bindings = new std::vector<std::pair<const Atom*, const BoundedAtom*> >();

	for (std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		const PropertySpace* property_space = (*ci).first.first;
		const BalancedPropertySet* balanced_property_set = (*ci).second;
		
		const std::vector<const BoundedAtom*>& added_facts = balanced_property_set->getAddedProperties();
		const std::vector<const BoundedAtom*>& removed_facts = balanced_property_set->getRemovedProperties();
		
		if (added_facts.empty() || removed_facts.empty())
		{
			continue;
		}
		
		const std::vector<const Object*>* invariable_term = property_space_invariables[property_space];
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << " ****************************** " << std::endl;
		std::cout << "Check all added and removed facts are accounted for: " << std::endl;
		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts.begin(); ci != added_facts.end(); ci++)
		{
			std::cout << "+ ";
			(*ci)->print(std::cout, bindings);
			std::cout << std::endl;
		}
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts.begin(); ci != removed_facts.end(); ci++)
		{
			std::cout << "- ";
			(*ci)->print(std::cout, bindings);
			std::cout << std::endl;
		}
#endif

		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts.begin(); ci != added_facts.end(); ci++)
		{
			const BoundedAtom* added_fact = *ci;
			bool is_added = false;
			
			// Find the property which is part of the added fact and the property space which is part of the ballanced set.
			const Property* linked_property = NULL;
			for (std::vector<const PropertyState*>::const_iterator ci = property_space->getPropertyStates().begin(); ci != property_space->getPropertyStates().end(); ci++)
			{
				const PropertyState* property_state = *ci;
				for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
				{
					const Property* property = *ci;
					
					for (std::vector<const Property*>::const_iterator ci = added_fact->getProperties().begin(); ci != added_fact->getProperties().end(); ci++)
					{
						const Property* bounded_atom_property = *ci;
						if (bounded_atom_property == property)
						{
							linked_property = property;
							break;
						}
					}
					
					if (linked_property != NULL) break;
				}
				if (linked_property != NULL) break;
			}
			
			assert (linked_property != NULL);
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " =++> Make sure the added fact: ";
			added_fact->print(std::cout, bindings);
			std::cout << "is accounted for..." << std::endl;
#endif
			
			// Make sure an effect actually added this fact.
			for (std::vector<const Atom*>::const_iterator ci = effects.begin();  ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
				
				if (effect->isNegative() == added_fact->getAtom().isNegative() &&
				    bindings.canUnify(*effect, action_step_id, added_fact->getAtom(), added_fact->getId()) &&
				    &effect->getTerms()[linked_property->getIndex()]->getDomain(action_step_id, bindings) == invariable_term)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "It's added by: ";
					effect->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
#endif
					is_added = true;
					add_effects_mapping_to_to_node->push_back(std::make_pair(effect, linked_property->getIndex()));
					add_effects_to_to_node_bindings->push_back(std::make_pair(effect, added_fact));
					break;
				}
			}
			
			if (!is_added)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "The effect: ";
				added_fact->print(std::cout, bindings);
				std::cout << " is not accounted for..." << std::endl;
#endif
				return NULL;
			}
		}
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Make sure all delete facts are accounted for!" << std::endl;
#endif
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts.begin(); ci != removed_facts.end(); ci++)
		{
			const BoundedAtom* removed_fact = *ci;
			bool is_a_precondition = false;
			bool is_removed = false;

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " =++> Make sure the removed fact: ";
			removed_fact->print(std::cout, bindings);
			std::cout << "is accounted for..." << std::endl;
#endif

			// Find the property which is part of the added fact and the property space which is part of the ballanced set.
			const Property* linked_property = NULL;
			for (std::vector<const PropertyState*>::const_iterator ci = property_space->getPropertyStates().begin(); ci != property_space->getPropertyStates().end(); ci++)
			{
				const PropertyState* property_state = *ci;
				for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
				{
					const Property* property = *ci;
					
					for (std::vector<const Property*>::const_iterator ci = removed_fact->getProperties().begin(); ci != removed_fact->getProperties().end(); ci++)
					{
						const Property* bounded_atom_property = *ci;
						if (bounded_atom_property == property)
						{
							linked_property = property;
							break;
						}
					}
					
					if (linked_property != NULL) break;
				}
				if (linked_property != NULL) break;
			}
			
			assert (linked_property != NULL);
			
			// Make sure an effect actually added this fact.
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin();  ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				
				if (precondition->isNegative() == removed_fact->getAtom().isNegative() &&
				    bindings.canUnify(*precondition, action_step_id, removed_fact->getAtom(), removed_fact->getId()) &&
				    &precondition->getTerms()[linked_property->getIndex()]->getDomain(action_step_id, bindings) == invariable_term)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "It's removed by: ";
					precondition->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
#endif
					precondition_mapping_to_from_node->push_back(std::make_pair(precondition, linked_property->getIndex()));
					precondition_to_from_node_bindings->push_back(std::make_pair(precondition, removed_fact));
					is_a_precondition = true;
					break;
				}
			}
			
			if (!is_a_precondition)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "The removed precondition: ";
				removed_fact->print(std::cout, bindings);
				std::cout << " is not accounted for..." << std::endl;
#endif
				return NULL;
			}
			
			for (std::vector<const Atom*>::const_iterator ci = effects.begin();  ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
				
				if (effect->isNegative() != removed_fact->getAtom().isNegative() &&
				    bindings.canUnify(*effect, action_step_id, removed_fact->getAtom(), removed_fact->getId()) &&
				    &effect->getTerms()[linked_property->getIndex()]->getDomain(action_step_id, bindings) == invariable_term)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "It's removed by: ";
					effect->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
#endif
					remove_effects_mapping_to_to_node->push_back(std::make_pair(effect, linked_property->getIndex()));
					is_removed = true;
					break;
				}
			}
			
			if (!is_removed)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "The precondition is not removed: ";
				removed_fact->print(std::cout, bindings);
				std::cout << " is not accounted for..." << std::endl;
#endif
				return NULL;
			}
		}
	}
	
	/**
	 * Start making the actual bindings!
	 */
	std::map<const PropertySpace*, const std::vector<const Object*>* > invariable_property_space_to_domain_mapping;
	
	for (std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		const PropertySpace* property_space = (*ci).first.first;
//		const std::vector<const Object*>* invariable_term = (*ci).first.second;
		const BalancedPropertySet* balanced_property_set = (*ci).second;
		
		const std::vector<const BoundedAtom*>& added_facts = balanced_property_set->getAddedProperties();
		const std::vector<const BoundedAtom*>& removed_facts = balanced_property_set->getRemovedProperties();
		
		if (added_facts.empty() || removed_facts.empty())
		{
			continue;
		}
		
		const std::vector<const Object*>* invariable_domain = property_space_invariables[property_space];
		
		std::map<const PropertySpace*, const std::vector<const Object*>* >::const_iterator ci = invariable_property_space_to_domain_mapping.find(property_space);
		
		if (ci != invariable_property_space_to_domain_mapping.end())
		{
			assert ((*ci).second == invariable_domain);
		}
		else
		{
			invariable_property_space_to_domain_mapping[property_space] = invariable_domain;
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "The invariable of the property space: " << *property_space << " is ";
			for (std::vector<const Object*>::const_iterator ci = invariable_domain->begin(); ci != invariable_domain->end(); ci++)
			{
				std::cout << **ci;
				if (ci != invariable_domain->end() - 1)
				{
					std::cout << ", ";
				}
			}
			std::cout << std::endl;
#endif
		}
	}
	
	/**
	 * Test the optional preconditions.
	 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify the optional preconditions!" << std::endl;
#endif

	for (std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		const PropertySpace* property_space = (*ci).first.first;
//		const std::vector<const Object*>* invariable_term = (*ci).first.second;
		const BalancedPropertySet* balanced_property_set = (*ci).second;
		
		const std::vector<const BoundedAtom*>& added_facts = balanced_property_set->getAddedProperties();
		const std::vector<const BoundedAtom*>& removed_facts = balanced_property_set->getRemovedProperties();
		
		if (!added_facts.empty() && !removed_facts.empty())
		{
			continue;
		}

		/**
		 * If no facts are added, than some facts must have been removed and these facts must be present in the set of preconditions.
		 */
		if (added_facts.empty())
		{
///#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
///			std::cout << "Unify the optional preconditions..." << std::endl;
///#endif
			if (!unifyDTGAtomsWithAction(removed_facts, from_node, preconditions, action_step_id, action, bindings, *invariable_property_space_to_domain_mapping[property_space]))
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "FAIL!" << std::endl;
#endif
				return NULL;
			}
		}
		/**
		 * If facts have been added, it means that either:
		 * 1) They are part of the effects, or
		 * 2) If the effects do not account for them then they must be present as preconditions.
		 */
		else
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "Unify the optional effects..." << std::endl;
#endif
			if (!unifyDTGAtomsWithAction(added_facts, to_node, effects, action_step_id, action, bindings, *invariable_property_space_to_domain_mapping[property_space]))
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << "Could not unify the optional effects, try as a precondition..." << std::endl;
#endif
				if (!unifyDTGAtomsWithAction(added_facts, to_node, preconditions, action_step_id, action, bindings, *invariable_property_space_to_domain_mapping[property_space]))
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "FAIL!" << std::endl;
#endif
					return NULL;
				}
			}
		}
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify the effects!" << std::endl;
#endif
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = add_effects_to_to_node_bindings->begin(); ci != add_effects_to_to_node_bindings->end(); ci++)
	{
		const Atom* added_effect = (*ci).first;
		const BoundedAtom* to_node_atom = (*ci).second;
		
		if (!bindings.unify(to_node_atom->getAtom(), to_node_atom->getId(), *added_effect, action_step_id))
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::createTransition] Could not perform the actual bindings on effects!" << std::endl;
			to_node_atom->print(std::cout, bindings);
			std::cout << " couldn't bind with: ";
			added_effect->print(std::cout, bindings, action_step_id);
			std::cout << std::endl;
#endif
			return NULL;
		}
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify the preconditions!" << std::endl;
#endif
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = precondition_to_from_node_bindings->begin(); ci != precondition_to_from_node_bindings->end(); ci++)
	{
		const Atom* precondition = (*ci).first;
		const BoundedAtom* from_node_atom = (*ci).second;

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "[Transition::createTransition] Unify the precondition: ";
		precondition->print(std::cout, bindings, action_step_id);
		std::cout << " with " << std::endl;
		from_node_atom->print(std::cout, bindings);
		std::cout << "." << std::endl;
#endif
		
		if (!bindings.unify(from_node_atom->getAtom(), from_node_atom->getId(), *precondition, action_step_id))
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::createTransition] Could not perform the actual bindings on preconditions!" << std::endl;
			from_node_atom->print(std::cout, bindings);
			std::cout << " couldn't bind with: ";
			precondition->print(std::cout, bindings, action_step_id);
			std::cout << std::endl;
#endif
			return NULL;
		}
	}
	
	/**
	 * Post process by checking if the transitions did not violate any static preconditions.
	 */
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		if (precondition->getPredicate().isStatic())
		{
			bool is_supported = false;
			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
			{
				const Atom* initial_fact = *ci;
				if (bindings.canUnify(*initial_fact, Step::INITIAL_STEP, *precondition, action_step_id))
				{
					is_supported = true;
					break;
				}
			}
			
			if (!is_supported)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "[Transition::createTransition] The static precondition: ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << " is not supported!" << std::endl;
#endif
				return NULL;
			}
		}
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify the persistent facts!" << std::endl;
#endif
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
	{
		const BoundedAtom* from_node_persistent_fact = (*ci).first;
		const BoundedAtom* to_node_persistent_fact = (*ci).second;
		
		for (unsigned int i = 0; i < from_node_persistent_fact->getAtom().getArity(); i++)
		{
			// Merge the terms together.
			bindings.unify(from_node_persistent_fact->getAtom(), from_node_persistent_fact->getId(), to_node_persistent_fact->getAtom(), to_node_persistent_fact->getId());
		}
	}

	/**
	 * All the facts in a DTG node are part of a balanced set. All preconditions which contain this invariable and could unify with
	 * a fact of the from node should do so. If the said precondition contains a term which is part of a balanced set, then this
	 * term is processed in the same way until all terms which are part of a balanced set are discovered and all preconditions which
	 * can be unified with a term in the from node are.
	 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify all preconditions containing an invariable." << std::endl;
#endif

	std::set<const std::vector<const Object*>* > open_list_balanced_domains;

	for (std::map<const PropertySpace*, const Variable*>::const_iterator ci = property_space_action_invariables->begin(); ci != property_space_action_invariables->end(); ci++)
	{
		const Variable* invariable = (*ci).second;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "\tThe invariable: ";
		invariable->print(std::cout, bindings, action_step->getStepId());
		std::cout << "(" << &invariable->getDomain(action_step->getStepId(), bindings) << ")" << std::endl;
#endif
		open_list_balanced_domains.insert(&invariable->getDomain(action_step->getStepId(), bindings));
	}
	
	std::set<const std::vector<const Object*>* > closed_list_balanced_domains;
	
	while (!open_list_balanced_domains.empty())
	{
		const std::vector<const Object*>* balanced_domain = *(open_list_balanced_domains.begin());
		open_list_balanced_domains.erase(open_list_balanced_domains.begin());
		
		closed_list_balanced_domains.insert(balanced_domain);
		
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;
			
	#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "Process: ";
			precondition->print(std::cout, bindings, action_step->getStepId());
			std::cout << std::endl;
	#endif
			
			for (std::vector<const Term*>::const_iterator precondition_terms_ci = precondition->getTerms().begin(); precondition_terms_ci != precondition->getTerms().end(); precondition_terms_ci++)
			{
				const Term* term = *precondition_terms_ci;
				unsigned int precondition_term_index = std::distance(precondition->getTerms().begin(), precondition_terms_ci);
				
				const std::vector<const Object*>& precondition_term_domain = term->getDomain(action_step->getStepId(), bindings);
				if (&precondition_term_domain == balanced_domain)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "\tContains an invariable!" << std::endl;
#endif

					// Look for a fact in the from dtg node to unify with which contains the same invariable.
					for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
					{
						const BoundedAtom* bounded_atom = *ci;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << "\t\tCompare v.s. ";
						bounded_atom->print(std::cout, bindings);
						std::cout << std::endl;
						
						std::cout << "Is: ";
						term->print(std::cout, bindings, action_step->getStepId());
						std::cout << " the same as the " << precondition_term_index << "th term of the bounded atom?" << std::endl;
						
						std::cout << "Can the predicate be substituted: " << bounded_atom->getAtom().getPredicate().canSubstitute(precondition->getPredicate()) << "?" << std::endl;
						if (bounded_atom->getAtom().getPredicate().canSubstitute(precondition->getPredicate()))
						{
							std::cout << "Are the terms the same: " << term->isTheSameAs(action_step->getStepId(), *bounded_atom->getAtom().getTerms()[precondition_term_index], bounded_atom->getId(), bindings) << "?" << std::endl;
						}
						
#endif
						
						if (precondition->getPredicate().canSubstitute(bounded_atom->getAtom().getPredicate()) &&
						    term->isTheSameAs(action_step->getStepId(), *bounded_atom->getAtom().getTerms()[precondition_term_index], bounded_atom->getId(), bindings))
						{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << "[EXTRA] Unify the precondition: ";
							precondition->print(std::cout, bindings, action_step->getStepId());
							std::cout << std::endl;
#endif
							
							if (!bindings.unify(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, action_step->getStepId()))
							{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
								std::cout << "Precondition could not be unified, transition is not possible!";
#endif
								return NULL;
							}
						}
					}
					
					// Check which other terms of this precondition are considered to be balanced.
					for (unsigned int i = 0; i < precondition->getArity(); i++)
					{
						const std::vector<const Object*>& other_precondition_term_domain = precondition->getTerms()[i]->getDomain(action_step->getStepId(), bindings);
						if (closed_list_balanced_domains.count(&other_precondition_term_domain) == 0)
						{
							open_list_balanced_domains.insert(&other_precondition_term_domain);
						}
					}
				}
			}
		}
	}

	/**
	 * Store for each precondition which variable is invariable for easy access later (getAllPreconditions()). This part assumes
	 * a transition can only work on a single balanced set, so a transition cannot affect two different sets of property spaces.
	 * TODO: Make this more appearant in the function, but splitting up the property_space_balanced_sets into a property_balanced_set
	 * and a separate set for optional preconditions.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> >* all_precondition_mappings = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;

		for (std::map<std::pair<const PropertySpace*, const std::vector<const Object*>* >, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
		{
			const PropertySpace* property_space = (*ci).first.first;
			BalancedPropertySet* balanced_property_set = (*ci).second;
			const std::vector<const BoundedAtom*>& added_facts = balanced_property_set->getAddedProperties();
			const std::vector<const BoundedAtom*>& removed_facts = balanced_property_set->getRemovedProperties();
			
			if (added_facts.empty() || removed_facts.empty())
			{
				continue;
			}
			
			const std::vector<const Object*>* invariable_domain = property_space_invariables[property_space];
			
			bool found_binding = false;
			for (InvariableIndex i = 0; i < precondition->getArity(); i++)
			{
				const Term* term = precondition->getTerms()[i];
				
				if (&term->getDomain(action_step_id, bindings) == invariable_domain)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "QQQ Precondition: ";
					precondition->print(std::cout, bindings, action_step_id);
					std::cout << " (" << i << ")" << std::endl;
#endif
					found_binding = true;
					
					all_precondition_mappings->push_back(std::make_pair(precondition, i));
					break;
				}
			}
			
			if (!found_binding)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "QQQ Precondition: ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << " (No binding!)" << std::endl;
#endif
				all_precondition_mappings->push_back(std::make_pair(precondition, NO_INVARIABLE_INDEX));
			}
		}
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Success!" << std::endl;
	std::cout << "Created a transition from " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), action_step->getStepId());
	std::cout << std::endl;
#endif
	return new Transition(action_step, from_node, to_node, *precondition_mapping_to_from_node, *add_effects_mapping_to_to_node, *remove_effects_mapping_to_to_node, *persistent_preconditions, *property_space_action_invariables, *all_precondition_mappings);
}

bool Transition::unifyDTGAtomsWithAction(const std::vector<const BoundedAtom*>& facts_to_unify, const DomainTransitionGraphNode& dtg_node, const std::vector<const Atom*>& action_atoms, StepID action_step_id, const Action& action, Bindings& bindings, const std::vector<const Object*>& invariable_domain)
{
	for (std::vector<const BoundedAtom*>::const_iterator ci = facts_to_unify.begin(); ci != facts_to_unify.end(); ci++)
	{
		const BoundedAtom* persistent_fact = *ci;
		InvariableIndex invariable_index = dtg_node.getIndex(*persistent_fact);
		if (invariable_index == INVALID_INDEX_ID)
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "The persistent fact: ";
			persistent_fact->print(std::cout, bindings);
			std::cout << " has no invariable!" << std::endl;
#endif
			continue;
///			assert (false);
		}
		
		bool unified = false;
		
		for (std::vector<const Atom*>::const_iterator ci = action_atoms.begin(); ci != action_atoms.end(); ci++)
		{
			const Atom* dtg_node_atom = *ci;
			
			if (dtg_node_atom->getPredicate().getName() == persistent_fact->getAtom().getPredicate().getName() &&
			    dtg_node_atom->getPredicate().getArity() == persistent_fact->getAtom().getArity() &&
			    dtg_node_atom->isNegative() == persistent_fact->getAtom().isNegative())
			{
				/**
				 * Only allow optional preconditions to merge if they do not refer to the invariable of the balanced set.
				 * TODO: Is this correct?
				 */
				if (dtg_node_atom->getTerms()[invariable_index]->canUnify(action_step_id, *persistent_fact->getAtom().getTerms()[invariable_index], persistent_fact->getId(), bindings) &&
				    &dtg_node_atom->getTerms()[dtg_node.getIndex(*persistent_fact)]->getDomain(action_step_id, bindings) != &invariable_domain)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "Unify the optional atom: ";
					persistent_fact->print(std::cout, bindings);
					std::cout << " with: ";
					dtg_node_atom->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
#endif

					if (!bindings.unify(persistent_fact->getAtom(), persistent_fact->getId(), *dtg_node_atom, action_step_id))
					{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << "Could not bind the optional atom: " << std::endl;
						persistent_fact->print(std::cout, bindings);
						std::cout << " with: ";
						dtg_node_atom->print(std::cout, bindings, action_step_id);
						std::cout << std::endl;
#endif
						return false;
					}
					else
					{
						unified = true;
						break;
					}
				}
			}
		}
		
		if (!unified)
		{
			return false;
		}
	}
	
	return true;
}

Transition::Transition(MyPOP::StepPtr step, MyPOP::SAS_Plus::DomainTransitionGraphNode& from_node, MyPOP::SAS_Plus::DomainTransitionGraphNode& to_node, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& preconditions, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& effects, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& affected, const std::vector<std::pair<const Atom*, InvariableIndex> >& persistent_preconditions, const std::map<const PropertySpace*, const Variable*>& action_invariables, const std::vector<std::pair<const Atom*, InvariableIndex> >& all_precondition_mappings)
	: step_(step), from_node_(&from_node), to_node_(&to_node), preconditions_(&preconditions), effects_(&effects), affected_(&affected), persistent_preconditions_(&persistent_preconditions), action_invariables_(&action_invariables), all_precondition_mappings_(&all_precondition_mappings)
{
/*	std::cout << "New transition: " << step->getAction() << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		(*ci).first->print(std::cout);
		std::cout << "(" << (*ci).second << "), ";
	}
	std::cout << "." << std::endl;*/
}

Transition* Transition::migrateTransition(const std::vector<const Atom*>& initial_facts, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node) const
{
	StepID new_id = from_node.getDTG().getBindings().createVariableDomains(step_->getAction());
	StepPtr new_step(new Step(new_id, step_->getAction()));
	
//	std::cout << "Migrate: " << *this << "." << std::endl;
	
	// Update the variables.
	for (std::vector<const Variable*>::const_iterator ci = step_->getAction().getVariables().begin(); ci != step_->getAction().getVariables().end(); ci++)
	{
		unsigned int action_variable_index = std::distance(step_->getAction().getVariables().begin(), ci);
		
//		std::cout << "Handle the " << action_variable_index << "th action variable!" << std::endl;
		
		const std::vector<const Object*>& org_action_variable_domain = (*ci)->getDomain(step_->getStepId(), from_node_->getDTG().getBindings());
		bool found_matching_from_variable = false;
		for (unsigned int i = 0; i < from_node_->getAtoms().size(); i++)
		{
			const BoundedAtom* org_from_fact = from_node_->getAtoms()[i];
			
			for (unsigned int j = 0; j < org_from_fact->getAtom().getArity(); j++)
			{
				const Term* org_term = org_from_fact->getAtom().getTerms()[j];
				const std::vector<const Object*>& org_term_domain = org_term->getDomain(org_from_fact->getId(), from_node_->getDTG().getBindings());
				
				if (&org_action_variable_domain == &org_term_domain)
				{
					if (new_step->getAction().getVariables()[action_variable_index]->unify(new_step->getStepId(), *from_node.getAtoms()[i]->getAtom().getTerms()[j], from_node.getAtoms()[i]->getId(), from_node.getDTG().getBindings()))
					{
//						std::cout << "The " << i << "th atom and " << j << "th term match in the from node!" << std::endl;
						found_matching_from_variable = true;
						break;
					}
					else
					{
//						std::cout << "The " << i << "th atom and " << j << "th term match in the from node! - NULL" << std::endl;
						return NULL;
					}
				}
			}
			
			if (found_matching_from_variable) break;
		}
		
		bool found_matching_to_variable = false;
		for (unsigned int i = 0; i < to_node_->getAtoms().size(); i++)
		{
			const BoundedAtom* org_to_fact = to_node_->getAtoms()[i];
//			std::cout << "Process: ";
//			org_to_fact->print(std::cout, to_node_->getDTG().getBindings());
//			std::cout << std::endl;
			
			for (unsigned int j = 0; j < org_to_fact->getAtom().getArity(); j++)
			{
				const Term* org_term = org_to_fact->getAtom().getTerms()[j];
				const std::vector<const Object*>& org_term_domain = org_term->getDomain(org_to_fact->getId(), to_node_->getDTG().getBindings());
				
				if (&org_action_variable_domain == &org_term_domain)
				{
					if (new_step->getAction().getVariables()[action_variable_index]->unify(new_step->getStepId(), *to_node.getAtoms()[i]->getAtom().getTerms()[j], to_node.getAtoms()[i]->getId(), to_node.getDTG().getBindings()))
					{
//						std::cout << "The " << i << "th atom and " << j << "th term match in the to node!" << std::endl;
						found_matching_to_variable = true;
						break;
					}
					else
					{
//						std::cout << "The " << i << "th atom and " << j << "th term match in the to node! - NULL" << std::endl;
						return NULL;
					}
				}
			}
			
			if (found_matching_to_variable) break;
		}
		
		if (found_matching_from_variable || found_matching_to_variable) continue;
		
		// Otherwise just make the domains equal to one another.
		new_step->getAction().getVariables()[action_variable_index]->makeDomainEqualTo(new_step->getStepId(), org_action_variable_domain, to_node_->getDTG().getBindings());
	}
	
	// Check if the newly constructed transition is actually viable!
	for (std::vector<const Variable*>::const_iterator ci = new_step->getAction().getVariables().begin(); ci != new_step->getAction().getVariables().end(); ci++)
	{
		const std::vector<const Object*>& new_action_variable_domain = (*ci)->getDomain(new_step->getStepId(), from_node.getDTG().getBindings());
		if (new_action_variable_domain.empty()) return NULL;
	}
	
	// Check the static preconditions if they are actually present.
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &new_step->getAction().getPrecondition());
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		if (!precondition->getPredicate().isStatic()) continue;
		
		bool is_supported = false;
		
		for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
		{
			const Atom* initial_fact = *ci;
			if (!initial_fact->getPredicate().isStatic()) continue;
			if (from_node.getDTG().getBindings().canUnify(*precondition, new_step->getStepId(), *initial_fact, Step::INITIAL_STEP))
			{
				is_supported = true;
				break;
			}
		}
		
		if (!is_supported) return NULL;
	}
	
	// After the transition is made and possible, update the bindings! :)
	return new Transition(new_step, from_node, to_node, *preconditions_, *effects_, *affected_, *persistent_preconditions_, *action_invariables_, *all_precondition_mappings_);
/*	std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >* t_preconditions = new std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >(*preconditions_);
	std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >* effects = new std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >(*effects_);
	std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >* affected = new std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >(*affected_); 
	std::vector<std::pair<const Atom*, InvariableIndex> >* persistent_preconditions = new std::vector<std::pair<const Atom*, InvariableIndex> >(*persistent_preconditions_); 
	std::map< const MyPOP::SAS_Plus::PropertySpace*, const MyPOP::Variable* >* action_invariables = new std::map< const MyPOP::SAS_Plus::PropertySpace*, const MyPOP::Variable* >(*action_invariables_);
	std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >* all_precondition_mappings = new std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >(*all_precondition_mappings_);

	new_step->getAction().print(std::cout, from_node.getDTG().getBindings(), new_step->getStepId());
	std::cout << std::endl;
	
	// Update the references.
	return new Transition(new_step, from_node, to_node, *t_preconditions, *effects, *affected, *persistent_preconditions, *action_invariables, *all_precondition_mappings);
*/
}

Transition* Transition::cloneWithNodes(const std::vector<const Atom*>& initial_facts) const
{
	DomainTransitionGraphNode* new_dtg_from_node = new DomainTransitionGraphNode(*from_node_, false);
	DomainTransitionGraphNode* new_dtg_to_node = new DomainTransitionGraphNode(*to_node_, false);
	Transition* new_transition = Transition::createTransition(step_->getAction(), *new_dtg_from_node, *new_dtg_to_node, initial_facts);
	
	if (new_transition == NULL)
	{
		assert (false);
	}
	
	// Fix the domains to match the original transition.
	for (std::vector<const Variable*>::const_iterator ci = step_->getAction().getVariables().begin(); ci != step_->getAction().getVariables().end(); ci++)
	{
		(*ci)->makeDomainEqualTo(step_->getStepId(), **ci, new_transition->getStep()->getStepId(), from_node_->getDTG().getBindings());
	}

	return new_transition;
}

void Transition::setStep(StepPtr step)
{
	step_ = step;
}

bool Transition::isPreconditionRemoved(const Atom& precondition, const Bindings& bindings) const
{
	const std::vector<const Atom*>& effects = getStep()->getAction().getEffects();
	for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		const Atom* effect = *ci;
		
		if (effect->isNegative() &&
		    bindings.areIdentical(*effect, getStep()->getStepId(), precondition, getStep()->getStepId()))
		{
			return true;
		}
	}
	
	return false;
}

bool Transition::achieves(const BoundedAtom& bounded_atom) const
{
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effects_->begin(); ci != effects_->end(); ci++)
	{
		const Atom* affected_atom = (*ci).first;

		if (affected_atom->getPredicate() != bounded_atom.getAtom().getPredicate())
		{
			continue;
		}

		if (shareVariableDomains(bounded_atom, *affected_atom))
		{
			return true;
		}
	}

	return false;
}

bool Transition::affects(const BoundedAtom& bounded_atom) const
{
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = affected_->begin(); ci != affected_->end(); ci++)
	{
		const Atom* affected_atom = (*ci).first;

		if (affected_atom->getPredicate() != bounded_atom.getAtom().getPredicate())
		{
			continue;
		}

		if (shareVariableDomains(bounded_atom, *affected_atom))
		{
			return true;
		}
	}

	return false;
}

bool Transition::isPreconditionPersistent(const Atom& atom, InvariableIndex index) const
{
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = persistent_preconditions_->begin(); ci != persistent_preconditions_->end(); ci++)
	{
		const Atom* persistent_atom = (*ci).first;
		InvariableIndex persistent_index = (*ci).second;
		std::cout << "is (" << &atom << "){" << index << "} persistent with: ";
		persistent_atom->print(std::cout, from_node_->getDTG().getBindings(), step_->getStepId());
		std::cout << "(" << persistent_atom << "){" << persistent_index << "}?" << std::endl;
		
		if (&atom == persistent_atom && persistent_index == index)
		{
			return true;
		}
	}
	return false;
}

bool Transition::shareVariableDomains(const BoundedAtom& bounded_atom, const Atom& atom) const
{
	for (std::vector<const Term*>::const_iterator ci = bounded_atom.getAtom().getTerms().begin(); ci != bounded_atom.getAtom().getTerms().end(); ci++)
	{
		const Term* term1 = *ci;

		bool is_linked = false;
		for (std::vector<const Term*>::const_iterator ci = atom.getTerms().begin(); ci != atom.getTerms().end(); ci++)
		{
			const Term* term2 = *ci;
			if (term1->isTheSameAs(bounded_atom.getId(), *term2, step_->getStepId(), from_node_->getDTG().getBindings()))
			{
				is_linked = true;
				break;
			}
		}

		if (!is_linked)
		{
			return false;
		}
	}

	return true;
}

bool Utilities::TransitionToNodeEquals::operator()(const Transition* transition, const DomainTransitionGraphNode* dtg_node) const
{
	return &transition->getToNode() == dtg_node;
}

std::ostream& operator<<(std::ostream& os, const Transition& transition)
{
	os << "Transition from: " << std::endl;
	transition.getFromNode().print(os);
	os << std::endl << " to " << std::endl;
	transition.getToNode().print(os);
	os << "[" << transition.getStep()->getAction() << "]" << std::endl;
	
	std::vector<std::pair<const Atom*, InvariableIndex> > all_preconditions = transition.getAllPreconditions();
	os << "All preconditions: " << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions.begin(); ci != all_preconditions.end(); ci++)
	{
		(*ci).first->print(os, transition.getFromNode().getDTG().getBindings(), transition.getStep()->getStepId());
		os << " (" << (*ci).second << ") Ox" << (*ci).first << "." << std::endl;
	}
	
	std::vector<std::pair<const Atom*, InvariableIndex> > effects = transition.getEffects();
	os << "All effects: " << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		(*ci).first->print(os, transition.getToNode().getDTG().getBindings(), transition.getStep()->getStepId());
		os << " (" << (*ci).second << ") Ox" << (*ci).first << "." << std::endl;
	}
	
	std::vector<std::pair<const Atom*, InvariableIndex> > persistent_facts = transition.getAllPersistentPreconditions();
	os << "All persistent preconditions: " << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
	{
		(*ci).first->print(os, transition.getToNode().getDTG().getBindings(), transition.getStep()->getStepId());
		os << " (" << (*ci).second << ") Ox" << (*ci).first << "." << std::endl;
	}
	return os;
}

};

};
