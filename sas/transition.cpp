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

//#define ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
//#define ENABLE_MYPOP_SAS_TRANSITION_DEBUG

namespace MyPOP {

namespace SAS_Plus {

bool CompareBalancedPropertySet::operator()(const BalancedPropertySet& lhs, const BalancedPropertySet& rhs) const
{
	if (lhs.property_space_ < rhs.property_space_)
		return true;
	
	if (lhs.property_space_ == rhs.property_space_)
		return true;
	
	return false;
}
	
BalancedPropertySet::BalancedPropertySet(const PropertySpace& property_space)
	: property_space_(&property_space)
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

Transition* Transition::createTransition(const Action& action, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node)
{
	Bindings& bindings = from_node.getDTG().getBindings();
	
	// Before making the actual transitions, check if this transition is even possible.
	std::map<const PropertySpace*, BalancedPropertySet*> property_space_balanced_sets;
	{
		StepID new_action_step_id = bindings.createVariableDomains(action);
		StepPtr new_step(new Step(new_action_step_id, action));
		
		DomainTransitionGraphNode* from_node_clone = new DomainTransitionGraphNode(from_node);
		DomainTransitionGraphNode* to_node_clone = new DomainTransitionGraphNode(to_node);
	
		Transition* transition = createTransition(new_step, *from_node_clone, *to_node_clone, property_space_balanced_sets);
		
		bool contains_empty_variable_domain = false;
		for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ++ci)
		{
			const std::vector<const Object*>& variable_domain = (*ci)->getDomain(new_action_step_id, bindings);
			if (variable_domain.empty())
			{
				contains_empty_variable_domain = true;
			}
		}
		
		delete from_node_clone;
		delete to_node_clone;
		if (transition == NULL || contains_empty_variable_domain)
		{
			return NULL;
		}
		delete transition;
	}
	
	/**
	 * Store per property state a pair of: removed properties and added properties.
	 * TODO: For recursive structures (Blocksworld / Depots) - store a per instance balanced set.
	 */
	StepID new_action_step_id = bindings.createVariableDomains(action);
	StepPtr new_step(new Step(new_action_step_id, action));
	property_space_balanced_sets.clear();
	
	Transition* transition = createTransition(new_step, from_node, to_node, property_space_balanced_sets);
	
	for (std::map<const PropertySpace*, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		delete (*ci).second;
	}
	
	if (transition != NULL)
	{
		assert (transition->getFromNodePreconditions().size() == from_node.getAtoms().size());
		assert (transition->getToNodeEffects().size() == to_node.getAtoms().size());
	}
	
	return transition;
}

Transition* Transition::createSimpleTransition(const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node)
{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createSimpleTransition] " << from_node << " >>>==-> " << to_node << std::endl;
#endif
	
	// Search for the effect achieving the fact in the to node.
	StepID action_step_id = action_step->getStepId();
	const Action& action = action_step->getAction();
	
	assert (to_node.getAtoms().size() == 1);
	const BoundedAtom* effect_to_achieve = to_node.getAtoms()[0];
	
	Bindings& bindings = from_node.getDTG().getBindings();
	
	const std::vector<const Atom*>& effects = action_step->getAction().getEffects();
	
	// No preconditions match up, because the precondition is negative!
	std::vector<std::pair<const Atom*, InvariableIndex> >* preconditions_in_from_node = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	
	std::vector<std::pair<const Atom*, InvariableIndex> >* effects_in_to_node = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		if ((*ci)->isNegative() == effect_to_achieve->getAtom().isNegative() && bindings.canUnify(**ci, action_step_id, effect_to_achieve->getAtom(), effect_to_achieve->getId()))
		{
			bindings.unify(**ci, action_step_id, effect_to_achieve->getAtom(), effect_to_achieve->getId());
			effects_in_to_node->push_back(std::make_pair(*ci, NO_INVARIABLE_INDEX));
			break;
		}
	}
	
	// Check that none of the variable domains are empty.
	for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ++ci)
	{
		const std::vector<const Object*>& variable_domain = (*ci)->getDomain(action_step_id, bindings);
		if (variable_domain.empty())
		{
			delete effects_in_to_node;
			delete preconditions_in_from_node;
			return NULL;
		}
	}
	
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &action.getPrecondition());
	
	/**
	 * If a action variable is not present in the preconditions it will be marked as 'free'.
	 */
	std::set<const Term*>* free_variables = new std::set<const Term*>();
	free_variables->insert(action.getVariables().begin(), action.getVariables().end());
	
	/**
	 * Post process by checking if the transitions did not violate any static preconditions.
	 */
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
		{
			free_variables->erase(*ci);
		}
	}

	/**
	 * Store for each precondition which variable is invariable for easy access later (getAllPreconditions()). This part assumes
	 * a transition can only work on a single balanced set, so a transition cannot affect two different sets of property spaces.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> >* all_precondition_mappings = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		all_precondition_mappings->push_back(std::make_pair(precondition, NO_INVARIABLE_INDEX));
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Pre: ";
		precondition->print(std::cout);
		std::cout << "." << std::endl;
#endif
	}

	std::vector<std::pair<const Atom*, InvariableIndex> >* all_effect_mappings = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		const Atom* effect = *ci;
		all_effect_mappings->push_back(std::make_pair(effect, NO_INVARIABLE_INDEX));
	}
	
	std::vector<std::pair<unsigned int, unsigned int> >* persistent_sets = new std::vector<std::pair<unsigned int, unsigned int> >();
	std::vector<std::pair<unsigned int, unsigned int> >* precondition_index_to_to_node = new std::vector<std::pair<unsigned int, unsigned int> >();
	
	Transition* transition = new Transition(action_step, from_node, to_node, *all_precondition_mappings, *preconditions_in_from_node, *all_effect_mappings, *effects_in_to_node, *persistent_sets, *precondition_index_to_to_node, *free_variables);
	if (transition != NULL)
	{
		assert (transition->getFromNodePreconditions().size() == from_node.getAtoms().size());
		assert (transition->getToNodeEffects().size() == to_node.getAtoms().size());
	}
	return transition;
}

Transition* Transition::createTransition(const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, std::map<const PropertySpace*, BalancedPropertySet*>& property_space_balanced_sets)
{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << std::endl << std::endl;
	std::cout << "[Transition::createTransition] " << std::endl;
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
	 * 3) If a fact is present in both nodes, the action must either have deleted and added the fact or not touched at all (persistent).
	 * 4) The action should either remove or add something.
	 * If any of these rules are broken, the action cannot be applied.
	 */
	
	/**
	 * Persistent facts appear in both the start and end node and are not affected by the transition. They are stored 
	 * as <from_node, to_node>.
	 */
	std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> > persistent_facts;

	/**
	 * Check which facts in the from node are removed and which are still present in the to node. Those which are still present 
	 * are marked as 'possible persistent'. Later we will check if this is actually the case or if a fact is removed and an identical
	 * facts is added in its stead.
	 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Check for persistent facts." << std::endl;
#endif
	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* from_fact = *ci;
/*#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "From fact: ";
		from_fact->print(std::cout, bindings);
		std::cout << "." << std::endl;
		std::cout << "Properties: ";
		for (std::vector<const Property*>::const_iterator ci = from_fact->getProperties().begin(); ci != from_fact->getProperties().end(); ci++)
		{
			std::cout << **ci << ", ";
		}
		std::cout << "." << std::endl;
#endif*/
		
		for (std::vector<const Property*>::const_iterator ci = from_fact->getProperties().begin(); ci != from_fact->getProperties().end(); ci++)
		{
			// Check if the property space this from_fact belongs to has already been created.
			const Property* from_fact_property = *ci;
			const PropertySpace& from_fact_property_space = from_fact_property->getPropertyState().getPropertySpace();

			BalancedPropertySet* balanced_property_set = NULL;
			
			std::map<const PropertySpace*, BalancedPropertySet*>::iterator property_space_i = property_space_balanced_sets.find(&from_fact_property_space);
			if (property_space_i == property_space_balanced_sets.end())
			{
				balanced_property_set = new BalancedPropertySet(from_fact_property_space);
				property_space_balanced_sets[&from_fact_property_space] = balanced_property_set;
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
/*#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "To fact: ";
				to_fact->print(std::cout, bindings);
				std::cout << "." << std::endl;
				std::cout << "Properties: ";
				for (std::vector<const Property*>::const_iterator ci = to_fact->getProperties().begin(); ci != to_fact->getProperties().end(); ci++)
				{
					std::cout << **ci << ", ";
				}
				std::cout << "." << std::endl;
#endif*/
				
				// Check if there is a property in the to_fact which overlaps with that of the from fact.
				for (std::vector<const Property*>::const_iterator ci = to_fact->getProperties().begin(); ci != to_fact->getProperties().end(); ci++)
				{
					// Check if the property space this from_fact belongs to has already been created.
					const Property* to_fact_property = *ci;

					// If the same fact appears in the to node we assume it is not deleted and thus is persistent. The next block of code
					// determines if this is really the case or if the action deletes and adds this fact.
					if (*from_fact_property == *to_fact_property &&
					    to_fact->getAtom().isNegative() == from_fact->getAtom().isNegative())
					{
						if (bindings.areEquivalent(from_fact->getAtom(), from_fact->getId(), to_fact->getAtom(), to_fact->getId()))
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
			std::map<const PropertySpace*, BalancedPropertySet*>::iterator property_space_i = property_space_balanced_sets.find(&to_fact_property_space);
			
			if (property_space_i == property_space_balanced_sets.end())
			{
				balanced_property_set = new BalancedPropertySet(to_fact_property_space);
				property_space_balanced_sets[&to_fact_property_space] = balanced_property_set;
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
					    to_fact->getAtom().isNegative() == from_fact->getAtom().isNegative())
					{
						if (bindings.areEquivalent(to_fact->getAtom(), to_fact->getId(), from_fact->getAtom(), from_fact->getId()))
						{
							is_added = false;
							break;
						}
					}
				}
				
				if (!is_added) break;
			}
			
			if (is_added)
			{
				balanced_property_set->addProperty(*to_fact);
			}
		}
	}

	StepID action_step_id = action_step->getStepId();
	const Action& action = action_step->getAction();
	
	const std::vector<const Atom*>& effects = action_step->getAction().getEffects();
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &action.getPrecondition());

	/**
	 * Check the facts that are persistent due to the fact that they are removed and added by this action. These are 
	 * not found by the previous analysis because we only compare the index of the invariable and check if the variable 
	 * domains overlap. An action is invalid if it does not interact with the nodes at all, so an action which adds and 
	 * removes the same fact, e.g. drive-truck removes (at ?truck ?location) and adds (at ?truck ?location). Based on the 
	 * previous analysis we conclude that the action does not interact, but we might discover that the action adds and 
	 * removes a similar fact and does interact with the nodes.
	 * 
	 * For example the transition from: (at truck loc) -> (at truck loc)
	 * at first it seems the fact is persistent, but when we find the effects ¬(at truck loc) and (at truck loc') we conclude
	 * that this is not the case and update the balanced property set accordingly and no longer mark these facts as 
	 * persistent.
	 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Validate: " << persistent_facts.size() << " persistent facts!" << std::endl;
#endif
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

			if (effect->isNegative() == to_persistent_atom->getAtom().isNegative() && 
			    bindings.canUnify(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()))
			{
				is_added = true;
			}

			if (bindings.affects(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()))
			{
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
				const Property* property = *ci;
				const PropertySpace& property_space = property->getPropertyState().getPropertySpace();

				std::map<const PropertySpace*, BalancedPropertySet*>::iterator i = property_space_balanced_sets.find(&property_space);
				
				assert (i != property_space_balanced_sets.end());
				
				(*i).second->addProperty(*to_persistent_atom);
				(*i).second->removeProperty(*from_persistent_atom);

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				to_persistent_atom->print(std::cout, bindings);
				std::cout << "." << std::endl;
#endif
			}
			
			for (std::vector<const Property*>::const_iterator ci = from_persistent_atom->getProperties().begin(); ci != from_persistent_atom->getProperties().end(); ci++)
			{
				const Property* property = *ci;
				const PropertySpace& property_space = property->getPropertyState().getPropertySpace();
				
				std::map<const PropertySpace*, BalancedPropertySet*>::iterator i = property_space_balanced_sets.find(&property_space);
				
				assert (i != property_space_balanced_sets.end());
				
				(*i).second->addProperty(*to_persistent_atom);
				(*i).second->removeProperty(*from_persistent_atom);
			}

			persistent_facts.erase(persistent_ci.base() - 1);
		}
	}
	
	/**
	 * Remove all facts from the add / remove sets if they are reported to be persistent!
	 */
	std::vector<const PropertySpace*> to_remove;
	for (std::map<const PropertySpace*, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		BalancedPropertySet* balanced_property_set = (*ci).second;
		const PropertySpace* key = (*ci).first;
		
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
	for (std::vector<const PropertySpace*>::const_iterator ci = to_remove.begin(); ci != to_remove.end(); ci++)
	{
		delete property_space_balanced_sets[*ci];
		property_space_balanced_sets.erase(*ci);
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	for (std::map<const PropertySpace*, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		std::cout << "Add / Remove sets: " << "(" << (*ci).first << ")" << std::endl;
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
	 * NOTE: There can be only ONE balanced property space!
	 */
	const PropertySpace* balanced_property_space = NULL;
	const Variable* balanced_action_variable = NULL;
	const std::vector<const Object*>* balanced_variable_domain = NULL;
	const BalancedPropertySet* balanced_exchanging_property_set = NULL;
	
	for (std::map<const PropertySpace*, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		// Only consider property spaces which get removed and added, if a fact is only added or removed it's an optional precondition.
		const PropertySpace* property_space = (*ci).first;
		BalancedPropertySet* balanced_property_set = (*ci).second;
		
		const std::vector<const BoundedAtom*>& added_facts = balanced_property_set->getAddedProperties();
		const std::vector<const BoundedAtom*>& removed_facts = balanced_property_set->getRemovedProperties();
		
		if (added_facts.empty() || removed_facts.empty())
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " Skip: " << std::endl;
			for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts.begin(); ci != added_facts.end(); ci++)
			{
				const BoundedAtom* added_fact = *ci;
				std::cout << "+ ";
				added_fact->print(std::cout, bindings);
				std::cout << "; resolved: " << added_fact->getProperties().size() << std::endl;
			}
			for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts.begin(); ci != removed_facts.end(); ci++)
			{
				const BoundedAtom* removed_fact = *ci;
				std::cout << "- ";
				removed_fact->print(std::cout, bindings);
				std::cout << "; resolved: " << removed_fact->getProperties().size() << std::endl;
			}
#endif
			continue;
		}
		
		// Again, there should only be a single property space which is balanced!
		//assert (balanced_property_space == NULL);
		//assert (balanced_action_variable == NULL);
		//assert (balanced_variable_domain == NULL);
		
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
			std::cout << "; resolved: " << removed_fact->getProperties().size() << std::endl;
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
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << "P: " << *property << std::endl;
#endif
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
				else
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "Cannot unify with precondition: ";
					precondition->print(std::cout, bindings, action_step_id);
					std::cout << "." << std::endl;
#endif
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
			balanced_property_space = property_space;
			balanced_variable_domain = *action_invariables.begin();
			balanced_action_variable = action_invariable_variable[balanced_variable_domain];
			balanced_exchanging_property_set = balanced_property_set;
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			for (std::vector<const Object*>::const_iterator ci = balanced_variable_domain->begin(); ci != balanced_variable_domain->end(); ci++)
			{
				std::cout << **ci;
				if (ci + 1 != balanced_variable_domain->end())
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
				if (&variable_domain == balanced_variable_domain)
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
	
	if (balanced_property_space == NULL)
	{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Found no invariables, so this transition is not possible" << std::endl;
#endif
		return NULL;
	}

#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
	/**
	 * Now that we know the invariables, make sure none of the persistent nodes are added or removed.
	 */
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::reverse_iterator persistent_ci = persistent_facts.rbegin(); persistent_ci != persistent_facts.rend(); persistent_ci++)
	{
		const BoundedAtom* to_persistent_atom = (*persistent_ci).second;
		
		for (std::vector<const Property*>::const_iterator ci = to_persistent_atom->getProperties().begin(); ci != to_persistent_atom->getProperties().end(); ci++)
		{
			const Property* property = *ci;
			if (&property->getPropertyState().getPropertySpace() != balanced_property_space) continue;
			
			// Check if the transitions removes this fact.
			for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;

				if (effect->isNegative() == to_persistent_atom->getAtom().isNegative() && 
				    bindings.canUnify(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()) &&
				    &effect->getTerms()[property->getIndex()]->getDomain(action_step_id, bindings) == balanced_variable_domain)
				{
					std::cout << "A persistent is added but not removed. This is invalid!" << std::endl;
					assert (false);
					return NULL;
				}

				if (bindings.affects(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()) &&
				    &effect->getTerms()[property->getIndex()]->getDomain(action_step_id, bindings) == balanced_variable_domain)
				{
					std::cout << "Removed but not added. This is invalid!" << std::endl;
					assert (false);
					return NULL;
				}
			}
		}
	}
#endif
	
	/**
	 * After we have found the invariable, check there are no mutex preconditions or effects.
	 *
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Check mutex relationships..." << std::endl;
#endif
	
	if (areMutex(from_node.getAtoms(), preconditions, action_step_id, *balanced_property_space, bindings, *balanced_action_variable) ||
	    areMutex(to_node.getAtoms(), preconditions, action_step_id, *balanced_property_space, bindings, *balanced_action_variable))
	{
		return NULL;
	}*/
	
	/**
	 * Make sure all the added and deleted facts are accounted for.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> > precondition_mapping_to_from_node;  // Pair of precondition and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > add_effects_mapping_to_to_node;     // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > remove_effects_mapping_to_to_node;  // Pair of effect and invariable index.
	
	std::vector<std::pair<const Atom*, const BoundedAtom*> > add_effects_to_to_node_bindings;
	std::vector<std::pair<const Atom*, const BoundedAtom*> > precondition_to_from_node_bindings;

	const std::vector<const BoundedAtom*>& added_facts = balanced_exchanging_property_set->getAddedProperties();
	const std::vector<const BoundedAtom*>& removed_facts = balanced_exchanging_property_set->getRemovedProperties();
	
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
		
		// Find the property which is part of the added fact and the property space which is part of the balanced set.
		const Property* linked_property = NULL;
		for (std::vector<PropertyState*>::const_iterator ci = balanced_property_space->getPropertyStates().begin(); ci != balanced_property_space->getPropertyStates().end(); ci++)
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
			    &effect->getTerms()[linked_property->getIndex()]->getDomain(action_step_id, bindings) == balanced_variable_domain)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "It's added by: ";
				effect->print(std::cout, bindings, action_step_id);
				std::cout << std::endl;
#endif
				is_added = true;
				add_effects_mapping_to_to_node.push_back(std::make_pair(effect, linked_property->getIndex()));
				add_effects_to_to_node_bindings.push_back(std::make_pair(effect, added_fact));
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

		// Find the property which is part of the added fact and the property space which is part of the balanced set.
		const Property* linked_property = NULL;
		for (std::vector<PropertyState*>::const_iterator ci = balanced_property_space->getPropertyStates().begin(); ci != balanced_property_space->getPropertyStates().end(); ci++)
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
			    &precondition->getTerms()[linked_property->getIndex()]->getDomain(action_step_id, bindings) == balanced_variable_domain)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "It's removed by: ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << std::endl;
#endif
				
				precondition_mapping_to_from_node.push_back(std::make_pair(precondition, linked_property->getIndex()));
				precondition_to_from_node_bindings.push_back(std::make_pair(precondition, removed_fact));
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
			    &effect->getTerms()[linked_property->getIndex()]->getDomain(action_step_id, bindings) == balanced_variable_domain)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "It's removed by: ";
				effect->print(std::cout, bindings, action_step_id);
				std::cout << std::endl;
#endif
				remove_effects_mapping_to_to_node.push_back(std::make_pair(effect, linked_property->getIndex()));
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
	
	/**
	 * Start making the actual bindings!
	 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify the effects!" << std::endl;
#endif
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = add_effects_to_to_node_bindings.begin(); ci != add_effects_to_to_node_bindings.end(); ci++)
	{
		const Atom* added_effect = (*ci).first;
		const BoundedAtom* to_node_atom = (*ci).second;

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "[Transition::createTransition] Unify the effect: " << std::endl;
		added_effect->print(std::cout, bindings, action_step_id);
		std::cout << " with: ";
		to_node_atom->print(std::cout, bindings);
		std::cout << std::endl;
#endif
		
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
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = precondition_to_from_node_bindings.begin(); ci != precondition_to_from_node_bindings.end(); ci++)
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
	 * If a action variable is not present in the preconditions it will be marked as 'free'.
	 */
	std::set<const Term*>* free_variables = new std::set<const Term*>();
	free_variables->insert(action.getVariables().begin(), action.getVariables().end());
	
	/**
	 * Post process by checking if the transitions did not violate any static preconditions.
	 */
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
		{
			free_variables->erase(*ci);
		}
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify the persistent facts!" << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	action.print(std::cout, bindings, action_step_id);
	std::cout << std::endl;
	std::cout << "Invariable: " << balanced_variable_domain << std::endl;
#endif
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
	{
		const BoundedAtom* from_node_persistent_fact = (*ci).first;
		const BoundedAtom* to_node_persistent_fact = (*ci).second;
		
		
		// Merge the terms together.
		if (!bindings.unify(from_node_persistent_fact->getAtom(), from_node_persistent_fact->getId(), to_node_persistent_fact->getAtom(), to_node_persistent_fact->getId()))
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "Unified: ";
			from_node_persistent_fact->print(std::cout, bindings);
			std::cout << " with: ";
			to_node_persistent_fact->print(std::cout, bindings);
			std::cout << "." << std::endl;
#endif
		}
		else
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "Could not unify: ";
			from_node_persistent_fact->print(std::cout, bindings);
			std::cout << " with: ";
			to_node_persistent_fact->print(std::cout, bindings);
			std::cout << "." << std::endl;
#endif

		}

		// Also unify the from node persistent fact with the matching precondition.
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;
			
			// Make sure the precondition is not removed!
			bool is_removed = false;
			for (std::map<const PropertySpace*, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
			{
				// Only consider property spaces which get removed and added, if a fact is only added or removed it's an optional precondition.
				BalancedPropertySet* balanced_property_set = (*ci).second;
				const std::vector<const BoundedAtom*>& removed_facts = balanced_property_set->getRemovedProperties();
				
				if (std::find(removed_facts.begin(), removed_facts.end(), from_node_persistent_fact) != removed_facts.end())
				{
					is_removed = true;
					break;
				}
			}
			
			
			if (is_removed ||
			    from_node_persistent_fact->getAtom().isNegative() != precondition->isNegative() ||
			    !bindings.canUnify(from_node_persistent_fact->getAtom(), from_node_persistent_fact->getId(), *precondition, action_step_id))
			{
				continue;
			}
			else
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Unified: ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << " with ";
				from_node_persistent_fact->print(std::cout, bindings);
				std::cout << "." << std::endl;
#endif
			}
/*
			// TODO: Uncomment as this does not work with Rovers.
			InvariableIndex precondition_invariable_index = precondition->containsVariableDomain(action_step_id, *balanced_variable_domain, bindings);
			InvariableIndex persistent_fact_invariable_index = from_node_persistent_fact->containsVariableDomain(*balanced_variable_domain, bindings);
			
			if (precondition_invariable_index != persistent_fact_invariable_index)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Could not unify the presistent facts because the invariable index do not match :(" << std::endl;
#endif
				continue;
			}

			if (bindings.unify(from_node_persistent_fact->getAtom(), from_node_persistent_fact->getId(), *precondition, action_step_id))
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Unified ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << " with ";
				from_node_persistent_fact->print(std::cout, bindings);
				std::cout << "." << std::endl;
#endif
			}
*/
		}
	}
	
	/**
	 * After all the bindings have been made, make sure the preconditions and facts in the nodes are not mutually exclusive.
	 */
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Check mutex relationships..." << std::endl;
#endif
	
	if (areMutex(from_node.getAtoms(), preconditions, action_step_id, *balanced_property_space, bindings, *balanced_action_variable) ||
	    areMutex(to_node.getAtoms(), effects, action_step_id, *balanced_property_space, bindings, *balanced_action_variable))
	{
		return NULL;
	}

	/**
	 * Store for each precondition which variable is invariable for easy access later (getAllPreconditions()). This part assumes
	 * a transition can only work on a single balanced set, so a transition cannot affect two different sets of property spaces.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> >* all_precondition_mappings = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		
		bool found_binding = false;
		for (InvariableIndex i = 0; i < precondition->getArity(); i++)
		{
			const Term* term = precondition->getTerms()[i];
			
			if (&term->getDomain(action_step_id, bindings) == balanced_variable_domain)
			{
				found_binding = true;
				
				all_precondition_mappings->push_back(std::make_pair(precondition, i));
				break;
			}
		}
		
		if (!found_binding)
		{
			all_precondition_mappings->push_back(std::make_pair(precondition, NO_INVARIABLE_INDEX));
		}
	}
	
	// Link all the preconditions to the facts in the from node.
	std::vector<std::pair<const Atom*, InvariableIndex> >* preconditions_in_from_node = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* from_node_fact = *ci;
		bool found_precondition = false;
		
		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_precondition_mappings->begin(); ci != all_precondition_mappings->end(); ci++)
		{
			const Atom* precondition = (*ci).first;
			InvariableIndex invariable_index = (*ci).second;
			
			if (bindings.areIdentical(*precondition, action_step_id, from_node_fact->getAtom(), from_node_fact->getId()))
			{
				found_precondition = true;
				preconditions_in_from_node->push_back(std::make_pair(precondition, invariable_index));
				break;
			}
		}
		
		if (!found_precondition)
		{
			const Atom* null_atom = NULL;
			preconditions_in_from_node->push_back(std::make_pair(null_atom, NO_INVARIABLE_INDEX));
		}
	}
	
	std::vector<std::pair<const Atom*, InvariableIndex> >* all_effect_mappings = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		const Atom* effect = *ci;
		
		bool found_binding = false;
		for (InvariableIndex i = 0; i < effect->getArity(); i++)
		{
			const Term* term = effect->getTerms()[i];
			
			if (&term->getDomain(action_step_id, bindings) == balanced_variable_domain)
			{
				found_binding = true;
				
				all_effect_mappings->push_back(std::make_pair(effect, i));
				break;
			}
		}
		
		if (!found_binding)
		{
			all_effect_mappings->push_back(std::make_pair(effect, NO_INVARIABLE_INDEX));
		}
	}
	
	// Link all the effects to the facts in the to node.
	std::vector<std::pair<const Atom*, InvariableIndex> >* effects_in_to_node = new std::vector<std::pair<const Atom*, InvariableIndex> >();
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* to_node_fact = *ci;
		bool found_effect = false;
		
		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_effect_mappings->begin(); ci != all_effect_mappings->end(); ci++)
		{
			const Atom* effect = (*ci).first;
			InvariableIndex invariable_index = (*ci).second;
			
			if (bindings.areIdentical(*effect, action_step_id, to_node_fact->getAtom(), to_node_fact->getId()))
			{
				found_effect = true;
				effects_in_to_node->push_back(std::make_pair(effect, invariable_index));
				break;
			}
		}
		
		if (!found_effect)
		{
			const Atom* null_atom = NULL;
			effects_in_to_node->push_back(std::make_pair(null_atom, NO_INVARIABLE_INDEX));
		}
	}
	
	std::vector<std::pair<unsigned int, unsigned int> >* persistent_sets = new std::vector<std::pair<unsigned int, unsigned int> >();
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
	{
		const BoundedAtom* from_node_persistent_fact = (*ci).first;
		const BoundedAtom* to_node_persistent_fact = (*ci).second;
		
		std::vector<BoundedAtom*>::const_iterator from_ci = std::find(from_node.getAtoms().begin(), from_node.getAtoms().end(), from_node_persistent_fact);
		std::vector<BoundedAtom*>::const_iterator to_ci = std::find(to_node.getAtoms().begin(), to_node.getAtoms().end(), to_node_persistent_fact);
		
		unsigned int from_index = std::distance(from_node.getAtoms().begin(), from_ci);
		unsigned int to_index = std::distance(to_node.getAtoms().begin(), to_ci);
		
		persistent_sets->push_back(std::make_pair(from_index, to_index));
	}
	
	std::vector<std::pair<unsigned int, unsigned int> >* precondition_index_to_to_node = new std::vector<std::pair<unsigned int, unsigned int> >();
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
	unsigned int nr_balanced_property_sets = 0;
	for (std::map<const PropertySpace*, BalancedPropertySet*>::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		std::cout << "Add / Remove sets: " << (*ci).first << std::endl;
		BalancedPropertySet* balanced_property_set = (*ci).second;
		
		if (!balanced_property_set->getAddedProperties().empty() &&
		    !balanced_property_set->getRemovedProperties().empty())
		{
			++nr_balanced_property_sets;
		}
	}
	
	assert (nr_balanced_property_sets == 1);
#endif
	
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
	Transition* transition = new Transition(action_step, from_node, to_node, *all_precondition_mappings, *preconditions_in_from_node, *all_effect_mappings, *effects_in_to_node, *persistent_sets, *precondition_index_to_to_node, *free_variables);
	assert (transition->getFromNodePreconditions().size() == from_node.getAtoms().size());
	assert (transition->getToNodeEffects().size() == to_node.getAtoms().size());
	return transition;
}

bool Transition::areMutex(const std::vector<BoundedAtom*>& facts, const std::vector<const Atom*>& preconditions, StepID action_step_id, const PropertySpace& balanced_property_space, const Bindings& bindings, const Variable& balanced_action_variable)
{
	const std::vector<const Object*>& balanced_variable_domain = balanced_action_variable.getDomain(action_step_id, bindings);
	for (std::vector<BoundedAtom*>::const_iterator ci = facts.begin(); ci != facts.end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
		{
			const Property* bounded_atom_property = *ci;
			const PropertySpace& property_space = bounded_atom_property->getPropertyState().getPropertySpace();
			
			if (&property_space != &balanced_property_space) continue;
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " * Checking precondition or effect against the from node atom * ";
			bounded_atom->print(std::cout, bindings);
			std::cout << std::endl;
#endif

			// Check all preconditions which contains the invariable.
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				
				if (precondition->containsVariableDomain(action_step_id, balanced_variable_domain, bindings) == std::numeric_limits<unsigned int>::max()) continue;
				
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << " * * Precondition: ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << "(Index=" << precondition->containsVariableDomain(action_step_id, balanced_variable_domain, bindings) << ")";
				std::cout << std::endl;
#endif

				for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
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
							
							if (precondition->getTerms()[invariable_index] != &balanced_action_variable)
							{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
								std::cout << "Invariables don't match, move on!" << std::endl;
#endif
								continue;
							}
							
							if (bounded_atom->isMutexWith(*precondition, action_step_id, bindings, invariable_index))
							{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
								std::cout << "The precondition ";
								precondition->print(std::cout, bindings, action_step_id);
								std::cout << " is mutex with the from fact ";
								bounded_atom->print(std::cout, bindings);
								std::cout << "." << std::endl;
#endif
								return true;
							}
						}
					}
				}
			}
		}
	}
	return false;
}

Transition::Transition(StepPtr step, 
                       SAS_Plus::DomainTransitionGraphNode& from_node,
                       SAS_Plus::DomainTransitionGraphNode& to_node,
                       std::vector< std::pair< const Atom*, InvariableIndex > >& all_precondition_mappings,
                       std::vector< std::pair< const Atom*, InvariableIndex > >& from_node_preconditions,
                       const std::vector< std::pair< const Atom*, InvariableIndex > >& all_effect_mappings,
                       std::vector< std::pair< const Atom*, InvariableIndex > >& to_node_effects,
                       std::vector<std::pair<unsigned int, unsigned int> >& persistent_sets,
                       std::vector<std::pair<unsigned int, unsigned int> >& precondition_index_to_to_node,
                       const std::set<const Term*>& free_variables)
	: step_(step), from_node_(&from_node), to_node_(&to_node), all_preconditions_(&all_precondition_mappings), from_node_preconditions_(&from_node_preconditions), all_effects_(&all_effect_mappings), to_node_effects_(&to_node_effects), persistent_sets_(&persistent_sets), precondition_index_to_to_node_(&precondition_index_to_to_node), free_variables_(&free_variables), balanced_term_(NULL)
{
	for (std::vector< std::pair< const Atom*, InvariableIndex > >::const_iterator ci = all_precondition_mappings.begin(); ci != all_precondition_mappings.end(); ci++)
	{
		if ((*ci).second != NO_INVARIABLE_INDEX)
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::Transition] The new balanced term is the " << (*ci).second << "th term of: ";
			(*ci).first->print(std::cout, from_node.getDTG().getBindings() ,step_->getStepId());
			std::cout << std::endl;
#endif
			balanced_term_ = (*ci).first->getTerms()[(*ci).second];
			break;
		}
	}

#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
	sanityCheck();
#endif
}

Transition::~Transition()
{
	//from_node_->getDTG().getBindings().removeBindings(getStepId());
	delete all_preconditions_;
	delete from_node_preconditions_;
	delete all_effects_;
	delete to_node_effects_;
	delete free_variables_;
	delete persistent_sets_;
	delete precondition_index_to_to_node_;
}

void Transition::sanityCheck() const
{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
	const Bindings& bindings = from_node_->getDTG().getBindings();
	
	std::cout << "Check sanity of: " << *this << std::endl;
	
	for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = persistent_sets_->begin(); ci != persistent_sets_->end(); ci++)
	{
		unsigned int from_dtg_index = (*ci).first;
		unsigned int to_dtg_index = (*ci).second;
		
		assert (from_node_->getAtoms().size() > from_dtg_index);
		assert (to_node_->getAtoms().size() > to_dtg_index);
		
		assert (from_node_->getAtoms()[from_dtg_index]->getAtom().getPredicate().getName() == to_node_->getAtoms()[to_dtg_index]->getAtom().getPredicate().getName());
		assert (bindings.canUnify(from_node_->getAtoms()[from_dtg_index]->getAtom(), from_node_->getAtoms()[from_dtg_index]->getId(), to_node_->getAtoms()[to_dtg_index]->getAtom(), to_node_->getAtoms()[to_dtg_index]->getId()));
	}
#endif
}

Transition* Transition::migrateTransition(DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts) const
{
	unsigned int from_mapping[from_node.getAtoms().size()];
	unsigned int to_mapping[to_node.getAtoms().size()];
	
	for (unsigned int i = 0; i < from_node.getAtoms().size(); i++)
	{
		from_mapping[i] = i;
	}
	
	for (unsigned int i = 0; i < to_node.getAtoms().size(); i++)
	{
		to_mapping[i] = i;
	}
	
	return migrateTransition(from_node, to_node, from_mapping, to_mapping, initial_facts);
}

Transition* Transition::migrateTransition(DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, unsigned int from_fact_ordering[], unsigned int to_fact_ordering[], const std::vector<const Atom*>& initial_facts) const
{
	Bindings& bindings = from_node_->getDTG().getBindings();
	StepID action_step_id =  bindings.createVariableDomains(getAction());

	assert (&getAction().getPrecondition() != NULL);
	
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &getAction().getPrecondition());
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
	std::cout << "Preconditions of the action; StepID: " << action_step_id << std::endl; 
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* atom = *ci;
		for (std::vector<const Term*>::const_iterator ci = atom->getTerms().begin(); ci != atom->getTerms().end(); ci++)
		{
			const Term* atom_term = *ci;

			bool is_action_term = false;
			for (std::vector<const Variable*>::const_iterator ci = getAction().getVariables().begin(); ci != getAction().getVariables().end(); ci++)
			{
				const Variable* action_variable = *ci;
				if (action_variable == atom_term)
				{
					is_action_term = true;
					break;
				}
			}
			
			assert (is_action_term);
		}
		
		std::cout << "* ";
		atom->print(std::cout, bindings, action_step_id);
		std::cout << std::endl;
	}
#endif

	StepPtr new_step = StepPtr(new Step(action_step_id, getAction()));
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::migrateTransition] Migrate " << *this << " to the new from and to nodes: " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << "to:" << std::endl;
	std::cout << to_node << std::endl;
	
	std::cout << "Mapping for the from node: " << std::endl;
	for (unsigned int i = 0; i < from_node.getAtoms().size(); i++)
	{
		std::cout << i << " -> " << from_fact_ordering[i] << std::endl;
	}
	
	std::cout << "Mapping for the to node: " << std::endl;
	for (unsigned int i = 0; i < to_node.getAtoms().size(); i++)
	{
		std::cout << i << " -> " << to_fact_ordering[i] << std::endl;
	}
#endif
	
	Transition* new_transition = performBindings(new_step, from_node, to_node, from_fact_ordering, to_fact_ordering, bindings, initial_facts);
	if (new_transition != NULL)
	{
		assert (new_transition->getFromNodePreconditions().size() == from_node.getAtoms().size());
		assert (new_transition->getToNodeEffects().size() == to_node.getAtoms().size());
		
		// Prune the variable domains such that they are not larger than the original transition.
		for (unsigned int i = 0; i < getAction().getVariables().size(); ++i)
		{
			const std::vector<const Object*>& variable_domain = getAction().getVariables()[i]->getDomain(getStepId(), bindings);
			const std::vector<const Object*>& new_variable_domain = new_transition->getAction().getVariables()[i]->getDomain(action_step_id, bindings);

/*
			std::cout << "Limit {";
			for (std::vector<const Object*>::const_iterator ci = new_variable_domain.begin(); ci != new_variable_domain.end(); ++ci)
			{
				std::cout << **ci << " ";
			}
			std::cout << "} to {";
			for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ++ci)
			{
				std::cout << **ci << " ";
			}
			std::cout << "}" << std::endl;
*/
			new_transition->getAction().getVariables()[i]->makeDomainEqualTo(action_step_id, variable_domain, bindings);
			if (new_variable_domain.empty())
			{
//				std::cout << "FAIL :(((" << std::endl;
				delete new_transition;
				new_transition = NULL;
				break;
			}
		}
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	if (new_transition != NULL)
	{
		std::cout << "[Transition::migrateTransition] POST Migration: " << *new_transition << std::endl;
	}
	else
	{
		std::cout << "[Transition::migrateTransition] Could not migrate the transition :(" << std::endl;
	}
#endif
	return new_transition;
}

Transition* Transition::performBindings(StepPtr step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, unsigned int from_fact_ordering[], unsigned int to_fact_ordering[], Bindings& bindings, const std::vector<const Atom*>& initial_facts) const
{
	// Map the preconditions.
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &step->getAction().getPrecondition());
	
	if (preconditions.size() != all_preconditions_->size())
	{
		std::cerr << "Could not perform bindings, because the preconditions do not match up!" << std::endl;
		std::cerr << "Preconditions of the action: " << std::endl;
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			std::cerr << "* ";
			(*ci)->print(std::cerr, bindings, step->getStepId());
			std::cerr << std::endl;
		}
		std::cerr << "Preconditions recorded by the transition: " << std::endl;
		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions_->begin(); ci != all_preconditions_->end(); ci++)
		{
			std::cerr << "* ";
			(*ci).first->print(std::cerr, getFromNode().getDTG().getBindings(), getStepId());
			std::cerr << std::endl;
		}
		assert (false);
		exit(1);
	}
	
	std::map<const Atom*, const Atom*> org_precondition_to_new;
	
	std::vector< std::pair< const Atom*, InvariableIndex > >* all_precondition_mappings = new std::vector< std::pair< const Atom*, InvariableIndex > >();
	for (unsigned int i = 0; i < preconditions.size(); i++)
	{
		all_precondition_mappings->push_back(std::make_pair(preconditions[i], (*all_preconditions_)[i].second));
		org_precondition_to_new[(*all_preconditions_)[i].first] = preconditions[i];
	}
	
	const std::vector<const Atom*>& effects = step->getAction().getEffects();
	
	assert (effects.size() == all_effects_->size());
	
	std::map<const Atom*, const Atom*> org_effect_to_new;
	
	std::vector< std::pair< const Atom*, InvariableIndex > >* all_effect_mappings = new std::vector< std::pair< const Atom*, InvariableIndex > >();
	for (unsigned int i = 0; i < effects.size(); i++)
	{
		all_effect_mappings->push_back(std::make_pair(effects[i], (*all_effects_)[i].second));
		org_effect_to_new[(*all_effects_)[i].first] = effects[i];
	}
	
	assert (from_node_preconditions_->size() <= from_node_->getAtoms().size());
	
	// Perform the bindings.
	std::vector< std::pair< const Atom*, InvariableIndex > >* clone_from_node_preconditions = new std::vector< std::pair< const Atom*, InvariableIndex > >(from_node_preconditions_->size());
	for (unsigned int i = 0; i < from_node_preconditions_->size(); i++)
	{
		const std::pair< const Atom*, InvariableIndex >& from_node_precondition = (*from_node_preconditions_)[i];
		
		unsigned int actual_index = from_fact_ordering[i];
		assert (actual_index < from_node.getAtoms().size());
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "The " << i << "th precondition is actually part of the " << actual_index << "th fact!" << std::endl;
#endif
		
		const Atom* org_precondition = from_node_precondition.first;
		const Atom* clone_precondition = NULL;
		if (org_precondition != NULL)
		{
			clone_precondition = org_precondition_to_new[org_precondition];
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "The original precondition: ";
			org_precondition->print(std::cout, bindings, step_->getStepId());
			std::cout << " maps to ";
			clone_precondition->print(std::cout, bindings, step->getStepId());
			std::cout << std::endl;
#endif
			
			if (!bindings.unify(from_node.getAtoms()[actual_index]->getAtom(), from_node.getAtoms()[actual_index]->getId(), *clone_precondition, step->getStepId()))
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "[Transition::performBindings]Cannot unify the preconditions: ";
				from_node.print(std::cout);
				std::cout << " and ";
				clone_precondition->print(std::cout, bindings, step->getStepId());
				std::cout << std::endl;
#endif
				delete all_precondition_mappings;
				delete all_effect_mappings;
				delete clone_from_node_preconditions;
				return NULL;
			}
		}
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		else
		{
			std::cout << "The original precondition: ";
			from_node.getAtoms()[i]->print(std::cout, bindings);
			std::cout << " maps to NULL[" << actual_index << "]" << std::endl;
		}
#endif
		
		//clone_from_node_preconditions->push_back(std::make_pair(clone_precondition, from_node_precondition.second));
		(*clone_from_node_preconditions)[actual_index] = std::make_pair<const Atom*, InvariableIndex>(clone_precondition, from_node_precondition.second);
	}
	
	std::vector< std::pair< const Atom*, InvariableIndex > >* clone_to_node_effects = new std::vector< std::pair< const Atom*, InvariableIndex > >(to_node_effects_->size());
	
	assert (to_node_effects_->size() == to_node.getAtoms().size());
	
	for (unsigned int i = 0; i < to_node_effects_->size(); i++)
	{
		const std::pair< const Atom*, InvariableIndex >& to_node_effect = (*to_node_effects_)[i];
		
		unsigned int actual_index = to_fact_ordering[i];
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS		
		std::cout << "Map the " << i << "th effect to " << actual_index << std::endl;
#endif
		
		assert (actual_index < clone_to_node_effects->size());
		
		const Atom* org_effect = to_node_effect.first;
		const Atom* clone_effect = NULL;
		if (org_effect != NULL)
		{
			clone_effect = org_effect_to_new[org_effect];
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "The original effect: ";
			org_effect->print(std::cout, bindings, step_->getStepId());
			std::cout << " maps to ";
			clone_effect->print(std::cout, bindings, step->getStepId());
			std::cout << std::endl;
#endif
			
			if (!bindings.unify(to_node.getAtoms()[actual_index]->getAtom(), to_node.getAtoms()[actual_index]->getId(), *clone_effect, step->getStepId()))
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "[Transition::performBindings]Cannot unify the effects: ";
				to_node.print(std::cout);
				std::cout << " and ";
				clone_effect->print(std::cout, bindings, step->getStepId());
				std::cout << std::endl;
#endif
				delete clone_to_node_effects;
				delete clone_from_node_preconditions;
				delete all_effect_mappings;
				delete all_precondition_mappings;
				return NULL;
			}
		}
		(*clone_to_node_effects)[actual_index] = std::make_pair(clone_effect, to_node_effect.second);
	}
	
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::performBindings] Handle persistent sets: " << std::endl;
#endif
	// Bind the persistent nodes.
	std::vector<std::pair<unsigned int, unsigned int> >* new_persistent_sets = new std::vector<std::pair<unsigned int, unsigned int> >();
	for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = persistent_sets_->begin(); ci != persistent_sets_->end(); ci++)
	{
		unsigned int from_index = (*ci).first;
		unsigned int to_index = (*ci).second;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "[Transition::performBindings] " << from_index << " <-> " << to_index << std::endl;
#endif
		unsigned int actual_from_index = from_fact_ordering[from_index];
		unsigned int actual_to_index = to_fact_ordering[to_index];
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "[Transition::performBindings] " << actual_from_index << " <-> " << actual_to_index << std::endl;
#endif
		
		assert (from_index < from_node.getAtoms().size());
		assert (to_index < to_node.getAtoms().size());
		
		if (!bindings.unify(from_node.getAtoms()[actual_from_index]->getAtom(), from_node.getAtoms()[actual_from_index]->getId(), to_node.getAtoms()[actual_to_index]->getAtom(), to_node.getAtoms()[actual_to_index]->getId()))
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::performBindings]Cannot unify the persistent facts: ";
			from_node.print(std::cout);
			std::cout << " and ";
			to_node.print(std::cout);
			std::cout << std::endl;
#endif
			delete clone_to_node_effects;
			delete clone_from_node_preconditions;
			delete all_effect_mappings;
			delete all_precondition_mappings;
			delete new_persistent_sets;
			return NULL;
		}
		
		new_persistent_sets->push_back(std::make_pair(actual_from_index, actual_to_index));
	}
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::performBindings] Handle persistent sets - DONE! " << std::endl;
#endif

	std::vector<std::pair<unsigned int, unsigned int> >* new_precondition_index_to_to_node = new std::vector<std::pair<unsigned int, unsigned int> >();
	for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = precondition_index_to_to_node_->begin(); ci != precondition_index_to_to_node_->end(); ci++)
	{
		unsigned int precondition_index = (*ci).first;
		unsigned int to_index = (*ci).second;
		unsigned int actual_to_index = to_fact_ordering[to_index];
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "[Transition::performBindings] Precondition to to node" << precondition_index << " <-> " << actual_to_index << std::endl;
		std::cout << "Precondition: ";
		preconditions[precondition_index]->print(std::cout, bindings, getStepId());
		std::cout << "." << std::endl;
		std::cout << "To node: ";
		to_node.getAtoms()[actual_to_index]->print(std::cout, bindings);
		std::cout << "." << std::endl;
#endif
		
		assert (precondition_index < preconditions.size());
		assert (to_index < to_node.getAtoms().size());
		
		if (!bindings.unify(*preconditions[precondition_index], step->getStepId(), to_node.getAtoms()[actual_to_index]->getAtom(), to_node.getAtoms()[actual_to_index]->getId()))
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::performBindings]Cannot unify the precondition to to node fact: ";
			from_node.print(std::cout);
			std::cout << " and ";
			to_node.print(std::cout);
			std::cout << std::endl;
#endif
			delete clone_to_node_effects;
			delete clone_from_node_preconditions;
			delete all_effect_mappings;
			delete all_precondition_mappings;
			delete new_persistent_sets;
			delete new_precondition_index_to_to_node;
			return NULL;
		}
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "[Transition::performBindings] POST: Precondition to to node" << precondition_index << " <-> " << actual_to_index << std::endl;
		std::cout << "Precondition: ";
		(*all_precondition_mappings)[precondition_index].first->print(std::cout, bindings, getStepId());
		std::cout << "." << std::endl;
		std::cout << "To node: ";
		to_node.getAtoms()[actual_to_index]->print(std::cout, bindings);
		std::cout << "." << std::endl;
#endif
		
		new_precondition_index_to_to_node->push_back(std::make_pair(precondition_index, actual_to_index));
	}
	
	// After all preconditions are bound, check if they satisfy the static preconditions.
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_precondition_mappings->begin(); ci != all_precondition_mappings->end(); ++ci)
	{
		const Atom* precondition = (*ci).first;
		if (precondition->getPredicate().isStatic())
		{
			bool found_satisficing_initial_fact = false;
			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
			{
				const Atom* initial_fact = *ci;
				if (initial_fact->getPredicate().isStatic() && bindings.canUnify(*initial_fact, Step::INITIAL_STEP, *precondition, step->getStepId()))
				{
					found_satisficing_initial_fact = true;
					break;
				}
			}
			
			if (!found_satisficing_initial_fact)
			{
				delete clone_to_node_effects;
				delete clone_from_node_preconditions;
				delete all_effect_mappings;
				delete all_precondition_mappings;
				delete new_persistent_sets;
				delete new_precondition_index_to_to_node;
				return NULL;
			}
		}
	}
	

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::performBindings] Figure out the new free variables." << std::endl;
#endif
	std::set<const Term*>* new_free_variables = new std::set<const Term*>();
	for (std::set<const Term*>::const_iterator ci = free_variables_->begin(); ci != free_variables_->end(); ci++)
	{
		const Term* free_variable = *ci;
		
		// Find to which variables are free.
		for (std::vector<const Variable*>::const_iterator ci = step_->getAction().getVariables().begin(); ci != step_->getAction().getVariables().end(); ci++)
		{
			const Variable* action_variable = *ci;
			
			if (free_variable == action_variable)
			{
				unsigned int free_variable_index = std::distance(step_->getAction().getVariables().begin(), ci);
				new_free_variables->insert(step->getAction().getVariables()[free_variable_index]);
			}
		}
	}
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::performBindings] Figure out the new free variables - DONE!" << std::endl;
#endif
	
	return new Transition(step, from_node, to_node, *all_precondition_mappings, *clone_from_node_preconditions, *all_effect_mappings, *clone_to_node_effects, *new_persistent_sets, *new_precondition_index_to_to_node, *new_free_variables);
}

void Transition::addedFromNodePrecondition(const Atom& precondition)
{
	InvariableIndex invariable_index = NO_INVARIABLE_INDEX;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions_->begin(); ci != all_preconditions_->end(); ci++)
	{
		if (&precondition == (*ci).first)
		{
			invariable_index = (*ci).second;
		}
	}
	from_node_preconditions_->push_back(std::make_pair(&precondition, invariable_index));
	
	assert (from_node_preconditions_->size() <= from_node_->getAtoms().size());
	
	unsigned int from_node_index = isFactContainedByNode(precondition, *from_node_);
	unsigned int to_node_index = isFactContainedByNode(precondition, *to_node_);
	if (to_node_index != NO_INVARIABLE_INDEX)
	{
		persistent_sets_->push_back(std::make_pair(from_node_index, to_node_index));
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
	sanityCheck();
#endif
}

void Transition::addedToNodeFact(const Atom& fact)
{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::addedToNodeFact] ";
	fact.print(std::cout, from_node_->getDTG().getBindings(), getStepId());
	std::cout << "." << std::endl;
#endif

	// Find the precondition or effect this fact is linked to.
	bool is_a_precondition = false;
	unsigned int precondition_index = NO_INVARIABLE_INDEX;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions_->begin(); ci != all_preconditions_->end(); ci++)
	{
		if (&fact == (*ci).first)
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::addedToNodeFact] Is a precondition!" << std::endl;
#endif
			precondition_index = std::distance((std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator)all_preconditions_->begin(), ci);
			is_a_precondition = true;
			break;
		}
	}
	
	bool is_an_effect = false;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_effects_->begin(); ci != all_effects_->end(); ci++)
	{
		if (&fact == (*ci).first)
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::addedToNodeFact] Is an effect!" << std::endl;
#endif
			to_node_effects_->push_back(*ci);
			is_an_effect = true;
			return;
		}
	}
	
	if (is_a_precondition && !is_an_effect)
	{
		const Atom* null_atom = NULL;
		to_node_effects_->push_back(std::make_pair(null_atom, NO_INVARIABLE_INDEX));

		// Check if it is a persistent fact.
		unsigned int to_node_index = isFactContainedByNode(fact, *to_node_);
		if (to_node_index == NO_INVARIABLE_INDEX) return;
		unsigned int from_node_index = isFactContainedByNode(fact, *from_node_);
		if (from_node_index == NO_INVARIABLE_INDEX)
		{
			precondition_index_to_to_node_->push_back(std::make_pair(precondition_index, to_node_index));
		}
		else
		{
			persistent_sets_->push_back(std::make_pair(from_node_index, to_node_index));
		}
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_DEBUG
		sanityCheck();
#endif
		
		return;
	}
	
	
	assert (false);
}

void Transition::deletedFact(unsigned int removed_fact_index, const DomainTransitionGraphNode& affected_node)
{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Removed the " << removed_fact_index << "th fact from: " << affected_node << "." << std::endl;
	std::cout << "Update the transition: " << *this << "." << std::endl;
#endif
	if (&affected_node == from_node_)
	{
		from_node_preconditions_->erase(from_node_preconditions_->begin() + removed_fact_index);
			
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Remove the " << removed_fact_index << "th from fact." << std::endl;
#endif
			
		for (std::vector<std::pair<unsigned int, unsigned int> >::reverse_iterator ri = persistent_sets_->rbegin(); ri != persistent_sets_->rend(); ri++)
		{
			if ((*ri).first == removed_fact_index)
			{
				persistent_sets_->erase(ri.base() - 1);
			}
		}
			
		// Update the persistent sets.
		for (std::vector<std::pair<unsigned int, unsigned int> >::iterator i = persistent_sets_->begin(); i != persistent_sets_->end(); i++)
		{
			unsigned int index = std::distance(persistent_sets_->begin(), i);
			if ((*i).first > removed_fact_index)
			{
				(*persistent_sets_)[index] = std::make_pair((*i).first - 1, (*i).second);
			}
		}
	}
	else if (&affected_node == to_node_)
	{
		to_node_effects_->erase(to_node_effects_->begin() + removed_fact_index);
				
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Remove the " << removed_fact_index << "th to fact." << std::endl;
#endif

		for (std::vector<std::pair<unsigned int, unsigned int> >::reverse_iterator ri = persistent_sets_->rbegin(); ri != persistent_sets_->rend(); ri++)
		{
			if ((*ri).second == removed_fact_index)
			{
				persistent_sets_->erase(ri.base() - 1);
			}
		}
				
		// Update the persistent sets.
		for (std::vector<std::pair<unsigned int, unsigned int> >::iterator i = persistent_sets_->begin(); i != persistent_sets_->end(); i++)
		{
			unsigned int index = std::distance(persistent_sets_->begin(), i);
			if ((*i).second > removed_fact_index)
			{
				(*persistent_sets_)[index] = std::make_pair((*i).first, (*i).second - 1);
			}
		}
	}
	else
	{
		assert (false);
	}
	
	assert (from_node_preconditions_->size() == from_node_->getAtoms().size());
	assert (to_node_effects_->size() == to_node_->getAtoms().size());
}

void Transition::ground(std::vector<Transition*>& grounded_transitions, const std::vector<const Atom*>& initial_facts, const std::vector<const std::vector<const Object*>*>& excluded_variable_domains) const
{
	unsigned int ground_index[step_->getAction().getVariables().size()];
	memset(&ground_index[0], 0, sizeof(unsigned int) * step_->getAction().getVariables().size());
	unsigned int max_ground_index[step_->getAction().getVariables().size()];
	for (unsigned int i = 0; i < step_->getAction().getVariables().size(); ++i)
	{
		const std::vector<const Object*>& variable_domain = getAction().getVariables()[i]->getDomain(getStepId(), from_node_->getDTG().getBindings());
		max_ground_index[i] = variable_domain.size();
	}
	bool excluded_variable_domains_indexes[step_->getAction().getVariables().size()];
	for (unsigned int i = 0; i < step_->getAction().getVariables().size(); ++i)
	{
		const std::vector<const Object*>& variable_domain = getAction().getVariables()[i]->getDomain(getStepId(), from_node_->getDTG().getBindings());
		excluded_variable_domains_indexes[i] = std::find(excluded_variable_domains.begin(), excluded_variable_domains.end(), &variable_domain) != excluded_variable_domains.end();
	}
	
	bool done = false;
	while (!done)
	{
		done = true;
		Transition* transition = migrateTransition(*from_node_, *to_node_, initial_facts);
		assert (transition != NULL);
		
//		std::cout << "Migrated: " << *this << std::endl;
		
		bool valid_transition = true;
		for (unsigned int i = 0; i < step_->getAction().getVariables().size(); ++i)
		{
			const std::vector<const Object*>& variable_domain = transition->getAction().getVariables()[i]->getDomain(transition->getStepId(), from_node_->getDTG().getBindings());
			if (excluded_variable_domains_indexes[i])
			{
				continue;
			}
/*			std::cout << "Limit the " << i << "th variable to: ";
			for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ++ci)
			{
				std::cout << **ci << " ";
			}
			std::cout << " <-- " << ground_index[i] << std::endl;*/
			assert (variable_domain.size() >= ground_index[i]);
			if (!transition->getAction().getVariables()[i]->unifyWith(transition->getStepId(), *variable_domain[ground_index[i]], from_node_->getDTG().getBindings()))
			{
/*				if (variable_domain[ground_index[i]] == NULL)
				{
					std::cout << "Cannot limit the " << i << "th variable to UNDEFINED" << std::endl;
				}
				else
				{
					std::cout << "Cannot limit the " << i << "th variable to: " << *variable_domain[ground_index[i]] << std::endl;
				}*/
				valid_transition = false;
				break;
			}
		}
		
		if (!valid_transition)
		{
			delete transition;
			continue;
		}
		
		grounded_transitions.push_back(transition);
		
//		std::cout << "Grounded transition: " << *transition << std::endl;
		
		for (unsigned int i = 0; i < step_->getAction().getVariables().size(); ++i)
		{
			if (ground_index[i] + 1 != max_ground_index[i])
			{
				ground_index[i] = ground_index[i] + 1;
				done = false;
				break;
			}
			else
			{
				ground_index[i] = 0;
			}
		}
	}
}

unsigned int Transition::isFactContainedByNode(const Atom& fact, const DomainTransitionGraphNode& node) const
{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "Check if ";
	fact.print(std::cout, from_node_->getDTG().getBindings(), step_->getStepId());
	std::cout << " is part of " << node << "." << std::endl;
#endif
	for (std::vector<BoundedAtom*>::const_iterator ci = node.getAtoms().begin(); ci != node.getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		if (from_node_->getDTG().getBindings().areIdentical(bounded_atom->getAtom(), bounded_atom->getId(), fact, step_->getStepId()))
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "The index is: " << std::distance(node.getAtoms().begin(), ci) << "." << std::endl;
#endif
			return std::distance(node.getAtoms().begin(), ci);
		}
	}
	
	return NO_INVARIABLE_INDEX;
}

bool Transition::isVariableFree(const MyPOP::Term& term) const
{
	return free_variables_->count(&term) != 0;
}

bool Transition::isPreconditionRemoved(const Atom& precondition) const
{
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_effects_->begin(); ci != all_effects_->end(); ci++)
	{
		const Atom* effect = (*ci).first;
		
		if (effect->isNegative() != precondition.isNegative() &&
		    from_node_->getDTG().getBindings().areIdentical(precondition, step_->getStepId(), *effect, step_->getStepId()))
		{
			return true;
		}
	}
	
	return false;
}

bool Transition::removePrecondition(const Atom& precondition)
{
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::reverse_iterator ri = all_preconditions_->rbegin(); ri != all_preconditions_->rend(); ri++)
	{
		if ((*ri).first == &precondition)
		{
			all_preconditions_->erase(ri.base() - 1);
		}
	}
	
	// Remove facts from the node if the precondition is part of a from node too.
	unsigned int nr_from_node_facts = from_node_preconditions_->size();
	for (unsigned int i = 0; i < nr_from_node_facts; ++i)
	{
		if ((*from_node_preconditions_)[i].first == &precondition)
		{
			from_node_preconditions_->erase(from_node_preconditions_->end() - (1 + i));
			from_node_->removeAtom(*from_node_->getAtoms()[from_node_->getAtoms().size() - (1 + i)]);
		}
	}
	
	return true;
}

bool Transition::finalise(const std::vector<const Atom*>& initial_facts)
{
	Bindings& bindings = from_node_->getDTG().getBindings();
	
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions_->begin(); ci != all_preconditions_->end(); ci++)
	{
		const Atom* precondition = (*ci).first;
		if (precondition->getPredicate().isStatic())
		{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << "[Transition::finalise] *: ";
			precondition->print(std::cout, bindings, step_->getStepId());
			std::cout << std::endl;
#endif
			
			std::set<const Object*> updated_domain_variables[precondition->getArity()];
			
			// Find all facts which can unify with this precondition.
			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
			{
				const Atom* initial_fact = *ci;
				if (bindings.canUnify(*precondition, getStepId(), *initial_fact, Step::INITIAL_STEP))
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "Supporting fact: ";
					initial_fact->print(std::cout, bindings, Step::INITIAL_STEP);
					std::cout << "." << std::endl;
#endif
					for (unsigned int i = 0; i < initial_fact->getArity(); ++i)
					{
						const std::vector<const Object*>& initial_fact_variable_domain = initial_fact->getTerms()[i]->getDomain(Step::INITIAL_STEP, bindings);
						updated_domain_variables[i].insert(initial_fact_variable_domain.begin(), initial_fact_variable_domain.end());
					}
				}
			}
			
			// Prune the original variable domains.
			for (unsigned int i = 0; i < precondition->getArity(); ++i)
			{
				const std::vector<const Object*>& org_variable_domain = precondition->getTerms()[i]->getDomain(getStepId(), bindings);
				std::vector<const Object*> copy_org_variable_domain = org_variable_domain;
				std::sort(copy_org_variable_domain.begin(), copy_org_variable_domain.end());
				
				std::set<const Object*> supported_objects = updated_domain_variables[i];
				
				std::vector<const Object*> intersection(std::max(org_variable_domain.size(), supported_objects.size()));
				std::vector<const Object*>::iterator ci = std::set_intersection(supported_objects.begin(), supported_objects.end(), copy_org_variable_domain.begin(), copy_org_variable_domain.end(), intersection.begin());
				
				intersection.resize(std::distance(intersection.begin(), ci));
				if (intersection.empty())
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "[Transition::finalise] Transition is NOT possible!" << std::endl;
#endif					
					return false;
				}
				
				precondition->getTerms()[i]->makeDomainEqualTo(getStepId(), intersection, bindings);
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Updated " << i << " variable domain to: ";
				for (std::vector<const Object*>::const_iterator ci = org_variable_domain.begin(); ci != org_variable_domain.end(); ++ci)
				{
					std::cout << **ci << " ";
				}
				std::cout << "." << std::endl;
#endif
			}
		}
	}
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "[Transition::finalise] Transition is possible!" << std::endl;
#endif
	return true;
}

std::ostream& operator<<(std::ostream& os, const Transition& transition)
{
	os << "Transition from: (" << &transition.getFromNode() << ") >>>==--> (" << &transition.getToNode() << ")" << std::endl;
	transition.getFromNode().print(os);
	os << std::endl << " to " << std::endl;
	transition.getToNode().print(os);
	os << std::endl;
	transition.getAction().print(os, transition.getFromNode().getDTG().getBindings(), transition.getStepId());

	std::vector<std::pair<const Atom*, InvariableIndex> > all_preconditions = transition.getAllPreconditions();
	os << "All preconditions: " << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions.begin(); ci != all_preconditions.end(); ci++)
	{
		(*ci).first->print(os, transition.getFromNode().getDTG().getBindings(), transition.getStepId());
		os << " (" << (*ci).second << ") Ox" << (*ci).first << "." << std::endl;
	}
	os << "Balanced term: " << transition.getBalancedTerm() << std::endl;
	os << "Preconditions linked to from node: " << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition.getFromNodePreconditions().begin(); ci != transition.getFromNodePreconditions().end(); ++ci)
	{
		if ((*ci).first == NULL)
			os << "\tNULL";
		else
			(*ci).first->print(os, transition.getFromNode().getDTG().getBindings(), transition.getStepId());
		os << std::endl;
	}
	os << "Effects linked to to node: " << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition.getToNodeEffects().begin(); ci != transition.getToNodeEffects().end(); ++ci)
	{
		if ((*ci).first == NULL)
			os << "\tNULL";
		else
			(*ci).first->print(os, transition.getFromNode().getDTG().getBindings(), transition.getStepId());
		os << std::endl;
	}
	os << "All persistent preconditions: " << std::endl;
	for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = transition.persistent_sets_->begin(); ci != transition.persistent_sets_->end(); ci++)
	{
		os << (*ci).first << " <-> " << (*ci).second << std::endl;
	}
	return os;
}

};

};
