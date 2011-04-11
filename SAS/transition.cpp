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


Transition* Transition::createTransition(const std::vector<BoundedAtom>& enablers, const Action& action, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
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
		transition = Transition::createTransition(enablers, action_step, from_node, to_node, initial_facts);
	}
	else
	{
		transition = Transition::createSimpleTransition(enablers, action_step, from_node, to_node, initial_facts);
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

Transition* Transition::createSimpleTransition(const std::vector<BoundedAtom>& enablers, const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
{
/*	std::cout << std::endl << std::endl;
	std::cout << "[Transition::createSimpleTransition] NEW TRANSITION!!!!" << std::endl;
	std::cout << "From: " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), action_step->getStepId());
	std::cout << std::endl;
*/
	if (&to_node.getDTG() != &from_node.getDTG())
	{
		std::cout << "[Transition::createSimpleTransition] FATAL ERROR! The nodes are not part of the same DTG!" << std::endl;
		assert(false);
	}

	DTGBindings& bindings = from_node.getDTG().getBindings();

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
		
		// Check if the property space this from_fact belongs to has already been created.
		const PropertySpace& from_fact_property_space = from_fact->getProperty()->getPropertyState().getPropertySpace();
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
	
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* to_fact = *ci;
	
		// Check if the property space this to_fact belongs to has already been created.
		const PropertySpace& to_fact_property_space = to_fact->getProperty()->getPropertyState().getPropertySpace();
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
	
/*	for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		std::cout << "Add / Remove sets: " << (*ci).first << std::endl;
		
		const std::vector<const BoundedAtom*>* add_set = (*ci).second.first;
		const std::vector<const BoundedAtom*>* remove_set = (*ci).second.second;
		
		for (std::vector<const BoundedAtom*>::const_iterator ci = add_set->begin(); ci != add_set->end(); ci++)
		{
			const BoundedAtom* add_atom = *ci;
			
			std::cout << "+ ";
			add_atom->print(std::cout, bindings);
			std::cout << std::endl;
		}
		
		for (std::vector<const BoundedAtom*>::const_iterator ci = remove_set->begin(); ci != remove_set->end(); ci++)
		{
			const BoundedAtom* add_atom = *ci;
			
			std::cout << "- ";
			add_atom->print(std::cout, bindings);
			std::cout << std::endl;
		}
	}
*/

	/**
	 * Make sure all the added and deleted facts are accounted for.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> > precondition_mapping_to_from_node; // Pair of precondition and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > add_effects_mapping_to_to_node;    // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > remove_effects_mapping_to_to_node; // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > persistent_preconditions; // Pair of precondition and invariable index.
	
	std::vector<std::pair<const Atom*, const BoundedAtom*> > add_effects_to_to_node_bindings;
	std::vector<std::pair<const Atom*, const BoundedAtom*> > precondition_to_from_node_bindings;
	
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
					add_effects_mapping_to_to_node.push_back(std::make_pair(effect, to_node.getIndex(*added_fact)));
					add_effects_to_to_node_bindings.push_back(std::make_pair(effect, added_fact));
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
					precondition_mapping_to_from_node.push_back(std::make_pair(precondition, from_node.getIndex(*removed_fact)));
					precondition_to_from_node_bindings.push_back(std::make_pair(precondition, removed_fact));
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
					remove_effects_mapping_to_to_node.push_back(std::make_pair(effect, from_node.getIndex(*removed_fact)));
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
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = add_effects_to_to_node_bindings.begin(); ci != add_effects_to_to_node_bindings.end(); ci++)
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
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = precondition_to_from_node_bindings.begin(); ci != precondition_to_from_node_bindings.end(); ci++)
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
	
	std::vector<std::pair<const Atom*, InvariableIndex> > all_precondition_mappings;
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		all_precondition_mappings.push_back(std::make_pair(precondition, NO_INVARIABLE_INDEX));
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
	
	return new Transition(enablers, action_step, from_node, to_node, precondition_mapping_to_from_node, add_effects_mapping_to_to_node, remove_effects_mapping_to_to_node, persistent_preconditions, *property_space_action_invariables, all_precondition_mappings);
}

Transition* Transition::createTransition(const std::vector<BoundedAtom>& enablers, const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
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

	DTGBindings& bindings = from_node.getDTG().getBindings();

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
	
	/**
	 * Persistent facts appear in both the start and end node and are not affected by the transition. They are stored 
	 * as <from_node, to_node>.
	 */
	std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> > persistent_facts;

	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* from_fact = *ci;
		
		// Check if the property space this from_fact belongs to has already been created.
		const PropertySpace& from_fact_property_space = from_fact->getProperty()->getPropertyState().getPropertySpace();
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
		
		assert (from_node.getIndex(*from_fact) != NO_INVARIABLE_INDEX);
		
		/**
		 * Determine if this fact has been removed (i.e. is not part of the to_node). If the fact has not been removed it is marked as
		 * persistent. This can later be undone if we find that the fact is removed and later added by the given action.
		 */
		bool is_removed = true;
		for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* to_fact = *ci;
			
			assert (to_node.getIndex(*to_fact) != NO_INVARIABLE_INDEX);

			// If the same fact appears in the to node we assume it is not deleted and thus is persistent. The next block of code
			// determines if this is really the case or if the action deletes and adds this fact.
			if (from_node.getIndex(*from_fact) == to_node.getIndex(*to_fact) &&
			    to_fact->getAtom().isNegative() == from_fact->getAtom().isNegative() &&
			    bindings.canUnify(from_fact->getAtom(), from_fact->getId(), to_fact->getAtom(), to_fact->getId()))
			{
				is_removed = false;
				persistent_facts.push_back(std::make_pair(from_fact, to_fact));
			}
		}

		if (is_removed)
		{
			add_remove_list.second->push_back(from_fact);
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* to_fact = *ci;
	
		// Check if the property space this to_fact belongs to has already been created.
		const PropertySpace& to_fact_property_space = to_fact->getProperty()->getPropertyState().getPropertySpace();
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
		
		const PropertySpace& from_fact_property_space = from_persistent_atom->getProperty()->getPropertyState().getPropertySpace();		
		std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::iterator from_property_space_i = property_space_balanced_sets.find(&from_fact_property_space);
		assert (from_property_space_i != property_space_balanced_sets.end());
		std::vector<const BoundedAtom*>* remove_list = (*from_property_space_i).second.second;
		
		const PropertySpace& to_fact_property_space = to_persistent_atom->getProperty()->getPropertyState().getPropertySpace();		
		std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::iterator to_property_space_i = property_space_balanced_sets.find(&to_fact_property_space);
		assert (to_property_space_i != property_space_balanced_sets.end());
		std::vector<const BoundedAtom*>* add_list = (*to_property_space_i).second.first;
		

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
//			std::cout << "Invallid persistent fact!" << std::endl;
			remove_list->push_back(from_persistent_atom);
			add_list->push_back(to_persistent_atom);
			persistent_facts.erase(persistent_ci.base() - 1);
		}
	}
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		std::cout << "Add / Remove sets: " << (*ci).first << std::endl;
		
		const std::vector<const BoundedAtom*>* add_set = (*ci).second.first;
		const std::vector<const BoundedAtom*>* remove_set = (*ci).second.second;
		
		for (std::vector<const BoundedAtom*>::const_iterator ci = add_set->begin(); ci != add_set->end(); ci++)
		{
			const BoundedAtom* add_atom = *ci;
			
			std::cout << "+ ";
			add_atom->print(std::cout, bindings);
			std::cout << std::endl;
		}
		
		for (std::vector<const BoundedAtom*>::const_iterator ci = remove_set->begin(); ci != remove_set->end(); ci++)
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
	
	for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		// Only consider property spaces which get removed and added, if a fact is only added or removed it's an optional precondition.
		const PropertySpace* property_space = (*ci).first;
		std::vector<const BoundedAtom*>* added_facts = (*ci).second.first;
		std::vector<const BoundedAtom*>* removed_facts = (*ci).second.second;
		
		if (added_facts->empty() || removed_facts->empty())
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
//		std::cout << "Find invariable for all added facts." << std::endl;
		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts->begin(); ci != added_facts->end(); ci++)
		{
			const BoundedAtom* added_fact = *ci;
			
//			std::cout << "- For ";
//			added_fact->print(std::cout, bindings);
//			std::cout << std::endl;
			
			std::set<const std::vector<const Object*>*> possible_add_invariables;
			
			for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
				
				if (bindings.canUnify(*effect, action_step_id, added_fact->getAtom(), added_fact->getId()))
				{
//					std::cout << "Get the index of ";
//					added_fact->print(std::cout, bindings);
//					std::cout << " from ";
//					to_node.print(std::cout);
//					std::cout << std::endl;
					
//					std::cout << "Possible invariable: ";
//					effect->print(std::cout, bindings, action_step_id);
//					std::cout << "(" << to_node.getIndex(*added_fact) << ")" << std::endl;
					
					possible_add_invariables.insert(&effect->getTerms()[to_node.getIndex(*added_fact)]->getDomain(action_step_id, bindings));
				}
			}
			
			// Prune the possible range.
			std::set<const std::vector<const Object*>*> tmp_set;
			std::set_intersection(possible_add_invariables.begin(), possible_add_invariables.end(), action_invariables.begin(), action_invariables.end(), std::inserter(tmp_set, tmp_set.begin()));
			
			action_invariables.clear();
			action_invariables.insert(tmp_set.begin(), tmp_set.end());
		}
		
//		std::cout << "Find invariable for all removed facts." << std::endl;
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts->begin(); ci != removed_facts->end(); ci++)
		{
			const BoundedAtom* removed_fact = *ci;
//			std::cout << "- For ";
//			removed_fact->print(std::cout, bindings);
//			std::cout << std::endl;
			
			///std::set<const Term*> possible_remove_invariables;
			std::set<const std::vector<const Object*>*> possible_remove_invariables;
			
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				
				if (bindings.canUnify(*precondition, action_step_id, removed_fact->getAtom(), removed_fact->getId()))
				{
//					std::cout << "Possible invariable: ";
//					precondition->print(std::cout, bindings, action_step_id);
//					std::cout << "(" << from_node.getIndex(*removed_fact) << ")" << std::endl;
					
					possible_remove_invariables.insert(&precondition->getTerms()[from_node.getIndex(*removed_fact)]->getDomain(action_step_id, bindings));
				}
			}
			
			// Prune the possible range.
			///std::set<const Term*> tmp_set;
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
			/*
			///for (std::set<const Term*>::const_iterator ci = action_invariables.begin(); ci != action_invariables.end(); ci++)
			for (std::set<const std::vector<const Object*>*>::const_iterator ci = action_invariables.begin(); ci != action_invariables.end(); ci++)
			{
				const Term* term = *ci;
				std::cout << "* " << *term << std::endl;
			}
			*/
			return NULL;
		}
	}
	
	if (property_space_invariables.size() == 0)
	{
		return NULL;
	}

	/**
	 * Now that we know the invariables, make sure none of the persistent nodes are added or removed.
	 */
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::reverse_iterator persistent_ci = persistent_facts.rbegin(); persistent_ci != persistent_facts.rend(); persistent_ci++)
	{
		const BoundedAtom* to_persistent_atom = (*persistent_ci).second;
		
//		std::cout << "Validate persistent fact: ";
//		from_persistent_atom->print(std::cout, bindings);
//		std::cout << std::endl;
		
		const std::vector<const Object*>* invariable_term = property_space_invariables[&to_persistent_atom->getProperty()->getPropertyState().getPropertySpace()];

		// Check if the transitions removes this fact.
		for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
		{
			const Atom* effect = *ci;
//			std::cout << " v.s. effect: ";
//			effect->print(std::cout, bindings, action_step_id);
//			std::cout << std::endl;

			if (effect->isNegative() == to_persistent_atom->getAtom().isNegative() && 
			    bindings.canUnify(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()) &&
			    &effect->getTerms()[to_node.getIndex(*to_persistent_atom)]->getDomain(action_step_id, bindings) == invariable_term)
			{
//				std::cout << "Is added!" << std::endl;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "A persistent is added but not removed. This is invalid!" << std::endl;
#endif
				return NULL;
			}

			if (bindings.affects(*effect, action_step_id, to_persistent_atom->getAtom(), to_persistent_atom->getId()) &&
			    &effect->getTerms()[to_node.getIndex(*to_persistent_atom)]->getDomain(action_step_id, bindings) == invariable_term)
			{
//				std::cout << "Is deleted!" << std::endl;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Removed but not added. This is invalid!" << std::endl;
#endif
				return NULL;
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
		if (bounded_atom->getProperty() == NULL)
		{
			continue;
		}
		const PropertySpace& property_space = bounded_atom->getProperty()->getPropertyState().getPropertySpace();

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
			std::cout << "[" << from_node.getIndex(*bounded_atom) << "]" << std::endl;
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
				
				for (std::vector<Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
				{
					const Property* property = *ci;
//					std::cout << "Compare against: " << property->getPredicate() << std::endl;
					
					if (precondition->getPredicate().getName() == property->getPredicate().getName() &&
						precondition->getPredicate().getArity() == property->getPredicate().getArity())
					{
						InvariableIndex invariable_index = property->getIndex();
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << "Compare if ";
						precondition->print(std::cout, bindings, action_step_id);
						std::cout << "(" << invariable_index << ") is the same as ";
						bounded_atom->print(std::cout, bindings);
						std::cout << "(" << from_node.getIndex(*bounded_atom) << ")" << std::endl;
#endif
						
						if (precondition->getTerms()[invariable_index] != invariable_precondition_term)
						{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << "Invariables don't match, move on!" << std::endl;
#endif
							continue;
						}
						
						if (precondition->getTerms()[invariable_index]->canUnify(action_step_id, *bounded_atom->getAtom().getTerms()[from_node.getIndex(*bounded_atom)], bounded_atom->getId(), bindings))
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
	
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		if (bounded_atom->getProperty() == NULL)
		{
			continue;
		}

		const PropertySpace& property_space = bounded_atom->getProperty()->getPropertyState().getPropertySpace();
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << " * Check effects against the to node: ";
		bounded_atom->print(std::cout, bindings);
		std::cout << std::endl;
#endif

		const std::vector<const Object*>* invariable_term = property_space_invariables[&property_space];
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
			
			for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
			{
				const PropertyState* property_state = *ci;
				
				for (std::vector<Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
				{
					const Property* property = *ci;
//					std::cout << "Compare against: " << property->getPredicate() << std::endl;
					
					if (effect->getPredicate().getName() == property->getPredicate().getName() &&
						effect->getPredicate().getArity() == property->getPredicate().getArity())
					{
						InvariableIndex invariable_index = property->getIndex();
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
						std::cout << " * * * Compare if ";
						effect->print(std::cout, bindings, action_step_id);
						std::cout << "(" << invariable_index << ") is the same as ";
						bounded_atom->print(std::cout, bindings);
						std::cout << "(" << to_node.getIndex(*bounded_atom) << ")" << std::endl;
#endif
						
						if (effect->getTerms()[invariable_index] != invariable_effect_term)
						{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << " * * * * Invariables don't match, move on!" << std::endl;
#endif
							continue;
						}
						
						if (effect->getTerms()[invariable_index]->canUnify(action_step_id, *bounded_atom->getAtom().getTerms()[to_node.getIndex(*bounded_atom)], bounded_atom->getId(), bindings))
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
	
	/**
	 * Make sure all the added and deleted facts are accounted for.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> > precondition_mapping_to_from_node; // Pair of precondition and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > add_effects_mapping_to_to_node;    // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > remove_effects_mapping_to_to_node; // Pair of effect and invariable index.
	std::vector<std::pair<const Atom*, InvariableIndex> > persistent_preconditions;
	
	std::vector<std::pair<const Atom*, const BoundedAtom*> > add_effects_to_to_node_bindings;
	std::vector<std::pair<const Atom*, const BoundedAtom*> > precondition_to_from_node_bindings;

	for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		const PropertySpace* property_space = (*ci).first;
		const std::vector<const BoundedAtom*>* added_facts = (*ci).second.first;
		const std::vector<const BoundedAtom*>* removed_facts = (*ci).second.second;
		
		if (added_facts->empty() || removed_facts->empty())
		{
			continue;
		}
		
		const std::vector<const Object*>* invariable_term = property_space_invariables[property_space];
		
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << " ****************************** " << std::endl;
		std::cout << "Check all added and removed facts are accounted for: " << std::endl;
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
#endif

		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts->begin(); ci != added_facts->end(); ci++)
		{
			const BoundedAtom* added_fact = *ci;
			bool is_added = false;
			
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
				    &effect->getTerms()[to_node.getIndex(*added_fact)]->getDomain(action_step_id, bindings) == invariable_term)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "It's added by: ";
					effect->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
#endif
					is_added = true;
					add_effects_mapping_to_to_node.push_back(std::make_pair(effect, to_node.getIndex(*added_fact)));
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
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts->begin(); ci != removed_facts->end(); ci++)
		{
			const BoundedAtom* removed_fact = *ci;
			bool is_a_precondition = false;
			bool is_removed = false;

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " =++> Make sure the removed fact: ";
			removed_fact->print(std::cout, bindings);
			std::cout << "is accounted for..." << std::endl;
#endif
			
			// Make sure an effect actually added this fact.
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin();  ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				
				if (precondition->isNegative() == removed_fact->getAtom().isNegative() &&
				    bindings.canUnify(*precondition, action_step_id, removed_fact->getAtom(), removed_fact->getId()) &&
				    &precondition->getTerms()[from_node.getIndex(*removed_fact)]->getDomain(action_step_id, bindings) == invariable_term)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "It's removed by: ";
					precondition->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
#endif
					precondition_mapping_to_from_node.push_back(std::make_pair(precondition, from_node.getIndex(*removed_fact)));
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
				    &effect->getTerms()[from_node.getIndex(*removed_fact)]->getDomain(action_step_id, bindings) == invariable_term)
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "It's removed by: ";
					effect->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
#endif
					remove_effects_mapping_to_to_node.push_back(std::make_pair(effect, from_node.getIndex(*removed_fact)));
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
	const PropertySpace* invariable_property_space = NULL;
	const std::vector<const Object*>* invariable_property_space_action_variable = NULL;
	for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		if ((*ci).second.first->empty() || (*ci).second.second->empty())
			continue;
		
		if (invariable_property_space != NULL)
		{
			const std::vector<const Object*>* new_invariable_property_space = property_space_invariables[(*ci).first];
			if (invariable_property_space_action_variable != new_invariable_property_space)
			{
				std::cout << "Previous property space: " << *invariable_property_space <<  " - " << invariable_property_space_action_variable << std::endl;
				std::cout << "New property space: " << *(*ci).first << " - " << property_space_invariables[(*ci).first] << std::endl;
				assert (false);
			}
		}
		else
		{
			invariable_property_space = (*ci).first;
			invariable_property_space_action_variable = property_space_invariables[invariable_property_space];
		}
	}
	
	/**
	 * Test the optional preconditions.
	 */
	for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
	{
		const std::vector<const BoundedAtom*>* added_facts = (*ci).second.first;
		const std::vector<const BoundedAtom*>* removed_facts = (*ci).second.second;
		
		if (!added_facts->empty() && !removed_facts->empty())
		{
			continue;
		}
		
		const std::vector<const BoundedAtom*>* persistent_facts = (!added_facts->empty() ? added_facts : removed_facts);
		const DomainTransitionGraphNode* dtg_node = (!added_facts->empty() ? &to_node : &from_node);
		
		/**
		 * Test if there exists a precondition with the same predicate name and can unify with the invariable. If that's the case then
		 * we have to unify with that precondition too.
		 */
		for (std::vector<const BoundedAtom*>::const_iterator ci = persistent_facts->begin(); ci != persistent_facts->end(); ci++)
		{
			const BoundedAtom* persistent_fact = *ci;
			InvariableIndex invariable_index = dtg_node->getIndex(*persistent_fact);
			assert (invariable_index != INVALID_INDEX_ID);
			
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				
				if (precondition->getPredicate().getName() == persistent_fact->getAtom().getPredicate().getName() &&
					precondition->getPredicate().getArity() == persistent_fact->getAtom().getArity())
				{
					/**
					 * Only allow optional preconditions to merge if they do not refer to the invariable of the balanced set.
					 * TODO: Is this correct?
					 */
					if (precondition->getTerms()[invariable_index]->canUnify(action_step_id, *persistent_fact->getAtom().getTerms()[invariable_index], persistent_fact->getId(), bindings) &&
					    &precondition->getTerms()[dtg_node->getIndex(*persistent_fact)]->getDomain(action_step_id, bindings) != invariable_property_space_action_variable)
					{
//						std::cout << "Unify the optional precondition ";
//						persistent_fact->print(std::cout, bindings);
//						std::cout << " with: ";
//						precondition->print(std::cout, bindings, action_step_id);
//						std::cout << std::endl;

						if (!bindings.unify(*precondition, action_step_id, persistent_fact->getAtom(), persistent_fact->getId()))
						{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
							std::cout << "Could not bind the optional precondition: " << std::endl;
							persistent_fact->print(std::cout, bindings);
							std::cout << " with: ";
							precondition->print(std::cout, bindings, action_step_id);
							std::cout << std::endl;
#endif
							return NULL;
						}
					}
				}
			}
		}
	}
	
//	std::cout << "[Transition::createTransition] Unify the effects!" << std::endl;
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = add_effects_to_to_node_bindings.begin(); ci != add_effects_to_to_node_bindings.end(); ci++)
	{
		const Atom* added_effect = (*ci).first;
		const BoundedAtom* to_node_atom = (*ci).second;
		
		if (!bindings.unify(*added_effect, action_step_id, to_node_atom->getAtom(), to_node_atom->getId()))
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
	
//	std::cout << "[Transition::createTransition] Unify the preconditions!" << std::endl;
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = precondition_to_from_node_bindings.begin(); ci != precondition_to_from_node_bindings.end(); ci++)
	{
		const Atom* precondition = (*ci).first;
		const BoundedAtom* from_node_atom = (*ci).second;
		
		if (!bindings.unify(*precondition, action_step_id, from_node_atom->getAtom(), from_node_atom->getId()))
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
	
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
	std::cout << "[Transition::createTransition] Unify the persistent facts!" << std::endl;
#endif
	for (std::vector<std::pair<const BoundedAtom*, const BoundedAtom*> >::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
	{
		const BoundedAtom* from_node_persistent_fact = (*ci).first;

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS

		const PropertySpace& property_space = from_node_persistent_fact->getProperty()->getPropertyState().getPropertySpace();
		const std::vector<const Object*>* invariable_term = property_space_invariables[&property_space];
		if (invariable_term == NULL)
		{
			std::cout << "Could not find the invariable term of ";
			from_node_persistent_fact->print(std::cout, bindings);
			std::cout << "[" << from_node.getIndex(*from_node_persistent_fact) << "]" << std::endl;
		}
#endif
		InvariableIndex invariable_index = from_node.getIndex(*from_node_persistent_fact);

#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
		std::cout << "Process: ";
		from_node_persistent_fact->print(std::cout, bindings);
		std::cout << "(" << invariable_index << ")" << std::endl;
#endif
		
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			std::cout << " - v.s. ";
			precondition->print(std::cout, bindings, action_step_id);
			std::cout << " -=- invariable = " << invariable_term << std::endl;
#endif
			
			// Make sure the precondition is linked to the invariable.
			const Term* invariable_precondition_term = NULL;
			for (std::map<const PropertySpace*, const std::vector<const Object*>*>::const_iterator ci = property_space_invariables.begin(); ci != property_space_invariables.end(); ci++)
			{
//				const PropertySpace* property_space = (*ci).first;
				const std::vector<const Object*>* domain = (*ci).second;
				for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
				{
					const Term* term = *ci;
					if (&term->getDomain(action_step_id, bindings) == domain)
					{
//						std::cout << "Possible state variable to merge with: " << *property_space << std::endl;
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
				std::cout << "Persistent does not contain the invariable, move on!" << std::endl;
#endif
///				continue;
			}
			
			if (precondition->getTerms()[invariable_index] != invariable_precondition_term)
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Invariables don't match, move on!" << std::endl;
#endif
///				continue;
			}
			
			if (bindings.canUnify(*precondition, action_step_id, from_node_persistent_fact->getAtom(), from_node_persistent_fact->getId()))
			{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
				std::cout << "Unify persistent fact: ";
				from_node_persistent_fact->print(std::cout, bindings);
				std::cout << " with the precondition ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << std::endl;
#endif
				
				if (!bindings.unify(*precondition, action_step_id, from_node_persistent_fact->getAtom(), from_node_persistent_fact->getId()))
				{
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
					std::cout << "Could not unify a persistent fact with the from_node." << std::endl;
#endif
					return NULL;
				}

				precondition_mapping_to_from_node.push_back(std::make_pair(precondition, from_node.getIndex(*from_node_persistent_fact)));
				persistent_preconditions.push_back(std::make_pair(precondition, from_node.getIndex(*from_node_persistent_fact)));
			}
#ifdef ENABLE_MYPOP_SAS_TRANSITION_COMMENTS
			else
			{
				std::cout << "Cannot add the persistent to the preconditions!" << std::endl;
			}
#endif
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
	
	/**
	 * Store for each precondition which variable is invariable for easy access later (getAllPreconditions()). This part assumes
	 * a transition can only work on a single balanced set, so a transition cannot affect two different sets of property spaces.
	 * TODO: Make this more appearant in the function, but splitting up the property_space_balanced_sets into a property_balanced_set
	 * and a separate set for optional preconditions.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> > all_precondition_mappings;
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		
		for (std::map<const PropertySpace*, std::pair<std::vector<const BoundedAtom*>*, std::vector<const BoundedAtom*>* > >::const_iterator ci = property_space_balanced_sets.begin(); ci != property_space_balanced_sets.end(); ci++)
		{
			const PropertySpace* property_space = (*ci).first;
			const std::vector<const BoundedAtom*>* added_facts = (*ci).second.first;
			const std::vector<const BoundedAtom*>* removed_facts = (*ci).second.second;
			
			if (added_facts->empty() || removed_facts->empty())
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
					
					all_precondition_mappings.push_back(std::make_pair(precondition, i));
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
				all_precondition_mappings.push_back(std::make_pair(precondition, NO_INVARIABLE_INDEX));
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
	return new Transition(enablers, action_step, from_node, to_node, precondition_mapping_to_from_node, add_effects_mapping_to_to_node, remove_effects_mapping_to_to_node, persistent_preconditions, *property_space_action_invariables, all_precondition_mappings);
}

Transition::Transition(const std::vector< MyPOP::SAS_Plus::BoundedAtom >& enablers, MyPOP::StepPtr step, MyPOP::SAS_Plus::DomainTransitionGraphNode& from_node, MyPOP::SAS_Plus::DomainTransitionGraphNode& to_node, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& preconditions, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& effects, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& affected, const std::vector<std::pair<const Atom*, InvariableIndex> >& persistent_preconditions, const std::map<const PropertySpace*, const Variable*>& action_invariables, const std::vector<std::pair<const Atom*, InvariableIndex> >& all_precondition_mappings)
	: enablers_(enablers), step_(step), from_node_(&from_node), to_node_(&to_node), preconditions_(preconditions), effects_(effects), affected_(affected), persistent_preconditions_(persistent_preconditions), action_invariables_(&action_invariables), all_precondition_mappings_(all_precondition_mappings)
{
/*	std::cout << "New transition: " << step->getAction() << std::endl;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		(*ci).first->print(std::cout);
		std::cout << "(" << (*ci).second << "), ";
	}
	std::cout << "." << std::endl;*/
}

Transition* Transition::cloneWithNodes(const std::vector<const Atom*>& initial_facts) const
{
	DomainTransitionGraphNode* new_dtg_from_node = new DomainTransitionGraphNode(*from_node_, false);
	DomainTransitionGraphNode* new_dtg_to_node = new DomainTransitionGraphNode(*to_node_, false);
	std::vector<BoundedAtom>* enablers = new std::vector<BoundedAtom>();
	Transition* new_transition = Transition::createTransition(*enablers, step_->getAction(), *new_dtg_from_node, *new_dtg_to_node, initial_facts);
	
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

void Transition::addEnabler(BoundedAtom enabler)
{
	// Don't add the same enabler twice!
	for (std::vector<BoundedAtom>::const_iterator ci = enablers_.begin(); ci != enablers_.end(); ci++)
	{
		if (&enabler.getAtom() == &(*ci).getAtom())
		{
			return;
		}
	}

	enablers_.push_back(enabler);
}

bool Transition::achieves(const BoundedAtom& bounded_atom) const
{
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
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
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = affected_.begin(); ci != affected_.end(); ci++)
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
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = persistent_preconditions_.begin(); ci != persistent_preconditions_.end(); ci++)
	{
		const Atom* persistent_atom = (*ci).first;
		InvariableIndex persistent_index = (*ci).second;
//		std::cout << "is (" << &atom << "){" << index << "} persistent with: ";
//		persistent_atom->print(std::cout, from_node_->getDTG().getBindings(), step_->getStepId());
//		std::cout << "(" << persistent_atom << "){" << persistent_index << "}?" << std::endl;
		
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
	os << "Transition from: ";
	transition.getFromNode().print(os);
	os << " to ";
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
