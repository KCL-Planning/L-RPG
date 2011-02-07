#include "transition.h"

#include "dtg_manager.h"
#include "dtg_node.h"
#include "property_space.h"
#include "../formula.h"
#include "../parser_utils.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

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

	return Transition::createTransition(enablers, action_step, from_node, to_node, initial_facts);
}

Transition* Transition::createTransition(const std::vector<BoundedAtom>& enablers, const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
{
	std::cout << std::endl << std::endl;
	std::cout << "[Transition::createTransition] NEW TRANSITION!!!!" << std::endl;
	std::cout << "From: " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), action_step->getStepId());
	std::cout << std::endl;

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
	std::vector<const BoundedAtom*> added_facts;
	std::vector<const BoundedAtom*> removed_facts;
	std::vector<const BoundedAtom*> persistent_facts;   // Stored from the to node.
	
	std::vector<std::pair<const BoundedAtom*, InvariableIndex> > optional_preconditions;
	
	unsigned int added_invariable_facts = 0;
	unsigned int removed_invariable_facts = 0;

	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* from_fact = *ci;
		
		assert (from_node.getIndex(*from_fact) != NO_INVARIABLE_INDEX);
		
		bool is_removed = true;
		for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* to_fact = *ci;
			
			assert (to_node.getIndex(*to_fact) != NO_INVARIABLE_INDEX);

			// If the same fact appears in the to node we assume it is not deleted and thus is persistent. The next block of code
			// determines if this is really the case or if the action deletes and adds this fact.
			if (from_node.getIndex(*from_fact) == to_node.getIndex(*to_fact) && bindings.canUnify(from_fact->getAtom(), from_fact->getId(), to_fact->getAtom(), to_fact->getId()))
			{
				is_removed = false;
				persistent_facts.push_back(to_fact);
			}
		}

		if (is_removed)
		{
			std::cout << "- Removed fact: ";
			from_fact->print(std::cout, bindings);
			
			///if (&from_fact->getProperty()->getPropertyState().getPropertySpace() == &from_node.getDTG().getPropertySpace())
			if (from_node.getDTG().containsPropertySpace(from_fact->getProperty()->getPropertyState().getPropertySpace()))
			{
				++removed_invariable_facts;
				std::cout << "[" << removed_invariable_facts << "]";
				removed_facts.push_back(from_fact);
			}
			else
			{
				optional_preconditions.push_back(std::make_pair(from_fact, from_node.getIndex(*from_fact)));
				std::cout << "[" << added_invariable_facts << "](optional)";
			}
			std::cout << std::endl;
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* to_fact = *ci;
		bool is_added = true;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* from_fact = *ci;

			// Check if the fact in the to node is added or was already present.
			bool is_added = true;
			
			if (to_node.getIndex(*to_fact) == from_node.getIndex(*from_fact) && bindings.canUnify(to_fact->getAtom(), to_fact->getId(), from_fact->getAtom(), from_fact->getId()))
			{
				is_added = false;
				break;
			}
		}
		
		if (is_added)
		{
			std::cout << "- Added fact: ";
			to_fact->print(std::cout, bindings);
			
			///if (&to_fact->getProperty()->getPropertyState().getPropertySpace() == &to_node.getDTG().getPropertySpace())
			if (to_node.getDTG().containsPropertySpace(to_fact->getProperty()->getPropertyState().getPropertySpace()))
			{
				++added_invariable_facts;
				std::cout << "[" << added_invariable_facts << "]";
				added_facts.push_back(to_fact);
			}
			else
			{
				optional_preconditions.push_back(std::make_pair(to_fact, to_node.getIndex(*to_fact)));
				std::cout << "[" << added_invariable_facts << "](optional)";
			}
			std::cout << std::endl;
		}
	}

	StepID action_step_id = action_step->getStepId();
	const Action& action = action_step->getAction();
	
	const std::vector<const Atom*>& effects = action_step->getAction().getEffects();

	// Check the facts that are persistent due to the fact that they are removed and added by this action. These are 
	// not found by the previous analysis because we only compare the index of the invariable and check if the variable 
	// domains overlap. An action is invalid if it does not interact with the nodes at all, so an action which adds and 
	// removes the same fact, e.g. drive-truck removes (at ?truck ?location) and adds (at ?truck ?location). Based on the 
	// previous analysis we conclude that the action does not interact, but we might discover that the action adds and 
	// removes a similar fact and does interact with the nodes.
	for (std::vector<const BoundedAtom*>::reverse_iterator persistent_ci = persistent_facts.rbegin(); persistent_ci != persistent_facts.rend(); persistent_ci++)
	{
		const BoundedAtom* persisent_atom = *persistent_ci;
		bool is_added = false;
		bool is_deleted = false;

		// Check if the transitions removes this fact.
		for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
		{
			const Atom* effect = *ci;

			if (effect->isNegative() == persisent_atom->getAtom().isNegative() && 
			    bindings.canUnify(*effect, action_step_id, persisent_atom->getAtom(), persisent_atom->getId()))
			{
				is_added = true;
			}

			if (bindings.affects(*effect, action_step_id, persisent_atom->getAtom(), persisent_atom->getId()))
			{
				is_deleted = true;
			}
		}

		if (is_added && is_deleted)
		{
			added_facts.push_back(persisent_atom);
			
			if (from_node.getDTG().containsPropertySpace(persisent_atom->getProperty()->getPropertyState().getPropertySpace()))
			///if (&persisent_atom->getProperty()->getPropertyState().getPropertySpace() == &from_node.getDTG().getPropertySpace())
			{
				++added_invariable_facts;
			}

			// Search for the equivalent in the from node.
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* from_atom = *ci;

				if (from_node.getIndex(*from_atom) == to_node.getIndex(*persisent_atom) && bindings.canUnify(persisent_atom->getAtom(), persisent_atom->getId(), from_atom->getAtom(), from_atom->getId()))
				{
					removed_facts.push_back(from_atom);
					if (from_node.getDTG().containsPropertySpace(from_atom->getProperty()->getPropertyState().getPropertySpace()))
					///if (&from_atom->getProperty()->getPropertyState().getPropertySpace() == &from_node.getDTG().getPropertySpace())
					{
						++removed_invariable_facts;
					}
					break;
				}
			}

			// This atom is no longer considered presistent.
			persistent_facts.erase(persistent_ci.base() - 1);
		}
	}

	// An action which does not interact with any of the nodes is invalid.
	if (removed_facts.size() == 0 || added_facts.size() == 0)
	{
		std::cout << "[Transition::createTransition] Nothing is added or removed by this action, not relevant!" << std::endl;
		return NULL;
	}
	
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &action.getPrecondition());
	
	/**
	 * Determine which of the variable(s) of the action are invariable and check if this relation holds for all removed nodes.
	 */
	const VariableDomain* action_invariable = NULL;
	const Variable* action_invariable_term = NULL;
	std::vector<std::pair<const Atom*, const BoundedAtom*> > precondition_to_from_node_bindings;
	std::vector<std::pair<const Atom*, InvariableIndex> > precondition_mapping_to_from_node;
	for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts.begin(); ci != removed_facts.end(); ci++)
	{
		const BoundedAtom* removed_fact = *ci;

		InvariableIndex invariable_term_index = from_node.getIndex(*removed_fact);

		// Validate that the removed fact is part of the precondition.
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;

			// Every precondition which matches with the removed node is added as a condidate and we check if the invariable constraint is
			// satisfied.
			if (bindings.canUnify(*precondition, action_step_id, removed_fact->getAtom(), removed_fact->getId()))
			{
				precondition_to_from_node_bindings.push_back(std::make_pair(precondition, removed_fact));
				precondition_mapping_to_from_node.push_back(std::make_pair(precondition, from_node.getIndex(*removed_fact)));
				
				// If the removed node is not related to the invariable of the DTG we move on.
				if (!from_node.getDTG().containsPropertySpace(removed_fact->getProperty()->getPropertyState().getPropertySpace()))
				///if (&removed_fact->getProperty()->getPropertyState().getPropertySpace() != &from_node.getDTG().getPropertySpace())
				{
					std::cout << "Skip the removed fact: ";
					removed_fact->print(std::cout, bindings);
					std::cout << std::endl;
					continue;
				}
				
				// Check which variable of the action matches with the invariable precondition term.
				for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ci++)
				{
					const Variable* action_variable = *ci;
					
					assert (invariable_term_index != NO_INVARIABLE_INDEX);
					
					if (action_variable->isTheSameAs(action_step_id, *precondition->getTerms()[invariable_term_index], action_step_id, bindings))
					{
						if (action_invariable == NULL)
						{
							action_invariable = &bindings.getVariableDomain(action_step_id, *action_variable);
							action_invariable_term = action_variable;
							std::cout << "Found invariable: " << *action_invariable << std::endl;
						}
						else
						{
							if (action_invariable != &bindings.getVariableDomain(action_step_id, *action_variable))
							{
								std::cout << "Another invariable!? " << bindings.getVariableDomain(action_step_id, *action_variable) << std::endl;
								std::cout << "[Transition::createTransition] Error, found a precondition which is linked to a different invariable which we cannot handle..." << std::endl;
								//assert (false);
								return NULL;
							}
						}
					}
				}
			}
		}
	}
	
	if (action_invariable == NULL)
	{
		std::cout << "[Transition::createTransition] Failed to find the invariable, break!" << std::endl;
		return NULL;
	}
	
	/**
	 * Make sure none of the preconditions are mutex with atoms in the start node.
	 */
	std::cout << "[Transition::createTransition] Check mutex relations between the preconditions and From Node." << std::endl;
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		
		InvariableIndex precondition_invariable = INVALID_INDEX_ID;
		
		for (InvariableIndex i = 0; i < precondition->getTerms().size(); i++)
		{
			if (precondition->getTerms()[i]->isTheSameAs(action_step_id, *action_invariable_term, action_step_id, bindings))
			{
				precondition_invariable = i;
				break;
			}
		}

		if (precondition_invariable == INVALID_INDEX_ID)
		{
			std::cout << "** Not linked to the invariable - skip!" << std::endl;
		}
		
		for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* from_node_bounded_atom = *ci;
			
			std::cout << "* Process: ";
			precondition->print(std::cout, bindings, action_step_id);
			std::cout << " v.s. ";
			from_node_bounded_atom->print(std::cout, bindings);
			std::cout << std::endl;
			
			if (from_node_bounded_atom->isMutexWith(precondition->getPredicate(), precondition_invariable))
			{
				std::cout << "[Transition::createTransition] The precondition ";
				precondition->print(std::cout, bindings, action_step_id);
				std::cout << " is mutex with ";
				from_node_bounded_atom->print(std::cout, bindings);
				std::cout << std::endl;
				return NULL;
			}
		}
	}
	
	/**
	 * Check the effects of this action, make sure it deletes all the deleted nodes and does not touch the persistent nodes. Also
	 * make sure it adds all the nodes which are to be added.
	 */
	unsigned int found_added_facts = 0;
	unsigned int found_removed_facts = 0;
	std::vector<std::pair<const Atom*, const BoundedAtom*> > add_effects_to_to_node_bindings;
	std::vector<std::pair<const Atom*, InvariableIndex> > add_effects_mapping_to_to_node;
	std::vector<std::pair<const Atom*, InvariableIndex> > remove_effects_mapping_to_to_node;
	std::cout << "[Transition::createTransition] Make sure all added and deleted atoms are accounted for and no mutex relations exists." << std::endl;
	for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		const Atom* effect = *ci;
		
		std::cout << "* Check the effects of this action: ";
		effect->print(std::cout, bindings, action_step_id);
		std::cout << std::endl;
		
		InvariableIndex effect_invariable = INVALID_INDEX_ID;

		for (InvariableIndex i = 0; i < effect->getTerms().size(); i++)
		{
			if (effect->getTerms()[i]->isTheSameAs(action_step_id, *action_invariable_term, action_step_id, bindings))
			{
				effect_invariable = i;
				break;
			}
		}
		
		if (effect_invariable == INVALID_INDEX_ID)
		{
			std::cout << "** Not linked to the invariable - skip!" << std::endl;
		}
		
		// Check if all added_facts are accounted for.
		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts.begin(); ci != added_facts.end(); ci++)
		{
			const BoundedAtom* added_fact = *ci;
			
			if (added_fact->getAtom().isNegative() == effect->isNegative() &&
					bindings.canUnify(*effect, action_step_id, added_fact->getAtom(), added_fact->getId()) &&
					effect_invariable == to_node.getIndex(*added_fact))
			{
				++found_added_facts;
				add_effects_to_to_node_bindings.push_back(std::make_pair(effect, added_fact));
				add_effects_mapping_to_to_node.push_back(std::make_pair(effect, to_node.getIndex(*added_fact)));
			}
		}
		
		// Do the same for removed facts.
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts.begin(); ci != removed_facts.end(); ci++)
		{
			const BoundedAtom* removed_fact = *ci;
			
			if (removed_fact->getAtom().isNegative() != effect->isNegative() &&
			    bindings.canUnify(*effect, action_step_id, removed_fact->getAtom(), removed_fact->getId()) &&
			    effect_invariable == from_node.getIndex(*removed_fact))
			{
				++found_removed_facts;
				remove_effects_mapping_to_to_node.push_back(std::make_pair(effect, from_node.getIndex(*removed_fact)));
			}
		}
		
		// Make sure the persistent facts are left untouched, if it is than this action cannot be applied.
		for (std::vector<const BoundedAtom*>::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
		{
			const BoundedAtom* persistent_fact = *ci;
			
			if (persistent_fact->getAtom().isNegative() != effect->isNegative() &&
			    bindings.canUnify(*effect, action_step_id, persistent_fact->getAtom(), persistent_fact->getId()) &&
			    effect_invariable == to_node.getIndex(*persistent_fact))
			{
				std::cout << "The presistent fact: ";
				persistent_fact->print(std::cout, bindings);
				std::cout << " is not left untouched!" << std::endl;
				return NULL;
			}
		}
		
		// Lastly, make sure this effect is not mutex with the existent nodes already present in the to_node.
		for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* to_node_atom = *ci;

			if (to_node_atom->getAtom().isNegative() == effect->isNegative() &&
			    to_node_atom->isMutexWith(effect->getPredicate(), effect_invariable))
			{
				std::cout << "The to_node fact: ";
				to_node_atom->print(std::cout, bindings);
				std::cout << " is mutex with the effect ";
				effect->print(std::cout, bindings, action_step_id);
				std::cout << std::endl;
				return NULL;
			}
		}
	}
	std::cout << "Added invariable facts: [" << found_added_facts << "/" << added_invariable_facts << "]" << std::endl;
	std::cout << "Removed invariable facts: [" << found_removed_facts << "/" << removed_invariable_facts << "]" << std::endl;

	assert (added_invariable_facts >= found_added_facts);
	assert (removed_invariable_facts >= found_removed_facts);
	
//	if (found_added_facts != added_facts.size())
	if (found_added_facts != added_invariable_facts)
	{
		std::cout << "[Transition::createTransition] Not all added facts were accounted for!" << std::endl;
		return NULL;
	}
	
//	if (found_removed_facts != removed_facts.size())
	if (found_removed_facts != removed_invariable_facts)
	{
		std::cout << "[Transition::createTransition] Not all removed facts were accounted for!" << std::endl;
		return NULL;
	}
	
	// Copy the action and its variable domains and bind it to the new transition.
	// TODO is this necessary???
	StepID new_action_step_id = bindings.createVariableDomains(action);
	StepPtr new_action_step(new Step(new_action_step_id, action));

	/**
	 * Test the optional preconditions.
	 */
	for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = optional_preconditions.begin(); ci != optional_preconditions.end(); ci++)
	{
		const BoundedAtom* optional_precondition = (*ci).first;
		InvariableIndex invariable_index = (*ci).second;
		
		/**
		 * Test if there exists a precondition with the same predicate name and can unify with the invariable. If that's the case then
		 * we have to unify with that precondition too.
		 */
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;
			
			if (precondition->getPredicate().getName() == optional_precondition->getAtom().getPredicate().getName() &&
			    precondition->getPredicate().getArity() == optional_precondition->getAtom().getArity())
			{
				if (precondition->getTerms()[invariable_index]->canUnify(action_step_id, *optional_precondition->getAtom().getTerms()[invariable_index], optional_precondition->getId(), bindings))
				{
					std::cout << "Unify the optional precondition ";
					optional_precondition->print(std::cout, bindings);
					std::cout << " with: ";
					precondition->print(std::cout, bindings, action_step_id);
					std::cout << std::endl;
					
					if (!bindings.unify(*precondition, new_action_step_id, optional_precondition->getAtom(), optional_precondition->getId()))
					{
						std::cout << "Could not bind the optional precondition." << std::endl;
						return NULL;
					}
				}
			}
		}
	}
	
	/**
	 * If all tests were succesful, perform the actual bindings!
	 */
	std::cout << "[Transition::createTransition] Unify the effects!" << std::endl;
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = add_effects_to_to_node_bindings.begin(); ci != add_effects_to_to_node_bindings.end(); ci++)
	{
		const Atom* added_effect = (*ci).first;
		const BoundedAtom* to_node_atom = (*ci).second;
		
		if (!bindings.unify(*added_effect, new_action_step_id, to_node_atom->getAtom(), to_node_atom->getId()))
		{
			std::cout << "[Transition::createTransition] Could not perform the actual bindings on effects!" << std::endl;
			return NULL;
		}
/*
		// Test if the bindings have actually been made.
		for (unsigned int i = 0; i < added_effect->getArity(); i++)
		{
			const Term* effect_term = added_effect->getTerms()[i];
			const Term* to_node_term = to_node_atom->getAtom().getTerms()[i];
			
			assert (to_node_term->isTheSameAs(to_node_atom->getId(), *effect_term, new_action_step_id, bindings));
		}
*/
	}
	
	std::cout << "[Transition::createTransition] Unify the preconditions!" << std::endl;
	for (std::vector<std::pair<const Atom*, const BoundedAtom*> >::const_iterator ci = precondition_to_from_node_bindings.begin(); ci != precondition_to_from_node_bindings.end(); ci++)
	{
		const Atom* removed_effect = (*ci).first;
		const BoundedAtom* from_node_atom = (*ci).second;
		
		if (!bindings.unify(*removed_effect, new_action_step_id, from_node_atom->getAtom(), from_node_atom->getId()))
		{
			std::cout << "[Transition::createTransition] Could not perform the actual bindings on preconditions!" << std::endl;
			std::cout << "[Transition::createTransition] ";
			from_node_atom->print(std::cout, bindings);
			std::cout << " couldn't bind with: ";
			removed_effect->print(std::cout, bindings, new_action_step_id);
			std::cout << std::endl;
///			assert (false);
			return NULL;
		}
/*
		// Test if the bindings have actually been made.
		for (unsigned int i = 0; i < removed_effect->getArity(); i++)
		{
			const Term* precondition_term = removed_effect->getTerms()[i];
			const Term* from_node_term = from_node_atom->getAtom().getTerms()[i];
			
			assert (from_node_term->isTheSameAs(from_node_atom->getId(), *precondition_term, new_action_step_id, bindings));
		}
*/
	}
	
	/**
	 * Post process by checking if the transitiosn did not violate any static preconditions.
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
				if (bindings.canUnify(*initial_fact, Step::INITIAL_STEP, *precondition, new_action_step_id))
				{
					is_supported = true;
					break;
				}
			}
			
			if (!is_supported)
			{
				std::cout << "[Transition::createTransition] The static precondition: ";
				precondition->print(std::cout, bindings, new_action_step_id);
				std::cout << " is not supported!" << std::endl;
				return NULL;
			}
		}
	}

	std::cout << "Created a transition from " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	new_action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), new_action_step->getStepId());
	std::cout << std::endl;

	return new Transition(enablers, new_action_step, from_node, to_node, precondition_mapping_to_from_node, add_effects_mapping_to_to_node, remove_effects_mapping_to_to_node, *action_invariable_term);
}

Transition::Transition(const std::vector< MyPOP::SAS_Plus::BoundedAtom >& enablers, MyPOP::StepPtr step, MyPOP::SAS_Plus::DomainTransitionGraphNode& from_node, MyPOP::SAS_Plus::DomainTransitionGraphNode& to_node, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& preconditions, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& effects, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& affected, const Variable& action_invariable)
	: enablers_(enablers), step_(step), from_node_(&from_node), to_node_(&to_node), preconditions_(preconditions), effects_(effects), affected_(affected), action_invariable_(&action_invariable)
{
/*	std::cout << "New transition: " << step->getAction() << std::endl;
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		(*ci)->print(std::cout);
		std::cout << ", ";
	}
	std::cout << "." << std::endl;
*/
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

void Transition::getAllPreconditions(std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions) const
{
	assert (preconditions_.size() > 0);

	std::cout << "Invariable: " << *action_invariable_;
	std::cout << "(" << preconditions_[0].second << ")";
	std::cout << std::endl;

	std::vector<const Atom*> action_preconditions;
	
	Utility::convertFormula(action_preconditions, &step_->getAction().getPrecondition());
	for (std::vector<const Atom*>::const_iterator ci = action_preconditions.begin(); ci != action_preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		InvariableIndex invariable_index = std::numeric_limits<unsigned int>::max();
		
		for (unsigned int i = 0; i < precondition->getTerms().size(); i++)
		{
			const Term* term = precondition->getTerms()[i];
			if (term->isTheSameAs(step_->getStepId(), *action_invariable_, step_->getStepId(), from_node_->getDTG().getBindings()))
			{
				invariable_index = i;
				break;
			}
		}
		
		preconditions.push_back(std::make_pair(precondition, invariable_index));
	}
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

};

};
