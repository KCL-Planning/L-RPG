#include "transition.h"

#include "dtg_manager.h"
#include "dtg_node.h"
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

	BindingsFacade& bindings = from_node.getDTG().getBindings();

	// Create the transition's action. We initiate the action by linking its precondition and effects
	// to this node and to_node respectively. This way we can force bindings on these nodes.
	StepID action_step_id = bindings.createVariableDomains(action);
	StepPtr action_step(new Step(action_step_id, action));

	return Transition::createTransition(enablers, action_step, from_node, to_node, initial_facts);
}

Transition* Transition::createTransition(const std::vector<BoundedAtom>& enablers, const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts)
{
/*	std::cout << "[Transition::createTransition] From: " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), action_step->getStepId());
	std::cout << std::endl;
*/
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

	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* from_fact = *ci;
		bool is_removed = true;
		for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* to_fact = *ci;

			// If the same fact appears in the to node we assume it is not deleted and thus is persistent. The next block of code
			// determines if this is really the case or if the action deletes and adds this fact.
			if (from_node.getIndex(*from_fact) == to_node.getIndex(*to_fact) && bindings.canUnify(from_fact->getAtom(), from_fact->getId(), to_fact->getAtom(), to_fact->getId()))
			{
				is_removed = false;
				persistent_facts.push_back(to_fact);
			}

			// Check if the fact in the to node is added or was already present.
			bool is_added = true;
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* from_fact2 = *ci;

				if (from_node.getIndex(*from_fact2) == to_node.getIndex(*to_fact) && bindings.canUnify(from_fact2->getAtom(), from_fact2->getId(), to_fact->getAtom(), to_fact->getId()))
				{
					is_added = false;
					break;
				}
			}
			if (is_added)
			{
				added_facts.push_back(to_fact);
			}
		}

		if (is_removed)
		{
			removed_facts.push_back(from_fact);
		}
	}

	StepID action_step_id = action_step->getStepId();
	const Action& action = action_step->getAction();

	// Determine which precondition of the action corresponds to this node.
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &action.getPrecondition());

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

			// Search for the equivalent in the from node.
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* from_atom = *ci;

				if (from_node.getIndex(*from_atom) == to_node.getIndex(*persisent_atom) && bindings.canUnify(persisent_atom->getAtom(), persisent_atom->getId(), from_atom->getAtom(), from_atom->getId()))
				{
					removed_facts.push_back(from_atom);
					break;
				}
			}

			// This atom is no longer considered presistent.
			persistent_facts.erase(persistent_ci.base() - 1);
		}
	}

	// An action which does not interact with any of the nodes in invalid.
	if (removed_facts.size() == 0 || added_facts.size() == 0)
	{
//		std::cout << "Nothing is added or removed by this action, not relevant!" << std::endl;
		return NULL;
	}

	// The invariable variable domain according to the DTG nodes which match with the effects.
	const VariableDomain* invariable_dtg_variable_domain = NULL;
	std::set<const VariableDomain*> closed_list;

	/**
	 * After determining which facts are added, removed and not touched we try to identify which of the variables is the invariable one.
	 * The invariable variable is a fact which:
	 * 1) Appears in the preconditions.
	 * 2) This precondition must be deleted.
	 * 3) A fact must be added which contains this variable.
	 * Try all possibilities of effects and preconditions of this transition which could link to the invariable domain of the DTGs.
	 * At the same time, we check if all the removed and added facts are accounted for by this action.
	 */
	while (invariable_dtg_variable_domain == NULL)
	{
//		std::cout << "Restart: " << std::endl;

		// Make sure all the removed facts are accounted for, i.e. make sure the deleted facts are part of the precondition.
		bool all_facts_accounted_for = true;
		for (std::vector<const BoundedAtom*>::const_iterator ci = removed_facts.begin(); ci != removed_facts.end(); ci++)
		{
			bool is_precondition = false;
			const BoundedAtom* bounded_atom = *ci;
//			std::cout << "Removed fact: " << bounded_atom->getAtom().getPredicate() << "(" << from_node.getIndex(*bounded_atom) << ")" << std::endl;

			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
	
				if (precondition->isNegative() == bounded_atom->getAtom().isNegative() && 
				    bindings.canUnify(*precondition, action_step_id, bounded_atom->getAtom(), bounded_atom->getId()))
				{
					// Check if the invariable matches the previous one (if any).
					const VariableDomain& vd = bindings.getVariableDomain(action_step_id, *precondition->getTerms()[from_node.getIndex(*bounded_atom)]->asVariable());

					// If this variable domain is in the closed list, don't consider it.
					if (invariable_dtg_variable_domain == NULL && closed_list.count(&vd) != 0)
					{
						continue;
					}

					// Check if the candidate invariable (if any) matches with the deleted precondition.
					if (invariable_dtg_variable_domain != NULL && &vd != invariable_dtg_variable_domain)
					{
						continue;
						// TODO: This should always fail, but because the analysis isn't 100% correct we sometimes try to add a transition
						// which cannot be applied. For example if we have a general at predicate (at ?object ?location), we try to add
						// all transition which do something with that predicate  even if it is not applicable. This should be fixed once
						// we do proper type analysis. But in the interest of time we leave this as it is.
						//std::cout << "invariable domains are different! - check TODO!" << std::endl;
						//assert (false);
						//return NULL;
					}
					else
					{
						invariable_dtg_variable_domain = &vd;
//						std::cout << "Invariable domain is: ";
//						precondition->print(std::cout, bindings, action_step_id);
//						std::cout << " " << from_node.getIndex(*bounded_atom) << "th term." << std::endl;
						is_precondition = true;
						closed_list.insert(&vd);
						break;
					}
				}
			}

			// If a removed precondition is not accounted for, the transition cannot happen.
			if (!is_precondition)
			{
//				std::cout << "Could not account for the removal of: ";
//				bounded_atom->getAtom().print(std::cout, bindings, bounded_atom->getId());
//				std::cout << std::endl;
				all_facts_accounted_for = false;
				break;
			}
		}

		if (!all_facts_accounted_for)
		{
			// If no invariable was found we have explored all options.
			if (invariable_dtg_variable_domain == NULL)
			{
				break;
			}

			// Start over.
			invariable_dtg_variable_domain = NULL;
			continue;
		}

		// Check if all added facts are accounted for.
		for (std::vector<const BoundedAtom*>::const_iterator ci = added_facts.begin(); ci != added_facts.end(); ci++)
		{
			bool is_effect = false;
			const BoundedAtom* bounded_atom = *ci;
			for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
			{
				const Atom* effect = *ci;
	
				if (effect->isNegative() == bounded_atom->getAtom().isNegative() && 
				    bindings.canUnify(*effect, action_step_id, bounded_atom->getAtom(), bounded_atom->getId()))
				{
					// Check if the invariable matches the previous one (if any).
					const VariableDomain& vd = bindings.getVariableDomain(action_step_id, *effect->getTerms()[to_node.getIndex(*bounded_atom)]->asVariable());

					// If this variable domain is in the closed list, don't consider it.
					if (invariable_dtg_variable_domain == NULL && closed_list.count(&vd) != 0)
					{
						continue;
					}

					if (invariable_dtg_variable_domain != NULL && &vd != invariable_dtg_variable_domain)
					{
						continue;
						// TODO: This should always fail, but because the analysis isn't 100% correct we sometimes try to add a transition
						// which cannot be applied. For example if we have a general at predicate (at ?object ?location), we try to add
						// all transition which do something with that predicate  even if it is not applicable. This should be fixed once
						// we do proper type analysis. But in the interest of time we leave this as it is.
						//std::cout << "invariable domains are different! - check TODO!" << std::endl;
						//assert (false);
						//return NULL;
					}
					else
					{
						invariable_dtg_variable_domain = &vd;
//						std::cout << "Invariable domain is: ";
//						effect->print(std::cout, bindings, action_step_id);
//						std::cout << " " << to_node.getIndex(*bounded_atom) << "th term." << std::endl;
						is_effect = true;
						closed_list.insert(&vd);
						break;
					}
				}
			}

			// If an added fact is not accounted for, the transition cannot happen.
			if (!is_effect)
			{
//				std::cout << "Could not account for the adding of: ";
//				bounded_atom->getAtom().print(std::cout, bindings, bounded_atom->getId());
//				std::cout << std::endl;

				all_facts_accounted_for = false;
				break;
			}
		}

		if (!all_facts_accounted_for)
		{
			// If no invariable was found we have explored all options.
			if (invariable_dtg_variable_domain == NULL)
			{
				break;
			}

			// Start over.
			invariable_dtg_variable_domain = NULL;
			continue;
		}
	}

	if (invariable_dtg_variable_domain == NULL)
	{
//		std::cout << "Could not find the invariable index, transition is impossible!" << std::endl;
		return NULL;
	}

	// At this point we have found the invariable index which matches with all the added and removed nodes of the DTG nodes.
	assert (invariable_dtg_variable_domain != NULL);
	
	//std::cout << "Invariable variable: " << *invariable_dtg_variable_domain << std::endl;

	/**
	 * Store all the preconditions which link to one of the facts in the from_node.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> > precondition_mapping;
	std::vector<const BoundedAtom*> precondition_dtg_atoms;

	//std::cout << "Preconditions: " << std::endl;
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		//std::cout << "Precondition: ";
		//precondition->print(std::cout, bindings, action_step_id);
		//std::cout << std::endl;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			InvariableIndex invariable_index = from_node.getIndex(*bounded_atom);
			
			//std::cout << "\t*";
			//bounded_atom->print(std::cout, bindings);
			//std::cout << "(" << invariable_index << ")" << std::endl;

			// If one of the preconditions matches a atom in the from node and the invariables match up, they must be able to unify
			// otherwise the transition is not possible.
			if (precondition->isNegative() == bounded_atom->getAtom().isNegative() && 
			    precondition->getPredicate().getName() == bounded_atom->getAtom().getPredicate().getName() &&
			    &bindings.getVariableDomain(action_step_id, *precondition->getTerms()[invariable_index]->asVariable()) == invariable_dtg_variable_domain)
			{
				if (!bindings.canUnify(*precondition, action_step_id, bounded_atom->getAtom(), bounded_atom->getId()))
				{
					return NULL;
				}
				else
				{
					//std::cout << "Match!" << std::endl;
					precondition_dtg_atoms.push_back(bounded_atom);
					precondition_mapping.push_back(std::make_pair(precondition, invariable_index));
				}
			}
//			std::cout << std::endl;
		}
	}
	
	// If no preconditions could match it isn't part of this DTG.
	/*if (precondition_atoms.size() == 0)
	{
		return NULL;
	}*/

	/**
	 * Make sure that none of the preconditions are mutex with the from node.
	 */
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* atom = *ci;

		const VariableDomain* variable_domain = NULL;
		unsigned int vd_index = 0;
		for (unsigned int i = 0 ; i < atom->getTerms().size(); i++)
		{
			const VariableDomain& tmp_vd = bindings.getVariableDomain(action_step_id, *atom->getTerms()[i]->asVariable());
			if (&tmp_vd == invariable_dtg_variable_domain)
			{
				assert (variable_domain == NULL);
				variable_domain = &tmp_vd;
				vd_index = i;
			}
		}

		// If none of the variables match with the invariable index, we can ignore it because it does not affect this DTG.
		if (variable_domain == NULL)
		{
			continue;
		}

		for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			if (atom->isNegative() == bounded_atom->getAtom().isNegative() && from_node.getDTG().areMutex(bounded_atom->getAtom().getPredicate(), from_node.getIndex(*bounded_atom), atom->getPredicate(), vd_index))
			{
//				std::cout << "The precondition: ";
//				atom->print(std::cout, bindings, action_step_id);
//				std::cout << "(" << vd_index << ") is mutex with the atom: ";
//				bounded_atom->getAtom().print(std::cout, bindings, bounded_atom->getId());
//				std::cout << "(" << from_node.getIndex(*bounded_atom) << ")" << std::endl;
				return NULL;
			}
		}
	}

	// Store all effects which delete facts from the from node.
	std::vector<std::pair<const Atom*, InvariableIndex> > affected_atoms_mapping;
	std::vector<const BoundedAtom*> affected_dtg_atoms;

	// Store all effects which add facts to the to node.
	std::vector<std::pair<const Atom*, InvariableIndex> > effect_mapping;
	std::vector<const BoundedAtom*> achieved_dtg_atoms;

//	std::cout << "Action: " << action << std::endl;
	
	// Determine which effect deletes facts and which adds them.
	bool added_invariable = false;
	for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		const Atom* action_effect = *ci;

		const VariableDomain* invariable_action_domain = NULL;
		unsigned int invariable_action_domain_index = 0;
		for (unsigned int i = 0 ; i < action_effect->getTerms().size(); i++)
		{
			const VariableDomain& tmp_vd = bindings.getVariableDomain(action_step_id, *action_effect->getTerms()[i]->asVariable());
			if (&tmp_vd == invariable_dtg_variable_domain)
			{
				assert (invariable_action_domain == NULL);
				invariable_action_domain = &tmp_vd;
				invariable_action_domain_index = i;
			}
		}

		// If none of the variables match with the invariable index, we can ignore it because it does not affect this DTG.
		if (invariable_action_domain == NULL)
		{
			continue;
		}

		for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;

			// Check if this atom and the effect are mutal exclusive.
			if (action_effect->isNegative() == bounded_atom->getAtom().isNegative() && to_node.getDTG().areMutex(bounded_atom->getAtom().getPredicate(), to_node.getIndex(*bounded_atom), action_effect->getPredicate(), invariable_action_domain_index))
			{
//				std::cout << "The effect: ";
//				atom->print(std::cout, bindings, action_step_id);
//				std::cout << " is mutex with the atom: ";
//				bounded_atom->getAtom().print(std::cout, bindings, bounded_atom->getId());
//				std::cout << std::endl;
				return NULL;
			}

			if (action_effect->isNegative() == bounded_atom->getAtom().isNegative() && bindings.canUnify(*action_effect, action_step_id, bounded_atom->getAtom(), bounded_atom->getId()))
			{
				if (invariable_action_domain == invariable_dtg_variable_domain && to_node.getIndex(*bounded_atom) == invariable_action_domain_index)
				{
					effect_mapping.push_back(std::make_pair(action_effect, invariable_action_domain_index));
					achieved_dtg_atoms.push_back(bounded_atom);
					added_invariable = true;
				}

				//std::cout << "type check: The action: ";
				//atom->print(std::cout, bindings, action_step_id);
				//std::cout << "; The DTG: ";
				//bounded_atom->getAtom().print(std::cout, bindings, bounded_atom->getId());
				//std::cout << std::endl;
			}
		}
	
		for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;

			if (bindings.affects(*action_effect, action_step_id, bounded_atom->getAtom(), bounded_atom->getId()))
			{
				affected_atoms_mapping.push_back(std::make_pair(action_effect, from_node.getIndex(*bounded_atom)));
				affected_dtg_atoms.push_back(bounded_atom);
			}	
		}
	}

	// If the achieving atom or affecting atom could not be found, than the action cannot be applied to this transition and the to
	// node should be removed from the DTG node.
	if (effect_mapping.size() == 0 || affected_atoms_mapping.size() == 0 || !added_invariable)
	{
//		assert (false);
//		std::cout << "No effect achieved!" << std::endl;
		return NULL;
	}

	// If a fact from the from node is not affected, it means it is still true in the to node. Make sure that all the atoms in the to node are not
	// mutex with this fact.
	for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* precondition_atom = *ci;

		bool is_affected = false;
		for (std::vector<const BoundedAtom*>::const_iterator ci = affected_dtg_atoms.begin(); ci != affected_dtg_atoms.end(); ci++)
		{
			const BoundedAtom* affected_atom = *ci;
			if (affected_atom == precondition_atom)
			{
				is_affected = true;
				break;
			}
		}

		if (is_affected)
		{
			continue;
		}

		// If it is not affected, check if it is mutex with any of the atoms in the to node.
		for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* effect_atom = *ci;
			if (from_node.getDTG().areMutex(effect_atom->getAtom().getPredicate(), to_node.getIndex(*effect_atom), precondition_atom->getAtom().getPredicate(), from_node.getIndex(*precondition_atom)))
			{
//				std::cout << effect_atom->getAtom().getPredicate() << " and " << precondition_atom->getAtom().getPredicate() << " are mutex!" << std::endl;
				return NULL;
			}
/*
TODO:
			if (effect_atom->getAtom().getPredicate() == precondition_atom->getAtom().getPredicate() &&
			    to_node.getIndex(*effect_atom) == from_node.getIndex(*precondition_atom) &&
			    from_node.getDTG().getBindings().canUnify(*effect_atom->getAtom().getTerms()[to_node.getIndex(*effect_atom)], effect_atom->getId(), *precondition_atom->getAtom().getTerms()[from_node.getIndex(*precondition_atom)], precondition_atom->getId()) &&
			    !from_node.getDTG().getBindings().canUnify(effect_atom->getAtom(), effect_atom->getId(), precondition_atom->getAtom(), precondition_atom->getId()))
			{
				// If the predicates are equal and the invariable domains can be unified, but the whole thing cannot, don't allow it!
				return NULL;
			}
*/
		}
	}

//	std::cout << "Unify the effect: ";
//	achieving_atom->print(std::cout, bindings, action_step->getStepId());
//	std::cout << " with ";
//	achieving_dtg_atom->getAtom().print(std::cout, bindings, achieving_dtg_atom->getId());
//	std::cout << std::endl;

	// Copy the action and its variable domains and bind it to the new transition.
	StepID new_action_step_id = bindings.createVariableDomains(action);
	for (unsigned int i = 0; i < action.getVariables().size(); i++)
	{
		const VariableDomain& variable_domain = bindings.getVariableDomain(action_step_id, *action.getVariables()[i]->asVariable());
		bindings.assign(new_action_step_id, *action.getVariables()[i], variable_domain.getDomain());
	}

	StepPtr new_action_step(new Step(new_action_step_id, action));

	// Now that we know the bindings can be enforced and the transition is possible, do it!
///	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effect_mapping.begin(); ci != effect_mapping.end(); ci++)
	assert (effect_mapping.size() == achieved_dtg_atoms.size());
	
	for (unsigned int i = 0; i < effect_mapping.size(); i++)
	{
		const Atom* atom = effect_mapping[i].first;
		const BoundedAtom* bounded_dtg_atom = achieved_dtg_atoms[i];
		
/*		std::cout << "Map the effect: ";
		atom->print(std::cout, bindings, new_action_step_id);
		std::cout << " to the atom in To Node: ";
		bounded_dtg_atom->print(std::cout, bindings);
		std::cout << std::endl;
*/		
		if (!bindings.unify(*atom, new_action_step_id, bounded_dtg_atom->getAtom(), bounded_dtg_atom->getId()))
		{
			return NULL;
		}
	}

//	std::cout << "Unify the precondition: ";
//	precondition_atom->print(std::cout, bindings, action_step->getStepId());
//	std::cout << " with ";
//	precondition_dtg_atom->getAtom().print(std::cout, bindings, precondition_dtg_atom->getId());
//	std::cout << std::endl;

//	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = precondition_mapping.begin(); ci != precondition_mapping.end(); ci++)
	assert (precondition_mapping.size() == precondition_dtg_atoms.size());
	for (unsigned int i = 0; i < precondition_mapping.size(); i++)
	{
		const Atom* atom = precondition_mapping[i].first;
		const BoundedAtom* bounded_dtg_atom = precondition_dtg_atoms[i];
/*	
		std::cout << "Map the precondition: ";
		atom->print(std::cout, bindings, new_action_step_id);
		std::cout << " to the atom in From Node: ";
		bounded_dtg_atom->print(std::cout, bindings);
		std::cout << std::endl;
*/		
		if (!bindings.unify(*atom, new_action_step_id, bounded_dtg_atom->getAtom(), bounded_dtg_atom->getId()))
		{
			return NULL;
		}
	}

	// Also unify the persistent atoms which appear in the to node.
	for (std::vector<const BoundedAtom*>::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ci++)
	{
		const BoundedAtom* persistent_fact = *ci;
		bool is_unifiable = false;

		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = precondition_mapping.begin(); ci != precondition_mapping.end(); ci++)
		{
			const Atom* atom = (*ci).first;

			//std::cout << "- Check against: ";
			//(*ci)->print(std::cout, bindings, new_action_step_id);

			// Only allow to unify if the indexes of the invariables are the same and the variables can unify.
			for (unsigned int i = 0; i < atom->getTerms().size(); i++)
			{
				// Check the invariables.
				if (&bindings.getVariableDomain(new_action_step_id, *atom->getTerms()[i]->asVariable()) == invariable_dtg_variable_domain &&
				    i == to_node.getIndex(*persistent_fact))
				{
					// Check if they can unify.
					if (bindings.unify(*atom, new_action_step_id, persistent_fact->getAtom(), persistent_fact->getId()))
					{
						is_unifiable = true;
						//std::cout << " - can unify! :D";
						break;
					}
				}
			}

			//std::cout << std::endl;
		}

		if (!is_unifiable)
		{
			//std::cout << "Persistent: ";
			//persistent_fact->print(std::cout, bindings);
			//std::cout << " could not be unified with the preconditions... ";

			// Unify the persistents by unifying the corresponding facts in the from node and to node.
			bool could_unify = false;
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* from_fact = *ci;
				if (from_node.getIndex(*from_fact) == to_node.getIndex(*persistent_fact) && bindings.canUnify(from_fact->getAtom(), from_fact->getId(), persistent_fact->getAtom(), persistent_fact->getId()))
				{
					could_unify = true;
					bindings.unify(from_fact->getAtom(), from_fact->getId(), persistent_fact->getAtom(), persistent_fact->getId());
					//std::cout << " unified it with the atom (from node: ";
					//from_fact->print(std::cout, bindings);
					//std::cout << "." << std::endl;
					break;
				}
			}

			assert (could_unify);
		}
	}

	// As a final step, make sure that by the above binding, none of the static preconditions were violated.
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;

		// If the precondition is static, make sure it is true in the initial state.
		if (precondition->getPredicate().isStatic())
		{
			//std::cout << "Check static: ";
			//precondition->print(std::cout, bindings, action_step_id);
			//std::cout << std::endl;
			
			// Limit the variable domains of the action to the facts which are true in the initial state.
			// TODO: implement this.
			
			bool can_ground = false;

			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
			{
				if (bindings.canUnify(**ci, Step::INITIAL_STEP, *precondition, new_action_step_id))
				{
					can_ground = true;
					break;
				}
			}
			
			if (!can_ground)
			{
				return NULL;
			}
		}
	}

/*	std::cout << "Created a transition from " << std::endl;
	std::cout << from_node << std::endl;
	std::cout << " to " << std::endl;
	std::cout << to_node << std::endl;
	std::cout << "Action: ";
	new_action_step->getAction().print(std::cout, from_node.getDTG().getBindings(), new_action_step->getStepId());
	std::cout << std::endl;
*/
	return new Transition(enablers, new_action_step, from_node, to_node, precondition_mapping, effect_mapping, affected_atoms_mapping, *invariable_dtg_variable_domain);
}

Transition::Transition(const std::vector< MyPOP::SAS_Plus::BoundedAtom >& enablers, MyPOP::StepPtr step, MyPOP::SAS_Plus::DomainTransitionGraphNode& from_node, MyPOP::SAS_Plus::DomainTransitionGraphNode& to_node, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& preconditions, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& effects, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& affected, const VariableDomain& invariable_dtg_variable_domain)
	: enablers_(enablers), step_(step), from_node_(&from_node), to_node_(&to_node), preconditions_(preconditions), effects_(effects), affected_(affected), invariable_dtg_variable_domain_(&invariable_dtg_variable_domain)
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
		from_node_->getDTG().getBindings().makeEqual(**ci, step_->getStepId(), **ci, new_transition->getStep()->getStepId());
	}

	return new_transition;
}

void Transition::getAllPreconditions(std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions) const
{
	// First figure out what the invariable index is of the action.
	// TODO: This should just be a property of the transition.
	assert (preconditions_.size() > 0);
	
	//const VariableDomain& invariable_vd = from_node_->getDTG().getBindings().getVariableDomain(step_->getStepId(), *step_->getAction().getVariables()[preconditions_[0].second]);
	const VariableDomain& invariable_vd = from_node_->getDTG().getBindings().getVariableDomain(step_->getStepId(), *preconditions_[0].first->getTerms()[preconditions_[0].second]->asVariable());
//	from_node_->getDTG().getBindings().getVariableDomain(step_->getStepId(), *step_->getAction().getVariables()[preconditions_[0].second]);
	
	std::cout << "Invariable: " << invariable_vd;
	std::cout << "(" << preconditions_[0].second << ")";
	std::cout << std::endl;

	//for (std::vector<const Variable*>::const_iterator ci = step_->getAction().getVariables().begin(); ci != step_->getAction().getVariables().end(); ci++)
	{
		//const VariableDomain& invariable_vd = from_node_->getDTG().getBindings().getVariableDomain(step_->getStepId(), **ci);
		//const VariableDomain& invariable_vd = *invariable_dtg_variable_domain_;
		//std::cout << "Invariable variable domain: " << invariable_vd << std::endl;
		
		std::vector<const Atom*> action_preconditions;
		
		Utility::convertFormula(action_preconditions, &step_->getAction().getPrecondition());
		for (std::vector<const Atom*>::const_iterator ci = action_preconditions.begin(); ci != action_preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;
			InvariableIndex invariable_index = std::numeric_limits<unsigned int>::max();
			
//			std::cout << "Compare with: ";
//			precondition->print(std::cout, from_node_->getDTG().getBindings(), step_->getStepId());
//			std::cout << std::endl;
			
			for (unsigned int i = 0; i < precondition->getTerms().size(); i++)
			{
				const Term* term = precondition->getTerms()[i];
				if (term->isVariable())
				{
					const VariableDomain& precondition_vd = from_node_->getDTG().getBindings().getVariableDomain(step_->getStepId(), *term->asVariable());
					if (&precondition_vd == &invariable_vd)
					{
//						std::cout << "Found!!! - " << i << std::endl;
						invariable_index = i;
						break;
					}
				}
			}
			
			preconditions.push_back(std::make_pair(precondition, invariable_index));
		}
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
		const Term* term = *ci;
		assert (term->isVariable());

		const VariableDomain& ba_vd = from_node_->getDTG().getBindings().getVariableDomain(bounded_atom.getId(), *term->asVariable());

		bool is_linked = false;
		for (std::vector<const Term*>::const_iterator ci = atom.getTerms().begin(); ci != atom.getTerms().end(); ci++)
		{
			const Term* term = *ci;
			assert (term->isVariable());
			const VariableDomain& vd = from_node_->getDTG().getBindings().getVariableDomain(step_->getStepId(), *term->asVariable());

			if (&ba_vd == &vd)
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
/*
Atom* carry_over_atom = NULL;

const Atom& Transition::getCarryOverAtom()
{
	if (Transition::carry_over_atom == NULL)
	{
		std::vector<const Type*>* types = new std::vector<const Type*>();
		Predicate* predicate = new Predicate("carry_over", *types, true);
		
		std::vector<const Term*>* terms = new std::vector<const Term*>();
		Transition::carry_over_atom = new Atom(*predicate, *terms, false);
	}
	
	return *Transition::carry_over_atom;
}
*/

// TODO: Also check if the precondition might be true in the initial state!
bool Utilities::transitionIsSupported(const Transition* transition, const DomainTransitionGraphManager* dtg_manager, const std::vector<const Atom*>& initial_facts)
{
	/*
	// Both nodes of the transition are part of the same DTG, so we just pick one.
	const DomainTransitionGraph& dtg = transition->getFromNode().getDTG();

	const StepPtr step = transition->getStep();
	const Action& action = step->getAction();
	const StepID action_id = step->getStepId();

	const Bindings& action_bindings = dtg.getBindings();

	std::cout << "!!! Check the action: " << action << std::endl;
	
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &action.getPrecondition());

	// Check if all preconditions are either static or part of a DTG.
	bool all_preconditions_satisfied = true;
	for (std::vector<const Atom*>::const_iterator atom_ci = preconditions.begin(); atom_ci != preconditions.end(); atom_ci++)
	{
		const Atom* precondition = *atom_ci;
		
		std::cout << "- ";
		precondition->print(std::cout, dtg.getBindings(), action_id);
		std::cout << std::endl;
		
		// Check if the precondition can be true in the initial state.
		bool unifiable_with_initial_state = false;
		for (std::vector<const Atom*>::const_iterator init_ci = initial_facts.begin(); init_ci != initial_facts.end(); init_ci++)
		{
			if (action_bindings.canUnify(**init_ci, Step::INITIAL_STEP, *precondition, action_id))
			{
				unifiable_with_initial_state = true;
				break;
			}
		}

		if (unifiable_with_initial_state)
		{
			std::cout << "TRUE IN INIT!" << std::endl;
			continue;
		}

		if (precondition->getPredicate().isStatic())
		{
			std::cout << "(STATIC)" << std::endl;
			continue;
		}
		
		bool precondition_satisfied = false;
		// Now check for each precondition if they appear in any of the DTG nodes, if not we can remove the transition.
		for (std::vector<DomainTransitionGraph*>::const_iterator all_dtgs_ci = dtg_manager->getManagableObjects().begin(); all_dtgs_ci != dtg_manager->getManagableObjects().end(); all_dtgs_ci++)
		{
			DomainTransitionGraph* all_dtg = *all_dtgs_ci;
			
			// Check for each node if they can exist.
			for (std::vector<DomainTransitionGraphNode*>::const_iterator dtg_node_ci = all_dtg->getNodes().begin(); dtg_node_ci != all_dtg->getNodes().end(); dtg_node_ci++)
			{
				DomainTransitionGraphNode* all_dtg_node = *dtg_node_ci;
				const Atom& dtg_node_atom = all_dtg_node->getAtom();

				if (all_dtg->getBindings().canUnify(all_dtg_node->getAtom(), all_dtg_node->getId(), *precondition, action_id, &action_bindings))
				{
					std::cout << "(OK) ";
					dtg_node_atom.print(std::cout, all_dtg->getBindings(), all_dtg_node->getId());
					std::cout << std::endl;

					precondition_satisfied = true;
					break;
				}
				else
				{
					std::cout << "(NOT) ";
					dtg_node_atom.print(std::cout, all_dtg->getBindings(), all_dtg_node->getId());
					std::cout << std::endl;
					
					continue;
				}
			}
		}
		
		if (!precondition_satisfied)
		{
			// This transition cannot take place!
			all_preconditions_satisfied = false;
			break;
		}
	}
	
	return all_preconditions_satisfied;*/
	return true;
}

bool Utilities::TransitionToNodeEquals::operator()(const Transition* transition, const DomainTransitionGraphNode* dtg_node) const
{
	return &transition->getToNode() == dtg_node;
}

};

};
