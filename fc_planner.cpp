#include "fc_planner.h"

#include <queue>
#include <cmath>
#include <time.h>

#include "sas/dtg_manager.h"
#include "predicate_manager.h"
#include "action_manager.h"
#include "type_manager.h"
#include "parser_utils.h"
#include "heuristics/dtg_reachability.h"
#include "heuristics/equivalent_object_group.h"

//#define MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
#include "type_manager.h"
#include "heuristics/fact_set.h"

namespace MyPOP {

std::vector<const GroundedAction*> GroundedAction::instantiated_grounded_actions_;
std::vector<const GroundedAtom*> GroundedAtom::instantiated_grounded_atoms_;

const GroundedAction& GroundedAction::getGroundedAction(const Action& action, const Object** variables)
{
	for (std::vector<const GroundedAction*>::const_iterator ci = instantiated_grounded_actions_.begin(); ci != instantiated_grounded_actions_.end(); ci++)
	{
		const GroundedAction* instantiated_action = *ci;
		if (instantiated_action->action_ != &action) continue;
		bool variables_match = true;
		for (unsigned int i = 0; i < action.getVariables().size(); i++)
		{
			if (variables[i] != instantiated_action->variables_[i])
			{
				variables_match = false;
				break;
			}
		}
		
		if (variables_match) return *instantiated_action;
	}
	
	const Object** copied_variables = new const Object*[action.getVariables().size()];
	for (unsigned int i = 0; i < action.getVariables().size(); ++i)
	{
		copied_variables[i] = variables[i];
	}
	
	GroundedAction* new_grounded_action = new GroundedAction(action, copied_variables);
	instantiated_grounded_actions_.push_back(new_grounded_action);
	return *new_grounded_action;
}

void GroundedAction::removeInstantiatedGroundedActions(std::vector<const GroundedAction*>::const_iterator begin, std::vector<const GroundedAction*>::const_iterator end)
{
	for (std::vector<const GroundedAction*>::reverse_iterator ri = instantiated_grounded_actions_.rbegin(); ri != instantiated_grounded_actions_.rend(); ++ri)
	{
		const GroundedAction* grounded_action = *ri;
		if (std::find(begin, end, grounded_action) == end)
		{
			delete *ri;
			instantiated_grounded_actions_.erase(ri.base() - 1);
		}
	}
}

void GroundedAction::removeInstantiatedGroundedActions()
{
	for (std::vector<const GroundedAction*>::const_iterator ci = instantiated_grounded_actions_.begin(); ci != instantiated_grounded_actions_.end(); ++ci)
	{
		delete *ci;
	}
	instantiated_grounded_actions_.clear();
}

unsigned int GroundedAction::numberOfGroundedActions()
{
	return instantiated_grounded_actions_.size();
}
	
GroundedAction::GroundedAction(const Action& action, const Object** variables)
	: action_(&action), variables_(variables)
{
	
}

GroundedAction::~GroundedAction()
{
	delete[] variables_;
}

std::ostream& operator<<(std::ostream& os, const GroundedAction& grounded_action)
{
	os << "(" << grounded_action.action_->getPredicate();
	for (unsigned int i = 0; i < grounded_action.action_->getVariables().size(); i++)
	{
		os << " " << *grounded_action.variables_[i];
	}
	os << ")";
	return os;
}

void GroundedAtom::removeInstantiatedGroundedAtom()
{
	for (std::vector<const GroundedAtom*>::const_iterator ci = instantiated_grounded_atoms_.begin(); ci != instantiated_grounded_atoms_.end(); ++ci)
	{
		const GroundedAtom* grounded_atom = *ci;
		delete grounded_atom;
	}
	instantiated_grounded_atoms_.clear();
}

void GroundedAtom::removeInstantiatedGroundedAtom(const std::vector<const GroundedAtom*>& exceptions)
{
	for (std::vector<const GroundedAtom*>::reverse_iterator ri = instantiated_grounded_atoms_.rbegin(); ri != instantiated_grounded_atoms_.rend(); ++ri)
	{
		const GroundedAtom* grounded_atom = *ri;
		if (std::find(exceptions.begin(), exceptions.end(), grounded_atom) == exceptions.end())
		{
			delete grounded_atom;
			instantiated_grounded_atoms_.erase(ri.base() - 1);
		}
	}
}

const GroundedAtom& GroundedAtom::getGroundedAtom(const Atom& atom, const Object** variables)
{
	for (std::vector<const GroundedAtom*>::const_iterator ci = instantiated_grounded_atoms_.begin(); ci != instantiated_grounded_atoms_.end(); ++ci)
	{
		const GroundedAtom* grounded_atom = *ci;
		
		if (grounded_atom->getAtom().getArity() != atom.getArity() ||
		    grounded_atom->getAtom().getPredicate().getName() != atom.getPredicate().getName())
		{
			continue;
		}
		
		bool variable_domain_match = true;
		for (unsigned int i = 0; i < grounded_atom->getAtom().getArity(); ++i)
		{
			if (&grounded_atom->getObject(i) != variables[i])
			{
				variable_domain_match = false;
				break;
			}
		}
		if (variable_domain_match)
		{
			delete[] variables;
			return *grounded_atom;
		}
	}
	
	GroundedAtom* new_grounded_atom = new GroundedAtom(atom, variables);
	instantiated_grounded_atoms_.push_back(new_grounded_atom);
	return *new_grounded_atom;
}

const GroundedAtom& GroundedAtom::getGroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings)
{
	const Object** variables = new const Object*[bounded_atom.getAtom().getArity()];
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); ++i)
	{
		variables[i] = bounded_atom.getVariableDomain(i, bindings)[0];
	}
	return getGroundedAtom(bounded_atom.getAtom(), variables);
}

unsigned int GroundedAtom::numberOfGroundedAtoms()
{
	return instantiated_grounded_atoms_.size();
}

GroundedAtom::GroundedAtom(const Atom& atom, const Object** variables)
	: atom_(&atom), variables_(variables)
{
//	std::cout << "New Grounded atom: " << *this << std::endl;
}

GroundedAtom::GroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings)
	: atom_(&bounded_atom.getAtom())
{
	variables_ = new const Object*[bounded_atom.getAtom().getArity()];
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		const std::vector<const Object*>& variable_domain = bounded_atom.getVariableDomain(i, bindings);
		assert (variable_domain.size() == 1);
		variables_[i] = variable_domain[0];
	}
	
//	std::cout << "New Grounded atom: " << *this << std::endl;
}

GroundedAtom::~GroundedAtom()
{
	delete[] variables_;
}

bool GroundedAtom::operator==(const GroundedAtom& rhs) const
{
	if (atom_->getPredicate().getName() != rhs.atom_->getPredicate().getName() ||
	    atom_->getPredicate().getArity() != rhs.atom_->getPredicate().getArity()) return false;
	
	for (unsigned int i = 0; i < atom_->getPredicate().getArity(); i++)
	{
		if (variables_[i] != rhs.variables_[i]) return false;
	}
	return true;
}

bool GroundedAtom::operator!=(const GroundedAtom& rhs) const
{
	return !(*this == rhs);
}

std::ostream& operator<<(std::ostream& os, const GroundedAtom& grounded_atom)
{
	os << "(" << grounded_atom.getAtom().getPredicate().getName();
	for (unsigned int i = 0; i < grounded_atom.getAtom().getArity(); i++)
	{
		os << " " << grounded_atom.getObject(i);
	}
	os << ")";
	return os;
}

State::State(const std::vector<const GroundedAtom*>& facts, bool created_by_helpful_action)
	: facts_(facts), distance_to_goal_(0), distance_from_start_(0), created_by_helpful_action_(created_by_helpful_action)
{
	assert (facts_.size() == facts.size());
	std::sort(facts_.begin(), facts_.end());
}

State::State(const State& rhs, const GroundedAction& grounded_action, bool created_by_helpful_action)
	: facts_(rhs.facts_), distance_to_goal_(rhs.distance_to_goal_), distance_from_start_(rhs.distance_from_start_ + 1), created_by_helpful_action_(created_by_helpful_action)
{
	achievers_.insert(achievers_.end(), rhs.achievers_.begin(), rhs.achievers_.end());
	achievers_.push_back(&grounded_action);
//	std::sort(facts_.begin(), facts_.end());
}

State::~State()
{
	for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		delete *ci;
	}
}

void State::getSuccessors(std::vector<State*>& successor_states, const ActionManager& action_manager, const TypeManager& type_manager, bool prune_unhelpful_actions) const
{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "Find successors of" << std::endl << *this << std::endl;
#endif
	for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
	{
		const Action* action = *ci;
		
		std::vector<const Atom*> preconditions;
		std::vector<const Equality*> equalities;
		Utility::convertFormula(preconditions, equalities, &action->getPrecondition());
		
		// Construct all grounded variants of this action which are applicable in this state.
		const Object* assigned_variables[action->getVariables().size()];
		memset(assigned_variables, 0, sizeof(Object*) * action->getVariables().size());
		
		instantiateAndExecuteAction(successor_states, *action, preconditions, equalities, 0, assigned_variables, type_manager, prune_unhelpful_actions);
	}
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "Found: " << successor_states.size() << " successors states for: " << std::endl << *this << std::endl;
#endif
}

bool State::isSuperSetOf(const std::vector<const GroundedAtom*>& facts) const
{
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts.begin(); ci != facts.end(); ci++)
	{
		const GroundedAtom* goal_fact = *ci;
		bool is_satisfied = false;
		
		for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end(); ci++)
		{
			if (**ci == *goal_fact)
			{
				is_satisfied = true;
				break;
			}
		}
		if (!is_satisfied) return false;
	}
	return true;
}

//void State::setHelpfulActions(const std::vector<std::pair<const Action*, std::vector<const Object*>**> >& helpful_actions)
void State::setHelpfulActions(const std::vector<const REACHABILITY::AchievingTransition*>& helpful_actions)
{
	deleteHelpfulActions();
	helpful_actions_ = helpful_actions;
	
//	std::cerr << *this << std::endl;
}

bool State::addFact(const MyPOP::GroundedAtom& fact, bool remove_fact)
{
	// Don't add a fact twice!
	for (std::vector<const GroundedAtom*>::iterator i = facts_.begin(); i != facts_.end(); i++)
	{
		if (*i == &fact)
		{
			return false;
		}
	}
	facts_.push_back(&fact);
	std::sort(facts_.begin(), facts_.end());
	return true;
}

void State::removeFact(const GroundedAtom& fact)
{
	for (unsigned int i = 0; i < facts_.size(); ++i)
	{
		if (*facts_[i] == fact)
		{
			facts_.erase(facts_.begin() + i);
			break;
		}
	}
	std::sort(facts_.begin(), facts_.end());
}

void State::instantiateAndExecuteAction(std::vector<State*>& successor_states, const Action& action, const std::vector<const Atom*>& preconditions, const std::vector<const Equality*>& equalities, unsigned int uninitialised_precondition_index, const Object** assigned_variables, const TypeManager& type_manager, bool prune_unhelpful_actions) const
{
/*	if (uninitialised_precondition_index == 0)
	{
		std::cout << "[State::instantiateAndExecuteAction]" << std::endl << *this << std::endl;
		std::cout << "Helpful actions: " << std::endl;
		for (std::vector<std::pair<const Action*, std::vector<const Object*>**> >::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
		{
			const Action* action = (*ci).first;
			std::vector<const Object*>** variable = (*ci).second;
			
			std::cout << "(" << action->getPredicate() << " ";
			for (unsigned int i = 0; i < action->getVariables().size(); ++i)
			{
				std::vector<const Object*>* variable_domain = variable[i];
				std::cout << "{";
				for (std::vector<const Object*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ++ci)
				{
					std::cout << **ci << " ";
				}
				std::cout << "} ";
			}
			std::cout << ")" << std::endl;
		}
	}
*/

	// Find facts in the current state which can unify with the 'uninitialised_precondition_index'th precondition and does not violate the already assigned variables.
	const Atom* precondition = preconditions[uninitialised_precondition_index];
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end(); ci++)
	{
		const GroundedAtom* grounded_atom = *ci;
		if (grounded_atom->getAtom().getArity() != precondition->getArity() || grounded_atom->getAtom().getPredicate().getName() != precondition->getPredicate().getName()) continue;
		
		// Check if none of the assigned variables are violated.
		bool constraints_satisfied = true;

		const Object* new_assigned_variables[action.getVariables().size()];
		memcpy(new_assigned_variables, assigned_variables, sizeof(const Object*) * action.getVariables().size());
		
		for (unsigned int i = 0; i < grounded_atom->getAtom().getArity(); i++)
		{
			assert (std::find(action.getVariables().begin(), action.getVariables().end(), precondition->getTerms()[i]) != action.getVariables().end());
			unsigned int variable_index = std::distance(action.getVariables().begin(), std::find(action.getVariables().begin(), action.getVariables().end(), precondition->getTerms()[i]));
			if ((assigned_variables[variable_index] != NULL && assigned_variables[variable_index] != &grounded_atom->getObject(i)) || !grounded_atom->getObject(i).getType()->isCompatible(*action.getVariables()[variable_index]->getType()))
			{
				constraints_satisfied = false;
				break;
			}
			new_assigned_variables[variable_index] = &grounded_atom->getObject(i);
		}
		
		// Check if the equality constraints are also satisfied.
		if (constraints_satisfied)
		{
			for (std::vector<const Equality*>::const_iterator ci = equalities.begin(); ci != equalities.end(); ci++)
			{
				const Equality* equality = *ci;
				assert (std::find(action.getVariables().begin(), action.getVariables().end(), &equality->getLHSTerm()) != action.getVariables().end());
				unsigned int lhs_term_index = std::distance(action.getVariables().begin(), std::find(action.getVariables().begin(), action.getVariables().end(), &equality->getLHSTerm()));
				
				assert (std::find(action.getVariables().begin(), action.getVariables().end(), &equality->getRHSTerm()) != action.getVariables().end());
				unsigned int rhs_term_index = std::distance(action.getVariables().begin(), std::find(action.getVariables().begin(), action.getVariables().end(), &equality->getRHSTerm()));
				
				if (assigned_variables[lhs_term_index] != NULL && assigned_variables[rhs_term_index] != NULL && (assigned_variables[lhs_term_index] == assigned_variables[rhs_term_index]) == equality->isNegative()) constraints_satisfied = false;
			}
		}
		
		if (!constraints_satisfied)
		{
			continue;
		}
		
		// Found an atom which satisfies all constraints, check if we now have a full assignment!
		if (uninitialised_precondition_index + 1 == preconditions.size())
		{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//			std::cout << "Found a successor state!" << std::endl;
#endif

			const Object** grounded_action_variables_templates = new const Object*[action.getVariables().size()];
			memcpy(grounded_action_variables_templates, new_assigned_variables, sizeof(const Object*) * action.getVariables().size());
			
			// Check if all the variables have been assigned. Those which are not assigned are free variables.
			std::vector<const Object**> all_grounded_action_variables;
			createAllGroundedVariables(all_grounded_action_variables, grounded_action_variables_templates, action, type_manager);
			
			delete[] grounded_action_variables_templates;
			
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "(" << all_grounded_action_variables.size() << ") Helpful actions: " << std::endl;
			for (std::vector<std::pair<const Action*, std::vector<const Object*>**> >::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
			{
				const Action* action = (*ci).first;
				std::vector<const Object*>** variable = (*ci).second;
				
				std::cout << "(" << action->getPredicate() << " ";
				for (unsigned int i = 0; i < action->getVariables().size(); ++i)
				{
					std::vector<const Object*>* variable_domain = variable[i];
					std::cout << "{";
					for (std::vector<const Object*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ++ci)
					{
						std::cout << **ci << " ";
					}
					std::cout << "} ";
				}
				std::cout << ")" << std::endl;
			}
#endif
			
	
			for (std::vector<const Object**>::const_iterator ci = all_grounded_action_variables.begin(); ci != all_grounded_action_variables.end(); ci++)
			{
				const Object** grounded_action_variables = *ci;

				// Check if this is a helpful action or not.
				bool is_helpful = helpful_actions_.empty();
				for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
				{
					const REACHABILITY::AchievingTransition* helpful_action = *ci;
//					std::cout << "Helpful action: " << *helpful_action << std::endl;
					
					if (action.getPredicate() != helpful_action->getAchiever()->getTransition().getAction().getPredicate() ||
					    action.getVariables().size() != helpful_action->getVariableAssignments().size())
					{
						continue;
					}
					
					bool all_variable_domains_match = true;
					for (unsigned int i = 0; i < action.getVariables().size(); ++i)
					{
						//std::vector<const Object*>* helpful_variable_domain = variable_domains[i];
						const HEURISTICS::VariableDomain& helpful_variable_domain = helpful_action->getVariableAssignments()[i]->getVariableDomain();
						if (!helpful_variable_domain.contains(*grounded_action_variables[i]))
						{
							all_variable_domains_match = false;
							break;
						}
					}
					if (all_variable_domains_match)
					{
						is_helpful = true;
						break;
					}
				}

//				const GroundedAction& dummy_grounded_action = GroundedAction::getGroundedAction(action, grounded_action_variables);
				if (prune_unhelpful_actions && !is_helpful)
				{
//					std::cout << "Unhelpful: " << dummy_grounded_action << std::endl;
					continue;
				}
//				std::cout << "Helpful: " << dummy_grounded_action << std::endl;

				const GroundedAction& grounded_action = GroundedAction::getGroundedAction(action, grounded_action_variables);
				
				// Apply the action to the new state!
				State* new_state = new State(*this, grounded_action, is_helpful);
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//				std::cout << "Copy the old state: " << *new_state << std::endl;
#endif

				std::vector<const GroundedAtom*> to_add;
				for (std::vector<const Atom*>::const_iterator ci = action.getEffects().begin(); ci != action.getEffects().end(); ci++)
				{
					const Atom* effect = *ci;
					const Object** effect_variables = new const Object*[effect->getArity()];
					
					for (unsigned int i = 0; i < effect->getArity(); i++)
					{
						assert (std::find(action.getVariables().begin(), action.getVariables().end(), effect->getTerms()[i]) != action.getVariables().end());
						unsigned int variable_index = std::distance(action.getVariables().begin(), std::find(action.getVariables().begin(), action.getVariables().end(), effect->getTerms()[i]));

						assert (grounded_action_variables[variable_index] != NULL);
						effect_variables[i] = grounded_action_variables[variable_index];
					}
					
//					GroundedAtom* grounded_effect = new GroundedAtom(*effect, effect_variables);
					const GroundedAtom& grounded_effect = GroundedAtom::getGroundedAtom(*effect, effect_variables);
					if (effect->isNegative())
					{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//						std::cout << "Remove: " << *grounded_effect << std::endl;
#endif
						new_state->removeFact(grounded_effect);
//						delete grounded_effect;
					}
					else
					{
						to_add.push_back(&grounded_effect);
					}
				}
				
				for (std::vector<const GroundedAtom*>::const_iterator ci = to_add.begin(); ci != to_add.end(); ci++)
				{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//					std::cout << "Add: " << *grounded_effect << std::endl;
#endif
					if (!new_state->addFact(**ci, true))
					{
//						delete *ci;
					}
				}
							
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//				std::cout << "Successor state: " << *new_state << std::endl;
#endif
				successor_states.push_back(new_state);
			}
			
			for (std::vector<const Object**>::const_iterator ci = all_grounded_action_variables.begin(); ci != all_grounded_action_variables.end(); ci++)
			{
				const Object** grounded_action_variables = *ci;
				delete[] grounded_action_variables;
			}
		}
		// Add it as a precondition and try to find atoms to satisfy the remainder of the preconditions.
		else
		{
			instantiateAndExecuteAction(successor_states, action, preconditions, equalities, uninitialised_precondition_index + 1, new_assigned_variables, type_manager, prune_unhelpful_actions);
		}
	}
}

void State::createAllGroundedVariables(std::vector<const Object**>& all_grounded_action_variables, const Object** grounded_action_variables, const Action& action, const TypeManager& type_manager) const
{
	unsigned int counters[action.getVariables().size()];
	memset(counters, 0, sizeof(unsigned int) * action.getVariables().size());
	
	std::vector<const Object*> object_sets[action.getVariables().size()];
	for (unsigned int i = 0; i < action.getVariables().size(); i++)
	{
		type_manager.getObjectsOfType(object_sets[i], *action.getVariables()[i]->getType());
	}
	
	while (true)
	{
		const Object** new_grounded_action_variables = new const Object*[action.getVariables().size()];
		memcpy(new_grounded_action_variables, grounded_action_variables, sizeof(const Object*) * action.getVariables().size());
		
		for (unsigned int i = 0; i < action.getVariables().size(); i++)
		{
			if (grounded_action_variables[i] != NULL) continue;
			new_grounded_action_variables[i] = object_sets[i][counters[i]];
		}
		
		for (unsigned int i = 0; i < action.getVariables().size(); i++)
		{
			assert (new_grounded_action_variables[i] != NULL);
		}
		
		all_grounded_action_variables.push_back(new_grounded_action_variables);
		
		bool counter_updated = false;
		for (unsigned int i = 0; i < action.getVariables().size(); i++)
		{
			if (grounded_action_variables[i] != NULL) continue;
			
			if (counters[i] + 1 != object_sets[i].size())
			{
				counters[i] = counters[i] + 1;
				counter_updated = true;
				break;
			}
			else
			{
				counters[i] = 0;
			}
		}
		
		if (!counter_updated) break;
	}
}

void State::deleteHelpfulActions()
{
	for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		delete *ci;
	}
/*
	for (std::vector<std::pair<const Action*, std::vector<const Object*>**> >::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		const Action* action = (*ci).first;
		std::vector<const Object*>** domains = (*ci).second;
		
		for (unsigned int i = 0; i < action->getVariables().size(); ++i)
		{
			delete domains[i];
		}
		delete[] domains;
	}
*/
	helpful_actions_.clear();
}

bool State::operator==(const State& state) const
{
	if (state.facts_.size() != facts_.size()) return false;
	
	for (unsigned int i = 0; i < state.facts_.size(); ++i)
	{
		if (state.facts_[i] != facts_[i])
		{
			return false;
		}
	}
	return true;
}

std::ostream& operator<<(std::ostream& os, const State& state)
{
	os << " ***** BEGIN STATE h=(" << state.getHeuristic() << ")";
	os << "Achieving actions: ";
	for (std::vector<const GroundedAction*>::const_iterator ci = state.getAchievers().begin(); ci != state.getAchievers().end(); ci++)
	{
		os << **ci << " - ";
	}
	os << " ***** " << std::endl;
	
	for (std::vector<const GroundedAtom*>::const_iterator ci = state.facts_.begin(); ci != state.facts_.end(); ci++)
	{
		if ((*ci)->getAtom().getPredicate().isStatic()) continue;
		os << "* " << **ci << std::endl;
	}
	os << " === Helpful actions === (" << state.getHelpfulActions().size() << ")" << std::endl;
	for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = state.helpful_actions_.begin(); ci != state.helpful_actions_.end(); ++ci)
	{
		os << **ci << std::endl;
	}
	os << " ***** END STATE ***** " << std::endl;
	return os;
}

bool CompareStates::operator()(const State* lhs, const State* rhs)
{
/*	if (!lhs->isCreatedByHelpfulAction() && rhs->isCreatedByHelpfulAction())
	{
		return true;
	}
	else if (lhs->isCreatedByHelpfulAction() && !rhs->isCreatedByHelpfulAction())
	{
		return false;
	}
	else*/
	{
		return lhs->getHeuristic() > rhs->getHeuristic();
	}
}

ForwardChainingPlanner::ForwardChainingPlanner(const ActionManager& action_manager, PredicateManager& predicate_manager, const TypeManager& type_manager)
	: action_manager_(&action_manager), predicate_manager_(&predicate_manager), type_manager_(&type_manager)
{
	
}

ForwardChainingPlanner::~ForwardChainingPlanner()
{
	
}

std::pair<int, int> ForwardChainingPlanner::findPlan(std::vector<const GroundedAction*>& plan, REACHABILITY::DTGReachability& analyst, const std::vector<const Atom*>& initial_facts, const std::vector<const Atom*>& goal_facts, bool prune_unhelpful_actions, bool allow_restarts, bool allow_new_goals_to_be_added)
{
	std::srand(std::time(NULL));
	unsigned int states_seen_without_improvement = 0;
	std::vector<const GroundedAtom*> grounded_initial_facts;
	for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		const Atom* initial_fact = *ci;
		const Object** variables = new const Object*[initial_fact->getArity()];

		for (unsigned int i = 0; i < initial_fact->getArity(); ++i)
		{
			variables[i] = static_cast<const Object*>(initial_fact->getTerms()[i]);
		}
		
		grounded_initial_facts.push_back(&GroundedAtom::getGroundedAtom(**ci, variables));
	}
	
	std::vector<const GroundedAtom*> grounded_goal_facts;
	for (std::vector<const Atom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ci++)
	{
		const Atom* goal_fact = *ci;
		const Object** variables = new const Object*[goal_fact->getArity()];

		for (unsigned int i = 0; i < goal_fact->getArity(); ++i)
		{
			variables[i] = static_cast<const Object*>(goal_fact->getTerms()[i]);
		}
		
		grounded_goal_facts.push_back(&GroundedAtom::getGroundedAtom(**ci, variables));
	}
	
/*
	std::vector<const REACHABILITY::ResolvedBoundedAtom*> resolved_grounded_goal_facts;
	for (std::vector<const SAS_Plus::BoundedAtom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ci++)
	{
		resolved_grounded_goal_facts.push_back(new REACHABILITY::ResolvedBoundedAtom((*ci)->getId(), (*ci)->getAtom(), bindings, analyst.getEquivalentObjectGroupManager(), *predicate_manager_));
	}
*/
	std::vector<const State*> processed_states;
	
	State* initial_state = new State(grounded_initial_facts, true);
	std::vector<REACHABILITY::ReachableFact*> initial_reachable_facts;
	for (std::vector<const GroundedAtom*>::const_iterator ci = initial_state->getFacts().begin(); ci != initial_state->getFacts().end(); ci++)
	{
		const GroundedAtom* grounded_atom = *ci;
		//REACHABILITY::EquivalentObjectGroup** variables = new REACHABILITY::EquivalentObjectGroup*[grounded_atom->getAtom().getArity()];
		std::vector<REACHABILITY::EquivalentObjectGroup*>* variables = new std::vector<REACHABILITY::EquivalentObjectGroup*>(grounded_atom->getAtom().getArity());
		for (unsigned int i = 0; i < grounded_atom->getAtom().getArity(); i++)
		{
			(*variables)[i] = &analyst.getEquivalentObjectGroupManager().getEquivalentObject(grounded_atom->getObject(i)).getEquivalentObjectGroup();
		}
		
		initial_reachable_facts.push_back(&REACHABILITY::ReachableFact::createReachableFact(grounded_atom->getAtom().getPredicate(), *variables));
	}

	setHeuristicForState(*initial_state, analyst, grounded_goal_facts, true, allow_new_goals_to_be_added);
/*
	{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
		std::cout << " *** CALCULATE THE HEURISTIC FOR *** " << std::endl;
		for (std::vector<REACHABILITY::ReachableFact*>::const_iterator ci = initial_reachable_facts.begin(); ci != initial_reachable_facts.end(); ci++)
		{
			std::cout << **ci << std::endl;
		}
#endif
		
		std::vector<const REACHABILITY::ReachableFact*> result;
		std::vector<const GroundedAtom*> persistent_facts;
//		analyst.performReachabilityAnalysis(result, initial_reachable_facts, bindings, persistent_facts);
		analyst.performReachabilityAnalysis(result, initial_reachable_facts, persistent_facts);
		unsigned int heuristic_value = analyst.getHeuristic(grounded_goal_facts, *predicate_manager_);
	
		initial_state->setDistanceToGoal(heuristic_value);
		initial_state->setHelpfulActions(analyst.getHelpfulActions());
		std::cout << "Heuristic: " << heuristic_value << std::endl;
	}
*/
	std::priority_queue<State*, std::vector<State*>, CompareStates> queue;
	queue.push(initial_state);
	
	unsigned int states_visited = 0;
	unsigned int successors_generated = 0;
	
	unsigned int best_heuristic_estimate = std::numeric_limits<unsigned int>::max();
	
	State* last_best_state_seen = initial_state;
	unsigned int base = 2;
	unsigned int min_power = 1;
	unsigned int max_power = 12;
	unsigned int current_power = min_power;
	
	std::vector<State*> current_states_to_explore;
	unsigned int current_best_value_in_list = initial_state->getHeuristic();
	
	while (!queue.empty() || !current_states_to_explore.empty())
	{
		// Create a list of states which have the same heuristic value.
		if (current_states_to_explore.empty() || queue.top()->getHeuristic() == current_best_value_in_list)
		{
			current_best_value_in_list = queue.top()->getHeuristic();
			
			while (!queue.empty() && queue.top()->getHeuristic() == current_best_value_in_list)
			{
				State* state = queue.top();
				queue.pop();
				current_states_to_explore.push_back(state);
			}
		}
		
		// From all the elements in the list, pick one at random to explore.
		unsigned int random_state_index = std::rand() % current_states_to_explore.size();
		
		State* state = current_states_to_explore[random_state_index];
		current_states_to_explore.erase(current_states_to_explore.begin() + random_state_index);
		
//		State* state = queue.top();
//		queue.pop();
		
		bool already_processed = false;
		for (std::vector<const State*>::const_iterator ci = processed_states.begin(); ci != processed_states.end(); ci++)
		{
			if (*state == **ci)
			{
				already_processed = true;
				break;
			}
		}
		
		if (already_processed)
		{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Already processed!?" << queue.size() << std::endl;
			std::cout << *state << std::endl;
#endif
			delete state;
			continue;
		}
		
		if (best_heuristic_estimate > state->getHeuristic())
		{
			states_seen_without_improvement = 0;
			current_power = min_power;
			
			if (last_best_state_seen != state)
			{
				last_best_state_seen->deleteHelpfulActions();
			}
			last_best_state_seen = state;
			best_heuristic_estimate = state->getHeuristic();
			std::cerr << "\t" << best_heuristic_estimate << " state = " << processed_states.size() << "; Grounded Actions = " << GroundedAction::numberOfGroundedActions() << "; Grounded atoms: " << GroundedAtom::numberOfGroundedAtoms() << std::endl;
//			std::cerr << *state << std::endl;
//			std::cout << "Best new heuristic, empty the queue!" << std::endl;
			// Try enforced hill climbing.
			while (!queue.empty())
			{
				const State* dead_state = queue.top();
				queue.pop();
				delete dead_state;
			}
			
			for (std::vector<State*>::const_iterator ci = current_states_to_explore.begin(); ci != current_states_to_explore.end(); ++ci)
			{
				delete *ci;
			}
			current_states_to_explore.clear();
			
			for (std::vector<const State*>::const_iterator ci = processed_states.begin(); ci != processed_states.end(); ci++)
			{
				delete *ci;
			}
			processed_states.clear();
			
			// Delete all grounded actions which are not stored in the states.
			GroundedAction::removeInstantiatedGroundedActions(state->getAchievers().begin(), state->getAchievers().end());
			
			// Delete all the grounded facts which are not contained in any state.
/*			std::vector<const GroundedAtom*> grounded_atoms_in_use;
			grounded_atoms_in_use.insert(grounded_atoms_in_use.end(), state->getFacts().begin(), state->getFacts().end());
			grounded_atoms_in_use.insert(grounded_atoms_in_use.end(), grounded_initial_facts.begin(), grounded_initial_facts.end());
			grounded_atoms_in_use.insert(grounded_atoms_in_use.end(), grounded_goal_facts.begin(), grounded_goal_facts.end());
			
			for (std::vector<const State*>::const_iterator ci = processed_states.begin(); ci != processed_states.end(); ci++)
			{
				grounded_atoms_in_use.insert(grounded_atoms_in_use.end(), (*ci)->getFacts().begin(), (*ci)->getFacts().end());
			}
			
			GroundedAtom::removeInstantiatedGroundedAtom(grounded_atoms_in_use);
*/
		}
		// If we have not seen any improvement quick enough we restart!
		else if (allow_restarts && states_seen_without_improvement > std::pow(base, current_power))
		{
			std::cerr << "\tRestart!" << states_seen_without_improvement << "/" << std::pow(base, current_power) << std::endl;
			while (!queue.empty())
			{
				const State* dead_state = queue.top();
				queue.pop();
				delete dead_state;
			}
			
			for (std::vector<const State*>::const_iterator ci = processed_states.begin(); ci != processed_states.end(); ci++)
			{
				if (*ci != last_best_state_seen)
				{
					delete *ci;
				}
			}
			processed_states.clear();
			
			for (std::vector<State*>::const_iterator ci = current_states_to_explore.begin(); ci != current_states_to_explore.end(); ++ci)
			{
				delete *ci;
			}
			current_states_to_explore.clear();
			
			// Delete all grounded actions which are not stored in the states.
			GroundedAction::removeInstantiatedGroundedActions(last_best_state_seen->getAchievers().begin(), last_best_state_seen->getAchievers().end());
			delete state;
			state = last_best_state_seen;
			current_best_value_in_list = state->getHeuristic();
			states_seen_without_improvement = 0;
			
			// If we could not find a solution in a reasonable amount of steps then we stop the search!
			if (prune_unhelpful_actions && current_power == max_power)
			{
				std::cerr << "Too many restarts, abort!" << std::endl;
				processed_states.push_back(state);
				break;
			}
			
			++current_power;
		}
		++states_seen_without_improvement;
		++states_visited;
		processed_states.push_back(state);
		
		if (states_visited % 1000 == 0) std::cerr << "M" << "s=" << processed_states.size() << ";g=" << GroundedAction::numberOfGroundedActions() << "q=" << queue.size();
		else if (states_visited % 100 == 0) std::cerr << ".";
		else std::cerr << "@";
		
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
		std::cout << "Work on: " << std::endl;
		std::cout << *state << std::endl;
#endif
		
		if (state->isSuperSetOf(grounded_goal_facts))
		{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Found a goal state:" << std::endl;
			std::cout << *state << std::endl;
#endif
//			std::cerr << "States visited: " << states_visited << std::endl;
//			std::cerr << "Generated successors: " << successors_generated << std::endl;
			
			plan.insert(plan.end(), state->getAchievers().begin(), state->getAchievers().end());
			
			while (!queue.empty())
			{
				const State* state = queue.top();
				queue.pop();
				delete state;
			}
			
			for (std::vector<const State*>::const_iterator ci = processed_states.begin(); ci != processed_states.end(); ci++)
			{
				delete *ci;
			}
			
			for (std::vector<State*>::const_iterator ci = current_states_to_explore.begin(); ci != current_states_to_explore.end(); ++ci)
			{
				delete *ci;
			}
			current_states_to_explore.clear();
			
//			for (std::vector<const REACHABILITY::ResolvedBoundedAtom*>::const_iterator ci = resolved_grounded_goal_facts.begin(); ci != resolved_grounded_goal_facts.end(); ++ci)
//			{
//				delete *ci;
//			}
			
			return std::make_pair(states_visited, plan.size());
		}
		
		std::vector<State*> successor_states;
		
		// Before finding the successors, search for helpful actions (if this option is enabled).
		if (prune_unhelpful_actions)
		{
			setHeuristicForState(*state, analyst, grounded_goal_facts, true, allow_new_goals_to_be_added);
		}
		state->getSuccessors(successor_states, *action_manager_, *type_manager_, prune_unhelpful_actions);
		
		for (std::vector<State*>::const_iterator ci = successor_states.begin(); ci != successor_states.end(); ci++)
		{
			State* successor_state = *ci;
			++successors_generated;
			if (prune_unhelpful_actions && !successor_state->isCreatedByHelpfulAction())
			{
				delete successor_state;
//				std::cerr << "*";
				continue;
			}
			
/*			if (prune_unhelpful_actions && successor_state->getHeuristic() < state->getHeuristic())
			{
				while (!queue.empty())
				{
					const State* state = queue.top();
					queue.pop();
					delete state;
				}
			}*/
			
			setHeuristicForState(*successor_state, analyst, grounded_goal_facts, false, allow_new_goals_to_be_added);
			
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Sucessor state:" << std::endl;
			std::cout << *successor_state << std::endl;
			std::cout << " ============== Helpful actions ============== " << std::endl;
			for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = analyst.getHelpfulActions().begin(); ci != analyst.getHelpfulActions().end(); ++ci)
			{
				std::cout << **ci << std::endl;
			}
#endif

			queue.push(successor_state);
		}
		
		//if (last_best_state_seen != state)
		{
			state->deleteHelpfulActions();
		}
	}
	
//	for (std::vector<const REACHABILITY::ResolvedBoundedAtom*>::const_iterator ci = resolved_grounded_goal_facts.begin(); ci != resolved_grounded_goal_facts.end(); ++ci)
//	{
//		delete *ci;
//	}
	
//	for (std::vector<const GroundedAtom*>::const_iterator ci = grounded_goal_facts.begin(); ci != grounded_goal_facts.end(); ++ci)
//	{
//		delete *ci;
//	}
	
	
	while (!queue.empty())
	{
		const State* state = queue.top();
		queue.pop();
		delete state;
	}
	
	for (std::vector<const State*>::const_iterator ci = processed_states.begin(); ci != processed_states.end(); ci++)
	{
		delete *ci;
	}
	processed_states.clear();
	
	for (std::vector<State*>::const_iterator ci = current_states_to_explore.begin(); ci != current_states_to_explore.end(); ++ci)
	{
		delete *ci;
	}
	current_states_to_explore.clear();
	
	std::cerr << "No plan found :((((((((((" << std::endl;
	
	return std::make_pair(-1, -1);
}

//void ForwardChainingPlanner::setHeuristicForState(MyPOP::State& state, REACHABILITY::DTGReachability& analyst, const std::vector<const GroundedAtom*>& goal_facts, const std::vector<const REACHABILITY::ResolvedBoundedAtom*>& resolved_grounded_goal_facts, const Bindings& bindings) const
void ForwardChainingPlanner::setHeuristicForState(MyPOP::State& state, REACHABILITY::DTGReachability& analyst, const std::vector<const GroundedAtom*>& goal_facts, bool find_helpful_actions, bool allow_new_goals_to_be_added) const
{
	analyst.getEquivalentObjectGroupManager().reset();
	std::vector<REACHABILITY::ReachableFact*> reachable_facts;
	for (std::vector<const GroundedAtom*>::const_iterator ci = state.getFacts().begin(); ci != state.getFacts().end(); ci++)
	{
		const GroundedAtom* grounded_atom = *ci;
		std::vector<REACHABILITY::EquivalentObjectGroup*>* variables = new std::vector<REACHABILITY::EquivalentObjectGroup*>(grounded_atom->getAtom().getArity());
		for (unsigned int i = 0; i < grounded_atom->getAtom().getArity(); i++)
		{
			(*variables)[i] = &analyst.getEquivalentObjectGroupManager().getEquivalentObject(grounded_atom->getObject(i)).getEquivalentObjectGroup();
		}
		
		reachable_facts.push_back(&REACHABILITY::ReachableFact::createReachableFact(grounded_atom->getAtom().getPredicate(), *variables));
	}

#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << " *** CALCULATE THE HEURISTIC FOR *** " << std::endl;
	for (std::vector<REACHABILITY::ReachableFact*>::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
#endif
	std::vector<const REACHABILITY::ReachableFact*> result;
	std::vector<const GroundedAtom*> persistent_facts;

	// Check which of the facts in the state correspond to the goal facts and prevent these from being deleted.
	for (std::vector<const GroundedAtom*>::const_iterator ci = state.getFacts().begin(); ci != state.getFacts().end(); ++ci)
	{
		const GroundedAtom* state_fact = *ci;
		for (std::vector<const GroundedAtom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ++ci)
		{
			const GroundedAtom* goal_fact = *ci;
			
			if (*state_fact == *goal_fact)
			{
				persistent_facts.push_back(goal_fact);
				break;
			}
		}
	}

	analyst.performReachabilityAnalysis(result, reachable_facts, persistent_facts);
	
	// Check if all the goals are reachable in the ultimate state of the lifted RPG.
	bool all_goal_facts_are_achieved = true;
	for (std::vector<const GroundedAtom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ++ci)
	{
		const GroundedAtom* goal_fact = *ci;
		bool goal_fact_achieved = false;
		for (std::vector<const REACHABILITY::ReachableFact*>::const_iterator ci = result.begin(); ci != result.end(); ++ci)
		{
			const REACHABILITY::ReachableFact* reachable_fact = *ci;
			if (goal_fact->getAtom().getArity() != reachable_fact->getPredicate().getArity() ||
					goal_fact->getAtom().getPredicate().getName() != goal_fact->getAtom().getPredicate().getName())
			{
				continue;
			}
			
			bool terms_match = true;
			for (unsigned int i = 0; i < goal_fact->getAtom().getArity(); ++i)
			{
				const REACHABILITY::EquivalentObjectGroup& eog = reachable_fact->getTermDomain(i);
				if (!eog.contains(goal_fact->getObject(i)))
				{
					terms_match = false;
					break;
				}
			}
			
			if (terms_match)
			{
				goal_fact_achieved = true;
				break;
			}
		}
		
		if (!goal_fact_achieved)
		{
			all_goal_facts_are_achieved = false;
			break;
		}
	}
	
	if (!all_goal_facts_are_achieved)
	{
		persistent_facts.clear();
		result.clear();
		analyst.getEquivalentObjectGroupManager().reset();
		reachable_facts.clear();
		
		for (std::vector<const GroundedAtom*>::const_iterator ci = state.getFacts().begin(); ci != state.getFacts().end(); ci++)
		{
			const GroundedAtom* grounded_atom = *ci;
			std::vector<REACHABILITY::EquivalentObjectGroup*>* variables = new std::vector<REACHABILITY::EquivalentObjectGroup*>(grounded_atom->getAtom().getArity());
			for (unsigned int i = 0; i < grounded_atom->getAtom().getArity(); i++)
			{
				(*variables)[i] = &analyst.getEquivalentObjectGroupManager().getEquivalentObject(grounded_atom->getObject(i)).getEquivalentObjectGroup();
			}
			
			reachable_facts.push_back(&REACHABILITY::ReachableFact::createReachableFact(grounded_atom->getAtom().getPredicate(), *variables));
		}
//		std::cerr << "!";
		analyst.performReachabilityAnalysis(result, reachable_facts, persistent_facts);
	}
	else
	{
//		std::cerr << "?";
	}
	
	unsigned int heuristic_value = analyst.getHeuristic(goal_facts, *predicate_manager_, allow_new_goals_to_be_added, find_helpful_actions, false);
	state.setDistanceToGoal(heuristic_value);
//	std::cerr << analyst.getHelpfulActions().size() << std::endl;
	if (find_helpful_actions)
	{
		state.setHelpfulActions(analyst.getHelpfulActions());
//		std::cerr << "H=" << analyst.getHelpfulActions().size() << std::endl;
	}
}


};
