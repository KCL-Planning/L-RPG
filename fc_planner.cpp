#include "fc_planner.h"

#include <queue>
#include <cmath>
#include <time.h>

#include "formula.h"
#include "predicate_manager.h"
#include "action_manager.h"
#include "type_manager.h"
#include "term_manager.h"
#include "parser_utils.h"
#include "heuristics/dtg_reachability.h"
#include "heuristics/equivalent_object_group.h"

//#define MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
#include "type_manager.h"
#include "heuristics/fact_set.h"

namespace MyPOP {

StateHeuristicListener::StateHeuristicListener(std::vector<State*>& found_states, const State& current_state, HEURISTICS::HeuristicInterface& heuristic, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager, bool find_helpful_actions, bool allow_new_goals_to_be_added)
	: found_states_(&found_states), current_state_(&current_state), heuristic_(&heuristic), goal_facts_(&goal_facts), term_manager_(&term_manager), find_helpful_actions_(find_helpful_actions), allow_new_goals_to_be_added_(allow_new_goals_to_be_added), found_better_state_(false)
{
	
}
	
void StateHeuristicListener::addNewState(State& state)
{
//	heuristic_->setHeuristicForState(state, *goal_facts_, *term_manager_, find_helpful_actions_, allow_new_goals_to_be_added_);
	heuristic_->setHeuristicForState(state, *goal_facts_, *term_manager_, false, allow_new_goals_to_be_added_);
	// Uncomment for less aggressive pruning technique.
	if (false && find_helpful_actions_ && state.getHeuristic() < current_state_->getHeuristic())
	{
		found_better_state_ = true;
		for (std::vector<State*>::const_iterator ci = found_states_->begin(); ci != found_states_->end(); ++ci)
		{
			delete *ci;
		}
		found_states_->clear();
	}
	found_states_->push_back(&state);
}

bool StateHeuristicListener::continueSearching()
{
	return !found_better_state_;
}

StateStoreListener::StateStoreListener(std::vector<State*>& found_states)
	: found_states_(&found_states)
{
	
}
	
void StateStoreListener::addNewState(State& state)
{
	found_states_->push_back(&state);
}
	
bool StateStoreListener::continueSearching()
{
	return true;
}
	
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
	for (std::vector<const GroundedAtom*>::reverse_iterator ri = instantiated_grounded_atoms_.rbegin(); ri != instantiated_grounded_atoms_.rend(); ++ri)
	{
		const GroundedAtom* grounded_atom = *ri;
		if (grounded_atom->getPredicate().isStatic())
		{
			continue;
		}
		
		delete grounded_atom;
		instantiated_grounded_atoms_.erase(ri.base() - 1);
/*
	for (std::vector<const GroundedAtom*>::const_iterator ci = instantiated_grounded_atoms_.begin(); ci != instantiated_grounded_atoms_.end(); ++ci)
	{
		const GroundedAtom* grounded_atom = *ci;
		delete grounded_atom;
*/
	}
//	instantiated_grounded_atoms_.clear();
}

void GroundedAtom::removeInstantiatedGroundedAtom(const std::vector<const GroundedAtom*>& exceptions)
{
	for (std::vector<const GroundedAtom*>::reverse_iterator ri = instantiated_grounded_atoms_.rbegin(); ri != instantiated_grounded_atoms_.rend(); ++ri)
	{
		const GroundedAtom* grounded_atom = *ri;
		if (grounded_atom->getPredicate().isStatic())
		{
			continue;
		}
		
		if (std::find(exceptions.begin(), exceptions.end(), grounded_atom) == exceptions.end())
		{
			delete grounded_atom;
			instantiated_grounded_atoms_.erase(ri.base() - 1);
		}
	}
}

const GroundedAtom& GroundedAtom::getGroundedAtom(const Predicate& predicate, const Object** variables)
{
	for (std::vector<const GroundedAtom*>::const_iterator ci = instantiated_grounded_atoms_.begin(); ci != instantiated_grounded_atoms_.end(); ++ci)
	{
		const GroundedAtom* grounded_atom = *ci;
		
		if (grounded_atom->getPredicate().getArity() != predicate.getArity() ||
		    grounded_atom->getPredicate().getName() != predicate.getName())
		{
			continue;
		}
		
		bool variable_domain_match = true;
		for (unsigned int i = 0; i < grounded_atom->getPredicate().getArity(); ++i)
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
	
	GroundedAtom* new_grounded_atom = new GroundedAtom(predicate, variables);
	instantiated_grounded_atoms_.push_back(new_grounded_atom);
	return *new_grounded_atom;
}
/*
const GroundedAtom& GroundedAtom::getGroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings)
{
	const Object** variables = new const Object*[bounded_atom.getAtom().getArity()];
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); ++i)
	{
		variables[i] = bounded_atom.getVariableDomain(i, bindings)[0];
	}
	return getGroundedAtom(bounded_atom.getAtom(), variables);
}
*/
unsigned int GroundedAtom::numberOfGroundedAtoms()
{
	return instantiated_grounded_atoms_.size();
}

GroundedAtom::GroundedAtom(const Predicate& predicate, const Object** variables)
	: predicate_(&predicate), variables_(variables)
{
//	std::cout << "New Grounded atom: " << *this << std::endl;
}
/*
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
*/
GroundedAtom::~GroundedAtom()
{
	delete[] variables_;
}

bool GroundedAtom::operator==(const GroundedAtom& rhs) const
{
	if (predicate_->getName() != rhs.predicate_->getName() ||
	    predicate_->getArity() != rhs.predicate_->getArity()) return false;
	
	for (unsigned int i = 0; i < predicate_->getArity(); i++)
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
	os << "(" << grounded_atom.getPredicate().getName();
	for (unsigned int i = 0; i < grounded_atom.getPredicate().getArity(); i++)
	{
		os << " " << grounded_atom.getObject(i);
	}
	os << ")";
	return os;
}

std::vector<const GroundedAtom*> State::static_facts_;

State::State(const std::vector<const GroundedAtom*>& facts, bool created_by_helpful_action)
	: facts_(facts), distance_to_goal_(0)/*, distance_from_start_(0)*/, created_by_helpful_action_(created_by_helpful_action)
{
	assert (facts_.size() == facts.size());
	std::sort(facts_.begin(), facts_.end());
}

State::State(const State& rhs, const GroundedAction& grounded_action, bool created_by_helpful_action)
	: facts_(rhs.facts_), distance_to_goal_(rhs.distance_to_goal_)/*, distance_from_start_(rhs.distance_from_start_ + 1)*/, created_by_helpful_action_(created_by_helpful_action)
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

void State::getSuccessors(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const ActionManager& action_manager, const TypeManager& type_manager, bool prune_unhelpful_actions) const
{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "Find successors of" << std::endl << *this << std::endl;
#endif
	
	// Instantiate all the helpful actions and try to find preconditions to match them.
	if (helpful_actions_.size() > 0 && false)
	{
		std::vector<const GroundedAction*> already_tried_actions;
		// TODO: Maybe shuffle? std::shuffle().
		for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
		{
			const REACHABILITY::AchievingTransition* transition = *ci;
			const Action& action = transition->getAchiever()->getTransition().getAction();
			
			unsigned int counter[action.getVariables().size()];
			memset(&counter[0], 0, sizeof(unsigned int) * action.getVariables().size());
			
			const Object* assigned_variables[action.getVariables().size()];
			
			std::vector<const Atom*> preconditions;
			std::vector<const Equality*> equalities;
			Utility::convertFormula(preconditions, equalities, &action.getPrecondition());
			
			bool done = false;
			while (!done)
			{
				done = true;
				memset(assigned_variables, 0, sizeof(Object*) * action.getVariables().size());
				
				for (unsigned int action_variable_index = 0; action_variable_index < action.getVariables().size(); ++action_variable_index)
				{
					HEURISTICS::VariableDomain* vd = transition->getVariableAssignments()[action_variable_index];
					assigned_variables[action_variable_index] = vd->getVariableDomain()[counter[action_variable_index]];
				}
				
				// Ground this action.
				const GroundedAction& grounded_action = GroundedAction::getGroundedAction(action, assigned_variables);
				
				// Make sure a symmetrical precondition has not been used.
				bool is_symmetrical = false;
				for (std::vector<const GroundedAction*>::const_iterator ci = already_tried_actions.begin(); ci != already_tried_actions.end(); ++ci)
				{
					const GroundedAction* old_action = *ci;
					if (old_action->getAction().getVariables().size() != grounded_action.getAction().getVariables().size() ||
							old_action->getAction().getPredicate() != grounded_action.getAction().getPredicate())
					{
						continue;
					}
					
					bool terms_are_symmetrical = true;
					for (unsigned int term_index = 0; term_index < old_action->getAction().getVariables().size(); ++term_index)
					{
						std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> eo_ci = symmetrical_groups.equal_range(&old_action->getVariablesAssignment(term_index));
						bool found_symmetrical_object = false;
						for (std::multimap<const Object*, const Object*>::const_iterator ci = eo_ci.first; ci != eo_ci.second; ++ci)
						{
							const Object* symmetrical_object = (*ci).second;
							if (symmetrical_object == &grounded_action.getVariablesAssignment(term_index))
							{
								found_symmetrical_object = true;
								break;
							}
						}
						
						if (!found_symmetrical_object)
						{
							terms_are_symmetrical = false;
							break;
						}
					}
					
					// If the terms are symmetrical than we do not need to persue this branch further!
					if (terms_are_symmetrical)
					{
		//				std::cerr << *fact << " == " << *grounded_atom << std::endl;
						is_symmetrical = true;
						break;
					}
				}
				
				if (is_symmetrical)
				{
					continue;
				}
/*
				// Search the initial state for facts which support the action's precondition.
				bool all_precondition_satisfied = true;
				for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
				{
					const Atom* precondition = *ci;
					const Object** assignments = new const Object*[precondition->getArity()];
					
					for (unsigned int term_index = 0; term_index < precondition->getArity(); ++term_index)
					{
						for (unsigned int action_index = 0; action_index < action.getVariables().size(); ++action_index)
						{
							if (precondition->getTerms()[term_index] == action.getVariables()[action_index])
							{
								assignments[term_index] = assigned_variables[action_index];
								break;
							}
						}
					}
					
					const GroundedAtom& grounded_precondition = GroundedAtom::getGroundedAtom(precondition->getPredicate(), assignments);
					
					bool precondition_part_of_init_state = false;
					for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end(); ++ci)
					{
						if (*ci == &grounded_precondition)
						{
							precondition_part_of_init_state = true;
							break;
						}
					}
					
					if (!precondition_part_of_init_state)
					{
						all_precondition_satisfied = false;
						break;
					}
				}

				if (all_precondition_satisfied)
*/
				{
					already_tried_actions.push_back(&grounded_action);
					// Create a new state!
					State* new_state = new State(*this, grounded_action, true);
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
							unsigned int variable_index = std::distance(action.getVariables().begin(), std::find(action.getVariables().begin(), action.getVariables().end(), effect->getTerms()[i]));
							effect_variables[i] = assigned_variables[variable_index];
						}
						
						const GroundedAtom& grounded_effect = GroundedAtom::getGroundedAtom(effect->getPredicate(), effect_variables);
						if (effect->isNegative())
						{
							new_state->removeFact(grounded_effect);
						}
						else
						{
							to_add.push_back(&grounded_effect);
						}
					}
					
					for (std::vector<const GroundedAtom*>::const_iterator ci = to_add.begin(); ci != to_add.end(); ci++)
					{
						new_state->addFact(**ci, true);
					}
					listener.addNewState(*new_state);
					//successor_states.push_back(new_state);
				}
				
				for (unsigned int action_variable_index = 0; action_variable_index < action.getVariables().size(); ++action_variable_index)
				{
					if (counter[action_variable_index] + 1 != transition->getVariableAssignments()[action_variable_index]->getVariableDomain().size())
					{
						done = false;
						counter[action_variable_index] = counter[action_variable_index] + 1;
						break;
					}
					else
					{
						counter[action_variable_index] = 0;
					}
				}
			}
		}
	}
	else
	{
		for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
		{
			const Action* action = *ci;
			
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Try: " << action->getPredicate() << std::endl;
#endif
			
			std::vector<const Atom*> preconditions;
			std::vector<const Equality*> equalities;
			Utility::convertFormula(preconditions, equalities, &action->getPrecondition());
			
			// Construct all grounded variants of this action which are applicable in this state.
			const Object* assigned_variables[action->getVariables().size()];
			memset(assigned_variables, 0, sizeof(Object*) * action->getVariables().size());
			
			instantiateAndExecuteAction(listener, symmetrical_groups, *action, preconditions, equalities, 0, assigned_variables, type_manager, prune_unhelpful_actions);
		}
	}
//#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//	std::cout << "Found: " << successor_states.size() << " successors states for: " << std::endl << *this << std::endl;
//#endif
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

void State::instantiateAndExecuteAction(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const Action& action, const std::vector<const Atom*>& preconditions, const std::vector<const Equality*>& equalities, unsigned int uninitialised_precondition_index, const Object** assigned_variables, const TypeManager& type_manager, bool prune_unhelpful_actions) const
{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "[State::instantiateAndExecuteAction] Handle: " << action.getPredicate() << " - Precondition: " << preconditions[uninitialised_precondition_index]->getPredicate() << "(" << uninitialised_precondition_index << "/ " << preconditions.size() << ")" << std::endl;
	
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
#endif
	// Find facts in the current state which can unify with the 'uninitialised_precondition_index'th precondition and does not violate the already assigned variables.
	const Atom* precondition = preconditions[uninitialised_precondition_index];
	std::vector<const GroundedAtom*> already_tried_facts;
	
	const std::vector<const GroundedAtom*>* relevant_facts = precondition->getPredicate().isStatic() ? &static_facts_ : &facts_;
	//const std::vector<const GroundedAtom*>* relevant_facts = &facts_;
	//for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end() && listener.continueSearching(); ci++)
	for (std::vector<const GroundedAtom*>::const_iterator ci = relevant_facts->begin(); ci != relevant_facts->end(); ++ci)
	{
		const GroundedAtom* grounded_atom = *ci;
		//const GroundedAtom* grounded_atom = (i < facts_.size() ? facts_[i] : static_facts_[i - facts_.size()]);
		if (grounded_atom->getPredicate().getArity() != precondition->getArity() || grounded_atom->getPredicate().getName() != precondition->getPredicate().getName())
		{
			continue;
		}
		
		// Check if none of the assigned variables are violated.
		bool constraints_satisfied = true;

		const Object* new_assigned_variables[action.getVariables().size()];
		memcpy(new_assigned_variables, assigned_variables, sizeof(const Object*) * action.getVariables().size());
		
		for (unsigned int i = 0; i < grounded_atom->getPredicate().getArity(); i++)
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
				
				if (assigned_variables[lhs_term_index] != NULL && assigned_variables[rhs_term_index] != NULL && (assigned_variables[lhs_term_index] == assigned_variables[rhs_term_index]) == equality->isNegative())
				{
					constraints_satisfied = false;
				}
			}
		}
		
		if (!constraints_satisfied)
		{
			continue;
		}
		
		// Make sure a symmetrical precondition has not been used.
		bool is_symmetrical = false;
		for (std::vector<const GroundedAtom*>::const_iterator ci = already_tried_facts.begin(); ci != already_tried_facts.end(); ++ci)
		{
			const GroundedAtom* fact = *ci;
			if (fact->getPredicate().getArity() != grounded_atom->getPredicate().getArity() ||
			    fact->getPredicate().getName() != grounded_atom->getPredicate().getName())
			{
				continue;
			}
			
			bool terms_are_symmetrical = true;
			for (unsigned int term_index = 0; term_index < fact->getPredicate().getArity(); ++term_index)
			{
				std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> eo_ci = symmetrical_groups.equal_range(&fact->getObject(term_index));
				bool found_symmetrical_object = false;
				for (std::multimap<const Object*, const Object*>::const_iterator ci = eo_ci.first; ci != eo_ci.second; ++ci)
				{
					const Object* symmetrical_object = (*ci).second;
					if (symmetrical_object == &grounded_atom->getObject(term_index))
					{
						found_symmetrical_object = true;
						break;
					}
				}
				
				if (!found_symmetrical_object)
				{
					terms_are_symmetrical = false;
					break;
				}
			}
			
			// If the terms are symmetrical than we do not need to persue this branch further!
			if (terms_are_symmetrical)
			{
//				std::cerr << *fact << " == " << *grounded_atom << std::endl;
				is_symmetrical = true;
				break;
			}
		}
		
		if (is_symmetrical)
		{
			continue;
		}
		
		already_tried_facts.push_back(grounded_atom);
		
		// Found an atom which satisfies all constraints, check if we now have a full assignment!
		if (uninitialised_precondition_index + 1 == preconditions.size())
		{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Found a successor state!" << std::endl;
#endif

			const Object** grounded_action_variables_templates = new const Object*[action.getVariables().size()];
			memcpy(grounded_action_variables_templates, new_assigned_variables, sizeof(const Object*) * action.getVariables().size());
			
			// Check if all the variables have been assigned. Those which are not assigned are free variables.
			std::vector<const Object**> all_grounded_action_variables;
			createAllGroundedVariables(all_grounded_action_variables, grounded_action_variables_templates, action, type_manager);
			
			delete[] grounded_action_variables_templates;
			
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "(" << all_grounded_action_variables.size() << ") Helpful actions: " << std::endl;
			for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
			{
				std::cout << **ci << std::endl;
			}
/*
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
*/
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
					
					const GroundedAtom& grounded_effect = GroundedAtom::getGroundedAtom(effect->getPredicate(), effect_variables);
					if (effect->isNegative())
					{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//						std::cout << "Remove: " << *grounded_effect << std::endl;
#endif
						new_state->removeFact(grounded_effect);
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
					new_state->addFact(**ci, true);
				}
							
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//				std::cout << "Successor state: " << *new_state << std::endl;
#endif
				listener.addNewState(*new_state);
				//successor_states.push_back(new_state);
				if (!listener.continueSearching())
				{
					break;
				}
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
			instantiateAndExecuteAction(listener, symmetrical_groups, action, preconditions, equalities, uninitialised_precondition_index + 1, new_assigned_variables, type_manager, prune_unhelpful_actions);
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

void State::addStaticFact(const GroundedAtom& static_fact)
{
	std::cout << "ADD STATIC FACT!" << std::endl;
	static_facts_.push_back(&static_fact);
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
		if ((*ci)->getPredicate().isStatic()) continue;
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

	if (lhs->getHeuristic() == rhs->getHeuristic())
	{
		return lhs->getAchievers().size() > rhs->getAchievers().size();
	}
	else
	{
		return lhs->getHeuristic() > rhs->getHeuristic();
	}
}

ForwardChainingPlanner::ForwardChainingPlanner(const ActionManager& action_manager, PredicateManager& predicate_manager, const TypeManager& type_manager, HEURISTICS::HeuristicInterface& heuristic)
	: action_manager_(&action_manager), predicate_manager_(&predicate_manager), type_manager_(&type_manager), heuristic_(&heuristic)
{
	
}

ForwardChainingPlanner::~ForwardChainingPlanner()
{
	
}

std::pair<int, int> ForwardChainingPlanner::findPlan(std::vector<const GroundedAction*>& plan, const std::vector<const Atom*>& initial_facts, const std::vector<const Atom*>& goal_facts, const TermManager& term_manager, bool prune_unhelpful_actions, bool allow_restarts, bool allow_new_goals_to_be_added)
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
		
		const GroundedAtom& grounded_atom = GroundedAtom::getGroundedAtom(initial_fact->getPredicate(), variables);
		if (initial_fact->getPredicate().isStatic())
		{
			State::addStaticFact(grounded_atom);
		}
		else
		{
			grounded_initial_facts.push_back(&grounded_atom);
		}
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
		
		if (!goal_fact->getPredicate().isStatic())
		{
			const GroundedAtom& grounded_atom = GroundedAtom::getGroundedAtom(goal_fact->getPredicate(), variables);
			grounded_goal_facts.push_back(&grounded_atom);
		}
	}
	
	std::vector<const State*> processed_states;
	State* initial_state = new State(grounded_initial_facts, true);
	heuristic_->setHeuristicForState(*initial_state, grounded_goal_facts, term_manager, true, allow_new_goals_to_be_added);

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
		
/*
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
*/
		
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
			//std::cerr << "\t" << best_heuristic_estimate << " state = " << processed_states.size() << "; Grounded Actions = " << GroundedAction::numberOfGroundedActions() << "; Grounded atoms: " << GroundedAtom::numberOfGroundedAtoms() << std::endl;
//			std::cerr << *state << std::endl;
//			std::cout << "Best new heuristic, empty the queue!" << std::endl;
			// Try enforced hill climbing.
			if (prune_unhelpful_actions)
			{
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
			}
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
			return std::make_pair(states_visited, plan.size());
		}
		
		std::vector<State*> successor_states;
		
		NewStateReachedListener* new_state_reached_listener = NULL;
		new_state_reached_listener = new StateHeuristicListener(successor_states, *state,  *heuristic_, grounded_goal_facts, term_manager, prune_unhelpful_actions, allow_new_goals_to_be_added);
		
		// Before finding the successors, search for helpful actions (if this option is enabled).
		if (prune_unhelpful_actions)
		{
			heuristic_->setHeuristicForState(*state, grounded_goal_facts, term_manager, true, allow_new_goals_to_be_added);
		}
		
		std::multimap<const Object*, const Object*> symmetrical_groups;
		heuristic_->getFunctionalSymmetricSets(symmetrical_groups, *state, grounded_goal_facts, term_manager);
	
		state->getSuccessors(*new_state_reached_listener, symmetrical_groups, *action_manager_, *type_manager_, prune_unhelpful_actions);
		delete new_state_reached_listener;
		
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
		std::cout << "Number of succcessors of " << *state << ": " << successor_states.size() << "." << std::endl;
		std::cout << *state << std::endl;
#endif
		
		for (std::vector<State*>::const_iterator ci = successor_states.begin(); ci != successor_states.end(); ci++)
		{
			State* successor_state = *ci;
			++successors_generated;
			if (prune_unhelpful_actions && !successor_state->isCreatedByHelpfulAction())
			{
				assert (false);
				delete successor_state;
				std::cerr << "*";
				continue;
			}

			bool already_processed = false;
			for (std::vector<const State*>::const_iterator state_ci = processed_states.begin(); state_ci != processed_states.end(); state_ci++)
			{
				if (*successor_state == **state_ci)
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
				delete successor_state;
				continue;
			}
			
			//heuristic_->setHeuristicForState(*successor_state, grounded_goal_facts, term_manager, false, allow_new_goals_to_be_added);
			
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Sucessor state:" << std::endl;
			std::cout << *successor_state << std::endl;
/*			std::cout << " ============== Helpful actions ============== " << std::endl;
			for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = analyst.getHelpfulActions().begin(); ci != analyst.getHelpfulActions().end(); ++ci)
			{
				std::cout << **ci << std::endl;
			}*/
#endif
			
			queue.push(successor_state);
			if (prune_unhelpful_actions && successor_state->getHeuristic() < state->getHeuristic())
			{
				for (std::vector<State*>::const_iterator other_ci = ci + 1; other_ci != successor_states.end(); other_ci++)
				{
					State* other_successor_state = *other_ci;
					delete other_successor_state;
				}
				break;
			}
		}
		
		state->deleteHelpfulActions();
	}
	
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

};
