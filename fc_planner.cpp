#include "fc_planner.h"

#include <queue>

#include "sas/dtg_manager.h"
#include "predicate_manager.h"
#include "action_manager.h"
#include "type_manager.h"
#include "parser_utils.h"
#include "heuristics/dtg_reachability.h"
#include "heuristics/equivalent_object_group.h"

//#define MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
#include "type_manager.h"

namespace MyPOP {

std::vector<const GroundedAction*> GroundedAction::instantiated_grounded_actions_;

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
	
	GroundedAction* new_grounded_action = new GroundedAction(action, variables);
	instantiated_grounded_actions_.push_back(new_grounded_action);
	return *new_grounded_action;
}
	
GroundedAction::GroundedAction(const Action& action, const Object** variables)
	: action_(&action), variables_(variables)
{
	
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
//	delete[] variables_;
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

State::State(const std::vector<const GroundedAtom*>& facts)
	: facts_(facts), distance_to_goal_(0), distance_from_start_(0)
{
	
}

State::State(const State& rhs, const GroundedAction& grounded_action)
	: facts_(rhs.facts_), distance_to_goal_(rhs.distance_to_goal_), distance_from_start_(rhs.distance_from_start_ + 1)
{
	achievers_.insert(achievers_.end(), rhs.achievers_.begin(), rhs.achievers_.end());
	achievers_.push_back(&grounded_action);
}

State::~State()
{
	
}

void State::getSuccessors(std::vector<State*>& successor_states, const ActionManager& action_manager, const TypeManager& type_manager) const
{
	for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
	{
		const Action* action = *ci;
		
		std::vector<const Atom*> preconditions;
		std::vector<const Equality*> equalities;
		Utility::convertFormula(preconditions, equalities, &action->getPrecondition());
		
		// Construct all grounded variants of this action which are applicable in this state.
		const Object* assigned_variables[action->getVariables().size()];
		memset(assigned_variables, 0, sizeof(Object*) * action->getVariables().size());
		
		instantiateAndExecuteAction(successor_states, *action, preconditions, equalities, 0, assigned_variables, type_manager);
	}
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//	std::cout << "Found: " << successor_states.size() << " successors states for: " << std::endl << *this << std::endl;
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

void State::addFact(const GroundedAtom& fact)
{
	// Don't add a fact twice!
	for (std::vector<const GroundedAtom*>::iterator i = facts_.begin(); i != facts_.end(); i++)
	{
		if (**i == fact)
		{
			return;
		}
	}
	facts_.push_back(&fact);
}

void State::removeFact(const GroundedAtom& fact)
{
	for (std::vector<const GroundedAtom*>::iterator i = facts_.begin(); i != facts_.end(); i++)
	{
		if (**i == fact)
		{
			facts_.erase(i);
			break;
		}
	}
}

void State::instantiateAndExecuteAction(std::vector<State*>& successor_states, const Action& action, const std::vector<const Atom*>& preconditions, const std::vector<const Equality*>& equalities, unsigned int uninitialised_precondition_index, const Object** assigned_variables, const TypeManager& type_manager) const
{
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
/*
			unsigned int variable_index = std::numeric_limits<unsigned int>::max();
			for (unsigned int j = 0; j < action.getVariables().size(); j++)
			{
				if (precondition->getTerms()[i] == action.getVariables()[j])
				{
					variable_index = j;
					break;
				}
			}
			assert (variable_index != std::numeric_limits<unsigned int>::max());
*/
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
	
			for (std::vector<const Object**>::const_iterator ci = all_grounded_action_variables.begin(); ci != all_grounded_action_variables.end(); ci++)
			{
				const Object** grounded_action_variables = *ci;
				//GroundedAction* grounded_action = new GroundedAction(action, grounded_action_variables);
				const GroundedAction& grounded_action = GroundedAction::getGroundedAction(action, grounded_action_variables);
				
				// Apply the action to the new state!
				State* new_state = new State(*this, grounded_action);
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//				std::cout << "Copy the old state: " << *new_state << std::endl;
#endif

				std::vector<GroundedAtom*> to_add;
				for (std::vector<const Atom*>::const_iterator ci = action.getEffects().begin(); ci != action.getEffects().end(); ci++)
				{
					const Atom* effect = *ci;
					const Object** effect_variables = new const Object*[effect->getArity()];
					
					for (unsigned int i = 0; i < effect->getArity(); i++)
					{
						assert (std::find(action.getVariables().begin(), action.getVariables().end(), effect->getTerms()[i]) != action.getVariables().end());
						unsigned int variable_index = std::distance(action.getVariables().begin(), std::find(action.getVariables().begin(), action.getVariables().end(), effect->getTerms()[i]));
/*
						unsigned int variable_index = std::numeric_limits<unsigned int>::max();
						for (unsigned int j = 0; j < action.getVariables().size(); j++)
						{
							if (effect->getTerms()[i] == action.getVariables()[j])
							{
								variable_index = j;
								break;
							}
						}
						
						assert (variable_index != std::numeric_limits<unsigned int>::max());
*/
						assert (grounded_action_variables[variable_index] != NULL);
						effect_variables[i] = grounded_action_variables[variable_index];
					}
					
					GroundedAtom* grounded_effect = new GroundedAtom(*effect, effect_variables);
					if (effect->isNegative())
					{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//						std::cout << "Remove: " << *grounded_effect << std::endl;
#endif
						new_state->removeFact(*grounded_effect);
						delete grounded_effect;
					}
					else
					{
						to_add.push_back(grounded_effect);
					}
				}
				
				for (std::vector<GroundedAtom*>::const_iterator ci = to_add.begin(); ci != to_add.end(); ci++)
				{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//					std::cout << "Add: " << *grounded_effect << std::endl;
#endif
					new_state->addFact(**ci);
				}
							
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//				std::cout << "Successor state: " << *new_state << std::endl;
#endif
				successor_states.push_back(new_state);
			}
		}
		// Add it as a precondition and try to find atoms to satisfy the remainder of the preconditions.
		else
		{
			instantiateAndExecuteAction(successor_states, action, preconditions, equalities, uninitialised_precondition_index + 1, new_assigned_variables, type_manager);
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

bool State::operator==(const State& state) const
{
	if (state.facts_.size() != facts_.size()) return false;
	
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end(); ci++)
	{
		const GroundedAtom* fact = *ci;
		if (fact->getAtom().getPredicate().isStatic()) continue;
		bool found_matching = false;
		for (std::vector<const GroundedAtom*>::const_iterator ci = state.facts_.begin(); ci != state.facts_.end(); ci++)
		{
			if ((*ci)->getAtom().getPredicate().isStatic()) continue;
			if (**ci == *fact)
			{
				found_matching = true;
				break;
			}
		}
		
		if (!found_matching) return false;
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
	os << " ***** END STATE ***** " << std::endl;
	return os;
}

bool CompareStates::operator()(const State* lhs, const State* rhs)
{
	 return lhs->getHeuristic() > rhs->getHeuristic();
}

ForwardChainingPlanner::ForwardChainingPlanner(const ActionManager& action_manager, const TypeManager& type_manager)
	: action_manager_(&action_manager), type_manager_(&type_manager)
{
	
}

ForwardChainingPlanner::~ForwardChainingPlanner()
{
	
}

void ForwardChainingPlanner::findPlan(std::vector<const GroundedAction*>& plan, REACHABILITY::DTGReachability& analyst, const std::vector<const SAS_Plus::BoundedAtom*>& initial_fact, const std::vector<const SAS_Plus::BoundedAtom*>& goal_facts, const Bindings& bindings, bool ground)
{
	std::vector<const GroundedAtom*> grounded_initial_facts;
	for (std::vector<const SAS_Plus::BoundedAtom*>::const_iterator ci = initial_fact.begin(); ci != initial_fact.end(); ci++)
	{
		grounded_initial_facts.push_back(new GroundedAtom(**ci, bindings));
	}
	
	std::vector<const GroundedAtom*> grounded_goal_facts;
	for (std::vector<const SAS_Plus::BoundedAtom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ci++)
	{
		grounded_goal_facts.push_back(new GroundedAtom(**ci, bindings));
	}
	
	std::vector<const State*> processed_states;
	
	State* initial_state = new State(grounded_initial_facts);
	initial_state->setDistanceToGoal(std::numeric_limits<unsigned int>::max());
	
	std::priority_queue<const State*, std::vector<const State*>, CompareStates> queue;
	queue.push(initial_state);
	
	unsigned int states_visited = 0;
	unsigned int successors_generated = 0;
	
	unsigned int best_heuristic_estimate = std::numeric_limits<unsigned int>::max();
	
	while (!queue.empty())
	{
		const State* state = queue.top();
		queue.pop();
		
		if (best_heuristic_estimate > state->getHeuristic())
		{
			best_heuristic_estimate = state->getHeuristic();
			std::cerr << "\t" << best_heuristic_estimate << std::endl;
		}
		
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
			delete state;
			continue;
		}
		
		++states_visited;
		processed_states.push_back(state);
		
		if (states_visited % 1000 == 0) std::cerr << "M";
		else if (states_visited % 100 == 0) std::cerr << ".";
		
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
			std::cerr << "States visited: " << states_visited << std::endl;
			std::cerr << "Generated successors: " << successors_generated << std::endl;
			
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
			
			return;
		}
		
		std::vector<State*> successor_states;
		state->getSuccessors(successor_states, *action_manager_, *type_manager_);
		
		for (std::vector<State*>::const_iterator ci = successor_states.begin(); ci != successor_states.end(); ci++)
		{
			State* successor_state = *ci;
			++successors_generated;
			
			analyst.getEquivalentObjectGroupManager().reset();
			
			std::vector<REACHABILITY::ReachableFact*> reachable_facts;
			for (std::vector<const GroundedAtom*>::const_iterator ci = successor_state->getFacts().begin(); ci != successor_state->getFacts().end(); ci++)
			{
				const GroundedAtom* grounded_atom = *ci;
				REACHABILITY::EquivalentObjectGroup** variables = new REACHABILITY::EquivalentObjectGroup*[grounded_atom->getAtom().getArity()];
				for (unsigned int i = 0; i < grounded_atom->getAtom().getArity(); i++)
				{
					variables[i] = &analyst.getEquivalentObjectGroupManager().getEquivalentObject(grounded_atom->getObject(i)).getEquivalentObjectGroup();
				}
				
				reachable_facts.push_back(new REACHABILITY::ReachableFact(grounded_atom->getAtom().getPredicate(), grounded_atom->getAtom().isNegative(), variables));
			}

#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << " *** CALCULATE THE HEURISTIC FOR *** " << std::endl;
			for (std::vector<REACHABILITY::ReachableFact*>::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
			{
				std::cout << **ci << std::endl;
			}
#endif
			
			unsigned int heuristic_value = analyst.getHeuristic(reachable_facts, goal_facts, bindings, ground);
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Heuristic value: " << heuristic_value << std::endl;
#endif
			if (heuristic_value == std::numeric_limits<unsigned int>::max())
			{
				continue;
			}
/*
			for (std::vector<REACHABILITY::ReachableFact*>::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
			{
				delete *ci;
			}
*/
			successor_state->setDistanceToGoal(heuristic_value);
			
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Sucessor state: (" << heuristic_value << ")" << std::endl;
			std::cout << *successor_state << std::endl;
#endif
			queue.push(successor_state);
		}
//		delete state;
	}
	std::cerr << "No plan could be found!" << std::endl;
}

};
