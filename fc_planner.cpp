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
#include "coloured_graph.h"

//#define FC_PLANNER_SAFE_MEMORY

namespace MyPOP {

StateHeuristicListener::StateHeuristicListener(std::vector<State*>& found_states, const State& current_state, HEURISTICS::HeuristicInterface& heuristic, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager, bool find_helpful_actions, bool allow_new_goals_to_be_added)
	: found_states_(&found_states), current_state_(&current_state), heuristic_(&heuristic), initial_facts_(&initial_facts), goal_facts_(&goal_facts), term_manager_(&term_manager), find_helpful_actions_(find_helpful_actions), allow_new_goals_to_be_added_(allow_new_goals_to_be_added), found_better_state_(false)
{
	
}

StateHeuristicListener::~StateHeuristicListener()
{

}
	
void StateHeuristicListener::addNewState(State& state)
{
	//heuristic_->setHeuristicForState(state, *goal_facts_, *term_manager_, find_helpful_actions_, allow_new_goals_to_be_added_);
	heuristic_->setHeuristicForState(state, *initial_facts_, *goal_facts_, *term_manager_, false, allow_new_goals_to_be_added_);
/*	if (find_helpful_actions_ && state.getHeuristic() < current_state_->getHeuristic())
	{
		found_better_state_ = true;
		for (std::vector<State*>::const_iterator ci = found_states_->begin(); ci != found_states_->end(); ++ci)
		{
			delete *ci;
		}
		found_states_->clear();
	}*/
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

StateStoreListener::~StateStoreListener()
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

void GroundedAction::removeInstantiatedGroundedActions(const State& state)
{
	std::vector<const GroundedAction*> not_remove_list;
	const State* parent = &state;
	while (parent != NULL)
	{
		not_remove_list.push_back(parent->getAchievingAction());
		parent = parent->getParent();
	}
	
	removeInstantiatedGroundedActions(not_remove_list.begin(), not_remove_list.end());
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

void GroundedAction::applyTo(std::vector<const GroundedAtom*>& facts) const
{
/*
	std::cout << "Apply: " << *this << std::endl;
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts.begin(); ci != facts.end(); ++ci)
	{
		std::cout << "* " << **ci << std::endl;
	}
*/
	std::vector<const GroundedAtom*> to_add;
	for (unsigned int effect_index = 0; effect_index < action_->getEffects().size(); ++effect_index)
	{
		const Atom* effect = action_->getEffects()[effect_index];
		const Object** effect_variables = new const Object*[effect->getArity()];
		for (unsigned int term_index = 0; term_index < effect->getArity(); term_index++)
		{
			unsigned int variable_index = action_->getActionVariable(effect_index, term_index);
			effect_variables[term_index] = variables_[variable_index];
		}
		
		const GroundedAtom& grounded_effect = GroundedAtom::getGroundedAtom(effect->getPredicate(), effect_variables);
		if (effect->isNegative())
		{
//			std::cout << "Remove: " << grounded_effect << std::endl;
			// Normalise we assume that effect can only delete facts which are mentioned in the preconditions. But some domains
			// like Satellite do not conform to this assumption.
			std::vector<const GroundedAtom*>::iterator ci = std::find(facts.begin(), facts.end(), &grounded_effect);
			if (ci != facts.end())
			{
				facts.erase(ci);
			}
		}
		else
		{
//			std::cout << "Add: " << grounded_effect << std::endl;
			to_add.push_back(&grounded_effect);
		}
	}
	
	facts.insert(facts.end(), to_add.begin(), to_add.end());
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

void GroundedAtom::generateGroundedAtoms(std::vector<const GroundedAtom*>& grounded_objects, const PredicateManager& predicate_manager, const TermManager& term_manager)
{
	for (std::vector<Predicate*>::const_iterator ci = predicate_manager.getManagableObjects().begin(); ci != predicate_manager.getManagableObjects().end(); ++ci)
	{
		const Predicate* predicate = *ci;
		
		unsigned int counter[predicate->getArity()];
		memset(&counter[0], 0, sizeof(unsigned int) * predicate->getArity());
		unsigned int max_counter[predicate->getArity()];
		
		for (unsigned int i = 0; i < predicate->getArity(); ++i)
		{
			std::vector<const Object*> objects;
			term_manager.getTypeManager().getObjectsOfType(objects, *predicate->getTypes()[i]);
			max_counter[i] = objects.size();
		}
		
		bool done = false;
		while (!done)
		{
			done = true;
			const Object** objects = new const Object*[predicate->getArity()];
			for (unsigned int i = 0; i < predicate->getArity(); ++i)
			{
				std::vector<const Object*> objects_of_type;
				term_manager.getTypeManager().getObjectsOfType(objects_of_type, *predicate->getTypes()[i]);
				objects[i] = objects_of_type[counter[i]];
			}
			
			const GroundedAtom& grounded_atom = getGroundedAtom(*predicate, objects);
			//std::cout << grounded_atom << std::endl;
			grounded_objects.push_back(&grounded_atom);
			
			// Update the counters.
			for (unsigned int i = 0; i < predicate->getArity(); ++i)
			{
				if (counter[i] + 1 == max_counter[i])
				{
					counter[i] = 0;
				}
				else
				{
					done = false;
					counter[i] = counter[i] + 1;
					break;
				}
			}
		}
	}
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

/*
State::State(const std::vector<const GroundedAtom*>& facts, bool created_by_helpful_action)
	: parent_(NULL), achieving_action_(NULL), facts_(facts), distance_to_goal_(0), distance_from_start_(0), created_by_helpful_action_(created_by_helpful_action)
{
	assert (facts_.size() == facts.size());
	std::sort(facts_.begin(), facts_.end());
	//checkSanity();
}
*/

State::State(bool created_by_helpful_action)
	: parent_(NULL), achieving_action_(NULL), distance_to_goal_(0), distance_from_start_(0), created_by_helpful_action_(created_by_helpful_action)
{
	
}

State::State(const State& rhs, const GroundedAction& grounded_action, bool created_by_helpful_action)
	: parent_(&rhs), achieving_action_(&grounded_action)/*, facts_(rhs.facts_)*/, distance_to_goal_(rhs.distance_to_goal_), distance_from_start_(rhs.distance_from_start_ + 1), created_by_helpful_action_(created_by_helpful_action)
{
	//achievers_.insert(achievers_.end(), rhs.achievers_.begin(), rhs.achievers_.end());
	//achievers_.push_back(&grounded_action);
	//	std::sort(facts_.begin(), facts_.end());
	//checkSanity();
}

/*
void State::checkSanity() const
{
	for (unsigned int i = 0; i < facts_.size(); ++i)
	{
		for (unsigned int j = 0; j < facts_.size(); ++j)
		{
			if (i == j)
			{
				continue;
			}
			
			if (facts_[i] == facts_[j])
			{
				assert (false);
				std::cerr << "£";
			}
		}
	}
}
*/


State::~State()
{
/*
	for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		const std::vector<HEURISTICS::VariableDomain*>* variable_domains = (*ci).second;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_domains->begin(); ci != variable_domains->end(); ++ci)
		{
			delete *ci;
		}
		delete variable_domains;
	}
*/
/*
	for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		delete *ci;
	}
*/
}

//bool State::areSymmetrical(const State& state, REACHABILITY::EquivalentObjectGroupManager& eog_manager, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager) const
bool State::areSymmetrical(const State& state, const HEURISTICS::HeuristicInterface& heuristic, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager) const
{
	std::multimap<const Object*, const Object*> lhs_symmetrical_groups;
	std::multimap<const Object*, const Object*> rhs_symmetrical_groups;
	
//	std::cout << "Are symmetrical?" << std::endl;
//	std::cout << *this << std::endl;
//	std::cout << " *** " << std::endl;
//	std::cout << state << std::endl;
	
	heuristic.getFunctionalSymmetricSets(lhs_symmetrical_groups, *this, initial_facts, goal_facts, term_manager);
	heuristic.getFunctionalSymmetricSets(rhs_symmetrical_groups, state, initial_facts, goal_facts, term_manager);
//	getSymmetricalObjects(lhs_reachable_facts, eog_manager, goal_facts, term_manager, lhs_symmetrical_groups);
//	state.getSymmetricalObjects(rhs_reachable_facts, eog_manager, goal_facts, term_manager, rhs_symmetrical_groups);
	
	ColouredGraph lhs_cg(lhs_symmetrical_groups);
	ColouredGraph rhs_cg(rhs_symmetrical_groups);
	
	std::vector<const GroundedAtom*> state_facts;
	getFacts(initial_facts, state_facts);
	
	//for (std::vector<const GroundedAtom*>::const_iterator ci = getFacts().begin(); ci != getFacts().end(); ++ci)
	for (std::vector<const GroundedAtom*>::const_iterator ci = state_facts.begin(); ci != state_facts.end(); ++ci)
	{
		const GroundedAtom* fact = *ci;
		
		std::vector<const Object*> objects;
		for (unsigned int i = 0; i < fact->getPredicate().getArity(); ++i)
		{
			objects.push_back(&fact->getObject(i));
		}
		
		for (unsigned int i = 0; i < fact->getPredicate().getArity(); ++i)
		{
			ColouredGraphNodePredicates& cgnp = lhs_cg.createPredicateNode(fact->getPredicate(), i, objects);
			
			ColouredGraphNodeObjects* node = lhs_cg.getNode(*objects[i]);
			assert (node != NULL);
			node->addEdge(cgnp);
		}
	}
	
	std::vector<const GroundedAtom*> other_state_facts;
	state.getFacts(initial_facts, other_state_facts);
	
	//for (std::vector<const GroundedAtom*>::const_iterator ci = state.getFacts().begin(); ci != state.getFacts().end(); ++ci)
	for (std::vector<const GroundedAtom*>::const_iterator ci = other_state_facts.begin(); ci != other_state_facts.end(); ++ci)
	{
		const GroundedAtom* fact = *ci;
		
		std::vector<const Object*> objects;
		for (unsigned int i = 0; i < fact->getPredicate().getArity(); ++i)
		{
			objects.push_back(&fact->getObject(i));
		}
		
		for (unsigned int i = 0; i < fact->getPredicate().getArity(); ++i)
		{
			ColouredGraphNodePredicates& cgnp = rhs_cg.createPredicateNode(fact->getPredicate(), i, objects);
			
			ColouredGraphNodeObjects* node = rhs_cg.getNode(*objects[i]);
			assert (node != NULL);
			node->addEdge(cgnp);
		}
	}
	
	for (std::vector<const GroundedAtom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ++ci)
	{
		const GroundedAtom* grounded_atom = *ci;
		ColouredGraphNodeGoal& cgng_lhs = lhs_cg.createGoalNode(**ci);
		ColouredGraphNodeGoal& cgng_rhs = rhs_cg.createGoalNode(**ci);
		
		for (unsigned int i = 0; i < grounded_atom->getPredicate().getArity(); ++i)
		{
			ColouredGraphNodeObjects* lhs_node = lhs_cg.getNode(grounded_atom->getObject(i));
			assert (lhs_node != NULL);
			lhs_node->addEdge(cgng_lhs);
			
			ColouredGraphNodeObjects* rhs_node = rhs_cg.getNode(grounded_atom->getObject(i));
			assert (rhs_node != NULL);
			rhs_node->addEdge(cgng_rhs);
		}
	}
	
	if (lhs_cg.isSymmetricalTo(rhs_cg))
	{
		return true;
	}
	return false;
}
/*
void State::getSymmetricalObjects(std::vector<REACHABILITY::ReachableFact*>& state_reachable_facts, REACHABILITY::EquivalentObjectGroupManager& eog_manager, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager, std::multimap<const Object*, const Object*>& symmetrical_groups) const
{
	eog_manager.reset();
	//std::vector<REACHABILITY::ReachableFact*> reachable_facts;
	for (std::vector<const GroundedAtom*>::const_iterator ci = getFacts().begin(); ci != getFacts().end(); ci++)
	{
		const GroundedAtom* grounded_atom = *ci;
		
		state_reachable_facts.push_back(&REACHABILITY::ReachableFact::createReachableFact(*grounded_atom, eog_manager));
	}

#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << " *** CALCULATE THE HEURISTIC FOR *** " << std::endl;
	for (std::vector<REACHABILITY::ReachableFact*>::const_iterator ci = state_reachable_facts.begin(); ci != state_reachable_facts.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
#endif

	eog_manager.initialise(state_reachable_facts);
	eog_manager.updateEquivalences(0);

#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "Found equivalence relationships: " << std::endl;
	std::cout << *eog_manager << std::endl;
#endif
	
	// Find which objects are equivalent in the initial state.
	std::map<const Object*, std::vector<const Object*>* > initial_symmetrical_groups;
	std::vector<std::vector<const Object*>* > delete_list;
	for (std::vector<REACHABILITY::EquivalentObjectGroup*>::const_iterator ci = eog_manager.getEquivalentObjectGroups().begin(); ci != eog_manager.getEquivalentObjectGroups().end(); ++ci)
	{
		REACHABILITY::EquivalentObjectGroup* eog = *ci;
		if (!eog->isRootNode())
		{
			continue;
		}
		
		std::vector<const Object*>* equivalent_objects = new std::vector<const Object*>();
		delete_list.push_back(equivalent_objects);
		for (std::vector<REACHABILITY::EquivalentObject*>::const_iterator ci = eog->begin(0); ci != eog->end(0); ++ci)
		{
			REACHABILITY::EquivalentObject* eo = *ci;
			equivalent_objects->push_back(&eo->getObject());
			initial_symmetrical_groups.insert(std::make_pair(&eo->getObject(), equivalent_objects));
		}
	}
	
	// Do the same for the goal.
	std::map<const Object*, std::vector<const Object*>* > goal_symmetrical_groups;
	
	eog_manager.reset();
	//reachable_facts.clear();
	std::vector<REACHABILITY::ReachableFact*> reachable_facts;
	for (std::vector<const GroundedAtom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ci++)
	{
		const GroundedAtom* grounded_atom = *ci;
		reachable_facts.push_back(&REACHABILITY::ReachableFact::createReachableFact(*grounded_atom, eog_manager));
	}

#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << " *** CALCULATE THE HEURISTIC FOR *** " << std::endl;
	for (std::vector<REACHABILITY::ReachableFact*>::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
#endif

	eog_manager.initialise(reachable_facts);
	eog_manager.updateEquivalences(0);

#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "Found equivalence relationships: " << std::endl;
	std::cout << eog_manager << std::endl;
#endif
	
	// Find which objects are equivalent in the initial state.
	for (std::vector<REACHABILITY::EquivalentObjectGroup*>::const_iterator ci = eog_manager.getEquivalentObjectGroups().begin(); ci != eog_manager.getEquivalentObjectGroups().end(); ++ci)
	{
		REACHABILITY::EquivalentObjectGroup* eog = *ci;
		if (!eog->isRootNode())
		{
			continue;
		}
		
		std::vector<const Object*>* equivalent_objects = new std::vector<const Object*>();
		delete_list.push_back(equivalent_objects);
		for (std::vector<REACHABILITY::EquivalentObject*>::const_iterator ci = eog->begin(0); ci != eog->end(0); ++ci)
		{
			REACHABILITY::EquivalentObject* eo = *ci;
			equivalent_objects->push_back(&eo->getObject());
			goal_symmetrical_groups.insert(std::make_pair(&eo->getObject(), equivalent_objects));
		}
	}
	
	/// Split the objects such that any set of equivalent objects from the initial state does not overlap with two
	/// equivalent objects from the goal state.
	for (std::vector<const Object*>::const_iterator ci = term_manager.getAllObjects().begin(); ci != term_manager.getAllObjects().end(); ++ci)
	{
		const Object* object = *ci;
		
		std::vector<const Object*>* init_objects = initial_symmetrical_groups[object];
		std::vector<const Object*>* goal_objects = goal_symmetrical_groups[object];
		
		if (init_objects == NULL || goal_objects == NULL)
		{
			continue;
		}
		
		// Take the intersection.
		for (std::vector<const Object*>::const_iterator init_ci = init_objects->begin(); init_ci != init_objects->end(); ++init_ci)
		{
			const Object* i_object = *init_ci;
			for (std::vector<const Object*>::const_iterator goal_ci = goal_objects->begin(); goal_ci != goal_objects->end(); ++goal_ci)
			{
				const Object* g_object = *goal_ci;
				if (i_object == g_object)
				{
					symmetrical_groups.insert(std::make_pair(object, i_object));
					break;
				}
			}
		}
	}
	
	for (std::vector<std::vector<const Object*> *>::const_iterator ci = delete_list.begin(); ci != delete_list.end(); ++ci)
	{
		delete *ci;
	}
}
*/

//void State::getSuccessors(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const ActionManager& action_manager, const TypeManager& type_manager, bool prune_unhelpful_actions, const std::vector<const State*>& all_states) const
//void State::getSuccessors(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const ActionManager& action_manager, const TypeManager& type_manager, bool prune_unhelpful_actions, const std::vector<const State*>& all_states, const TermManager& term_manager, const std::vector<const GroundedAtom*>& goals, const HEURISTICS::HeuristicInterface& heuristic) const
void State::getSuccessors(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const ActionManager& action_manager, const TypeManager& type_manager, bool prune_unhelpful_actions, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >& helpful_actions) const
{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "Find successors of" << std::endl << *this << std::endl;
#endif
	
	/*
	// Instantiate all the helpful actions and try to find preconditions to match them.
	//if (helpful_actions_.size() > 0 && false)
	if (false)
	{
					
		std::vector<const GroundedAction*> already_tried_actions;
		// TODO: Maybe shuffle? std::shuffle().
		
		
		for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
		{
			const REACHABILITY::AchievingTransition* transition = (*ci).first;
			const std::vector<HEURISTICS::VariableDomain*>* variable_domains = (*ci).second;
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
					//HEURISTICS::VariableDomain* vd = transition->getVariableAssignments()[action_variable_index];
					HEURISTICS::VariableDomain* vd = (*variable_domains)[action_variable_index];
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

				
				//if (all_precondition_satisfied)
				{
					already_tried_actions.push_back(&grounded_action);
					// Create a new state!
					State* new_state = new State(*this, grounded_action, true);
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
//				std::cout << "Copy the old state: " << *new_state << std::endl;
#endif
					listener.addNewState(*new_state);
				}
				
				for (unsigned int action_variable_index = 0; action_variable_index < action.getVariables().size(); ++action_variable_index)
				{
					//if (counter[action_variable_index] + 1 != transition->getVariableAssignments()[action_variable_index]->getVariableDomain().size())
					if (counter[action_variable_index] + 1 != (*variable_domains)[action_variable_index]->getVariableDomain().size())
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
	else*/
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
			
			instantiateAndExecuteAction(listener, symmetrical_groups, *action, preconditions, equalities, 0, assigned_variables, type_manager, prune_unhelpful_actions, initial_facts, helpful_actions);
		}
	}
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
	std::cout << "Found: " << action_manager.getManagableObjects().size() << " successors states for: " << std::endl << *this << std::endl;
#endif
}

bool State::isSuperSetOf(const std::vector<const GroundedAtom*>& initial_facts, const std::vector<const GroundedAtom*>& facts) const
{
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts.begin(); ci != facts.end(); ci++)
	{
		const GroundedAtom* goal_fact = *ci;
		bool is_satisfied = false;
		
		std::vector<const GroundedAtom*> state_facts;
		getFacts(initial_facts, state_facts);
		
		//for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end(); ci++)
		for (std::vector<const GroundedAtom*>::const_iterator ci = state_facts.begin(); ci != state_facts.end(); ++ci)
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

void State::getFacts(const std::vector<const GroundedAtom*>& initial_facts, std::vector<const GroundedAtom*>& facts) const
{
	if (parent_ != NULL)
	{
		parent_->getFacts(initial_facts, facts);
		achieving_action_->applyTo(facts);
	}
	
	// If there is no parent then we are at the initial state.
	else
	{
		facts.insert(facts.end(), initial_facts.begin(), initial_facts.end());
	}
	std::sort(facts.begin(), facts.end());
}

/*
void State::getSymmetricalObjects(std::map<const Object*, std::vector<const Object*>*>& symmetrical_object_mappings, const std::vector<const GroundedAtom*>& goal_facts, REACHABILITY::EquivalentObjectManager& eog_manager) const
{
	std::vector<ReachableFact*> facts;
	
	for (const GroundedAtom* grounded_atom : facts_)
	{
		REACHABILITY::ReachableFact& fact = REACHABILITY::ReachableFact::createReachableFact(*grounded_atom, eog_manager);
		facts.push_back(&fact);
	}
	
	eog_manager.reset();
	eog_manager.initialise(facts);
	eog_manager.updateEquivalences(0);
	
	// Find which objects are equivalent in the initial state.
	for (REACHABILITY::EquivalentObjectGroup* eog : eog_manager.getEquivalentObjectGroups())
	{
		if (!eog->isRootNode())
		{
			continue;
		}
		
		std::vector<const Object*>* equivalent_objects = new std::vector<const Object*>();
		for (std::vector<REACHABILITY::EquivalentObject*>::const_iterator ci = eog->begin(0); ci != eog->end(0); ++ci)
		{
			REACHABILITY::EquivalentObject* eo = *ci;
			equivalent_objects->push_back(&eo->getObject());
			symmetrical_object_mappings.insert(std::make_pair(&eo->getObject(), equivalent_objects));
		}
	}
	
	facts.empty();
	for (const GroundedAtom* grounded_atom : goal_facts)
	{
		REACHABILITY::ReachableFact& fact = REACHABILITY::ReachableFact::createReachableFact(*grounded_atom, eog_manager);
		facts.push_back(&fact);
	}
	
	// Check if the same holds for the goal sstate.
	eog_manager.reset();
	eog_manager.initialise(facts);
	eog_manager.updateEquivalences(0);
	
	for (REACHABILITY::EquivalentObjectGroup* eog : eog_manager.getEquivalentObjectGroups())
	{
		if (!eog->isRootNode())
		{
			continue;
		}
		
		std::vector<const Object*>* equivalent_objects = new std::vector<const Object*>();
		for (std::vector<REACHABILITY::EquivalentObject*>::const_iterator ci = eog->begin(0); ci != eog->end(0); ++ci)
		{
			REACHABILITY::EquivalentObject* eo = *ci;
			equivalent_objects->push_back(&eo->getObject());
			symmetrical_object_mappings.insert(std::make_pair(&eo->getObject(), equivalent_objects));
		}
		
		for (Object* object : equivalent_objects)
		{
			std::map<const Object*, std::vector<const Object*>*>::const_iterator map_ci = symmetrical_object_mappings.find(object);
			
			if (map_ci == symmetrical_object_mappings.end())
			{
				continue;
			}
			
			std::vector<const Object*>* symmetrical_objects = (*map_ci).second;
			std::vector<const Object*>* split_mapping = new std::vector<const Object*>();
			
			// Check if there is a discepancy between the symmetrical objects in the initial state and those in the goal state.
			for (std::vector<const Object*>::reverse_iterator ri = symmetrical_objects->rbegin(); ri != symmetrical_objects->rend(); ++ri)
			{
				// If this object is in equivalent objects, we need to put it in a new group.
				if (std::find(equivalent_objects->begin(), equivalent_objects->end(), object) != equivalent_objects->end())
				{
					split_mapping->push_back(object);
					symmetrical_objects->erase((*ri.base()) - 1);
					symmetrical_object_mappings.insert(std::make_pair(*ri, split_mapping));
				}
			}
		}
	}
}
*/
/*
//void State::setHelpfulActions(const std::vector<std::pair<const Action*, std::vector<const Object*>**> >& helpful_actions)
void State::setHelpfulActions(const std::vector<const REACHABILITY::AchievingTransition*>& helpful_actions)
{
	deleteHelpfulActions();
	helpful_actions_ = helpful_actions;
	
//	std::cerr << *this << std::endl;
}
*/

/*
void State::setHelpfulActions(const std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >& helpful_actions)
{
	deleteHelpfulActions();
	helpful_actions_ = helpful_actions;
	for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >::const_iterator ci = helpful_actions.begin(); ci != helpful_actions.end(); ++ci)
	{
		if ((*ci).first->getAchiever() == NULL)
		{
			std::cerr << "WTF!" << std::endl;
			assert (false);
		}
	}
}
*/

/*
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
*/
void State::instantiateAndExecuteAction(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const Action& action, const std::vector<const Atom*>& preconditions, const std::vector<const Equality*>& equalities, unsigned int uninitialised_precondition_index, const Object** assigned_variables, const TypeManager& type_manager, bool prune_unhelpful_actions, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >& helpful_actions) const
{
	// Find facts in the current state which can unify with the 'uninitialised_precondition_index'th precondition and does not violate the already assigned variables.
	const Atom* precondition = preconditions[uninitialised_precondition_index];
	std::vector<const GroundedAtom*> already_tried_facts;
	
	//std::cout << "Try to apply: " << action << "." << std::endl;
	
	std::vector<const GroundedAtom*> state_facts;
	getFacts(initial_facts, state_facts);
	
	//for (std::vector<const GroundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end() && listener.continueSearching(); ci++)
	for (std::vector<const GroundedAtom*>::const_iterator ci = state_facts.begin(); ci != state_facts.end() && listener.continueSearching(); ++ci)
	{
		const GroundedAtom* grounded_atom = *ci;
		if (grounded_atom->getPredicate().getArity() != precondition->getArity() || grounded_atom->getPredicate().getName() != precondition->getPredicate().getName()) continue;
		
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
			//std::cout << "\tConstraints not satisfied." << std::endl;
			continue;
		}
		
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
		std::cout << "Try to apply: (" << action.getPredicate() << " ";
		for (unsigned int i = 0; i < action.getVariables().size(); ++i)
		{
			if (new_assigned_variables[i] == NULL)
				std::cout << "UNASIGNED ";
			else
				std::cout << new_assigned_variables[i]->getName() << " ";
		}
		std::cout << ")" << std::endl;
#endif
		
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
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
				std::cerr << *fact << " == " << *grounded_atom << std::endl;
#endif
				is_symmetrical = true;
				break;
			}
		}
		
		if (is_symmetrical)
		{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "\tIs symmetrical." << std::endl;
#endif
			continue;
		}
		
		// Found an atom which satisfies all constraints, check if we now have a full assignment!
		if (uninitialised_precondition_index + 1 == preconditions.size())
		{
			already_tried_facts.push_back(grounded_atom);
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Found a successor state!" << std::endl;
#endif

			const Object** grounded_action_variables_templates = new const Object*[action.getVariables().size()];
			memcpy(grounded_action_variables_templates, new_assigned_variables, sizeof(const Object*) * action.getVariables().size());
			
			// Check if all the variables have been assigned. Those which are not assigned are free variables.
			std::vector<const Object**> all_grounded_action_variables;
			createAllGroundedVariables(all_grounded_action_variables, grounded_action_variables_templates, action, type_manager);
			
			delete[] grounded_action_variables_templates;
/*
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "(" << all_grounded_action_variables.size() << ") Helpful actions: " << std::endl;
			for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>*> >::const_iterator ci = helpful_actions.begin(); ci != helpful_actions.end(); ++ci)
			{
				const REACHABILITY::AchievingTransition* action = (*ci).first;
				const std::vector<HEURISTICS::VariableDomain*>* variable = (*ci).second;
				
				std::cout << *action << std::endl;
				
				for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable->begin(); ci != variable->end(); ++ci)
				{
					std::cout << **ci << std::endl;
				}
			}
#endif
*/
			for (std::vector<const Object**>::const_iterator ci = all_grounded_action_variables.begin(); ci != all_grounded_action_variables.end(); ci++)
			{
				const Object** grounded_action_variables = *ci;

				// Check if this is a helpful action or not.
				bool is_helpful = helpful_actions.empty();
				//for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
				for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >::const_iterator ci = helpful_actions.begin(); ci != helpful_actions.end(); ++ci)
				{
					const REACHABILITY::AchievingTransition* helpful_action = (*ci).first;
					const std::vector<HEURISTICS::VariableDomain*>* variable_domains = (*ci).second;
					//const REACHABILITY::AchievingTransition* helpful_action = *ci;
//					std::cout << "Helpful action: " << *helpful_action << std::endl;
					
					if (action.getPredicate() != helpful_action->getAchiever()->getTransition().getAction().getPredicate() ||
					    action.getVariables().size() != variable_domains->size())
					{
						continue;
					}
					
					bool all_variable_domains_match = true;
					for (unsigned int i = 0; i < action.getVariables().size(); ++i)
					{
						//std::vector<const Object*>* helpful_variable_domain = variable_domains[i];
						//const HEURISTICS::VariableDomain& helpful_variable_domain = helpful_action->getVariableAssignments()[i]->getVariableDomain();
						const HEURISTICS::VariableDomain& helpful_variable_domain = (*variable_domains)[i]->getVariableDomain();
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
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
					std::cout << "\tUnhelpful action." << std::endl;
					//std::cout << "Unhelpful: " << dummy_grounded_action << std::endl;
#endif
					continue;
				}
				//std::cout << "Helpful: " << dummy_grounded_action << std::endl;

				const GroundedAction& grounded_action = GroundedAction::getGroundedAction(action, grounded_action_variables);
				
				// Apply the action to the new state!
				State* new_state = new State(*this, grounded_action, is_helpful);
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
				std::cout << "Successor state: " << *new_state << std::endl;
#endif
				/*
				// Check if this state is symmetrical to any state we are already considering.
				
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
				*/
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
			instantiateAndExecuteAction(listener, symmetrical_groups, action, preconditions, equalities, uninitialised_precondition_index + 1, new_assigned_variables, type_manager, prune_unhelpful_actions, initial_facts, helpful_actions);
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

/*
void State::deleteHelpfulActions()
{
	for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		delete (*ci).first;
		const std::vector<HEURISTICS::VariableDomain*>* variable_domain = (*ci).second;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ++ci)
		{
			delete *ci;
		}
		delete variable_domain;
	}
	
	helpful_actions_.clear();
}
*/

bool State::isEqualTo(const State& other, const std::vector<const GroundedAtom*>& initial_facts) const
{
	std::vector<const GroundedAtom*> state_facts, other_state_facts;
	getFacts(initial_facts, state_facts);
	other.getFacts(initial_facts, other_state_facts);
	
	if (state_facts.size() != other_state_facts.size()) return false;
	
	for (unsigned int i = 0; i < other_state_facts.size(); ++i)
	{
		if (other_state_facts[i] != state_facts[i])
		{
			return false;
		}
	}
	return true;
}

bool State::operator==(const State& state) const
{
	assert (false);
	
	/*
	if (state.facts_.size() != facts_.size()) return false;
	
	for (unsigned int i = 0; i < state.facts_.size(); ++i)
	{
		if (state.facts_[i] != facts_[i])
		{
			return false;
		}
	}
	return true;
	*/
	return false;
}

std::ostream& operator<<(std::ostream& os, const State& state)
{
	os << " ***** BEGIN STATE h=(" << state.getHeuristic() << ")";
	/*os << "Achieving actions: ";
	for (std::vector<const GroundedAction*>::const_iterator ci = state.getAchievers().begin(); ci != state.getAchievers().end(); ci++)
	{
		os << **ci << " - ";
	}
	os << " ***** " << std::endl;*/
/*	
	for (std::vector<const GroundedAtom*>::const_iterator ci = state.facts_.begin(); ci != state.facts_.end(); ci++)
	{
		if ((*ci)->getPredicate().isStatic()) continue;
		os << "* " << **ci << std::endl;
	}
	os << " === Helpful actions === (" << state.getHelpfulActions().size() << ")" << std::endl;
	for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >::const_iterator ci = state.helpful_actions_.begin(); ci != state.helpful_actions_.end(); ++ci)
	{
		os << (*ci).first->getAchiever()->getTransition().getAction().getPredicate();
		const std::vector<HEURISTICS::VariableDomain*>* variable_domain = (*ci).second;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ++ci)
		{
			os << **ci << ", ";
		}
	}
*/
/*
	for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = state.helpful_actions_.begin(); ci != state.helpful_actions_.end(); ++ci)
	{
		os << **ci << std::endl;
	}
*/
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
		//return lhs->getAchievers().size() > rhs->getAchievers().size();
		return true;
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
		
		grounded_initial_facts.push_back(&GroundedAtom::getGroundedAtom(initial_fact->getPredicate(), variables));
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
		
		grounded_goal_facts.push_back(&GroundedAtom::getGroundedAtom(goal_fact->getPredicate(), variables));
	}
	
	// All the grounded atoms that should never be removed.
	std::vector<const GroundedAtom*> grounded_atoms_not_to_be_removed;
	grounded_atoms_not_to_be_removed.insert(grounded_atoms_not_to_be_removed.end(), grounded_initial_facts.begin(), grounded_initial_facts.end());
	grounded_atoms_not_to_be_removed.insert(grounded_atoms_not_to_be_removed.end(), grounded_goal_facts.begin(), grounded_goal_facts.end());
	
	std::vector<const State*> processed_states;
	//State* initial_state = new State(grounded_initial_facts, true);
	State* initial_state = new State(true);
	
	// Test.
	//std::map<const Object*, std::vector<const Object*>*> symmetrical_object_mappings;
	//initial_state->getSymmetricalObjects(symmetrical_object_mappings, grounded_goal_facts, eog_manager);
	
	
	heuristic_->setHeuristicForState(*initial_state, grounded_initial_facts, grounded_goal_facts, term_manager, true, allow_new_goals_to_be_added);
	GroundedAtom::removeInstantiatedGroundedAtom(grounded_atoms_not_to_be_removed);
	
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
		
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
		std::cout << "Current state: " << *state << std::endl;
		
		std::vector<const GroundedAtom*> grounded_atom;
		state->getFacts(grounded_initial_facts, grounded_atom);
		
		for (std::vector<const GroundedAtom*>::const_iterator ci = grounded_atom.begin(); ci != grounded_atom.end(); ci++)
		{
			if ((*ci)->getPredicate().isStatic()) continue;
			std::cout << "* " << **ci << std::endl;
		}
#endif
		
//		State* state = queue.top();
//		queue.pop();
		
		bool already_processed = false;
		for (std::vector<const State*>::const_iterator ci = processed_states.begin(); ci != processed_states.end(); ci++)
		{
			//if (*state == **ci)
			if (state->isEqualTo(**ci, grounded_initial_facts))
			{
				already_processed = true;
				break;
			}
#ifdef FC_PLANNER_SAFE_MEMORY
			GroundedAtom::removeInstantiatedGroundedAtom(grounded_atoms_not_to_be_removed);
#endif
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

#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
		if (state->getHeuristic() == std::numeric_limits<unsigned int>::max())
		{
			std::cerr << "Deadend?" << std::endl;
			std::cerr << *state << std::endl;
			
			std::vector<const GroundedAtom*> grounded_atom;
			state->getFacts(grounded_initial_facts, grounded_atom);
			
			for (std::vector<const GroundedAtom*>::const_iterator ci = grounded_atom.begin(); ci != grounded_atom.end(); ci++)
			{
				if ((*ci)->getPredicate().isStatic()) continue;
				std::cout << "* " << **ci << std::endl;
			}
		}
#endif

		if (best_heuristic_estimate > state->getHeuristic())
		{
			states_seen_without_improvement = 0;
			current_power = min_power;
			
			//if (last_best_state_seen != state)
			//{
			//	last_best_state_seen->deleteHelpfulActions();
			//}
			last_best_state_seen = state;
			best_heuristic_estimate = state->getHeuristic();
			std::cerr << "\t" << best_heuristic_estimate << " state = " << processed_states.size() << "; Grounded Actions = " << GroundedAction::numberOfGroundedActions() << "; Grounded atoms: " << GroundedAtom::numberOfGroundedAtoms() << std::endl;
//			std::cerr << *state << std::endl;
//			std::cout << "Best new heuristic, empty the queue!" << std::endl;
			/*
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
			
			for (std::vector<const State*>::reverse_iterator ri = processed_states.rbegin(); ri != processed_states.rend(); ri++)
			{
				bool is_parent = false;
				const State* parent = state->getParent();
				while (parent != NULL)
				{
					if (parent == *ri)
					{
						is_parent = true;
						break;
					}
					parent = parent->getParent();
				}
				
				if (!is_parent)
				{
					delete *ri;
					processed_states.erase(ri.base() - 1);
				}
			}
//			processed_states.clear();
			
			// Delete all grounded actions which are not stored in the states.
#ifdef FC_PLANNER_SAFE_MEMORY
			GroundedAction::removeInstantiatedGroundedActions(*state);
#endif
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
					//delete *ci;
				}
			}
			processed_states.clear();
			
			for (std::vector<State*>::const_iterator ci = current_states_to_explore.begin(); ci != current_states_to_explore.end(); ++ci)
			{
				delete *ci;
			}
			current_states_to_explore.clear();
			
			// Delete all grounded actions which are not stored in the states.
			//GroundedAction::removeInstantiatedGroundedActions(last_best_state_seen->getAchievers().begin(), last_best_state_seen->getAchievers().end());
//			GroundedAction::removeInstantiatedGroundedActions(*last_best_state_seen);
//			delete state;
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
		//else std::cerr << "@";
		
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
		std::cout << "Work on: " << std::endl;
		std::cout << *state << std::endl;
#endif
		
		if (state->isSuperSetOf(grounded_initial_facts, grounded_goal_facts))
		{
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Found a goal state:" << std::endl;
			std::cout << *state << std::endl;
#endif
//			std::cerr << "States visited: " << states_visited << std::endl;
//			std::cerr << "Generated successors: " << successors_generated << std::endl;
			
			//plan.insert(plan.end(), state->getAchievers().begin(), state->getAchievers().end());
			
			const State* parent = state;
			while (parent != NULL && parent->getAchievingAction() != NULL)
			{
				plan.insert(plan.begin(), parent->getAchievingAction());
				parent = parent->getParent();
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
			
			for (std::vector<State*>::const_iterator ci = current_states_to_explore.begin(); ci != current_states_to_explore.end(); ++ci)
			{
				delete *ci;
			}
			current_states_to_explore.clear();
			return std::make_pair(states_visited, plan.size());
		}
		
		std::vector<State*> successor_states;
		
		NewStateReachedListener* new_state_reached_listener = NULL;
		//if (prune_unhelpful_actions)
		{
			new_state_reached_listener = new StateHeuristicListener(successor_states, *state,  *heuristic_, grounded_initial_facts, grounded_goal_facts, term_manager, prune_unhelpful_actions, allow_new_goals_to_be_added);
		}
		//else
		//{
		//	new_state_reached_listener = new StateStoreListener(successor_states);
		//}
		
		// Before finding the successors, search for helpful actions (if this option is enabled).
		if (prune_unhelpful_actions)
		{
			heuristic_->setHeuristicForState(*state, grounded_initial_facts, grounded_goal_facts, term_manager, true, allow_new_goals_to_be_added);
#ifdef FC_PLANNER_SAFE_MEMORY
			GroundedAtom::removeInstantiatedGroundedAtom(grounded_atoms_not_to_be_removed);
#endif
		}
		else
		{
			heuristic_->deleteHelpfulActions();
		}
		
		std::multimap<const Object*, const Object*> symmetrical_groups;
		heuristic_->getFunctionalSymmetricSets(symmetrical_groups, *state, grounded_initial_facts, grounded_goal_facts, term_manager);
		GroundedAtom::removeInstantiatedGroundedAtom(grounded_atoms_not_to_be_removed);
	
		std::vector<const State*> all_states;
		all_states.insert(all_states.end(), current_states_to_explore.begin(), current_states_to_explore.end());
		
		//std::priority_queue<State*, std::vector<State*>, CompareStates> queue;
		
		State* const* first_state = &queue.top();
		for (unsigned int i = 0; i < queue.size(); ++i)
		{
			const State* state = first_state[i];
			all_states.push_back(state);
		}
		/*
		for (std::vector<const State*>::const_iterator ci = all_states.begin(); ci != all_states.end(); ++ci)
		{
			std::cout << **ci << std::endl;
		}
		*/
		
		state->getSuccessors(*new_state_reached_listener, symmetrical_groups, *action_manager_, *type_manager_, prune_unhelpful_actions, grounded_initial_facts, heuristic_->getHelpfulActions());
#ifdef FC_PLANNER_SAFE_MEMORY
		GroundedAtom::removeInstantiatedGroundedAtom(grounded_atoms_not_to_be_removed);
#endif
		delete new_state_reached_listener;
		
		
		//TODO: REMOVE.
		//std::cout << "S(" << successor_states.size() << "){" << queue.size() << "}";
		
		for (std::vector<State*>::const_iterator ci = successor_states.begin(); ci != successor_states.end(); ci++)
		{
			State* successor_state = *ci;
			++successors_generated;
			if (prune_unhelpful_actions && !successor_state->isCreatedByHelpfulAction())
			{
				assert (false);
				delete successor_state;
//				std::cerr << "*";
				continue;
			}
			
			/*
			if (successor_state->getHeuristic() == std::numeric_limits<unsigned int>::max())
			{
				delete successor_state;
				continue;
			}
			*/
			
			/// Prune the states that are symmetrical with other states we are already exploring.
			/*
			// Check if there exists a state that is symmetrical with this one. If that is the case then ignore this state.
			bool found_symmetrical_state = false;
			for (std::vector<const State*>::const_iterator ci = all_states.begin(); ci != all_states.end(); ++ci)
			{
				if ((*ci)->areSymmetrical(*successor_state, *heuristic_, grounded_goal_facts, term_manager))
				{
//					std::cout << " *** NEW STATE *** " << std::endl;
//					std::cout << *successor_state << std::endl;
//					std::cout << " * IS EQUIVALENT TO * " << std::endl;
//					std::cout << **ci << std::endl;
					std::cerr << "!";
					found_symmetrical_state = true;
					break;
				}
			}
			if (found_symmetrical_state)
			{
				delete successor_state;
				continue;
			}
			all_states.push_back(successor_state);
			*/
			//heuristic_->setHeuristicForState(*successor_state, grounded_goal_facts, term_manager, false, allow_new_goals_to_be_added);
			
#ifdef MYPOP_FORWARD_CHAIN_PLANNER_COMMENTS
			std::cout << "Sucessor state:" << std::endl;
			std::cout << *successor_state << std::endl;
			
			std::vector<const GroundedAtom*> grounded_atom;
			successor_state->getFacts(grounded_initial_facts, grounded_atom);
			
			for (std::vector<const GroundedAtom*>::const_iterator ci = grounded_atom.begin(); ci != grounded_atom.end(); ci++)
			{
				if ((*ci)->getPredicate().isStatic()) continue;
				std::cout << "* " << **ci << std::endl;
			}
#endif
			
//			std::cout << " ============== Helpful actions ============== " << std::endl;
//			for (std::vector<const REACHABILITY::AchievingTransition*>::const_iterator ci = analyst.getHelpfulActions().begin(); ci != analyst.getHelpfulActions().end(); ++ci)
//			{
//				std::cout << **ci << std::endl;
//			}
//#endif
			queue.push(successor_state);
/*
			if (prune_unhelpful_actions && successor_state->getHeuristic() < state->getHeuristic())
			{
				for (std::vector<State*>::const_iterator other_ci = ci + 1; other_ci != successor_states.end(); other_ci++)
				{
					State* other_successor_state = *other_ci;
					delete other_successor_state;
				}
				break;
			}
*/
		}
		
		//state->deleteHelpfulActions();
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
