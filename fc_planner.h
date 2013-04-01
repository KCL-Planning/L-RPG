#ifndef MYPOP_FORWARD_CHAINING_PLANNER
#define MYPOP_FORWARD_CHAINING_PLANNER

#include <vector>
#include <ostream>

#include "heuristics/heuristic_interface.h"

namespace MyPOP
{
class Action;
class ActionManager;
class Atom;
class Equality;
class PredicateManager;
class TypeManager;
class Object;
class Predicate;

/*namespace SAS_Plus
{
class BoundedAtom;
};*/

namespace REACHABILITY
{
class AchievingTransition;
class DTGReachability;
class ResolvedTransition;
class ResolvedBoundedAtom;
};

/**
 * Listener for whenever a new state has been reached, this class is an aid for the instantiateAndExecuteAction method. Sometimes
 * we just want to add the state to a list, other times we want to calculate its heuristic and prune the search for new states.
 */
class NewStateReachedListener
{
public:
	
	
	/**
	 * Every time the method instantiateAndExecuteAction create a new state, this method is called.
	 * @param state The new state that has been reached.
	 */
	virtual void addNewState(State& state) = 0;
	
	/**
	 * This function is called by instantiateAndExecuteAction to determine whether the algorithm should continue to search for more 
	 * states.
	 */
	virtual bool continueSearching() = 0;
};

/**
 * For each new state we calculate its heuristic and we stop finding more states if we found a state better than the current state.
 */
class StateHeuristicListener : public NewStateReachedListener
{
public:
	StateHeuristicListener(std::vector<State*>& found_states, const State& current_state, HEURISTICS::HeuristicInterface& heuristic, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager, bool find_helpful_actions, bool allow_new_goals_to_be_added);
	
	void addNewState(State& state);
	
	bool continueSearching();
private:
	std::vector<State*>* found_states_;
	const State* current_state_;
	HEURISTICS::HeuristicInterface* heuristic_;
	const std::vector<const GroundedAtom*>* goal_facts_;
	const TermManager* term_manager_;
	bool find_helpful_actions_, allow_new_goals_to_be_added_, found_better_state_;
};

/**
 * Each new state is added to the given list.
 */
class StateStoreListener : public NewStateReachedListener
{
public:
	StateStoreListener(std::vector<State*>& found_states);
	
	void addNewState(State& state);
	
	bool continueSearching();
	
private:
	std::vector<State*>* found_states_;
};

class GroundedAction
{
public:
	static const GroundedAction& getGroundedAction(const Action& action, const Object** variables);
	static void removeInstantiatedGroundedActions();
	static void removeInstantiatedGroundedActions(std::vector<const GroundedAction*>::const_iterator begin, std::vector<const GroundedAction*>::const_iterator end);
	static unsigned int numberOfGroundedActions();
	
	const Action& getAction() const { return *action_; }
	
	const Object& getVariablesAssignment(unsigned int index) const { return *variables_[index]; }
private:
	
	static std::vector<const GroundedAction*> instantiated_grounded_actions_;
	GroundedAction(const Action& action, const Object** variables);
	
	~GroundedAction();
	
	const Action* action_;
	const Object** variables_;
	
	friend std::ostream& operator<<(std::ostream& os, const GroundedAction& grounded_action);
};

std::ostream& operator<<(std::ostream& os, const GroundedAction& grounded_action);

/**
 * Like BoundedAtom, but it is grounded.
 */
class GroundedAtom
{
public:
	static void removeInstantiatedGroundedAtom();
	static void removeInstantiatedGroundedAtom(const std::vector<const GroundedAtom*>& exceptions);
	static const GroundedAtom& getGroundedAtom(const Predicate& predicate, const Object** variables);
//	static const GroundedAtom& getGroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings);
	
	static unsigned int numberOfGroundedAtoms();
	
	virtual ~GroundedAtom();

	//const Atom& getAtom() const { return *atom_; }
	const Predicate& getPredicate() const { return *predicate_; }
	const Object& getObject(unsigned int term_index) const { return *variables_[term_index]; }
 	
	bool operator==(const GroundedAtom& rhs) const;
	bool operator!=(const GroundedAtom& rhs) const;
	
private:
	GroundedAtom(const Predicate& predicate, const Object** variables);
//	GroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings);
	
	static std::vector<const GroundedAtom*> instantiated_grounded_atoms_;

	const Predicate* predicate_;
	const Object** variables_;
	
	friend std::ostream& operator<<(std::ostream& os, const GroundedAtom& grounded_atom);
};

std::ostream& operator<<(std::ostream& os, const GroundedAtom& grounded_atom);

class State
{
public:
	State(const std::vector<const GroundedAtom*>& facts, bool created_by_helpful_action);
	
	State(const State& rhs, const GroundedAction& achiever, bool created_by_helpful_action);
	
	virtual ~State();
	
	void setDistanceToGoal(unsigned int distance_to_goal) { distance_to_goal_ = distance_to_goal; }
	
	unsigned int getHeuristic() const { return /*distance_from_start_ + */distance_to_goal_; }
	
	void getSuccessors(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const ActionManager& action_manager, const TypeManager& type_manager, bool prune_unhelpful_actions) const;
	
	bool isSuperSetOf(const std::vector<const GroundedAtom*>& facts) const;
	
	const std::vector<const GroundedAtom*>& getFacts() const { return facts_; }
	
	const std::vector<const GroundedAction*>& getAchievers() const { return achievers_; }
	
	void setHelpfulActions(const std::vector<const REACHABILITY::AchievingTransition*>& helpful_actions);
	
	const std::vector<const REACHABILITY::AchievingTransition*>& getHelpfulActions() const { return helpful_actions_; }
	
	bool isCreatedByHelpfulAction() const { return created_by_helpful_action_; }
	
	static void addStaticFact(const GroundedAtom& static_fact);
	
	static std::vector<const GroundedAtom*>& getStaticFacts() { return static_facts_; }
	
	void deleteHelpfulActions();
	
	bool operator==(const State& state) const;
	
private:
	std::vector<const GroundedAtom*> facts_;
	
	unsigned int distance_to_goal_;
	//unsigned int distance_from_start_;
	
	std::vector<const GroundedAction*> achievers_;
	
	//std::vector<std::pair<const Action*, std::vector<const Object*>**> > helpful_actions_;
	
	std::vector<const REACHABILITY::AchievingTransition*> helpful_actions_;
	
	bool created_by_helpful_action_;
	
	bool addFact(const GroundedAtom& fact, bool remove_fact);
	void removeFact(const GroundedAtom& fact);
	
	void instantiateAndExecuteAction(NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const MyPOP::Action& action, const std::vector< const MyPOP::Atom* >& preconditions, const std::vector< const MyPOP::Equality* >& equalities, unsigned int uninitialised_precondition_index, const MyPOP::Object** assigned_variables, const MyPOP::TypeManager& type_manager, bool prune_unhelpful_actions) const;
	void instantiateAndExecuteAction(const std::vector<const GroundedAtom*>& relevant_facts, NewStateReachedListener& listener, const std::multimap<const Object*, const Object*>& symmetrical_groups, const Action& action, const std::vector<const Atom*>& preconditions, const std::vector<const Equality*>& equalities, unsigned int uninitialised_precondition_index, const Object** assigned_variables, const TypeManager& type_manager, bool prune_unhelpful_actions) const;
	
	void createAllGroundedVariables(std::vector<const Object**>& all_grounded_action_variables, const Object** grounded_action_variables, const Action& action, const TypeManager& type_manager) const;
	
	static std::vector<const GroundedAtom*> static_facts_;
	
	friend std::ostream& operator<<(std::ostream& os, const State& state);
};

std::ostream& operator<<(std::ostream& os, const State& state);

class CompareStates {
public:
	bool operator()(const State* lhs, const State* rhs);
};

/**
 * Implementation of a forward chaining planner.
 */
class ForwardChainingPlanner
{
public:
	ForwardChainingPlanner(const ActionManager& action_manager, PredicateManager& predicate_manager, const TypeManager& type_manager, HEURISTICS::HeuristicInterface& heuristic);
	
	virtual ~ForwardChainingPlanner();
	
	std::pair<int, int> findPlan(std::vector< const MyPOP::GroundedAction* >& plan, const std::vector< const MyPOP::Atom* >& initial_facts, const std::vector< const MyPOP::Atom* >& goal_facts, const TermManager& term_manager, bool prune_unhelpful_actions, bool allow_restarts, bool allow_new_goals_to_be_added);
	
private:
	
	//void setHeuristicForState(MyPOP::State& state, MyPOP::REACHABILITY::DTGReachability& analyst, const std::vector< const MyPOP::GroundedAtom* >& goal_facts, const std::vector< const MyPOP::REACHABILITY::ResolvedBoundedAtom* >& resolved_grounded_goal_facts, const MyPOP::Bindings& bindings) const;
	//void setHeuristicForState(MyPOP::State& state, MyPOP::REACHABILITY::DTGReachability& analyst, const std::vector<const GroundedAtom*>& goal_facts, bool find_helpful_actions, bool allow_new_goals_to_be_added) const;
	
	/**
	 * Check if the given state satisfy the facts in the goal state.
	 * @param current_state The current state to evaluate.
	 * @return True if the goal facts are a subset of the current state, false otherwise.
	 */
	bool satisfyGoal(const State& current_state, const std::vector<const GroundedAtom*>& goal_facts) const;
	
	const ActionManager* action_manager_;
	PredicateManager* predicate_manager_;
	const TypeManager* type_manager_;
	
	HEURISTICS::HeuristicInterface* heuristic_;
};

};

#endif
