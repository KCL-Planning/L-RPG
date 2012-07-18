#ifndef MYPOP_FORWARD_CHAINING_PLANNER
#define MYPOP_FORWARD_CHAINING_PLANNER

#include <vector>
#include "formula.h"

namespace MyPOP
{
class Action;
class ActionManager;
class PredicateManager;
class TypeManager;

namespace SAS_Plus
{
class BoundedAtom;
};

namespace REACHABILITY
{
class DTGReachability;
};

class GroundedAction
{
public:
	static const GroundedAction& getGroundedAction(const Action& action, const Object** variables);
	
private:
	
	static std::vector<const GroundedAction*> instantiated_grounded_actions_;
	
	GroundedAction(const Action& action, const Object** variables);
	
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
	GroundedAtom(const Atom& atom, const Object** variables);
	GroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings);

	virtual ~GroundedAtom();

	const Atom& getAtom() const { return *atom_; }
	const Object& getObject(unsigned int term_index) const { return *variables_[term_index]; }
 	
	bool operator==(const GroundedAtom& rhs) const;
	bool operator!=(const GroundedAtom& rhs) const;
	
private:
	const Atom* atom_;
	const Object** variables_;
	
	friend std::ostream& operator<<(std::ostream& os, const GroundedAtom& grounded_atom);
};

std::ostream& operator<<(std::ostream& os, const GroundedAtom& grounded_atom);

class State
{
public:
	State(const std::vector<const GroundedAtom*>& facts);
	
	State(const State& rhs, const GroundedAction& achiever);
	
	virtual ~State();
	
	void setDistanceToGoal(unsigned int distance_to_goal) { distance_to_goal_ = distance_to_goal; }
	
	unsigned int getHeuristic() const { return /*distance_from_start_ + */distance_to_goal_; }
	
	void getSuccessors(std::vector<State*>& successor_states, const ActionManager& action_manager, const TypeManager& type_manager) const;
	
	bool isSuperSetOf(const std::vector<const GroundedAtom*>& facts) const;
	
	const std::vector<const GroundedAtom*>& getFacts() const { return facts_; }
	
	//const GroundedAction* getAchiever() const { return achiever_; }
	const std::vector<const GroundedAction*>& getAchievers() const { return achievers_; }
	
	//const State& getParent() const { return *parent_state_; }
	
	bool operator==(const State& state) const;
	
private:
	std::vector<const GroundedAtom*> facts_;
	
	unsigned int distance_to_goal_;
	unsigned int distance_from_start_;
	
	std::vector<const GroundedAction*> achievers_;
	
	void addFact(const GroundedAtom& fact);
	void removeFact(const GroundedAtom& fact);
	
	void instantiateAndExecuteAction(std::vector< MyPOP::State* >& successor_states, const MyPOP::Action& action, const std::vector< const MyPOP::Atom* >& preconditions, const std::vector< const MyPOP::Equality* >& equalities, unsigned int uninitialised_precondition_index, const MyPOP::Object** assigned_variables, const MyPOP::TypeManager& type_manager) const;
	
	void createAllGroundedVariables(std::vector<const Object**>& all_grounded_action_variables, const Object** grounded_action_variables, const Action& action, const TypeManager& type_manager) const;
	
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
	ForwardChainingPlanner(const ActionManager& action_manager, const PredicateManager& predicate_manager, const TypeManager& type_manager);
	
	virtual ~ForwardChainingPlanner();
	
	void findPlan(std::vector< const MyPOP::GroundedAction* >& plan, MyPOP::REACHABILITY::DTGReachability& analyst, const std::vector< const MyPOP::SAS_Plus::BoundedAtom* >& initial_fact, const std::vector< const MyPOP::SAS_Plus::BoundedAtom* >& goal_facts, const MyPOP::Bindings& bindings, bool ground);
	
private:
	
	/**
	 * Check if the given state satisfy the facts in the goal state.
	 * @param current_state The current state to evaluate.
	 * @return True if the goal facts are a subset of the current state, false otherwise.
	 */
	bool satisfyGoal(const State& current_state, const std::vector<const GroundedAtom*>& goal_facts) const;
	
	const ActionManager* action_manager_;
	const PredicateManager* predicate_manager_;
	const TypeManager* type_manager_;
};

};

#endif
