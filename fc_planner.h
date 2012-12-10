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
class AchievingTransition;
class DTGReachability;
class ResolvedTransition;
class ResolvedBoundedAtom;
};

class GroundedAction
{
public:
	static const GroundedAction& getGroundedAction(const Action& action, const Object** variables);
	static void removeInstantiatedGroundedActions();
	static void removeInstantiatedGroundedActions(std::vector<const GroundedAction*>::const_iterator begin, std::vector<const GroundedAction*>::const_iterator end);
	static unsigned int numberOfGroundedActions();
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
	static const GroundedAtom& getGroundedAtom(const Atom& atom, const Object** variables);
	static const GroundedAtom& getGroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings);
	
	static unsigned int numberOfGroundedAtoms();
	
	virtual ~GroundedAtom();

	const Atom& getAtom() const { return *atom_; }
	const Object& getObject(unsigned int term_index) const { return *variables_[term_index]; }
 	
	bool operator==(const GroundedAtom& rhs) const;
	bool operator!=(const GroundedAtom& rhs) const;
	
private:
	GroundedAtom(const Atom& atom, const Object** variables);
	GroundedAtom(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings);
	
	static std::vector<const GroundedAtom*> instantiated_grounded_atoms_;

	const Atom* atom_;
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
	
	void getSuccessors(std::vector<State*>& successor_states, const ActionManager& action_manager, const TypeManager& type_manager) const;
	
	bool isSuperSetOf(const std::vector<const GroundedAtom*>& facts) const;
	
	const std::vector<const GroundedAtom*>& getFacts() const { return facts_; }
	
	//const GroundedAction* getAchiever() const { return achiever_; }
	const std::vector<const GroundedAction*>& getAchievers() const { return achievers_; }
	
	//void setHelpfulActions(const std::vector<std::pair<const Action*, std::vector<const Object*>**> >& helpful_actions);
	void setHelpfulActions(const std::vector<const REACHABILITY::AchievingTransition*>& helpful_actions);
	
//	const std::vector<std::pair<const Action*, std::vector<const Object*>**> >& getHelpfulActions() const { return helpful_actions_; }
	const std::vector<const REACHABILITY::AchievingTransition*>& getHelpfulActions() const { return helpful_actions_; }
	
	bool isCreatedByHelpfulAction() const { return created_by_helpful_action_; }
	
	//const State& getParent() const { return *parent_state_; }
	
	void deleteHelpfulActions();
	
	bool operator==(const State& state) const;
	
private:
	std::vector<const GroundedAtom*> facts_;
	
	unsigned int distance_to_goal_;
	unsigned int distance_from_start_;
	
	std::vector<const GroundedAction*> achievers_;
	
	//std::vector<std::pair<const Action*, std::vector<const Object*>**> > helpful_actions_;
	
	std::vector<const REACHABILITY::AchievingTransition*> helpful_actions_;
	
	bool created_by_helpful_action_;
	
	bool addFact(const GroundedAtom& fact, bool remove_fact);
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
	ForwardChainingPlanner(const ActionManager& action_manager, PredicateManager& predicate_manager, const TypeManager& type_manager);
	
	virtual ~ForwardChainingPlanner();
	
	std::pair<int, int> findPlan(std::vector< const MyPOP::GroundedAction* >& plan, MyPOP::REACHABILITY::DTGReachability& analyst, const std::vector< const Atom* >& initial_fact, const std::vector< const Atom* >& goal_facts, bool prune_unhelpful_actions);
	
private:
	
	//void setHeuristicForState(MyPOP::State& state, MyPOP::REACHABILITY::DTGReachability& analyst, const std::vector< const MyPOP::GroundedAtom* >& goal_facts, const std::vector< const MyPOP::REACHABILITY::ResolvedBoundedAtom* >& resolved_grounded_goal_facts, const MyPOP::Bindings& bindings) const;
	void setHeuristicForState(MyPOP::State& state, MyPOP::REACHABILITY::DTGReachability& analyst, const std::vector<const GroundedAtom*>& goal_facts) const;
	
	/**
	 * Check if the given state satisfy the facts in the goal state.
	 * @param current_state The current state to evaluate.
	 * @return True if the goal facts are a subset of the current state, false otherwise.
	 */
	bool satisfyGoal(const State& current_state, const std::vector<const GroundedAtom*>& goal_facts) const;
	
	const ActionManager* action_manager_;
	PredicateManager* predicate_manager_;
	const TypeManager* type_manager_;
};

};

#endif
