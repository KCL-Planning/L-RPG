#ifndef MYPOP_PLAN_H
#define MYPOP_PLAN_H

#include <vector>
#include <limits>
#include <algorithm>
#include <limits.h>

#include "plan_orderings.h"
#include "pointers.h"
#include "plan_types.h"

namespace MyPOP {

class BindingsPropagator;
class ActionManager;
class TermManager;
class TypeManager;
class Bindings;
class Link;
class Atom;
class Formula;
class Action;

/**
 * A step is a single action in the plan. Using the ID of the step and the
 * ID of the included action we can derive the bindings of the action's
 * parameters.
 * Between steps there can be ordering constraints (step X before / after
 * step Y, etc).
 */
class Step
{
public:

	// TODO: Check if the compiler makes this enumeration unsigned or not...
	enum IDs { INVALID_STEP = UINT_MAX, INITIAL_STEP = 0, GOAL_STEP = 1 };
	static const Step* dummy_step;

	Step(StepID stepId, const Action& action)
		: stepId_(stepId), action_(&action)
	{
	
	}

	const Action& getAction() const { return *action_; }

	StepID getStepId() const { return stepId_; }

	friend std::ostream& operator<<(std::ostream& os, const Step& step);

private:

	/**
	 * Print a formula for debug purposes.
	 */
//	void printFormula(std::ostream& os, const Formula& formula) const;

	StepID stepId_;
	const Action* action_;
};

std::ostream& operator<<(std::ostream& os, const Step& step);

/**
 * Causal links are connections the planner makes between the effects of actions and 
 * open condition flaws. We say that a causal links achieves an open condition.
 */
class Link
{
public:
	Link (StepPtr from_step, StepPtr to_step, const Atom& condition);

	// Get the achieving step.
	StepPtr getFromStep() const { return from_step_; }

	// Get the supported step.
	StepPtr getToStep() const { return to_step_; }

	// Get the supported condition.
	const Atom& getCondition() const { return *condition_; }

	friend std::ostream& operator<<(std::ostream& os, const Link& other);

private:
	// The step which achieves the open condition.
	StepPtr from_step_;

	// The step which is supported.
	StepPtr to_step_;

	// The condition which is supported.
	const Atom* condition_;
};

std::ostream& operator<<(std::ostream& os, const Link& other);

/**
 * A partial plan is defined as the tupple <A, O, C, B> with:
 * A: The set of lifted operators (the steps).
 * O: The ordering constraints between steps.
 * C: The causal links between the effects and preconditions of steps.
 * B: The binding constraints on parameters of the operators.
 */
class Plan
{
public:
	Plan(const ActionManager&, const TermManager&, const TypeManager&, const BindingsPropagator& propagator);

	/**
	 * Copy constructor, extremely inefficient! Need to find a better way of making copies
	 * of plans. Note: Have a look at the Chain class for VHPOP.
	 */
	Plan(const Plan& plan);


	~Plan();

	/**
	 * Construct the initial plan. Create the initial step, containing all the atoms true in
	 * the initial state and order this step before the step containing an action with all the
	 * goals as its precondition.
	 * No bindings and no causal links. This is the most basic starting point for partial order
	 * planners.
	 */
	void makeInitialPlan(const Action& initialAction, const Action& goalAction);

	/**
	 * Add a new step to this plan who will be linked the given action.
	 * Optionally a specific step id can be given, but this should only
	 * be used when you know what you're doing! Currenly this is only
	 * used to initialize the initial and goal actions.
	 */
	StepPtr createStep(const Action& new_action);

	/**
	 * Try to create a causal link from a step in the plan to another step. If this operation fails
	 * this function will return false. True otherwise.
	 */
	bool createCausalLink(StepPtr from_step, const Atom& supporting_effect, const OpenCondition& open_condition, bool is_new_step);

	/**
	 * Check if the given unsafe is still unsafe in this plan.
	 */
	bool isThreat(const Unsafe& unsafe) const;

	/**
	 * Get all the open conditions.
	 */
	const std::vector<OpenConditionPtr>& getOpenConditions() const { return open_conditions_; }

	/**
	 * Add an open condition to the plan.
	 */
	void addOpenCondition(OpenConditionPtr open_condition);
	
	/**
	 * Get all the unsafes.
	 */
	const std::vector<UnsafePtr>& getUnsafes() const { return unsafes_; }

	/**
	 * Get the bindings of this plan.
	 */
	Bindings& getBindings() const { return *bindings_; }

	/**
	 * Get the orderings of this plan.
	 */
	Orderings& getOrderings() const { return *orderings_; }

	/**
	 * Get all the steps in the plan.
	 */
	const std::vector<StepPtr>& getSteps() const { return steps_; }

	/**
	 * Remove an unsafe from the plan.
	 */
	void removeUnsafe(const Unsafe& unsafe);

	/**
	 * Add an unsafe to the plan.
	 */
	void addUnsafe(UnsafePtr unsafe);

	/**
	 * Get the unique id of this plan.
	 */
	int getPlanId() const { return plan_id_; }

	/**
	 * Get the number of plans generated.
	 */
	static int getPlansGenerated() { return Plan::plan_counter_; }

	friend std::ostream& operator<<(std::ostream& os, const Plan& plan);

private:

	static int plan_counter_;
	int plan_id_;

	/**
	 * To make sure we do not allow plans which can never be executed we need to check for threats
	 * due to adding new steps or links. We can these threats unsafes as they threaten an
	 * established causal link. Resolutions for these are to:
	 * 1) promote the threatening step (i.e. order if after the affected step).
	 * 2) demote the threatening step (i.e. order it before the supporting step).
	 * 3) separate it (i.e. make sure the variable domains do not overlap).
	 */
	/**
	 * Given a link, find all steps which threaten this link and store all these as unsafes.
	 */
	void checkLinkThreats(LinkPtr link);
	
	/**
	 * Given a step, find all links it threatens and store all these as unsafes.
	 */
	void checkStepThreats(StepPtr step);
	
	/**
	 * Utility function to help the function above to function (as they do the same thing).
	 */
	void checkThreat(StepPtr step, LinkPtr link);
	
	/**
	 * Add a goal to the plan, this means we add new open conditions based on the
	 * formula of the actions which has been inserted into the plan.
	 */
	void addGoal(const Formula& goal, StepPtr step);

	const ActionManager* action_manager_;
	const TermManager* term_manager_;
	const TypeManager* type_manager_;

	// The open conditions in this partial plan.
	std::vector<OpenConditionPtr> open_conditions_;
	
	// All unsafe links.
	std::vector<UnsafePtr> unsafes_;
	
	// The mutex relations in this partial plan.
	std::vector<MutexPtr> mutexes_;

	// The steps in the plan. A step is linked to the action which is performed
	// at that step.
	std::vector<StepPtr> steps_;

	// The causal links in the plan. These represent the commitments of the plan to
	// support preconditions of actions by another action.
	std::vector<LinkPtr> causal_links_;

	// The bindings in the plan. A bindings are made between the parameters of actions,
	// internally a binding is stored as a mapping from: step_id, parameter_number and
	// the set of terms (objects or other variables) it must be linked to.
	Bindings* bindings_;

	// The orderings between steps in the plan. Ordering can either be: before or after.
	BinaryOrderings* orderings_;
};

std::ostream& operator<<(std::ostream& os, const Plan& plan);

};

#endif
