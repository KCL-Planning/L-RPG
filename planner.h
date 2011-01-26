#ifndef MYPOP_PLANNER_H
#define MYPOP_PLANNER_H

#include <vector>
#include <queue>

#include "pointers.h"
#include "flaw_selector.h"

namespace MyPOP {

class Plan;
class Flaw;
class Atom;
class ActionManager;
class TermManager;
class TypeManager;

/**
 * Temporal heuristic function.
 */
class ComparePlans {
public:
	bool operator()(const Plan* p1, const Plan* p2);
};

class Planner{
public:
    Planner(const Plan& initial_plan, const ActionManager& action_manager, const TermManager& term_manager, const TypeManager& type_manager, const FlawSelectionStrategy& flaw_selector);

    ~Planner();

	// Start the search process.
	const Plan* getSolution();

	bool promote(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe);

	bool demote(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe);

	bool separate(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe);

	/**
	 * An unsafe is a step which threatens a causal link and is handled by the following refinements:
	 * 1) Demotion.
	 * 2) Promotion.
	 * 3) Separation.
	 */
	void handleUnsafe(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe);

	/**
	 * To handle an open condition a causal link is introduced.
	 */
	void handleOpenCondition(std::vector<const Plan*>& refinement, const Plan& plan, const OpenCondition& open_condition);

	/**
	 * Handle a mutex relation between.
	 */
	void handleMutex(std::vector<const Plan*>& refinement, const Plan& plan, const Mutex& mutex);
	
	/**
	 * Flaw selection strategy.
	 */
	const Flaw& selectOpenCondition(const Plan& plan);

	/**
	 * Get the number of dead ends encountered.
	 */
	int getDeadEnds() const { return dead_ends_; }


	/**
	 * Get the number of plans visited.
	 */
	int getPlansVisited() const { return plans_visited_; }

private:
	std::priority_queue<const Plan*, std::vector<const Plan*>, ComparePlans > plans_;

	const ActionManager* action_manager_;
	const TermManager* term_manager_;
	const TypeManager* type_manager_;
	
	const FlawSelectionStrategy* flaw_selector_;

	// Some statistics.
	int dead_ends_;
	int plans_visited_;
};

};

#endif
