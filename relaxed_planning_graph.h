#ifndef MYPOP_RPGRELAXED_PLANNING_GRAPH_H
#define MYPOP_RPGRELAXED_PLANNING_GRAPH_H
#include <utility>
#include <vector>
#include <ostream>
#include "plan_types.h"
#include "plan_bindings.h"
#include "formula.h"

namespace MyPOP {

class BindingsPropagator;
class ActionManager;
class Plan;
class TermManager;
class Atom;
class Step;

namespace SAS_Plus {
	class BoundedAtom;
};

namespace REACHABILITY {
	class ResolvedBoundedAtom;
	class EquivalentObjectGroupManager;
};

namespace RPG {

//typedef std::pair<StepID, const Atom*> BoundedAtom;

class ResolvedAction
{
public:
	ResolvedAction(const Action& action, StepID step_id, const Bindings& bindings, const REACHABILITY::EquivalentObjectGroupManager& eog_manager);
	
	~ResolvedAction();
	
	const std::vector<const REACHABILITY::ResolvedBoundedAtom*>& getPreconditions() const { return preconditions_; }
	
	const std::vector<const REACHABILITY::ResolvedBoundedAtom*>& getEffects() const { return effects_; }
	
	const StepID getStepID() const { return step_id_; }
	
	const Action& getAction() const { return *action_; }
	
	const Bindings& getBindings() const { return *bindings_; }
	
private:
	
	const StepID step_id_;
	const Action* action_;
	const Bindings* bindings_;
	
	std::vector<const REACHABILITY::ResolvedBoundedAtom*> preconditions_;
	std::vector<const REACHABILITY::ResolvedBoundedAtom*> effects_;
};

std::ostream& operator<<(std::ostream& os, const ResolvedAction& resolved_action);

/**
 * Because we allow no duplicate facts in a layer we first check if the atom can be bounded to an existing
 * one already present in the layer. If this is the case it will not be added.
 */
class FactLayer
{
public:
	/**
	 * Create a new empty fact layer.
	 */
	FactLayer(bool delete_facts = false);

	/**
	 * Copy constructor.
	 */
	FactLayer(const FactLayer& fact_layer);
	
	~FactLayer();

	/**
	 * Add a fact to this fact layer, this method only succeeds if the bounded atom cannot be unified
	 * with any atoms already present in this fact layer.
	 */
	bool addFact(const REACHABILITY::ResolvedBoundedAtom& bounded_atom);

	/**
	 * Return all the facts stored in this fact layer.
	 */
	const std::vector<const REACHABILITY::ResolvedBoundedAtom*>& getFacts() const { return facts_; }
	
	const std::vector<const REACHABILITY::ResolvedBoundedAtom*>* getFacts(const REACHABILITY::ResolvedBoundedAtom& precondition) const;

private:
	
	bool delete_facts_;
	
	std::string getUniqueName(const REACHABILITY::ResolvedBoundedAtom& atom) const;
	
	// All the facts stored in this fact layer.
	std::vector<const REACHABILITY::ResolvedBoundedAtom*> facts_;
	
	std::map<std::string, std::vector<const REACHABILITY::ResolvedBoundedAtom*>* > mapped_facts_;
	
	std::vector<std::vector<const REACHABILITY::ResolvedBoundedAtom*>*> mapped_facts_to_remove_;
};

/**
 * A relaxed planning graph is a serries of facts and action layers alternating between the two. Starting at the initial layer
 * all actions which can be applied will be added to the next fact layer and its effects (minus the delete effects) will be added
 * to the next fact layer in addition to the facts already present (no-ops).
 */
class RelaxedPlanningGraph
{
public:
	/**
	 * Create a relaxed planning graph from the intial state to the goal state. These can be found in the
	 * initial plan. The relaxed planning graph is only allowed to make use of the lifted actions.
	 */
	RelaxedPlanningGraph(const ActionManager& action_manager, const Plan& initial_plan, const REACHABILITY::EquivalentObjectGroupManager& eog_manager);

	~RelaxedPlanningGraph();

	const std::vector<std::vector<const ResolvedAction*>* >& getActionLayers() const { return action_layers_; }

	const std::vector<FactLayer* >& getFactLayers() const { return fact_layers_; }

private:

	// The action layers.
	//std::vector<std::vector<const Step*>* > action_layers_;
	std::vector<std::vector<const ResolvedAction*>* > action_layers_;

	// The fact layers.
	std::vector<FactLayer* > fact_layers_;
	
	std::vector<const ResolvedAction*> all_grounded_actions_;

	// The bindings of the actions.
	Bindings* bindings_;
};

std::ostream& operator<<(std::ostream& os, const RelaxedPlanningGraph& rpg);

}

}

#endif
