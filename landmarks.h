#ifndef LANDMARK_LANDMARKS_H
#define LANDMARK_LANDMARKS_H

#include <vector>

#include "VALfiles/ptree.h"
#include "VALfiles/SASActions.h"
#include "VALfiles/ToFunction.h"
#include "plan_bindings.h"
#include "plan_orderings.h"
#include "bindings_propagator.h"

namespace MyPOP {
class ActionManager;
class TypeManager;
class Plan;

namespace SAS_Plus {
class DomainTransitionGraphManager;
class CausalGraph;
};

namespace LANDMARKS {

class Landmark;
class PreconditionLandmark;
class LandmarkGraph;

/**
 * Adapted orderings class, we do not want to deduce any additional orderings as it will make the graphs very messy!
 */
class LandmarkOrderings : public BinaryOrderings
{
public:
	virtual bool addOrdering(const Ordering& ordering);
};

/**
 * Process the planning problem and produce landmarks based on the lifted action representation.
 */
class LandmarkManager
{
public:
	LandmarkManager(const ActionManager& action_manager, const TypeManager& type_manager, const TermManager& term_manager);

	~LandmarkManager();
	
	/**
	 * Start generating the landmark graph. Internally the SAS+ representation of the actions are mapped in
	 * SAS::FunctionStructure from the operators to the actual representation. Therefor we need the operator
	 * list to unearth the SAS+ representation.
	 */
	//void generateLandmarks(const VAL::operator_list& operators, const VAL::pddl_type_list& types, Plan& initial_plan);

	/**
	 * Find landmarks by regressive search. Start off with the goals as the initial landmarks and find landmarks
	 * by checking which actions share the same preconditions.
	 */
	void findLandmarksFromGoal(const VAL::operator_list& operators, const VAL::pddl_type_list& types, MyPOP::Plan& initial_plan, const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const SAS_Plus::CausalGraph& causal_graph);
	
	/**
	 * Find landmarks by checking the DTG structures and see if any nodes must be present in the graph to traverse
	 * the graph from the initial state to the goal state.
	 */
	void findClosestLandmarksInDTG(std::vector<const PreconditionLandmark*>& found_landmarks, const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const Landmark& from_landmark, const Landmark& to_landmark);
	//void findLandmarksInDTGs(const SAS_Plus::DomainTransitionGraphManager& dtg_manager, Plan& initial_plan);
	//void findLandmarksInDTG(const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const Landmark& from_landmark, const Landmark& to_landmark);

	/**
	 * Get the landmark graph with all landmarks found so far.
	*/
	const LandmarkGraph& getLandmarkGraph() const { return *landmark_graph_; }

protected:
	void getSharedPreconditions(std::vector<const Atom*>& shared_preconditions, const std::vector<StepPtr>& action_steps) const;
	
	void getCommonPreconditions(std::vector<const PreconditionLandmark*>& landmarks, const PreconditionLandmark& landmark, Plan& initial_plan, const SAS_Plus::DomainTransitionGraphManager& dtg_manager) const;

	void getFirstAchievers(std::vector<const PreconditionLandmark*>& landmarks, const PreconditionLandmark& landmark, Plan& initial_plan, const SAS_Plus::DomainTransitionGraphManager& dtg_manager) const;
private:

	// The action manager contains all information about the action.
	const ActionManager* action_manager_;

	// The type manager contains all information about the types.
	const TypeManager* type_manager_;
	
	// The term manager contains all information about the terms.
	const TermManager* term_manager_;
	
	// The landmark graph, all found landmarks will be inserted in this graph.
	LandmarkGraph* landmark_graph_;
};

/**
 * A landmark is defined as a fact which must be true in any valid solution to a problem. The landmark
 * fact is captured in atom_ and it is bound to a specific landmark graph which contains the fact's
 * bindings.
 */
class Landmark
{
public:
	/**
	 * Create a new landmark. The landmarks' bindings will be copied to the bindings of the landmark
	 * graph.
	 * @param step_id The ID used to bind all te variables of atom in the given bindings.
	 * @param atom The landmark fact.
	 * @param bindings Contains the mappings between the fact's variables and its domains.
	 * @param landmark_graph The landmark grah this landmark will be added to.
	 */
	Landmark(StepID step_id, const Atom& atom, const BindingsFacade& bindings, LandmarkGraph& landmark_graph);
	
	~Landmark();
	
	const Atom& getAtom() const { return *atom_; }
	
	StepID getStepId() const { return step_id_; }
	void setStepId(StepID step_id) { step_id_ = step_id; }

	const LandmarkGraph& getLandmarkGraph() const { return *landmark_graph_; }

private:
	
	// The step id under which the variables are bound in the landmark graph's bindings.
	StepID step_id_;
	
	// The landmark.
	const Atom* atom_;

	// The landmark graph it is added to.
	const LandmarkGraph* landmark_graph_;
};

std::ostream& operator<<(std::ostream& os, const Landmark& landmark);

/**
 * A precondition landmark is a landmark which has been discovered when looking at shared preconditions.
 * It contains pointers to the landmarks which are shared preconditions of the same set of actions.
 */
class PreconditionLandmark : public Landmark
{
public:
	PreconditionLandmark(StepID step_id, const Atom& atom, const BindingsFacade& bindings, LandmarkGraph& landmark_graph);

	void setSharedLandmarks(const std::vector<const PreconditionLandmark*>& landmarks);

	const std::vector<const PreconditionLandmark*>& getSharedLandmarks() const { return *shared_landmarks_; }

	void setAchievingActions(const std::vector<StepPtr>& achieving_actions);

	const std::vector<StepPtr>& getAchievingActions() const { return *achieving_actions_; }

private:
	// The common set of preconditions of the set of actions which have these landmarks as their precondition.
	const std::vector<const PreconditionLandmark*>* shared_landmarks_;

	// The set of actions which achieve this landmark. The shared landmarks are the shared preconditions
	// of this set of actions.
	const std::vector<StepPtr>* achieving_actions_;
};

/**
 * Landmark graph keeps a list of landmarks and the orderings between them.
 */
class LandmarkGraph
{
public:
	/**
	 * Create a landmark graph with no initial bindings.
	 */
	LandmarkGraph(const TermManager& term_manager);
	
	/**
	 * Create a landmark graph and copy the bindings from the given one.
	 */
	LandmarkGraph(const BindingsFacade& bindings);
	
	/**
	 * Get the bindings of the landmarks.
	 */
	const BindingsFacade& getBindings() const { return *bindings_; }
	BindingsFacade& getBindings() { return *bindings_; }
	
	/**
	 * Get the orderings between the landmarks.
	 */
	const Orderings& getOrderings() const { return orderings_; }
	Orderings& getOrderings() { return orderings_; }
	
	/**
	 * Get all the landmarks.
	 */
	const std::vector<const Landmark*>& getLandmarks() const { return landmarks_; }
	
	/**
	 * Add a landmark to this graph. The bindings of the variables of the landmark are not necessarily 
	 * bounded by bindings_, another Bindings object might have been used to find the variables. These bindings
	 * will be copied to this landmark graph's own bindings object. The step id of the given landmark will
	 * be changed after the bindings have been made.
	 */
	void addLandmark(Landmark& landmark, const BindingsFacade& atom_bindings);

	/**
	 * Order one landmark before another one, if this ordering fails an exception will be thrown.
	 */
	void addOrdering(const Landmark& from_landmark, const Landmark& to_landmark);

	/**
	 * Return true if the given landmark is unifiable with the given action and its bindings.
	 */
	bool isUnifiable(StepPtr initial_step, const BindingsFacade& bindings, const PreconditionLandmark& landmark) const;
	
private:
	// The propagator we use to prune the bindings.
	SimpleBindingsPropagator propagator_;
	
	// The bindings of all landmarks' variables.
	BindingsFacade* bindings_;
	
	// The orderings between landmarks.
	//BinaryOrderings orderings_;
	LandmarkOrderings orderings_;
	
	// All landmarks contained in this landmark graph.
	std::vector<const Landmark*> landmarks_;
};

std::ostream& operator<<(std::ostream& os, const LandmarkGraph& landmark_graph);

};

namespace Graphviz {
	
// Utility functions to print landmark graphs to DOT format.
void printToDot(const LANDMARKS::LandmarkGraph& landmark_graph);

};

};

#endif
