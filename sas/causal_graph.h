#ifndef SAS_PLUS_CAUSAL_GRAPH_H
#define SAS_PLUS_CAUSAL_GRAPH_H

#include <map>
#include <set>
#include <vector>
#include <iostream>

#include "../plan_types.h"

namespace MyPOP {

class Atom;
class ActionManager;
class Bindings;
class GroundedAtom;
class PredicateManager;

namespace SAS_Plus {

class LiftedDTG;
class MultiValuedTransition;
class PropertySpace;

/**
 * The causal graph contains the dependencies between the state variables. An edge between two state variables v and v' exists if:
 * v != v'
 * The Domain Transition Graph of v has a transition with some condition on v'.
 * An operator exists which affects both v and v'.
 */
class CausalGraph
{
public:
	/**
	 * Create the causal graph and map the dependencies between the DTGs.
	 */
	CausalGraph(const std::vector< MyPOP::SAS_Plus::LiftedDTG* >& all_lifted_dtgs, const MyPOP::ActionManager& action_manager/*, const MyPOP::TypeManager& type_manager*/, const MyPOP::PredicateManager& predicate_manager);
	
	/**
	 * Destructor.
	 */
	~CausalGraph();
	
	/**
	 * Remove all cycles!
	 */
	//void breakCycles(const std::vector<const GroundedAtom*>& goals, const Bindings& bindings);
	void breakCycles(const std::vector<const GroundedAtom*>& goals);
	
	/**
	 * Get the action manager.
	 */
	const ActionManager& getActionManager() const { return *action_manager_; }
	
	/**
	 * Get all the transition from the given DTG.
	 */
	void getTransitionsFrom(std::vector<const LiftedDTG*>& transitions, const LiftedDTG& dtg) const;
	
	/**
	 * Get all the transition to the given DTG.
	 */
	void getTransitionsTo(std::vector<const LiftedDTG*>& transitions, const LiftedDTG& dtg) const;
	
	/**
	 * Find all the DTGs which contain the given fact, such that the given fact contains the invariable of the DTG.
	 * @param dtgs The list of DTGs which contain the given fact, such that the given fact contains the invariable of the DTG.
	 * @param dtg_manager The DTG manager.
	 * @param step_id The StepID of the given fact.
	 * @param fact The fact to look for.
	 * @param bindings The bindings used to bind the given fact using the given step id.
	 */
	//void getDTGs(std::vector< const MyPOP::SAS_Plus::DomainTransitionGraph* >& dtgs, const MyPOP::StepID step_id, const MyPOP::Atom& fact, const MyPOP::Bindings& bindings) const;
	
	/**
	 * Check if a dependency exists between two DTGs. This function always returns true if &from == &to.
	 * @param from The high-level DTG for which the dependency is checked.
	 * @param to The low-level DTG we check the dependency against.
	 * @return True if from is dependent on to (i.e. an arc (from, to) exists in the causal graph).
	 */
	bool containsDependency(const SAS_Plus::LiftedDTG& from, const SAS_Plus::LiftedDTG& to, bool use_cache = true) const;
	
	void getAllDependencies(std::vector<const LiftedDTG*>& dependencies, const LiftedDTG& lifted_dtg) const;
	
	const std::set<const LiftedDTG*>& getAllDirectDependencies(const LiftedDTG& lifted_dtg) const;

	const std::vector<LiftedDTG*>& getAllLiftedDTGs() const { return *all_lifted_dtgs_; }
	
private:
	
	// The transitions between DTGs.
	typedef std::map<const LiftedDTG*, std::set<const LiftedDTG*>* > DTGtoDTG;
	DTGtoDTG transitions_;
	DTGtoDTG reverse_transitions_;
	
	typedef std::map<std::pair<const LiftedDTG*, const LiftedDTG*>, std::set<const MultiValuedTransition*>* > TransitionToWeightMapping;
	TransitionToWeightMapping arc_weights_;
	
	/**
	 * Add a transition between two DTGs.
	 */
	void addTransition(const LiftedDTG& from_dtg, const LiftedDTG& to_dtg, const MultiValuedTransition& transition);
	
	/**
	 * Apply Tarjan's algorithm for finding the strongly connected components of this causal graph.
	 */
	void findStronglyConnectedComponents(std::vector<std::vector<const LiftedDTG*>* >& strongly_connected_components) const;
	
	/**
	 * Part of Tarjan's algorithm.
	 */
	void strongConnect(std::vector< std::vector< const MyPOP::SAS_Plus::LiftedDTG* >* >& strongly_connected_components, std::vector< const MyPOP::SAS_Plus::LiftedDTG* >& stack, const MyPOP::SAS_Plus::LiftedDTG& dtg, std::map< const MyPOP::SAS_Plus::LiftedDTG*, std::pair< unsigned int, unsigned int > >& indexes, unsigned int& lowest_index) const;
	
	unsigned int getWeight(const MyPOP::SAS_Plus::LiftedDTG& dtg) const;
	
	void removeEdge(const LiftedDTG& from_dtg, const LiftedDTG& to_dtg);
	
	//void cacheDependencies();
	
	// The DTG manager.
	const std::vector<LiftedDTG*>* all_lifted_dtgs_;
	
	// The action manager.
	const ActionManager* action_manager_;
	
	// Cache the dependencies between DTGs.
	bool** cached_dependencies_;
	
	const PredicateManager*predicate_manager_;
};

std::ostream& operator<<(std::ostream& os, const CausalGraph& casual_graph);

};

namespace Graphviz {

// Printing the CG.
void printToDot(const std::string& file_name, const SAS_Plus::CausalGraph& causal_graph);

void printToDot(std::ofstream& ofs, const SAS_Plus::PropertySpace& property_space);

};

};

#endif // SAS_PLUS_CAUSAL_GRAPH_H
