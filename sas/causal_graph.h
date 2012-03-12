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

	
namespace SAS_Plus {

class DomainTransitionGraphManager;
class DomainTransitionGraph;
class Transition;
class BoundedAtom;
	

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
	CausalGraph(const DomainTransitionGraphManager& dtg_manager, const ActionManager& action_manager);
	
	/**
	 * Get the DTG manager.
	 */
	const DomainTransitionGraphManager& getDTGManager() const { return *dtg_manager_; }
	
	/**
	 * Get the action manager.
	 */
	const ActionManager& getActionManager() const { return *action_manager_; }
	
	/**
	 * Get all the transition from the given DTG.
	 */
	void getTransitionsFrom(std::vector<const DomainTransitionGraph*>& transitions, const DomainTransitionGraph& dtg) const;
	
	/**
	 * Get all the transition to the given DTG.
	 */
	void getTransitionsTo(std::vector<const DomainTransitionGraph*>& transitions, const DomainTransitionGraph& dtg) const;

private:
	// The transitions between DTGs.
	typedef std::map<const DomainTransitionGraph*, std::set<const DomainTransitionGraph*>* > DTGtoDTG;
	DTGtoDTG transitions_;
	DTGtoDTG reverse_transitions_;
	
	/**
	 * Add a transition between two DTGs.
	 */
	void addTransition(const DomainTransitionGraph* from_dtg, const DomainTransitionGraph* to_dtg);
	
	// The DTG manager.
	const DomainTransitionGraphManager* dtg_manager_;
	
	// The action manager.
	const ActionManager* action_manager_;
};

std::ostream& operator<<(std::ostream& os, const CausalGraph& casual_graph);

};

namespace Graphviz {

// Printing the CG.
void printToDot(const SAS_Plus::CausalGraph& causal_graph);

};

};

#endif // SAS_PLUS_CAUSAL_GRAPH_H
