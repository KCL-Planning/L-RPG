#ifndef SAS_PLUS_REACHABILITY_H
#define SAS_PLUS_REACHABILITY_H

#include <set>
#include <map>
#include <vector>
#include <iostream>

#include "../plan_types.h"
#include "../plan_bindings.h"
#include "dtg_types.h"

namespace MyPOP {

class Atom;

namespace LANDMARKS {
class Landmark;
};
	
namespace SAS_Plus {

class DomainTransitionGraphManager;
class DomainTransitionGraphNode;
class DomainTransitionGraph;
class DTGBindings;
class Transition;
class BoundedAtom;

class ReachabilityAnalist;
class ReachabilityTransition;
	

struct PathfinderNode {
	PathfinderNode(const PathfinderNode* parent, const DomainTransitionGraphNode& node)
		: steps_(parent == NULL ? 0 : parent->steps_ + 1), parent_(parent), node_(&node)
	{

	}

	unsigned int steps_;
	const PathfinderNode* parent_;
	const DomainTransitionGraphNode* node_;
};

struct PathfinderNodeComparer {
	bool operator() (const PathfinderNode* node1, const PathfinderNode* node2) const
	{
		return node1->steps_ > node2->steps_;
	}
};



/**
* Pathfinder to traverse the DTG graphs.
*/
class Pathfinder {
	
public:
	/**
	 * Construct a pathfinder to find paths in the given DTG.
	 */
	Pathfinder(const DomainTransitionGraph& dtg);
	
	/**
	 * Find a path from the given node to the end node. If no path can be found the return value will
	 * be false, true otherwise. The path found will be stored in the given vector.
	 */
	bool isReachable(const DomainTransitionGraphNode& from, const DomainTransitionGraphNode& to) const;

	/**
	 * Find the sortest path from the given nodes to the end nodes. If no path can be found the return value will
	 * be false, true otherwise. The path found will be stored in the given vector.
	 */
	bool getPath(std::vector<const DomainTransitionGraphNode*>& path, const std::vector<const DomainTransitionGraphNode*>& from, const std::vector<const DomainTransitionGraphNode*>& to) const;

	/**
	 * Instruct the pathfinder not to use the given node when searching for a path.
	 */
	void ignoreNode(const DomainTransitionGraphNode& dtg_node);
	
	/**
	 * Clear all the nodes in the ignore list.
	 */
	void clearIgnoreList();
private:
	
	// The domain transition graph this pathfinder will search for paths.
	const DomainTransitionGraph* dtg_;
	
	// The nodes to ignore when doing pathfinding.
	std::set<const DomainTransitionGraphNode*> ignore_list_;
};


/**
 * Node containing all reachability analysis information of a DTG Node. This is the nodes which can
 * be reached from this node and vice-versa from which nodes this node can be reached.
 */
class ReachableDTGNode
{
public:
	/**
	 * Create a reachability node linked to a DTG node. The initial reachable assignments is empty.
	 * @param dtg_node The DTG node this reachable node is linked to.
	 */
	ReachableDTGNode(ReachabilityAnalist& reachability_analist, const DomainTransitionGraphNode& dtg_node);
	
	/**
	 * Create a reachability node linked to a DTG node.
	 * @param dtg_node The DTG node this reachable node is linked to.
	 * @param init_assignments The initial assignments to the variable domains of the underlying DTG node
	 * which are valid. The contents of this container are copied to the internal datastructure of this class.
	 */
	ReachableDTGNode(MyPOP::SAS_Plus::ReachabilityAnalist& reachability_analist, const MyPOP::SAS_Plus::DomainTransitionGraphNode& dtg_node, const std::vector< const std::vector<std::pair<const MyPOP::SAS_Plus::BoundedAtom*, InvariableIndex> >* >& init_assignments);

	/**
	 * Add link from another node to this node. This means that this node can be reached through the given
	 * dtg_node.
	 */
	void addFromNode(const ReachableDTGNode& dtg_node); //, const std::vector<const BoundedAtom*>& reachable_facts);

	/**
	 * Add a link from this node to the given node.
	 */
	void addReachableNode(const ReachableDTGNode& dtg_node);
	
	/**
	 * Add facts to this node which are reachable from other nodes.
	 * @return True if the reachable facts have changed, false otherwise.
	 */
	bool addReachableFacts(const std::vector< const std::vector< std::pair< const MyPOP::SAS_Plus::BoundedAtom*, InvariableIndex > >* >& new_reachable_facts);
	
	void addTransition(ReachabilityTransition& reachable_transition);

	/**
	 * Get all nodes from which this node can be reached.
	 */
	const std::vector<const ReachableDTGNode*>& getReachableFromNodes() const { return reachable_from_; }

	/**
	 * Get all nodes reachable from this node.
	 */
	const std::vector<const ReachableDTGNode*>& getReachableNodes() const { return reachable_; }
	
	/**
	 * Get the DTG node this reachability node is linked to.
	 */
	const DomainTransitionGraphNode& getDTGNode() const { return *dtg_node_; }
	
	const std::vector<ReachabilityTransition*>& getTransitions() const { return transitions_; }

	/**
	 * Get all the facts which are reachable.
	 */
	const std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >& getReachableFacts() const { return reachable_facts_; }

private:
	ReachabilityAnalist* reachability_analist_;
	
	// All the nodes this node is reachable from.
	std::vector<const ReachableDTGNode*> reachable_from_;

	// All the nodes reachable from this node.
	std::vector<const ReachableDTGNode*> reachable_;

	// The DTG node this node is linked to.
	const DomainTransitionGraphNode* dtg_node_;

	// The values all domains can take.
	std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* > reachable_facts_;
	
	// All the transitions.
	std::vector<ReachabilityTransition*> transitions_;
};

std::ostream& operator<<(std::ostream& os, const ReachableDTGNode& reachable_dtg_node);

/**
 * 
 */
class ReachabilityTransition
{
public:
	ReachabilityTransition(ReachabilityAnalist& reachability_analist, const Transition& transition);
	
	/**
	 * Propagate the effects of applying this transition to its from node.
	 */
	bool propagateEffects(const std::vector< const MyPOP::LANDMARKS::Landmark* >& landmarks, const std::vector< const MyPOP::Atom* >& initial_facts);
	
	const Transition& getTransition() const { return *transition_; }

private:
	ReachabilityAnalist* reachability_analist_;
	
	const Transition* transition_;
};

/**
 * Given the initial state this class determines which DTG nodes can be reached and through which transitions.
 */
class ReachabilityAnalist
{

public:
	/**
	 * Constructor.
	 */
	ReachabilityAnalist(const DomainTransitionGraphManager& dtg_mamager);

	void initialiseReachablilityGraph(const std::vector<const Atom*>& initial_facts, const BindingsFacade& initial_fact_bindings);
	
	/**
	 * Construct the reachability graph by:
	 * 1) Mark all DTG nodes which are true in the initial state, add all transitions from these nodes in an open list.
	 * 2) For each transition from the open list check if the preconditions are met, i.e. is the DTG node marked?
	 * 2.1) If this is the case than mark the DTG node the transition led to and add all its transitions to the open list.
	 * 2.2) If this is not the case, than leave it in the open list for the next round.
	 * 3) Continue this until no new nodes can be marked.
	 */
	void constructReachablilityGraph(const std::vector< const MyPOP::LANDMARKS::Landmark* >& landmarks, const std::vector<const Atom*>& initial_facts);
	
	/**
	 * Declare that a node should not be used as a jump off point for transitions. That is to say, it can still be marked
	 * but none of its transitions will be added to the open list.
	 */
	void ignoreNode(const DomainTransitionGraphNode& dtg_node);
	
	/**
	 * Constrain the variable domains of the transitions. When we are looking for the first-achievers of a landmark
	 * we disallow that landmark to appear as a precondition in any transition. Adding this constraint will ensure
	 * no transition with the given constraint can be used to traverse the graph.
	 */
	void addTransitionConstraint(const BoundedAtom& bounded_atom);

	/**
	 * Clear all the nodes added by the ignoreNode function.
	 */
	void clearIgnoreList();
	
	/**
	 * Lookup the information of a DTG node after the analysis. If NULL is returned it means that the node is not reachable
	 * from the initial state with the conditions set by 'clearIgnoreList'.
	 */
	ReachableDTGNode* getReachableDTGNode(const DomainTransitionGraphNode& dtg_node);
	
	const std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>& getReachableDTGNodes() const { return reachable_nodes_; };

	/**
	 * Same as getReachableDTGNode, but only for internal use.
	 * @param dtg_node The underlying DTG node this reachability node is constructed for. If a reachability node already exists for the given
	 * DTG node we return that one instead of creating a new one.
	 * @param possible_assignments If this argument is given, a newly created reachability node will take these as the initial reachable 
	 * assignments to the variable domains of the underlying DTG node. If a reachability node was already created, however, this argument
	 * is ignored.
	 */
	ReachableDTGNode& createReachableDTGNode(const MyPOP::SAS_Plus::DomainTransitionGraphNode& dtg_node, const std::vector< const std::vector< std::pair< const MyPOP::SAS_Plus::BoundedAtom*, InvariableIndex > >* >* possible_assignments);
	
private:
	
	void initialiseTransitions();

	// The DTG manager from which we query DTGs and its nodes.
	const DomainTransitionGraphManager* dtg_manager_;

	// Mapping from DTG nodes to ReachableDTGNode, for easy lookup.
	std::map<const DomainTransitionGraphNode*, ReachableDTGNode*> reachable_nodes_;

	// All the nodes whos transitions we ignore.
	std::set<const DomainTransitionGraphNode*> ignore_list_;
	
	// All the prohibited preconditions.
	std::vector<const BoundedAtom*> transition_constrains_;
};

};

namespace Graphviz {

// Printing the reachability graph.
void printToDot(const SAS_Plus::ReachabilityAnalist& reachability_analysis, const std::vector<const LANDMARKS::Landmark*>& landmarks);
void printToDot(std::ofstream& ofs, const SAS_Plus::ReachableDTGNode& reachability_node);


};

};

#endif // SAS_PLUS_DTG_NODE_H
