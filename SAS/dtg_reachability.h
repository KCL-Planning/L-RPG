#ifndef MYPOP_SAS_PLUS_DTG_REACHABLITY_H
#define MYPOP_SAS_PLUS_DTG_REACHABLITY_H

#include <map>
#include <vector>
#include <iosfwd>

namespace MyPOP {
	
class Object;
class TermManager;
	
namespace SAS_Plus {

class BoundedAtom;
class DomainTransitionGraph;
class DomainTransitionGraphNode;
class DTGReachability;

/**
 * Group together equivalent objects.
 */
class EquivalentObjectGroup
{
public:
	EquivalentObjectGroup(const Object& object);
	
	EquivalentObjectGroup(const Object& object, std::vector<const DomainTransitionGraphNode*>& initial_dtgs);
	
	/**
	 * Add an object and initial DTG node to this object group.
	 */
	bool addInitialDTGNodeMapping(const Object& object, const DomainTransitionGraphNode& dtg_node);
	
	/**
	 * Try to merge the given objectGroup with this group. If the merge can take place, the other object place is merged with
	 * this one. We can merge two groups if the initial DTG node of this group is reachable from the initial DTG node of the other
	 * group and visa versa, and - in addition - if the types of the objects are the same.
	 * @param objectGroup The object group which we try to merge with this node.
	 * @param reachable_nodes Reachability mapping from all DTG nodes.
	 * @return True if the groups could be merged, false otherwise.
	 */
	bool tryToMergeWith(const EquivalentObjectGroup& objectGroup, const std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* >& reachable_nodes);
	
private:
	
	/**
	 * Merge the given object group with this group.
	 * @param objectGroup The group that has to merge with this group.
	 */
	void mergeWith(const EquivalentObjectGroup& objectGroup);
	
	std::map<const Object*, std::vector<const DomainTransitionGraphNode*> *> initial_mapping_;
	
	friend std::ostream& operator<<(std::ostream& os, const EquivalentObjectGroup& group);
};

std::ostream& operator<<(std::ostream& os, const EquivalentObjectGroup& group);

/**
 * Manager the individual objects groups.
 */
class EquivalentObjectGroupManager
{
public:
	/**
	 * Initialise the individual groups.
	 */
	EquivalentObjectGroupManager(const DTGReachability& dtg_reachability, const DomainTransitionGraph& dtg_graph, const TermManager& term_manager, const std::vector<const BoundedAtom*>& initial_facts);
	
	void updateEquivalences(const std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* >& reachable_nodes_);
	
private:
	
	/**
	 * Merge two equivalent groups and declare them identical.
	 */
	void merge(const Object& object1, const Object& object2);

	std::map<const Object*, EquivalentObjectGroup*> object_to_equivalent_group_mapping_;
	std::vector<EquivalentObjectGroup*> equivalent_groups_;
	
	const DTGReachability* dtg_reachability_;
};
	
/**
 * Utility class to perform relaxed reachability analysis on a given DTG.
 */
class DTGReachability
{
public:
	/**
	 * Constructor.
	 */
	DTGReachability(const DomainTransitionGraph& dtg_graph);
	
	void performReachabilityAnalsysis(const std::vector<const BoundedAtom*>& initial_facts, const TermManager& term_manager);

	/** 
	 * Find all possible supports for @ref(atoms_to_achieve) from all the facts in @ref(initial_facts). Whilst working
	 * though this list all variable assignments are recorded in @ref(variable_assignments), all facts choosen for supporting the facts
	 * are stored in @ref(initial_supporting_facts). Each full valid assignment is stored in @ref(supporting_tupples).
	 * @param supporting_tupples All found sets which can be unified with all the items of @ref(atoms_to_achieve)
	 * are inserted in this vector.
	 * @param variable_assignments Maps variable domains to a set of objects which has been assigned to that domain. As the
	 * algorithm works through all the facts to be achieved it stores the assignments made so far and if an assignment
	 * cannot be made - there is a conflict - the algorithm will backtrack and try other assignments until it finds one
	 * which supports all the facts in @ref(atoms_to_achieve). This assignment is then added to @ref(supporting_tupples).
	 * @param atoms_to_achieve The set of facts we want to achieve.
	 * @param initial_supporting_facts Set of facts which support the atoms to achieve. This list will 
	 * progressively be filled with supporting facts. The size of this list determines which fact from
	 * @ref(atoms_to_achieve) to work on next (the initial_supporting_facts.size()'th fact to be precise).
	 * @param initial_facts List of facts which we know to be true. From this set the supporting facts will
	 * be drawn.
	 */
	void getSupportingFacts(std::vector<std::vector<const BoundedAtom*>* >& supporting_tupples, const std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >& variable_assignments, const std::vector<BoundedAtom*>& atoms_to_achieve, const std::vector<const BoundedAtom*>& initial_supporting_facts, const std::vector<const BoundedAtom*>& initial_facts) const;
	
private:
	
	/**
	 * After every iteration the reachable nodes are propagated through the graph.
	 */
	void propagateReachableNodes();
	
	/**
	 * This method is called every time a DTG node is reachable from another node. It effectively makes
	 * the from node a subset of the to node.
	 * @param from The DTG node from which the reachable transition starts.
	 * @param to The DTG node at which the reachable transtion ends.
	 */
	void makeReachable(const DomainTransitionGraphNode& from, const DomainTransitionGraphNode& to);
	
	/**
	 * The combined DTG graph we are working on.
	 */
	const DomainTransitionGraph* dtg_graph_;
	
	/**
	 * Record for every DTG node which facts support it.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const BoundedAtom*>* >* > supported_facts_;
	
	/**
	 * Per node we record which nodes are reachable from it.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* > reachable_nodes_;
	
	EquivalentObjectGroupManager* equivalent_object_manager_;
};

};

};

#endif // MYPOP_SAS_PLUS_DTG_REACHABLITY_H