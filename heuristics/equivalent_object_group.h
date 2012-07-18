#ifndef MYPOP_SAS_PLUS_EQUIVALENT_OBJECT_GROUP_H
#define MYPOP_SAS_PLUS_EQUIVALENT_OBJECT_GROUP_H

#include <map>
#include <vector>
#include <iosfwd>
#include <set>
#include <assert.h>
#include <stdio.h>

namespace MyPOP {

class Object;
class Predicate;
class TermManager;
class PredicateManager;

namespace UTILITY {
class MemoryPool;
}
	
namespace SAS_Plus {
class DomainTransitionGraph;
class DomainTransitionGraphManager;
};

namespace REACHABILITY {
class EquivalentObjectGroup;
class ReachableFact;

/**
 * The equivalent object class keeps track of a single object and its initial state. The initial state records both
 * the DTG the object is part of and all relations to other objects based on the predicates it is part of.
 */
class EquivalentObject
{
public:
	EquivalentObject(const Object& object, EquivalentObjectGroup& equivalent_object_group, unsigned int number_of_objects_in_domain);
	
	~EquivalentObject();
	
	void canReachInitialStateOf(const EquivalentObject& equivalent_object, unsigned int iteration);
	
	unsigned int getEquivalentIteration(const EquivalentObject& equivalent_object) const;

	void reset();
	
	EquivalentObjectGroup& getEquivalentObjectGroup() const { return *equivalent_group_; }
	
	void addInitialFact(ReachableFact& reachable_fact);
	
	const std::vector<const ReachableFact*>& getInitialFacts() const { return initial_facts_; }
	
	bool areEquivalent(const EquivalentObject& other) const;
	
	const Object& getObject() const { return *object_; }
	
	bool isInitialStateReachable(const std::vector<ReachableFact*>& reachable_facts) const;

private:
	
	const Object* object_;
	
	EquivalentObjectGroup* equivalent_group_;
	
	std::vector<const ReachableFact*> initial_facts_;
		
	unsigned int number_of_objects_in_domain_;
	unsigned int* is_super_set_of_at_iteration_;
	
	friend std::ostream& operator<<(std::ostream& os, const EquivalentObject& equivalent_object);
};

std::ostream& operator<<(std::ostream& os, const EquivalentObject& equivalent_object);

/**
 * Equivalent objects are object for which the following property holds:
 * If two equivalent objects A and B both can reach the same DTG node then all transitions which can be
 * applied to A can also be applied to B. This does not mean that all objects which belong to the same
 * equivalent object group can reach the same DTG nodes, this is only the case if the initial location
 * of A is reachable by B and vice versa.
 *
 * If an object A reaches the initial location of B we merge the equivalent object group of B with that
 * of A. If A can reach its initial DTG nodes than A and B are equivalent, but until that is proven B is
 * a sub set of A.
 *
 * Note: This is not implemented like this at the moment. Only when two objects are truly equivalent will
 * they become part of the the same EOG. Otherwise we will not be able to differentiate between two objects
 * which are part of the same EOG as the facts they can reach are dependable on its the initial state. Something
 * to do later :).
 */
class EquivalentObjectGroup
{
public:
	EquivalentObjectGroup(const std::vector<EquivalentObjectGroup*>& all_eogs, const SAS_Plus::DomainTransitionGraph& dtg_graph, const Object* object, bool is_grounded);

	~EquivalentObjectGroup();
	
	void reset();
	
	static void setMaxArity(unsigned int max_arity);
	
	//static void initMemoryPool(unsigned int max_arity);
	static void initMemoryPool();
	
	static void deleteMemoryPool();
	
	static EquivalentObjectGroup** allocateMemory(unsigned int size);

	void addEquivalentObject(EquivalentObject& eo);
	
	void addReachableFact(ReachableFact& reachable_fact);
	
	bool isRootNode() const;
	
	inline bool isGrounded() const { return is_grounded_; }
	inline bool isPartOfAPropertyState() const { return is_not_part_of_property_state_; }
	
	bool contains(const Object& object) const;
	bool contains(const Object& object, unsigned int iteration) const;
	
	bool isIdenticalTo(EquivalentObjectGroup& other);
	
	const std::vector<EquivalentObject*>& getEquivalentObjects() const { return equivalent_objects_; }
	
	bool hasSameFingerPrint(const EquivalentObjectGroup& other) const;
	
	const std::vector<ReachableFact*>& getReachableFacts() const { return reachable_facts_; }
	
	bool operator==(const EquivalentObjectGroup& other) const;
	bool operator!=(const EquivalentObjectGroup& other) const;
	
	/**
	 * As equivalent object groups are merged the merged node will become a child node of the node it got merged into. Internally
	 * we store this relationship which means that EOGs do not need to be deleted and any calls to the methods will automatically
	 * be redirected to the root node.
	 * @return The root node of this EOG.
	 */
	EquivalentObjectGroup& getRootNode();
	
	/**
	 * Remove all the reachable facts which have been marked for removal.
	 */
	void deleteRemovedFacts();
	
	void updateEquivalences(const std::vector<EquivalentObjectGroup*>& all_eogs, std::vector<EquivalentObjectGroup*>& affected_groups, unsigned int iteration, bool ground);
	
	std::vector<EquivalentObject*>::const_iterator begin(unsigned int layer_level) const;
	std::vector<EquivalentObject*>::const_iterator end(unsigned int layer_level) const;
	const EquivalentObjectGroup& getEOGAtLayer(unsigned int layer_level) const;
	
	void printObjects(std::ostream& os) const;
	void printObjects(std::ostream& os, unsigned int iteration) const;
	
	void printGrounded(std::ostream& os) const;

private:
	
	/**
	 * Try to merge the given objectGroup with this group. If the merge can take place, the other object place is merged with
	 * this one. We can merge two groups if the initial DTG node of this group is reachable from the initial DTG node of the other
	 * group and visa versa, and - in addition - if the types of the objects are the same.
	 * @param objectGroup The object group which we try to merge with this node.
	 * @return True if the groups could be merged, false otherwise.
	 */
	bool tryToMergeWith(EquivalentObjectGroup& object_group, std::vector<EquivalentObjectGroup*>& affected_groups, unsigned int iteration);
	
	static MyPOP::UTILITY::MemoryPool** g_eog_arrays_memory_pool_;
	
	static unsigned int max_arity_;
	
	static bool memory_pool_initialised_;
	
	// The set of objects which are equivalent.
	std::vector<EquivalentObject*> equivalent_objects_;

	// Flag to indicate if the object is grounded.
	bool is_grounded_;
	bool is_not_part_of_property_state_;
	
	// If the EOG is in use link_ is equal to NULL. Once it is made obsolete due to being merged with
	// another Equivalent Object Group link will link to that object instead.
	EquivalentObjectGroup* link_;
	
	// For the group of objects, we keep a list of reachable facts which can be achieved and contain the equivalent objects.
	std::vector<ReachableFact*> reachable_facts_;
	
	/**
	 * Every equivalent object group has a finger print which correlates to the terms of the facts in the DTG nodes
	 * the object can be a part of. At the moment we do not consider sub / super sets yet.
	 */
	void initialiseFingerPrint(const SAS_Plus::DomainTransitionGraph& dtg_graph, const Object& object);
	
	/**
	 * Merge the given group with this group.
	 */
	void merge(EquivalentObjectGroup& other_group, std::vector<EquivalentObjectGroup*>& affected_groups);
	
	// We only allow objects to be made equivalent if their finger prints match. The finger print is based on the object's membership in the 
	// lifted transition graph nodes.
	bool* finger_print_;
	unsigned int finger_print_size_;
	
	static unsigned int max_finger_print_id_;
	unsigned int finger_print_id_;
	
	// We keep track of both the size and when this EOG was merged. That way we can reconstruct the reachable facts 
	// which have been made true during each iteration.
	unsigned int merged_at_iteration_;
	std::vector<unsigned int> size_per_iteration_;

	friend std::ostream& operator<<(std::ostream& os, const EquivalentObjectGroup& group);
};

inline bool EquivalentObjectGroup::isRootNode() const
{
	return link_ == NULL;
}

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
	EquivalentObjectGroupManager(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::SAS_Plus::DomainTransitionGraph& dtg_graph, const MyPOP::TermManager& term_manager, const MyPOP::PredicateManager& predicate_manager);
	
	~EquivalentObjectGroupManager();
	
	void reset();
	
	void initialise(const std::vector<ReachableFact*>& initial_facts);
	
	/**
	 * Try to merge as many EOGs as possible.
	 * @param iteration The iteration we are currently at.
	 */
	void updateEquivalences(unsigned int iteration, bool ground);
	
	EquivalentObject& getEquivalentObject(const Object& object) const;
	
	EquivalentObjectGroup& getZeroArityEOG() const { return *zero_arity_equivalent_object_group_; }
	
	void getAllReachableFacts(std::vector<const ReachableFact*>& result) const;
	
	unsigned int getNumberOfEquivalentGroups() const;
	
private:
	
	/**
	 * Merge two equivalent groups and declare them identical.
	 */
	void merge(const Object& object1, const Object& object2);

	std::map<const Object*, EquivalentObject*> object_to_equivalent_object_mapping_;
	std::vector<EquivalentObjectGroup*> equivalent_groups_;
	
	EquivalentObjectGroup* zero_arity_equivalent_object_group_;
	
	friend std::ostream& operator<<(std::ostream& os, const EquivalentObjectGroupManager& group);
};

std::ostream& operator<<(std::ostream& os, const EquivalentObjectGroupManager& group);

};

};
#endif
