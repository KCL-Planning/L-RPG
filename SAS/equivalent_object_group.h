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
	
namespace SAS_Plus {

class DomainTransitionGraph;
class DomainTransitionGraphManager;
class EquivalentObjectGroup;
class ReachableFact;

/**
 * The equivalent object class keeps track of a single object and its initial state. The initial state records both
 * the DTG the object is part of and all relations to other objects based on the predicates it is part of.
 */
class EquivalentObject
{
public:
	EquivalentObject(const Object& object, EquivalentObjectGroup& equivalent_object_group);
	
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
	EquivalentObjectGroup(const DomainTransitionGraph& dtg_graph, const Object* object, bool is_grounded);
	
	~EquivalentObjectGroup();

	void addEquivalentObject(EquivalentObject& eo);
	
	void addReachableFact(ReachableFact& reachable_fact);
	
	bool isRootNode() const;
	
	inline bool isGrounded() const { return is_grounded_; }
	
	bool contains(const Object& object) const;
	
	bool isIdenticalTo(EquivalentObjectGroup& other);
	
	inline const std::vector<EquivalentObject*>& getEquivalentObjects() const { return equivalent_objects_; }
	
	bool hasSameFingerPrint(const EquivalentObjectGroup& other) const;
	
	inline const std::vector<ReachableFact*>& getReachableFacts() const { return reachable_facts_; }
	
	/**
	 * Try to merge the given objectGroup with this group. If the merge can take place, the other object place is merged with
	 * this one. We can merge two groups if the initial DTG node of this group is reachable from the initial DTG node of the other
	 * group and visa versa, and - in addition - if the types of the objects are the same.
	 * @param objectGroup The object group which we try to merge with this node.
	 * @return True if the groups could be merged, false otherwise.
	 */
	bool tryToMergeWith(EquivalentObjectGroup& object_group, std::vector<EquivalentObjectGroup*>& affected_groups);
	
	bool operator==(const EquivalentObjectGroup& other) const;
	bool operator!=(const EquivalentObjectGroup& other) const;
	
	void printObjects(std::ostream& os) const;
	
	void printGrounded(std::ostream& os) const;
	
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

private:
	
	// The set of objects which are equivalent.
	std::vector<EquivalentObject*> equivalent_objects_;

	// Flag to indicate if the object is grounded.
	bool is_grounded_;
	
	// If the EOG is in use link_ is equal to NULL. Once it is made obsolete due to being merged with
	// another Equivalent Object Group link will link to that object instead.
	EquivalentObjectGroup* link_;
	
	// For the group of objects, we keep a list of reachable facts which can be achieved and contain the equivalent objects.
	std::vector<ReachableFact*> reachable_facts_;
	
	/**
	 * Every equivalent object group has a finger print which correlates to the terms of the facts in the DTG nodes
	 * the object can be a part of. At the moment we do not consider sub / super sets yet.
	 */
	void initialiseFingerPrint(const DomainTransitionGraph& dtg_graph, const Object& object);
	
	/**
	 * Merge the given group with this group.
	 */
	void merge(EquivalentObjectGroup& other_group, std::vector<EquivalentObjectGroup*>& affected_groups);
	
	bool* finger_print_;
	unsigned int finger_print_size_;

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
	EquivalentObjectGroupManager(const DomainTransitionGraphManager& dtg_manager, const DomainTransitionGraph& dtg_graph, const TermManager& term_manager);
	
	~EquivalentObjectGroupManager();
	
	void initialise(const std::vector<ReachableFact*>& initial_facts);
	
	void updateEquivalences();
	
	EquivalentObject& getEquivalentObject(const Object& object) const;
	
	EquivalentObjectGroup& getZeroArityEOG() const { return *zero_arity_equivalent_object_group_; }
	
	void getAllReachableFacts(std::vector<const ReachableFact*>& result) const;
	
	unsigned int getNumberOfEquivalentGroups() const { return equivalent_groups_.size(); }
	
	// Output methods.
	void print(std::ostream& os) const;
	
	void printAll(std::ostream& os) const;
	
private:
	
	/**
	 * Merge two equivalent groups and declare them identical.
	 */
	void merge(const Object& object1, const Object& object2);

	std::map<const Object*, EquivalentObject*> object_to_equivalent_object_mapping_;
	std::vector<EquivalentObjectGroup*> equivalent_groups_;
	std::vector<EquivalentObjectGroup*> old_equivalent_groups_;
	
	EquivalentObjectGroup* zero_arity_equivalent_object_group_;
};

};

};
#endif
