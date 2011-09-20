#ifndef MYPOP_SAS_PLUS_DTG_REACHABLITY_H
#define MYPOP_SAS_PLUS_DTG_REACHABLITY_H

#include <map>
#include <vector>
#include <iosfwd>
#include <set>
#include <assert.h>
#include <stdio.h>

#include "dtg_types.h"
#include "plan_types.h"
#include "dtg_node.h"
#include "dtg_manager.h"

namespace MyPOP {

class Atom;
class Bindings;
class Object;
class Predicate;
class TermManager;
	
namespace SAS_Plus {

class Property;
class PropertySpace;

class BoundedAtom;
class DomainTransitionGraph;
class DomainTransitionGraphNode;
class DTGReachability;
class Transition;

class DTGPropagator;
class EquivalentObjectGroup;
class EquivalentObjectGroupManager;

class ReachableFact
{
public:
	ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager);
	
	ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, EquivalentObjectGroup** term_domain_mapping_);
	
	bool conflictsWith(const std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>&) const;
	
	void updateMappings(std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>&) const;
	
	bool containsNonRootEOG() const;
	
	bool isEquivalentTo(const ReachableFact& other) const;
	
	bool isIdenticalTo(const ReachableFact& other) const;
	
	void printGrounded(std::ostream& os) const;
	
	void getAllReachableFacts(std::vector<const BoundedAtom*>& results) const;
	
	EquivalentObjectGroup& getTermDomain(unsigned int index) const
	{
		assert (index < bounded_atom_->getAtom().getArity());
		EquivalentObjectGroup* eog = term_domain_mapping_[index];
		assert (eog != NULL);
		return *eog;
	}
	
	void sanityCheck() const
	{
		assert (bounded_atom_ != NULL);
		bounded_atom_->print(std::cout, *bindings_);
		std::cout << std::endl;
		for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
		{
			EquivalentObjectGroup* eog = term_domain_mapping_[i];
			assert (eog != NULL);
		}
	}
	
	EquivalentObjectGroup** getTermDomains() const { return term_domain_mapping_; }
	
	const BoundedAtom& getBoundedAtom() const { return *bounded_atom_; }
	
	const Bindings& getBindings() const { return *bindings_; }
	
private:
	
	const BoundedAtom* bounded_atom_;
	const Bindings* bindings_;
	
	EquivalentObjectGroup** term_domain_mapping_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact);
};

std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact);

class ReachableNode
{
public:
	ReachableNode(const DomainTransitionGraphNode& dtg_node, const std::vector<const ReachableFact*>& supporting_facts)
		: dtg_node_(&dtg_node), supporting_facts_(&supporting_facts)
	{
		std::cout << "NEW REACHABLE NODE!!!!" << std::endl;
		assert (supporting_facts.size() == dtg_node_->getAtoms().size());
		
		std::cout << "New reachable node for: " << dtg_node << "." << std::endl;
		
		std::cout << "VAlidate reachable facts!" << std::endl;
		sanityCheck();
	}
	
	void sanityCheck() const
	{
		for (std::vector<const ReachableFact*>::const_iterator ci = supporting_facts_->begin(); ci != supporting_facts_->end(); ci++)
		{
			const ReachableFact* reachable_fact = *ci;
			assert (reachable_fact != NULL);
			for (unsigned int i = 0; i < (*ci)->getBoundedAtom().getAtom().getArity(); i++)
			{
				reachable_fact->getTermDomain(i);
			}
		}
	}
	
	bool isEquivalentTo(const ReachableNode& other) const;
	
	bool isIdenticalTo(const ReachableNode& other) const;
	
	const DomainTransitionGraphNode& getDTGNode() const { return *dtg_node_; }
	
	const ReachableFact& getSupportingFact(unsigned int i) const
	{
		assert (dtg_node_->getAtoms().size() > i);
		return *(*supporting_facts_)[i];
	}
	
	const std::vector<const ReachableFact*>& getSupportingFacts() const { return *supporting_facts_; };

private:
	
	const DomainTransitionGraphNode* dtg_node_;
	const std::vector<const ReachableFact*>* supporting_facts_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node);
};

std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node);

struct ReachableTransition
{
public:
	ReachableTransition(const Transition& transition)
		: transition_(&transition)
	{
		
	}
	
	void addMapping(const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& new_mapping);
	
	const std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >& getPossibleMappings() const { return possible_mappings_; }
	
private:
	const Transition* transition_;
	
	std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* > possible_mappings_;
};

/**
 * The equivalent object class keeps track of a single object and its initial state. The initial state records both
 * the DTG the object is part of and all relations to other objects based on the predicates it is part of.
 */
class EquivalentObject
{
public:
	EquivalentObject(const Object& object, EquivalentObjectGroup& equivalent_object_group);
	
	EquivalentObjectGroup& getEquivalentObjectGroup() const { return *equivalent_group_; }
	
	void addInitialFact(const ReachableFact& reachable_fact);
	
	const std::vector<const ReachableFact*>& getInitialFacts() const { return initial_facts_; }
	
	bool areEquivalent(const EquivalentObject& other) const;
	
	const Object& getObject() const { return *object_; }

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
	EquivalentObjectGroup(const DomainTransitionGraph& dtg_graph, const Object& object);
	
	void updateReachableFacts(const Object& object, const DomainTransitionGraphNode& dtg_node);
	
	bool makeReachable(const DomainTransitionGraphNode& dtg_node, const BoundedAtom& bounded_atom, ReachableFact& reachable_fact);
	
	void addEquivalentObject(const EquivalentObject& eo);
	
	void getSupportingFacts(std::vector<const ReachableFact*>& results, const DomainTransitionGraphNode& dtg_node, const BoundedAtom& bounded_atom) const;
	
	void getSupportingFacts(std::vector<const ReachableFact*>& results, const BoundedAtom& bounded_atom, const Bindings& bindings) const;
	
	bool isRootNode() const;
	
	bool contains(const Object& object) const;
	
	bool isIdenticalTo(EquivalentObjectGroup& other);
	
	const std::vector<const EquivalentObject*>& getEquivalentObjects() const { return equivalent_objects_; }
	
	/**
	 * Try to merge the given objectGroup with this group. If the merge can take place, the other object place is merged with
	 * this one. We can merge two groups if the initial DTG node of this group is reachable from the initial DTG node of the other
	 * group and visa versa, and - in addition - if the types of the objects are the same.
	 * @param objectGroup The object group which we try to merge with this node.
	 * @param reachable_nodes Reachability mapping from all DTG nodes.
	 * @return True if the groups could be merged, false otherwise.
	 */
	bool tryToMergeWith(EquivalentObjectGroup& object_group, const std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* >& reachable_nodes);
	
	
	bool operator==(const EquivalentObjectGroup& other) const;
	bool operator!=(const EquivalentObjectGroup& other) const;
	
	void printObjects(std::ostream& os) const;
	
	void printGrounded(std::ostream& os) const;
	
	void getAllReachableFacts(std::vector<const BoundedAtom*>& results) const;
	
private:
	
	/**
	 * As equivalent object groups are merged the merged node will become a child node of the node it got merged into. Internally
	 * we store this relationship which means that EOGs do not need to be deleted and any calls to the methods will automatically
	 * be redirected to the root node.
	 * @return The root node of this EOG.
	 */
	EquivalentObjectGroup& getRootNode();
	
	
	std::vector<const EquivalentObject*> equivalent_objects_;
	
	// All the facts which are reachable by all objects in this domain.
	std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*> reachable_facts_;
	
	// Map properties to the set of reachable facts.
	std::multimap<std::pair<std::string, unsigned int>, ReachableFact*> reachable_properties_;
	
	const DomainTransitionGraph* dtg_graph_;

	// If the EOG is in use link_ is equal to NULL. Once it is made obsolete due to being merged with
	// another Equivalent Object Group link will link to that object instead.
	EquivalentObjectGroup* link_;
	
	/**
	 * Every equivalent object group has a finger print which correlates to the terms of the facts in the DTG nodes
	 * the object can be a part of. At the mommnt we do not consider sub / super sets yet.
	 */
	void initialiseFingerPrint(const Object& object);
	
	/**
	 * Merge the given group with this group.
	 */
	void merge(EquivalentObjectGroup& other_group);
	
	bool* finger_print_;
	unsigned int finger_print_size_;

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
	
	EquivalentObject& getEquivalentObject(const Object& object) const;
	
	bool makeReachable(const DomainTransitionGraphNode&, const ReachableNode&);

	void getSupportingFacts(std::vector<const ReachableNode*>& results, const DomainTransitionGraphNode& dtg_node) const;
	
	void getSupportingFacts(std::vector<const ReachableFact*>& results, const BoundedAtom& bounded_atom, const Bindings& bindings) const;
	
	// Output methods.
	void print(std::ostream& os) const;
	
	void printAll(std::ostream& os) const;
	
	void getAllReachableFacts(std::vector<const BoundedAtom*>& results) const;
	
private:
	
	void deleteMergedEquivalenceGroups();
	
	/**
	 * Merge two equivalent groups and declare them identical.
	 */
	void merge(const Object& object1, const Object& object2);

	std::map<const Object*, EquivalentObject*> object_to_equivalent_object_mapping_;
	std::vector<EquivalentObjectGroup*> equivalent_groups_;
	
	std::multimap<const DomainTransitionGraphNode*, const ReachableNode*> supported_dtg_nodes_;
	
	const DTGReachability* dtg_reachability_;
	
	const DomainTransitionGraph* dtg_graph_;
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
	
	void performReachabilityAnalsysis(std::vector<const BoundedAtom*>& reachable_facts, const std::vector<const BoundedAtom*>& initial_facts, const TermManager& term_manager);

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
	
	ReachableTransition& getReachableTransition(const Transition& transition) const;
	
	void makeToNodeReachable(const Transition& transition, const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& possible_mapping) const;
		
private:
	
	bool canSatisfyPreconditions(const Transition& transition, const ReachableNode& supporting_fact, std::set<const std::vector<const Object*>* >& invariables) const;
	
	const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* canSatisfyPrecondition(std::vector<std::pair<const Atom*, InvariableIndex> >& all_preconditions, unsigned int index, const Transition& transition, std::set<const std::vector<const Object*>* >& invariables, std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& domain_variable_mapping) const;
	
	bool iterateTillFixPoint(DTGPropagator& propagator, std::vector<const BoundedAtom*>& established_facts, std::set<const Transition*>& achieved_transitions);
	
	/**
	 * This method is called every time a DTG node is reachable from another node. It effectively makes
	 * the from node a subset of the to node.
	 * @param dtg_node The DTG node for which we want to add a new set of supporting facts.
	 * @param reachable_facts The reachable facts.
	 */
	bool makeReachable(const DomainTransitionGraphNode& dtg_node, std::vector<const BoundedAtom*>& reachable_facts);
	
	bool handleExternalDependencies(std::vector<const BoundedAtom*>& established_facts);
	
	/**
	 * The combined DTG graph we are working on.
	 */
	const DomainTransitionGraph* dtg_graph_;
	
	/**
	 * Propagator.
	 */
	DTGPropagator* dtg_propagator_;
	
	/**
	 * Record for every DTG node which facts support it.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const BoundedAtom*>* >* > supported_facts_;
	
	/**
	 * Per node we record which nodes are reachable from it.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* > reachable_nodes_;
	
	EquivalentObjectGroupManager* equivalent_object_manager_;
	
	std::vector<const ReachableFact*> static_facts_;
	
	std::map<const Transition*, ReachableTransition*> reachable_transitions_;
};


/**
 * Clas which takes care of propagating reachable facts from transitions which have been proven to be possible.
 */
class DTGPropagator
{
public:
	DTGPropagator(DTGReachability& dtg_reachability, EquivalentObjectGroupManager& equivalent_object_manager, const DomainTransitionGraph& dtg_graph);

	void propagateReachableNodes();
	
private:
	
	void mapPossibleFacts(std::vector<const ReachableNode*>& results, const std::vector<const ReachableFact*>* cached_reachable_facts[], const DomainTransitionGraphNode& dtg_node, const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& mappings, const std::vector<const ReachableFact*>& assignments);
	
	DTGReachability* dtg_reachability_;
	
	EquivalentObjectGroupManager* equivalent_object_manager_;
	
	const DomainTransitionGraph* dtg_graph_;
	
	std::set<std::pair<const DomainTransitionGraphNode*, const ReachableNode*> > dtg_graph_closed_list_;
	std::set<std::pair<const Transition*, const ReachableNode*> > closed_list_;
};

};

};

#endif // MYPOP_SAS_PLUS_DTG_REACHABLITY_H