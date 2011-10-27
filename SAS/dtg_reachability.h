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

class ReachableTransition;

class ReachableFact
{
public:
	ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager);
	
	ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, EquivalentObjectGroup** term_domain_mapping);
	
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

/**
 * To improve the speed of the algorithms we want to eliminate all calls to any Bindings object. The nodes
 * of the DTG nodes will not change anymore so we can resolve all the bindings and refer to the variable domains
 * directly.
 */
class ResolvedBoundedAtom
{
public:
	
	ResolvedBoundedAtom(const BoundedAtom& bounded_atom, const Bindings& bindings);
	
	const Atom& getAtom() const { return *atom_; }
	
	const std::vector<const Object*>& getVariableDomain(unsigned int index) const;
	
private:
	
	const Atom* atom_;
	
	std::vector<const std::vector<const Object*>* > variable_domains_;
	
};

/**
 * During the reachability algorithm we try to find all the sets of reachable facts which can unify with
 * either the set of preconditions of a reachable transition or with the set of preconditions in a node.
 *
 * Because we work with lifted atoms we cannot create an array of all possible reachable facts and link 
 * them with all the preconditions of the actions which require these facts. This is because this would
 * actually require us to ground. Instead we store the set of all reachable facts which can unify with 
 * every bounded atom in the set and then try to form sets of reachable facts which can unify with all 
 * bounded atoms in the set.
 */
class ReachableSet
{
public:
	/**
	 * Default constructor.
	 */
	ReachableSet(const EquivalentObjectGroupManager& eog_manager);
	
protected:
	const EquivalentObjectGroupManager* eog_manager_;
	
	/**
	 * Initialise the reachable set by matching the initial facts.
	 * This method is only called once at the start of the reachability analysis, the rest is done through
	 * propagation.
	 */
	void initialiseInitialFacts(const std::vector<ReachableFact*>& initial_facts);

	/**
	 * All subclasses can add a set of bounded atoms which are the set or preconditions
	 * which are part of their set.
	 */
	void addBoundedAtom(const BoundedAtom& bounded_atom, const Bindings& bindings);
	
	/**
	 * A new reachable fact has been proven to be reachable. This function should only ever be
	 * called if that fact is actually relevant to this node.
	 * @param reachable_fact A new fact which is proven to be reachable.
	 * @param index The index of the set this fact can unify with.
	 */
	void processNewReachableFact(const ReachableFact& reachable_fact, unsigned int index);
	
private:
	
	/**
	 * After a new fact has been made reachable which wasn't part of this set yet, we try to generate
	 * new sets of reachable facts.
	 * @param reachable_sets_to_process A set to which the new fact has been added and needs to be expended
	 * with all possible other facts which match all the constraints.
	 */
	void generateNewReachableSets(std::vector<const ReachableFact*>& reachable_sets_to_process);
	
	/**
	 * When we try to generate new sets of reachable facts we need to make sure that every set is consistent.
	 * For every set of facts, some variable domains are equal and if this is the case than the same relationship
	 * needs to hold for the assigned reachable facts. This method tests this relationship.
	 * @param reachable_fact The reachable facts which needs to be checked.
	 * @param reachble_set All the assignments made thus far, reachable fact is the ||reachable_set||th fact to be added.
	 * @return True if the constraints are consistent, false otherwise.
	 */
	bool canSatisfyConstraints(const ReachableFact& reachable_fact, std::vector<const ReachableFact*>& reachable_set) const;
	
	// This is the set of bounded atoms which is either part of a Lifted Transition or is part of a
	// node of the Lifted Transition Graph.
	std::vector<const ResolvedBoundedAtom*> facts_set_;
	
	// For every bounded atom in this set, we store a list of reachable facts which can unify with
	// that bounded atom.
	std::vector<std::vector<const ReachableFact*>*> reachable_set_;
	
	// All sets which are completely unitable are stored in the fully_reachable_sets.
	std::vector<std::vector<const ReachableFact*>* > fully_reachable_sets_;
	
	// When generating the reachable sets we need to make sure the constraints are satisfied, so for 
	// every atom in the fact set we record for every index which other indexes of other facts must
	// be the same.
	std::vector<std::vector<std::pair<unsigned int, unsigned int> >** > constraints_set_;
};

/**
 * To speed up the reachability, we create a ReachableNode object for every node in the Lifted Tranition
 * Graph.
 */
class ReachableNode : public ReachableSet
{
public:
	ReachableNode(const DomainTransitionGraphNode& dtg_node, const EquivalentObjectGroupManager& eog_manager);

	/**
	 * Inititialise the structure by matching all the facts true in the initial state with both the set of nodes
	 * in this node, but also with all the transitions linked to this node.
	 */
	void initialise(const std::vector<ReachableFact*>& initial_facts);
	
	const DomainTransitionGraphNode& getDTGNode() const { return *dtg_node_; }
	
	void addReachableTransition(ReachableTransition& reachable_transition);
	
private:
	
	const DomainTransitionGraphNode* dtg_node_;
	
	// All the transitions which have this node as from node.
	std::vector<ReachableTransition*> reachable_transitions_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node);
};

std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node);

/**
 * When a transition is reachable we state that the transition is reachable for all possible mappings of the from node
 * of that transition. However, we need to keep track of all the domains of variables which are not present in the from node.
 * for example:
 *
 * (at truck loc) -> (driving driver truck) (at truck loc)
 *
 * we need to know the value of driver which - in this case - is bounded by the precondition (at driver loc). Since loc is 
 * grounded we only need to lookup all the values of driver at that location and insert it.
 */
struct ReachableTransition : public ReachableSet
{
public:
	ReachableTransition(const Transition& transition, const ReachableNode& from_node, const ReachableNode& to_node, const EquivalentObjectGroupManager& eog_manager);
	
	/**
	 * Inititialise the structure by matching all the facts true in the initial state with the set of preconditions which are
	 * not part of the from node.
	 */
	void initialise(const std::vector<ReachableFact*>& initial_facts);
private:
	
	const ReachableNode* from_node_;
	const ReachableNode* to_node_;
	
	const Transition* transition_;
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
	DTGReachability(const DomainTransitionGraphManager& dtg_manager, const DomainTransitionGraph& dtg_graph, const TermManager& term_manager);
	
	void performReachabilityAnalsysis(std::vector<const ReachableFact*>& result, const std::vector<const BoundedAtom*>& initial_facts, const Bindings& bindings);

	ReachableTransition& getReachableTransition(const Transition& transition) const;
	
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

	const TermManager* term_manager_;
	
	// The set of nodes we are working on.
	std::vector<ReachableNode*> reachable_nodes_;
	
	std::vector<ReachableFact*> established_reachable_facts_;
	
	/**
	 * Propagator.
	 */
	DTGPropagator* dtg_propagator_;
	
	/**
	 * Record for every DTG node which facts support it.
	 */
	//std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const BoundedAtom*>* >* > supported_facts_;
	
	/**
	 * Per node we record which nodes are reachable from it.
	 */
	//std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* > reachable_nodes_;
	
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