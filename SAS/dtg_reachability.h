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
	
	ReachableFact(const Atom& atom, EquivalentObjectGroup** term_domain_mapping);
	
	/**
	 * This method is called everytime a merge has taken place which involves a Equivalent Object Group 
	 * which is part of this reachable fact. In such an occasion we end up with at least one term in this
	 * reachable fact which is no longer a root node (and thus yields incomplete information).
	 * 
	 * In order to fix this problem this method updates all the equivalent object group points so they link
	 * to the proper root node.
	 * 
	 * @return True if a Equivalent Object Group had to be updated, false otherwise.
	 * @note This function should always return true, we only want to call it if an update is due!
	 */
	bool updateTermsToRoot();
	
	/**
	 * Two reachable facts are equivalent iff:
	 * 1) All the objects have the same signature.
	 * 2) Those variables which have been labeled as unballanced must be identical.
	 */
	bool isEquivalentTo(const ReachableFact& other) const;
	
	/**
	 * Two reachable facts are identical iff:
	 * 1) All the objects have the same signature.
	 * 2) All variables are identical.
	 */
	bool isIdenticalTo(const ReachableFact& other) const;
	
	void printGrounded(std::ostream& os) const;
	
	void getAllReachableFacts(std::vector<const BoundedAtom*>& results) const;
	
	EquivalentObjectGroup& getTermDomain(unsigned int index) const
	{
		assert (index < atom_->getArity());
		EquivalentObjectGroup* eog = term_domain_mapping_[index];
		assert (eog != NULL);
		return *eog;
	}
	
	EquivalentObjectGroup** getTermDomains() const { return term_domain_mapping_; }
	
	const Atom& getAtom() const { return *atom_; }
	
	// Seee removed_flag_;
	void markForRemoval() { removed_flag_ = true; }
	
	bool isMarkedForRemoval() const { return removed_flag_; }
	
private:
	
	//const BoundedAtom* bounded_atom_;
	const Atom* atom_;
	
//	const Bindings* bindings_;
	
	EquivalentObjectGroup** term_domain_mapping_;
	
	// During the construction of the reachability graph terms can be merged and because of that some reachable facts are
	// removed because they have become identical to others. E.g. consider the following two reachable facts:
	//
	// * (at truck1 s1)
	// * (at truck2 s1)
	//
	// Suppose that truck1 and truck2 become equivalent, then we remove one of the two and update the other to:
	// * (at {truck1, truck2} s1)
	//
	// Reachable facts can be shared among multiple objects, so in this case the EOG linked to s1 will contain the following 
	// reachable facts:
	// * (at truck1 s1)
	// * (at {truck1, truck2} s1)
	//
	// By marking the former for removal we can remove the remaining reachable fact.
	bool removed_flag_;

	char mask_;
	
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
	
	ResolvedBoundedAtom(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager);
	
	ResolvedBoundedAtom(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager);
	
	const StepID getId() const { return id_; }
	
	const Atom& getAtom() const { return *atom_; }
	
	const std::vector<const Object*>& getVariableDomain(unsigned int index) const;
	
	bool isGrounded(unsigned int index) const;
	
	bool canUnifyWith(const ResolvedBoundedAtom& other) const;
	
private:
	
	StepID id_;
	
	const Atom* atom_;
	
	std::vector<const std::vector<const Object*>* > variable_domains_;
	
	bool* is_grounded_;
	
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

	/**
	 * Return all the sets of reachable facts which satisfy all the constraints and have a reachable fact 
	 * for every fact in the fact set.
	 */
	const std::vector<std::vector<ReachableFact*>* >& getReachableSets() const { return fully_reachable_sets_; }
	
	const std::vector<const ResolvedBoundedAtom*>& getFactsSet() const { return facts_set_; }
	
	/**
	 * A new reachable fact has been proven to be reachable. This function should only ever be
	 * called if that fact is actually relevant to this node.
	 * @param reachable_fact A new fact which is proven to be reachable.
	 * @param index The index of the set this fact can unify with.
	 */
	void processNewReachableFact(ReachableFact& reachable_fact, unsigned int index);
	
	virtual void print(std::ostream& os) const = 0;
	
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
	
private:
	
	/**
	 * After a new fact has been made reachable which wasn't part of this set yet, we try to generate
	 * new sets of reachable facts.
	 * @param reachable_sets_to_process A set to which the new fact has been added and needs to be expended
	 * with all possible other facts which match all the constraints.
	 */
	void generateNewReachableSets(std::vector<ReachableFact*>& reachable_sets_to_process);
	
	/**
	 * When we try to generate new sets of reachable facts we need to make sure that every set is consistent.
	 * For every set of facts, some variable domains are equal and if this is the case than the same relationship
	 * needs to hold for the assigned reachable facts. This method tests this relationship.
	 * @param reachable_fact The reachable facts which needs to be checked. It is not part yet of reachable_set so
	 * we test if it can be the ||reachable_set||th member by checking the constraints imposed on the facts which
	 * are already part of @ref reachable_set.
	 * @param reachable_set All the assignments made thus far, reachable fact is the ||reachable_set||th fact to be added.
	 * @return True if the constraints are consistent, false otherwise.
	 */
	bool canSatisfyConstraints(const ReachableFact& reachable_fact, std::vector<ReachableFact*>& reachable_set) const;
	
	// This is the set of bounded atoms which is either part of a Lifted Transition or is part of a
	// node of the Lifted Transition Graph.
	std::vector<const ResolvedBoundedAtom*> facts_set_;
	
	// For every bounded atom in this set, we store a list of reachable facts which can unify with
	// that bounded atom.
	std::vector<std::vector<ReachableFact*>*> reachable_set_;
	
	// Sets which are not fully constructed yet.
	std::vector<std::vector<ReachableFact*>* > wip_sets_;
	
	// All sets which are completely unitable are stored in the fully_reachable_sets.
	std::vector<std::vector<ReachableFact*>* > fully_reachable_sets_;
	
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
	
	bool propagateReachableFacts();
	
	void print(std::ostream& os) const;
	
private:
	
	const DomainTransitionGraphNode* dtg_node_;
	
	// All the transitions which have this node as from node.
	std::vector<ReachableTransition*> reachable_transitions_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node);
};

std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node);

/**
 * Used to map the variable of an action to the facts in either a reachable transition or a reachable node. We record
 * the indexes of the fact and the term which defines the value of the variable domain. The boolean value is there to
 * distinguish between variables which are defined by the transition(true) or node(false).
 */
struct VariableToValues
{
	VariableToValues(unsigned int fact_index, unsigned int term_index, bool is_transition)
		: fact_index_(fact_index), term_index_(term_index), is_transition_(is_transition)
	{
			
	}
	
	unsigned int fact_index_;
	unsigned int term_index_;
	bool is_transition_;
};

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
class ReachableTransition : public ReachableSet
{
public:
	ReachableTransition(const Transition& transition, const ReachableNode& from_node, const ReachableNode& to_node, const EquivalentObjectGroupManager& eog_manager);
	
	/**
	 * After all the reachable nodes and reachable transitions have been created we do one more post analysis and
	 * determine for every effect that can be generated which preconditions are satisfied by that.
	 */
	void finalise(const std::vector<ReachableSet*>& all_reachable_sets);
	
	/**
	 * Inititialise the structure by matching all the facts true in the initial state with the set of preconditions which are
	 * not part of the from node.
	 */
	void initialise(const std::vector<ReachableFact*>& initial_facts);
	
	/**
	 * Generate all the possible new reachable facts by combining the full sets of this reachable transition with those
	 * of its from node.
	 */
	void generateReachableFacts(std::vector<const ReachableFact*>& results);
	
	const Transition& getTransition() const { return *transition_; }
	
	void print(std::ostream& os) const;
private:
	
	const ReachableNode* from_node_;
	const ReachableNode* to_node_;
	
	const Transition* transition_;
	
	// To speed up the process we resolve all the variable domains of all the effects.
	std::vector<ResolvedBoundedAtom*> effects_;
	
	// Mapping from a variable to a reachable set containing its possible values.
	// The reachable set is accessed as: <fact index, term index>.
	std::map<const std::vector<const Object*>*, VariableToValues* > variable_to_values_mapping_;
	
	// For every effect we register all the ReachableSets for which the function processNewReachableFact must be called
	// when the effect is reached.
	std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* > effect_propagation_listeners_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition);
};

std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition);

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

};

};

#endif // MYPOP_SAS_PLUS_DTG_REACHABLITY_H