#ifndef MYPOP_SAS_PLUS_DTG_REACHABLITY_H
#define MYPOP_SAS_PLUS_DTG_REACHABLITY_H

#include <map>
#include <vector>
#include <iosfwd>
#include <set>
#include <assert.h>
#include <stdio.h>

#include "sas/dtg_types.h"
#include "plan_types.h"
#include "sas/dtg_node.h"
#include "sas/dtg_manager.h"
#include "utility/memory_pool.h"

namespace MyPOP {

class Atom;
class Bindings;
class Object;
class Predicate;
class TermManager;
class PredicateManager;
	
namespace SAS_Plus {

class Property;
class PropertySpace;

class BoundedAtom;
class DomainTransitionGraph;
class DomainTransitionGraphNode;
class Transition;
};

namespace REACHABILITY {

class ReachableTree;
class DTGReachability;

class EquivalentObjectGroup;
class EquivalentObjectGroupManager;

class ReachableTransition;
class ReachableTreeNode;
class ReachableFactLayer;
	
class ReachableFact
{
public:
	ReachableFact(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager);
	
	ReachableFact(const Atom& atom, EquivalentObjectGroup** term_domain_mapping);
	
	ReachableFact(const ReachableFact& reachable_fact);
	
	~ReachableFact();
	
	static void* operator new (size_t size);
	
	static void operator delete (void* p);
	
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
	 * 2) Those variables which have been labeled as unbalanced must be identical.
	 */
	bool isEquivalentTo(const ReachableFact& other) const;
	
	/**
	 * Two reachable facts are identical iff:
	 * 1) All the objects have the same signature.
	 * 2) All variables are identical.
	 */
	bool isIdenticalTo(const ReachableFact& other) const;
	
	EquivalentObjectGroup& getTermDomain(unsigned int index) const;
	
	EquivalentObjectGroup** getTermDomains() const { return term_domain_mapping_; }
	
	const Atom& getAtom() const { return *atom_; }
	
	/**
	 * When updating the Equivalent Object Group, we need to update the Reachable Facts. We pick a single ReachableFact to update its 
	 * EOGs and create a link for all all reachable facts which are subsumed.
	 * @param replacement The ReachableFact which subsumes this reachable fact.
	 */
	void replaceBy(ReachableFact& replacement);
	
	/**
	 * Check if this reachable fact has been subsumed by another reachable fact. Call @ref getReplacement to get its replacement.
	 * @return True if this reachable fact has been subsumed, false otherwise.
	 */
	bool isMarkedForRemoval() const { return replaced_by_ != NULL; }
	
	/**
	 * @return The reachable fact which has subsumed this fact, or this if it has not been subsumed.
	 */
	const ReachableFact& getReplacement() const;
	
	void print(std::ostream& os, unsigned int iteration) const;
	
private:

	const Atom* atom_;
	
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
	ReachableFact* replaced_by_;
	
	//friend class ReachableFactMemoryPool;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact);
};

std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact);

static MyPOP::UTILITY::MemoryPool* g_reachable_fact_memory_pool = new MyPOP::UTILITY::MemoryPool(sizeof(ReachableFact));


/**
 * To improve the speed of the algorithms we want to eliminate all calls to any Bindings object. The nodes
 * of the DTG nodes will not change anymore so we can resolve all the bindings and refer to the variable domains
 * directly.
 */
class ResolvedBoundedAtom
{
public:
	
	ResolvedBoundedAtom(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager);
	
	~ResolvedBoundedAtom();
	
	const StepID getId() const { return id_; }
	
	const Atom& getOriginalAtom() const { return *atom_; }
	
	const Atom& getCorrectedAtom() const { return *corrected_atom_; }
	
	const std::vector<const Object*>& getVariableDomain(unsigned int index) const;
	
	bool isGrounded(unsigned int index) const;
	
	bool canUnifyWith(const ResolvedBoundedAtom& other) const;
	
	bool canSubstitude(const ReachableFact& reachable_fact) const;
	
protected:
	
	void init(const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager);
	
	StepID id_;
	
	const Atom* atom_;
	
	const Atom* corrected_atom_;
	
	std::vector<const std::vector<const Object*>* > variable_domains_;
	
	bool* is_grounded_;
};

std::ostream& operator<<(std::ostream& os, const ResolvedBoundedAtom& resolved_bounded_atom);

/**
 * To speed up the reachability analysis we resolve all the variable domains of the effects in advance.
 */
class ResolvedEffect : public ResolvedBoundedAtom
{
public:
	/**
	 * @param id The id by which the variable domains of the @ref atom are bound.
	 * @param atom The atom of the effect.
	 * @param bindings The class which holds all the bindings.
	 * @param eog_manager The EOG manager.
	 * @param free_variables An array which indicates which indexes of the atom are free variables. For these we look at the type of the variable and
	 * search for all EOGs in the @ref eog_manager which match the bill.
	 * @param predicate_manager The predicate manager.
	 */
	ResolvedEffect(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, bool free_variables[], PredicateManager& predicate_manager);
	
	~ResolvedEffect();
	
	/**
	 * After the EOGs have been updated, we need to update the free variables to point to the merged EOGs.
	 */
	void updateVariableDomains();
	
	/**
	 * @return True if the variable at the given index is a free variable, false otherwise.
	 */
	bool isFreeVariable(unsigned int index) const;
	
	bool containsFreeVariables() const { return free_variables_.size() != 0; }
	
	/**
	 * Given the @ref effect_domains create new reachable facts and store them in @ref results.
	 * @param results A vector in which all the  generated reachable facts will be put.
	 * @param effect_domains An array of EOGs whose index match that of the effect. Using this one-to-one mapping 
	 * the new reachable facts are produced.
	 */
	void createReachableFacts(std::vector<ReachableFact*>& results, EquivalentObjectGroup** effect_domains) const;
	
private:
	// Array with length equal to that of the effect's atom's arity.
	bool* is_free_variable_;
	
	// The terms which are free.
	std::vector<const Term*> free_variables_;
	
	// For every free variable we record it's domain.
	std::vector<std::vector<EquivalentObjectGroup*>* > free_variable_domains_;
	
	// Links every index of this effect's atom to the variable of the action it is part of. If the index is a free 
	// variable, the variable's index it is linked to is equal to the action's arity (thus out of bounds!).
	int* index_to_variable_;
};

std::ostream& operator<<(std::ostream& os, const ResolvedEffect& resolved_bounded_atom);

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
	
	virtual ~ReachableSet();
	
	bool arePreconditionsEquivalent(const ReachableSet& other_set) const;

	/**
	 * Return all the sets of reachable facts which satisfy all the constraints and have a reachable fact 
	 * for every fact in the fact set.
	 */
	const std::vector<ReachableTree*>& getReachableTrees() const { return reachability_tree_; }

	/**
	 * Per iteration, we keep track of the number of reachable facts which were made reachable prior to 
	 * that iteration. Thus we avoid using facts which were made reachable during that iteration.
	 * @return The highest index of the fact which was made true during the last iteration.
	 */
	unsigned int getCachedReachableTreesSize()
	{
		if (!cache_is_valid_)
		{
			cached_reachability_tree_size_ = reachability_tree_.size();
			cache_is_valid_ = true;
		}
		
		return cached_reachability_tree_size_;
	}
	
	void resetCachedReachableTreesSize()
	{
		cache_is_valid_ = false;
		getCachedReachableTreesSize();
	}
	
	const std::vector<std::list<ReachableFact*>* >& getReachableSets() const { return reachable_set_; }
	
	const std::vector<const ResolvedBoundedAtom*>& getFactsSet() const { return facts_set_; }
	
	/**
	 * A new reachable fact has been proven to be reachable. This function should only ever be
	 * called if that fact is actually relevant to this node.
	 * @param reachable_fact A new fact which is proven to be reachable.
	 * @param index The index of the set this fact can unify with.
	 * @return True if a new reachable fact could be added, false if it was already part of the set.
	 */
	bool processNewReachableFact(ReachableFact& reachable_fact, unsigned int index);
	
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
	void addBoundedAtom(StepID step_id, const Atom& atom, const Bindings& bindings, PredicateManager& predicate_manager);
	
	/**
	 * Called every time the equivalence relationships have been updated. All the ReachableFacts which 
	 * have been marked for removal need to be deleted.
	 */
	virtual void equivalencesUpdated(unsigned int iteration);
	
private:
	
	/**
	 * After a new fact has been made reachable which wasn't part of this set yet, we try to generate
	 * new sets of reachable facts.
	 * @param reachable_sets_to_process A set to which the new fact has been added and needs to be expended
	 * with all possible other facts which match all the constraints.
	 * @return True if new reachable facts could be created, false otherwise.
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
	
	bool tryToFindMapping(bool* mapping, unsigned int index, const ReachableSet& other_set) const;
	
	// This is the set of bounded atoms which is either part of a Lifted Transition or is part of a
	// node of the Lifted Transition Graph.
	std::vector<const ResolvedBoundedAtom*> facts_set_;
	
	// For every bounded atom in this set, we store a list of reachable facts which can unify with
	// that bounded atom.
	std::vector<std::list<ReachableFact*>*> reachable_set_;
	
	// All the facts which have been combined into a partial of complete assignment to all the facts in the set.
	std::vector<ReachableTree*> reachability_tree_;
	
	// We only allow access to the facts which were made true during the last iteration. These point to the highest index 
	// of the fact which was made true during the last iteration.
	unsigned int cached_reachability_tree_size_;
	bool cache_is_valid_;
	
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
	ReachableNode(const SAS_Plus::DomainTransitionGraphNode& dtg_node, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager);
	
	virtual ~ReachableNode();

	/**
	 * Inititialise the structure by matching all the facts true in the initial state with both the set of nodes
	 * in this node, but also with all the transitions linked to this node.
	 */
	void initialise(const std::vector<ReachableFact*>& initial_facts);
	
	const SAS_Plus::DomainTransitionGraphNode& getDTGNode() const { return *dtg_node_; }
	
	void addReachableTransition(ReachableTransition& reachable_transition);
	
	bool propagateReachableFacts(ReachableFactLayer& current_fact_layer);

	void equivalencesUpdated(unsigned int iteration);
	
	std::vector<ReachableTransition*>& getReachableTransitions() { return reachable_transitions_; }
	
	void print(std::ostream& os) const;
	
private:
	
	const SAS_Plus::DomainTransitionGraphNode* dtg_node_;
	
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
	ReachableTransition(const SAS_Plus::Transition& transition, ReachableNode& from_node, const ReachableNode& to_node, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager);
	
	virtual ~ReachableTransition();
	
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
	bool generateReachableFacts(ReachableFactLayer& fact_layer);
	
	void equivalencesUpdated(unsigned int iteration);
	
	const SAS_Plus::Transition& getTransition() const { return *transition_; }
	
	ReachableNode& getFromNode() const { return *from_node_; }
	const ReachableNode& getToNode() const { return *to_node_; }
	
	static unsigned int generated_new_reachable_facts;
	static unsigned int accepted_new_reachable_facts;

	
	void print(std::ostream& os) const;
private:
	
	ReachableNode* from_node_;
	const ReachableNode* to_node_;
	
	const SAS_Plus::Transition* transition_;
	
	// To speed up the process we resolve all the variable domains of all the effects.
	std::vector<ResolvedEffect*> effects_;
	
	// Mapping from a variable to a reachable set containing its possible values.
	// The reachable set is accessed as: <fact index, term index>.
	std::map<const std::vector<const Object*>*, VariableToValues* > variable_to_values_mapping_;
	
	std::map<const std::vector<const Object*>*, unsigned int > domain_to_action_variable_mapping_;
	
	// For every effect we register all the ReachableSets for which the function processNewReachableFact must be called
	// when the effect is reached.
	std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* > effect_propagation_listeners_;
	
	// Cache all the groups which have been processed so we do not create the same reachable facts from this
	// node over and over again.
	std::vector<EquivalentObjectGroup**> processed_groups_;
	
	/**
	 * Called by the generateReachableFacts method. Once we have two complete sets of facts, one containing a mapping to all 
	 * facts in the from node and one containing all the facts which are hold by the reachable transition we combine the 
	 * assignments made to the variables to construct the set of effects.
	 * @param effect The effect we try to construct.
	 * @param effect_index The index of the effect of the original transition.
	 * @param from_node_reachable_set The full set of assignments to the facts in the from node.
	 * @param transition_reachable_set The full set of assignments to the facts in the transition.
	 * @return True if a new effect could be created (i.e. it wasn't already created previously), false otherwise.
	 */
	bool createNewReachableFact(const ResolvedEffect& effect, unsigned int effect_index, const ReachableTreeNode& from_reachable_node, const ReachableTreeNode* transition_reachable_node, ReachableFactLayer& current_fact_layer);
	
	// To speed up the createNewReachableFact method we keep track of all the combinations of sets we have already combined 
	// in the past so we don't redo the same thing.
	unsigned int latest_processed_from_node_set_;
	unsigned int latest_processed_transition_set_;
	
	// To speed things up we reuse created arrays of OEGs - used to compare if a similar array was already constructed.
	// See the generateReachableFacts method.
	bool use_previous_action_domains_;
	EquivalentObjectGroup** action_domains_;
	
	// Instead of putting a new vector on the stack for a function call to createNewReachableFact, we simply use this one :).
	const std::vector<ReachableFact*> empty_transition_reachable_set_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition);
};

std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition);
/*
class ActionLayerItem
{
public:
	
private:
	const ReachableTransition* achiever_;
	const std::vector<const ReachableFactLayerItem*> effects_;
};

class ActionLayer
{
public:
	
private:
	
};
*/

class ReachableFactLayerItem
{
public:
	ReachableFactLayerItem(const ReachableFactLayer& reachable_fact_layer, const ReachableFact& reachable_fact);
	~ReachableFactLayerItem();
	
	void addAchiever(const ReachableTransition& achiever, const ReachableTreeNode& from_tree_node, const ReachableTreeNode* transition_tree_node);
	const std::vector<std::pair<const ReachableTransition*, std::vector<const ReachableFactLayerItem*>* > >& getAchievers() const { return achievers_; }
	
	const ReachableFact& getReachableFactCopy() const { return *reachable_fact_copy_; }
	const ReachableFact& getActualReachableFact() const { return *link_to_actual_reachable_fact_; }
	
	const ReachableFactLayer& getReachableFactLayer() const { return *reachable_fact_layer_; }
	
private:
	const ReachableFactLayer* reachable_fact_layer_;
	const ReachableFact* reachable_fact_copy_;
	const ReachableFact* link_to_actual_reachable_fact_;
	
	std::vector<std::pair<const ReachableTransition*, std::vector<const ReachableFactLayerItem*>* > > achievers_;
};

class ReachableFactLayer
{
public:
	ReachableFactLayer(unsigned int nr, const ReachableFactLayer* previous_layer);
	void addFact(const ReachableFact& reachable_fact);
	void addFact(const ReachableFact& reachable_fact, const ReachableTransition& achiever, const ReachableTreeNode& from_tree_node, const ReachableTreeNode* transition_tree_node, bool already_exists);
	const std::vector<ReachableFactLayerItem*>& getReachableFacts() const;
	const ReachableFactLayerItem* contains(const ResolvedBoundedAtom& resolved_bounded_atom) const;
	unsigned int getLayerNumber() const;
	const ReachableFactLayer* getPreviousLayer() const;
	void extractPreconditions(std::vector<const ReachableFactLayerItem*>& preconditions, const ReachableTreeNode& reachable_set) const;
	const ReachableFactLayerItem& findPrecondition(const ReachableFact& reachable_fact) const;
private:
	unsigned int nr_;
	const ReachableFactLayer* previous_layer_;
	std::vector<ReachableFactLayerItem*> reachable_facts_;
};

class compareReachableFactLayerItem
{
public: 
	bool operator() (std::pair<const ReachableFactLayerItem*, const Object**> lhs, std::pair<const ReachableFactLayerItem*, const Object**> rhs) const
	{
		return (lhs.first->getReachableFactLayer().getLayerNumber() < rhs.first->getReachableFactLayer().getLayerNumber());
	}
};

std::ostream& operator<<(std::ostream& os, const ReachableFactLayer& reachable_fact_layer);

/**
 * Utility class to perform relaxed reachability analysis on a given DTG.
 */
class DTGReachability
{
public:
	/**
	 * Constructor.
	 */
	DTGReachability(const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const SAS_Plus::DomainTransitionGraph& dtg_graph, const TermManager& term_manager, PredicateManager& predicate_manager);
	
	~DTGReachability();
	
	/**
	 * Perform a reachability analysis and return the heuristic value.
	 */
	void performReachabilityAnalysis(std::vector<const ReachableFact*>& result, const std::vector<const SAS_Plus::BoundedAtom*>& initial_facts, const Bindings& bindings);
	
	unsigned int getHeuristic(const std::vector<const SAS_Plus::BoundedAtom*>& bounded_goal_facts, const Bindings& bindings, PredicateManager& predicate_manager) const;
	
	const EquivalentObjectGroupManager& getEquivalentObjectGroupManager() const { return *equivalent_object_manager_; }
	
private:
	
	void mapInitialFactsToReachableSets(const std::vector<ReachableFact*>& initial_facts);
	
	const TermManager* term_manager_;
	
	// The set of nodes we are working on.
	std::vector<ReachableNode*> reachable_nodes_;
	
	std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >* predicate_id_to_reachable_sets_mapping_;

	EquivalentObjectGroupManager* equivalent_object_manager_;
	
	ReachableFactLayer* current_fact_layer_;
};

};

};

#endif // MYPOP_SAS_PLUS_DTG_REACHABLITY_H
