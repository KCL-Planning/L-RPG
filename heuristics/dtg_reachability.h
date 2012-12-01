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
#include "reachable_tree.h"

namespace MyPOP {

class GroundedAtom;


class Atom;
class Bindings;
class Object;
class Predicate;
class TermManager;
class PredicateManager;

void printVariableDomain(ostream& os, const std::vector<const Object*>& result);
void takeIntersection(std::vector<const Object*>& result, const std::vector<const Object*>& set1, const std::vector<const Object*>& set2);
bool doVariableDomainsOverlap(const std::vector<const Object*>& set1, const std::vector<const Object*>& set2);

namespace SAS_Plus {

class Property;
class PropertySpace;

class BoundedAtom;
class DomainTransitionGraph;
class DomainTransitionGraphNode;
class Transition;

};

namespace HEURISTICS {
class FactSet;
class LiftedTransition;
class VariableDomain;
class TransitionFact;
};

namespace REACHABILITY {

class ReachableTree;
class DTGReachability;

class EquivalentObject;
class EquivalentObjectGroup;
class EquivalentObjectGroupManager;

class ReachableTransition;
class ReachableTreeNode;
class ReachableFactLayer;

class ReachableFactLayerItem;
	
class ReachableFact
{
public:
	static ReachableFact& createReachableFact(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager);
	
	static ReachableFact& createReachableFact(const Predicate& predicate, std::vector<EquivalentObjectGroup*>& term_domain_mapping);
	
	static ReachableFact& createReachableFact(const GroundedAtom& grounded_atom, const EquivalentObjectGroupManager& eog_manager);
	
	static ReachableFact& createReachableFact(const ReachableFact& reachable_fact);
	
	static void deleteAllReachableFacts(const std::vector< MyPOP::REACHABILITY::ReachableFact* >& initial_facts);
	
	~ReachableFact();
	
//	static void* operator new (size_t size);
	
//	static void operator delete (void* p);
	
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
	 * 2) Those variables which do not have the same index as @ref variant_eog or are unbalanced must be identical.
	 */
	bool isEquivalentTo(const ReachableFact& other, const EquivalentObjectGroup& variant_eog) const;
	
	/**
	 * Two reachable facts are identical iff:
	 * 1) All the objects have the same signature.
	 * 2) All variables are identical.
	 */
	bool isIdenticalTo(const ReachableFact& other) const;
	
	EquivalentObjectGroup& getTermDomain(unsigned int index) const;
	
//	EquivalentObjectGroup** getTermDomains() const { return term_domain_mapping_; }
	const std::vector<EquivalentObjectGroup*>& getTermDomains() const { return *term_domain_mapping_; }
	
//	const Atom& getAtom() const { return *atom_; }
	const Predicate& getPredicate() const { return *predicate_; }
	
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
	
	bool canUnifyWith(const Atom& atom, StepID step_id, const Bindings& bindings, unsigned int iteration) const;
	
	void print(std::ostream& os, unsigned int iteration) const;
	
private:
	
	static std::vector<const ReachableFact*> all_created_reachable_facts_;
	
	ReachableFact(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager);
	
	ReachableFact(const Predicate& predicate, std::vector<EquivalentObjectGroup*>& term_domain_mapping);
	
	ReachableFact(const GroundedAtom& grounded_atom, const EquivalentObjectGroupManager& eog_manager);
	
	ReachableFact(const ReachableFact& reachable_fact);
	
	ReachableFact& operator=(const ReachableFact& other);

	const Predicate* predicate_;
	
	//EquivalentObjectGroup** term_domain_mapping_;
	std::vector<EquivalentObjectGroup*>* term_domain_mapping_;
	
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

//static MyPOP::UTILITY::MemoryPool* g_reachable_fact_memory_pool = new MyPOP::UTILITY::MemoryPool(sizeof(ReachableFact));
//static MyPOP::UTILITY::MemoryPool* g_reachable_fact_memory_pool = NULL;


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
	ReachableSet(const EquivalentObjectGroupManager& eog_manager, const HEURISTICS::FactSet& fact_set);
	
	virtual void reset();
	
	virtual ~ReachableSet();
	
	const HEURISTICS::FactSet& getFactSet() const { return *fact_set_; }

	/**
	 * Return all the sets of reachable facts which satisfy all the constraints and have a reachable fact 
	 * for every fact in the fact set.
	 */
	const std::vector<ReachableTree*>& getReachableTrees() const { return reachability_tree_; }

	/**
	 * Per iteration, we keep track of the number of reachable facts which were made reachable prior to 
	 * that iteration. Thus we avoid using facts which were made reachable during that iteration. Calling 
	 * this function also caches the number of leafs.
	 * @return The highest index of the fact which was made true during the last iteration.
	 */
	unsigned int getCachedReachableTreesSize();
	
	void resetCachedReachableTreesSize()
	{
		cache_is_valid_ = false;
		getCachedReachableTreesSize();
	}
	
	const std::vector<std::list<ReachableFact*>* >& getReachableSets() const { return reachable_set_; }
	
	/**
	 * A new reachable fact has been proven to be reachable. This function should only ever be
	 * called if that fact is actually relevant to this node.
	 * @param reachable_fact A new fact which is proven to be reachable.
	 * @param index The index of the set this fact can unify with.
	 * @return True if a new reachable fact could be added, false if it was already part of the set.
	 */
	bool processNewReachableFact(ReachableFact& reachable_fact, unsigned int index);
	
	/**
	 * Initialise the reachable set by matching the initial facts.
	 * This method is only called once at the start of the reachability analysis, the rest is done through
	 * propagation.
	 */
	void initialiseInitialFacts(const std::vector<ReachableFact*>& initial_facts);
	
	const std::vector<std::vector<std::pair<unsigned int, unsigned int> >* >& getConstraints() const { return constraints_set_; }

	/**
	 * Called every time the equivalence relationships have been updated. All the ReachableFacts which 
	 * have been marked for removal need to be deleted.
	 */
	void equivalencesUpdated(unsigned int iteration);
	
private:
	
	const EquivalentObjectGroupManager* eog_manager_;
	
	const HEURISTICS::FactSet* fact_set_;
	
	// For every bounded atom in this set, we store a list of reachable facts which can unify with
	// that bounded atom.
	std::vector<std::list<ReachableFact*>*> reachable_set_;
	
	// All the facts which have been combined into a partial of complete assignment to all the facts in the set.
	std::vector<ReachableTree*> reachability_tree_;
	
	// We only allow access to the facts which were made true during the last iteration. These point to the highest index 
	// of the fact which was made true during the last iteration.
	unsigned int cached_reachability_tree_size_;
	bool cache_is_valid_;

	std::vector<std::vector<std::pair<unsigned int, unsigned int> >* > constraints_set_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableSet& reachable_set);
};

std::ostream& operator<<(std::ostream& os, const ReachableSet& reachable_set);

/**
 * Tupple to hold the results of creating effects.
 */
class AchievingTransition
{
public:
	AchievingTransition(unsigned int effect_index, unsigned int effect_set_index, const std::vector<const ReachableFact*>& preconditions, ReachableFact& fact, const ReachableTransition& achiever, const std::vector<HEURISTICS::VariableDomain*>& variable_assignments, const ReachableFactLayer& fact_layer);
	
	// Make sure the default copy constructor is not used!
	AchievingTransition(const AchievingTransition& achieving_transition);
	AchievingTransition(const AchievingTransition& achieving_transition, bool remove_copy_automatically);
	
	// For creating noops.
	static AchievingTransition& createNoop(const std::vector<const ReachableFactLayerItem*>& preconditions);
	
	static void removeAllAchievingTransitions();

	//AchievingTransition(const ReachableTransition& reachable_transition, const std::vector<const ReachableFactLayerItem*>& preconditions, const std::vector<const HEURISTICS::VariableDomain*>& variable_domains);
	
	~AchievingTransition();
	
	unsigned int getEffectIndex() const { return effect_index_; }
	
	unsigned int getEffectSetIndex() const { return effect_set_index_; }

	const std::vector<const ReachableFact*>& getPreconditions() const { return preconditions_; }
	
	const std::vector<const ReachableFactLayerItem*>& getPreconditionFactLayerItems() const { return preconditions_fact_layer_items_; }
	
	ReachableFact& getReachableFact() const { return *reachable_fact_; }
	
	const ReachableTransition* getAchiever() const { return achiever_; }
	
	const std::vector<HEURISTICS::VariableDomain*>& getVariableAssignments() const { return variable_assignments_; }
	
	/**
	 * Get the substitutions that need to be made to allow this action to achieve the given effect.
	 * @param needed_substituted The substitutions that need to be made are added to this list.
	 * @param reachable_fact The effect to be achieved with this action.
	 * @param object_bindings The constraints on the effect's variable domains.
	 * @param eog_manager The EOG manager.
	 * @param effect_set_index The index of the set the effect is a part of.
	 * @param effect_index The index of the effect in the effect set which can be achieved by this action.
	 */
	void getNeededSubstitutes(std::vector<std::pair<const EquivalentObject*, const EquivalentObject*> >& needed_substituted, const ReachableFactLayerItem& reachable_fact, std::vector<const Object*>** object_bindings, const EquivalentObjectGroupManager& eog_manager, unsigned int effect_set_index, unsigned int effect_index) const;
	
	/**
	 * Get the effect index which can achieve reachable_fact given the object binding constraints.
	 * @param reachable_fact The fact to achieve.
	 * @param object_bindings Every index of the fact to achieve is constrained by these sets of objects.
	 * @return (std::numeric_limits<unsigned int>, std::numeric_limits<unsigned int>) if the fact is not achievable by this fact, 
	 * otherwise (effect set index, effect index).
	 */
	std::pair<unsigned int, unsigned int> getEffectIndexAchieving(const ReachableFactLayerItem& reachable_fact, std::vector<const Object*>** object_bindings) const;
	
	/**
	 * Given this transition, update the variable domains so that it is constrained by the effect we 
	 * wish to achieve. However, we will leave any variable domain of the action whose intersection with 
	 * the variable domains of the given action is empty. 
	 * @param reachable_fact The effect we want to achieve with this action.
	 * @param object_bindings The bindings of the effect's variable domains.
	 * @param effect_set_index The index of the set the effect is a part of.
	 * @param effect_index The index of the effect in the effect set which can be achieved by this action.
	 */
	void updateVariablesToAchieve(const ReachableFactLayerItem& reachable_fact, std::vector<const Object*>** object_bindings, unsigned int effect_set_index, unsigned int effect_index) const;
	
private:
	
	AchievingTransition(const std::vector<const ReachableFactLayerItem*>& preconditions);
	
	unsigned int effect_index_; // The index of the fact in the reachable set.
	unsigned int effect_set_index_;
	std::vector<const ReachableFact*> preconditions_;
	std::vector<const ReachableFactLayerItem*> preconditions_fact_layer_items_;
	std::vector<const HEURISTICS::TransitionFact*> precondition_atoms_;
	ReachableFact* reachable_fact_;
	const ReachableTransition* achiever_;
	std::vector<HEURISTICS::VariableDomain*> variable_assignments_;
	
	static std::vector<const AchievingTransition*> all_created_achieving_transitions_;
};

std::ostream& operator<<(std::ostream& os, const AchievingTransition& executed_action);

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
class ReachableTransition
{
public:
	ReachableTransition(const HEURISTICS::LiftedTransition& lifted_transition, const std::vector<ReachableSet*>& preconditions, const std::vector<ReachableSet*>& effects);
	
	~ReachableTransition();
	
	void reset();
	
	const HEURISTICS::LiftedTransition& getTransition() const { return *transition_; }
	
	/**
	 * Generate all the possible new reachable facts by combining the full sets of this reachable transition with those
	 * of its from node.
	 */
	bool generateReachableFacts(const MyPOP::REACHABILITY::EquivalentObjectGroupManager& eog_manager, MyPOP::REACHABILITY::ReachableFactLayer& fact_layer, const std::vector< const MyPOP::REACHABILITY::ReachableFact* >& persistent_facts);
	
	void equivalencesUpdated(unsigned int iteration);
	
	void finalise(const std::vector<ReachableSet*>& all_reachable_sets);
	
	//void print(std::ostream& os) const;
private:
	
	//bool generateReachableFacts(const MyPOP::REACHABILITY::EquivalentObjectGroupManager& eog_manager, std::vector<const AchievingTransition* >& newly_created_reachable_facts, std::vector< const MyPOP::REACHABILITY::ReachableFact* >& preconditions, std::vector< MyPOP::REACHABILITY::EquivalentObjectGroup* >& current_variable_assignments, unsigned int precondition_index, MyPOP::REACHABILITY::ReachableFactLayer& fact_layer);
	void generateReachableFacts(const MyPOP::REACHABILITY::EquivalentObjectGroupManager& eog_manager, std::vector< const MyPOP::REACHABILITY::AchievingTransition* >& newly_created_reachable_facts, std::vector< const MyPOP::REACHABILITY::ReachableFact* >& preconditions, std::vector< MyPOP::REACHABILITY::EquivalentObjectGroup* >& current_variable_assignments, unsigned int precondition_index, MyPOP::REACHABILITY::ReachableFactLayer& fact_layer);
	
	const HEURISTICS::LiftedTransition* transition_;
	const std::vector<ReachableSet*>* preconditions_reachable_sets_;
	const std::vector<ReachableSet*>* effect_reachable_sets_;
	
	// Cache all the groups which have been processed so we do not create the same reachable facts from this
	// node over and over again.
	std::vector<const std::vector<EquivalentObjectGroup*>*> processed_groups_;
	
	std::vector<std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >* > effect_propagation_listeners_;
	
	// Instead of putting a new vector on the stack for a function call to createNewReachableFact, we simply use this one :).
	//const std::vector<ReachableFact*> empty_transition_reachable_set_;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition);
};

std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition);

class ReachableFactLayerItem
{
public:
	ReachableFactLayerItem(const ReachableFactLayer& reachable_fact_layer, const ReachableFact& reachable_fact);
	~ReachableFactLayerItem();
	
	bool canBeAchievedBy(const ResolvedBoundedAtom& precondition, StepID id, const Bindings& bindings, bool debug) const;
	
	//void addAchiever(const ReachableTransition& achiever, const ReachableTreeNode& from_tree_node, const ReachableTreeNode* transition_tree_node);
	//void addAchiever(const ReachableTransition& achiever, const std::vector<const ReachableFact*>& preconditions);
	//void addAchiever(const ReachableTransition& achiever, const std::vector<const ReachableFact*>& preconditions, const std::vector<const HEURISTICS::VariableDomain*>& variable_domains);
	
	void addAchiever(const AchievingTransition& achiever);
	
	void addNoop(const ReachableFactLayerItem& noop);
//	const std::vector<std::pair<const ReachableTransition*, std::vector<const ReachableFactLayerItem*>* > >& getAchievers() const { return achievers_; }
	const std::vector<const AchievingTransition*>& getAchievers() const { return achievers_; }
	
	const ReachableFact& getReachableFactCopy() const { return *reachable_fact_copy_; }
	const ReachableFact& getActualReachableFact() const { return *link_to_actual_reachable_fact_; }
	
	const ReachableFactLayer& getReachableFactLayer() const { return *reachable_fact_layer_; }
	
private:
	const ReachableFactLayer* reachable_fact_layer_;
	const ReachableFact* reachable_fact_copy_;
	const ReachableFact* link_to_actual_reachable_fact_;
	
	//std::vector<std::pair<const ReachableTransition*, std::vector<const ReachableFactLayerItem*>* > > achievers_;
	std::vector<const AchievingTransition*> achievers_;
};

std::ostream& operator<<(std::ostream& os, const ReachableFactLayerItem& reachable_fact_layer);

class ReachableFactLayer
{
public:
	ReachableFactLayer(unsigned int nr, const ReachableFactLayer* previous_layer);
	~ReachableFactLayer();
	//void finalise();
	
	void removeAllFacts();
	
	/**
	 * Add a fact to this fact to the layer without any achievers.
	 */
	void addFact(const ReachableFact& reachable_fact);
	void addFact(const AchievingTransition& achieved_transition, bool already_exists);
	const std::vector<ReachableFactLayerItem*>& getReachableFacts() const;
	const ReachableFactLayerItem* contains(const Atom& atom) const;
	unsigned int getLayerNumber() const;
	const ReachableFactLayer* getPreviousLayer() const;
	void extractPreconditions(std::vector<const ReachableFactLayerItem*>& preconditions, const ReachableTreeNode& reachable_set) const;
	const ReachableFactLayerItem* findPrecondition(const ReachableFact& reachable_fact) const;
private:
	unsigned int nr_;
	const ReachableFactLayer* previous_layer_;
	std::vector<ReachableFactLayerItem*> reachable_facts_;
};

class compareReachableFactLayerItem
{
public: 
	//bool operator() (std::pair<const ReachableFactLayerItem*, const Object**> lhs, std::pair<const ReachableFactLayerItem*, const Object**> rhs) const
	bool operator() (std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> lhs, std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> rhs) const
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
//	DTGReachability(const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const SAS_Plus::DomainTransitionGraph& dtg_graph, const TermManager& term_manager, PredicateManager& predicate_manager);

	DTGReachability(const std::vector<HEURISTICS::LiftedTransition*>& lifted_transitions, const TermManager& term_manager, PredicateManager& predicate_manager);
	
	~DTGReachability();
	
	/**
	 * Perform a reachability analysis and return the heuristic value.
	 * @param result All the facts which are reachable under the relexation constraint are added to this list.
	 * @param initial_facts All the facts which are tru in the initial state.
	 * @param bindings The bindings.
	 * @param persistent_facts These facts (which may or may not true in the initial state) cannot be made untrue. Any action which does so cannot be executed.
	 */
	//void performReachabilityAnalysis(std::vector<const ReachableFact*>& result, const std::vector<REACHABILITY::ReachableFact*>& initial_facts, const Bindings& bindings, const std::vector<const GroundedAtom*>& persistent_facts);
	void performReachabilityAnalysis(std::vector<const ReachableFact*>& result, const std::vector<REACHABILITY::ReachableFact*>& initial_facts, const std::vector<const GroundedAtom*>& persistent_facts);
	
	unsigned int getHeuristic(const std::vector< const GroundedAtom* >& bounded_goal_facts, MyPOP::PredicateManager& predicate_manager);
	
	EquivalentObjectGroupManager& getEquivalentObjectGroupManager() const { return *equivalent_object_manager_; }
	
	//const std::vector<std::pair<const Action*, std::vector<const Object*>**> >& getHelpfulActions() const { return helpful_actions_; }
	const std::vector<const AchievingTransition*>& getHelpfulActions() const { return helpful_actions_; }
	
	const ReachableFactLayer* getLastFactLayer() const { return current_fact_layer_; }
	
private:
	
	std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> createNewGoal(const Atom& resolved_goal);
	
	std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> findFactWhichAchieves(const MyPOP::REACHABILITY::ReachableFactLayerItem& current_goal, std::vector< const MyPOP::Object* >** object_bindings, std::set< std::pair< const MyPOP::REACHABILITY::EquivalentObject*, const MyPOP::REACHABILITY::EquivalentObject* > >& combined_eogs);
	
	unsigned int makeSubstitutions(const ReachableFactLayerItem& current_goal, std::vector< const MyPOP::Object* >** object_bindings, std::set< std::pair< const EquivalentObject*, const EquivalentObject* > >& made_substitutions);
	
	std::vector<ReachableTransition*> reachable_transition_;
	
	void mapInitialFactsToReachableSets(const std::vector<ReachableFact*>& initial_facts);
	
	const TermManager* term_manager_;
	
	std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >* predicate_id_to_reachable_sets_mapping_;

	EquivalentObjectGroupManager* equivalent_object_manager_;
	
	ReachableFactLayer* current_fact_layer_;
	
	//std::vector<std::pair<const Action*, std::vector<const Object*>**> > helpful_actions_;
	std::vector<const AchievingTransition*> helpful_actions_;
	
	std::map<const HEURISTICS::FactSet*, ReachableSet*> fact_set_to_reachable_set_;
};

};

};

#endif // MYPOP_SAS_PLUS_DTG_REACHABLITY_H
