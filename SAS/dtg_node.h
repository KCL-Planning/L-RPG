#ifndef SAS_PLUS_DTG_NODE_H
#define SAS_PLUS_DTG_NODE_H

#include <map>
#include <set>
#include <vector>
#include <iostream>
#include <limits>

#include "../plan_types.h"
#include "dtg_types.h"

namespace MyPOP {

class Atom;
class Action;
class Term;
class Bindings;
class Object;

namespace SAS_Plus {

class DomainTransitionGraph;
class Transition;
class BoundedAtom;
class DomainTransitionGraphNode;

/**
 * All possible values a state variable can take are stored in DTG nodes. We use a lifted
 * SAS+ representation so every node might correspond to multiple possible values a state
 * variable can be assigned to. The possible values depend on:
 * 1) The atoms (thus predicates) of this node.
 * 2) The bindings enforced on the variables of these atoms. These can be retrieved from the
 * bindings object and the VariableDomains assigned to the variables.
 */
class DomainTransitionGraphNode
{
public:
	DomainTransitionGraphNode(DomainTransitionGraph& dtg, unsigned int unique_id);

	/**
	 * Make a copy of an existing DTG node. We inherrit the same domain for the variables and atom,
	 * but it is in no way linked to the node it is copied from. All the transitions from the given
	 * node are copied as are all transitions to the other node.
	 */
	DomainTransitionGraphNode(const DomainTransitionGraphNode& dtg_node);
	
	/**
	 * Make a copy of an existing DTG node. We inherrit the same domain for the variables and atom,
	 * but it is in no way linked to the node it is copied from. None of the transitions are copied
	 * but the node is linked given DTG, but not added to it!
	 */
	DomainTransitionGraphNode(const DomainTransitionGraphNode& dtg_node, DomainTransitionGraph& dtg);
	
	~DomainTransitionGraphNode();

	/**
	 * Add an atom to this node.
	 * @param bounded_atom The atom to add.
	 * @param index The index which is considered to be invariable (depricated!).
	 * @return True if the atom was added, false if the atom was already part of this node.
	 */
	bool addAtom(BoundedAtom& bounded_atom, InvariableIndex index);
	
	/**
	 * Test if the given atom is present in this DTG.
	 */
	bool contains(StepID id, const Atom& atom, InvariableIndex index) const;
	
	/**
	 * Test if the given bounded atom is part of this DTG node. The domains must match exactly!
	 */
	bool containsExactCopyOf(const BoundedAtom& bounded_atom) const;

	/**
	 * Remove atoms (lazy remove).
	 */
	void removeAtom(const BoundedAtom& bounded_atom);

	/**
	 * Get the index of the invariable variable of one of the node's atoms.
	 * @param atom An atom contained by atoms_.
	 * @return The index of the variable which is invariable.
	 */
	InvariableIndex getIndex(const BoundedAtom& atom) const;
	
	/**
	 * Get the index of the invariable variable of a atom which is not part of this DTG node.
	 * For example, all transitions leading to and from this node share variable domains with
	 * this node. This function returns the index of the variable which is invariable.
	 * @param id The step id of the given atom.
	 * @param atom The atom which is linked to this DTG node.
	 * @return The index of the variable which is invariable.
	 */
	InvariableIndex getIndex(StepID id, const Atom& atom) const;
	
	/**
	 * Check if a one-to-one mapping can be made between the facts in this DTG node and the provided
	 * mapping.
	 * @param mapping The set of facts which we need to map to the facts of the DTG node.
	 * @return True if such a mapping can be found, false otherwise.
	 */
	bool canMap(const std::vector<const BoundedAtom*>& mapping) const;
	
	/**
	 * Add a transition from this node to to_node, without checking for static preconditions.
	 */
	bool addTransition(const Action& action, DomainTransitionGraphNode& to_node);

	/**
	 * Add a transition to this node.
	 */
	bool addTransition(const Transition& transition);

	/**
	 * Get the atoms linked to this node.
	 */
	const std::vector<BoundedAtom*>& getAtoms() const { return atoms_; }
	
	/**
	 * Get the DTG this node is part of.
	 */
	const DomainTransitionGraph& getDTG() const { return *dtg_; }
	DomainTransitionGraph& getDTG() { return *dtg_; }

	/**
	 * Get all transition from this node.
	 */
	const std::vector<const Transition*>& getTransitions() const { return transitions_; }
	std::vector<const Transition*>& getTransitionsNonConst() { return transitions_; }
	
	/**
	 * Remove a transition from this node.
	 */
	bool removeTransition(const Transition& transition);
	
	/**
	 * Remove all transitions from this node.
	 * @param reset_cached_actions Every time a transitions is added to this node, we store it in
	 * the cache so we do not need to iterate over all possible operators to determine which ones are
	 * applicable. The way the DTG nodes are refined guarantees that once a transition is established
	 * it will always be applicable. However the reverse is not always true, sometimes - for example when
	 * an external invariable is merged with this DTG node - a refinement necessitates a reevaluation of
	 * all applicable operators, because new ones might be applicable to this node. If this parameter is 
	 * true the cached actions are cleared and a new cache can be build up.
	 */
	void removeTransitions();

	/**
	 * Two DTG nodes are equal if they have the same atoms and both atoms their variable domains contain the
	 * same values. They can be separate objects!
	 */
	bool operator==(const DomainTransitionGraphNode& dtg_node) const;

	friend std::ostream& operator<<(std::ostream&, const DomainTransitionGraphNode& node);

	/**
	 * Ground out a specific term of all Atoms. All possible instantiations are produced and stored in the given vector. This node
	 * remains unchanged, to replace this node it has to be removed from the DTG and all the produced nodes added. Transitions are not
	 * copied or affected.
	 * @param ground_nodes This will contain the grounded out copies of this node.
	 * @param variable_to_ground The variable which needs to be grounded, membership is tested through pointer checking.
	 * @return true if at least one grounded node was produced, false otherwise.
	 */
	bool groundTerm(std::vector<DomainTransitionGraphNode*>& grounded_nodes, const Term& term_to_ground, StepID term_id) const;
	
	bool groundTerms(std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > >& grounded_nodes, const std::vector<const std::vector<const Object*>* >& variable_domains_to_ground);

	bool groundTerms(std::vector<DomainTransitionGraphNode*>& grounded_nodes, const std::vector<const std::vector<const Object*>* >& variable_domains_to_ground, const std::map<const std::vector<const Object*>*, const Object*>& bound_objects);
	
	/**
	 * Check if this node contains an empty variable domain, in that case the node has to be removed.
	 */
	bool containsEmptyVariableDomain() const;

	bool removeUnsupportedTransitions();
	
	void print(std::ostream& os) const;
	
	bool isSupported(unsigned int id, const Atom& atom, const Bindings& bindings) const;

	/**
	 * Utility function, used to evaluate which objects are part of the invariable term's domain. First of all the term_mappings
	 * contain the mappings of the first mapping of an initial fact to the first bounded atom of a node. This function recursively
	 * explores the other bounded atoms and evaluates if the bindings hold or not.
	 * @param dtg_node The DTG node which is evaluated.
	 * @param begin An iterator pointing to the BoundedAtom which should be evalulated.
	 * @param end An iterator pointing one past the last BoundedAtom to be evaluated.
	 * @param initial_facts The list of initial facts.
	 * @param term_mappings The mapping from terms to the corresponding domains.
	 * @return True if the given mapping is possible with respect to the bounded atoms in the interval [begin, end);
	 */
	bool validateTermMappings(std::vector<BoundedAtom*>::const_iterator begin,
                             std::vector<BoundedAtom*>::const_iterator end,
                             const std::vector<const Atom*>& initial_facts,
                             const std::map<const std::vector<const Object*>*, std::vector<const Object*>* >& term_mappings) const;
	/**
	 * Utility function of the copy constructor. Copy all the atoms to the new copy of the DTG node.
	 */
	void copyAtoms(const DomainTransitionGraphNode& dtg_node);
	
	/**
	 * Find all the DTG nodes which are a subset of this node.
	 * @param subsets The vector to add all the DTG nodes which are a subset of this node.
	 * @param all_dtg_nodes The vector of all the DTG nodes to find the subsets from.
	 */
	void getSubsets(std::vector<DomainTransitionGraphNode*>& subsets, const std::vector<DomainTransitionGraphNode*>& all_dtg_nodes) const;

	/**
	 * Check if this DTG node is a super set of the given node.
	 * @param dtg_node The DTG node to check.
	 * @return True if this node is a super set of the given dtg node, false otherwise.
	 */
	bool isSuperSetOf(const DomainTransitionGraphNode& dtg_node) const;
	
	/**
	 * Check if this DTG node is a sub set of the given node.
	 * @param dtg_node The DTG node to check.
	 * @return True if this node is a sub set of the given dtg node, false otherwise.
	 */
	bool isSubSetOf(const DomainTransitionGraphNode& dtg_node) const;
	
	bool isEquivalentTo(const DomainTransitionGraphNode& other) const;
	
	bool isTermGrounded(const Term& term) const;
	
	bool canUnifyWith(const DomainTransitionGraphNode& other) const;
	
	void resolveProperties();
	
	void setDTG(DomainTransitionGraph& dtg_graph) { dtg_ = &dtg_graph; }
	
private:
	
	/**
	 * Find a one-to-one mapping between the given list of facts - starting at the given index. Facts
	 * of this DG node which have been masked cannot be used for the mapping. After such a mapping is found
	 * the index is increased, the mapping is updated so the same fact cannot be selected twice to make the
	 * mapping, and the function is called again until a mapping is found for the last fact or until all options
	 * have been explored.
	 * @param mapping The set of facts to find a mapping for.
	 * @param index The index of the maping to find a mapping for.
	 * @param mask Determines which facts of the DTG node can be used in the mapping. True means it cannot be used.
	 * @return True if a mapping is found, false otherwise.
	 */
	bool findMapping(const std::vector<const BoundedAtom*>& mapping, unsigned int index, bool mask[]) const;
	
	// The DTG this node is part of.
	DomainTransitionGraph* dtg_;

	// The value of this node.
	std::vector<BoundedAtom*> atoms_;

	// The set of transitions from this node to any other node.
	std::vector<const Transition*> transitions_;

	// To create a DTG a set of predicates are combined to construct a 'balanced set', i.e.
	// taken all the effects of all actions involving these predicates there will always be
	// a single value true in any given state for the above objects. The int is the parameter
	// number of the predicate reserved for the objects linked to this DTG. Between any transition
	// the object on the given position will always be the same; e.g. (at PACKAGE ?loc) -> (in PACKAGE ?truck).
	// Read: Exhibiting Knowledge in Planning Problems to Minimize State Encoding Length
	// by Stefan Edelkamp and Malte Helmert.
	std::map<const BoundedAtom*, InvariableIndex> indexes_;
	
	std::vector<unsigned int> unique_ids_;
	
	// The set of terms which are grounded.
	std::set<const Term*> grounded_terms_;
	
	// All proper sub sets of this DTG nodes. A sub set should contain no other facts than those in this node
	// and they should be identical.
	std::vector<const DomainTransitionGraphNode*> sub_sets_;
	
	// When copying DTG nodes we create new variables to create new Atoms. These are not registered with 
	// the term manager and thus needs to be removed manually.
	bool delete_terms_;
};

std::ostream& operator<<(std::ostream&, const DomainTransitionGraphNode& node);

};

};

#endif // SAS_PLUS_DTG_NODE_H
