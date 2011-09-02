#ifndef SAS_PLUS_TRANSITION_H
#define SAS_PLUS_TRANSITION_H

#include <map>
#include <vector>
#include <iostream>

#include "../plan_types.h"
#include "../pointers.h"
#include "dtg_types.h"

namespace MyPOP {

class Predicate;


class Atom;
class Action;
class Bindings;
class Object;
class Variable;
	
namespace SAS_Plus {

class DomainTransitionGraphManager;
class DomainTransitionGraphNode;
class DomainTransitionGraph;
class Transition;
class BoundedAtom;
class PropertySpace;

/**
 * To make my life easier I created a couple of function to help executing functions like std::remove_if.
 */
namespace Utilities {

	/**
	 * Check if the given DTG node is the destination node for the given transition.
	 */
	struct TransitionToNodeEquals : public std::binary_function<const Transition*, const DomainTransitionGraphNode*, bool>
	{
		bool operator()(const Transition* transition, const DomainTransitionGraphNode* dtg_node) const;
	};
	
	/**
	 * Check if the given transition is supported by any of the initial facts or by other DTG nodes.
	 */
	/*struct TransitionIsSupported : public std::binary_function<const Transition*, const DomainTransitionGraphManager*, bool>
	{
		bool operator()(const Transition* transition, const DomainTransitionGraphManager* dtg_manager) const;
	};*/
};

class BalancedPropertySet;

struct CompareBalancedPropertySet {
	bool operator()(const BalancedPropertySet& lhs, const BalancedPropertySet& rhs) const;
};

class BalancedPropertySet {
	
public:
	
	BalancedPropertySet(const PropertySpace& property_space, const std::vector<const Object*>* invariable_domain);
	
	void removeProperty(const BoundedAtom& fact);
	
	void addProperty(const BoundedAtom& fact);
	
	const std::vector<const BoundedAtom*>& getAddedProperties() const;
	
	const std::vector<const BoundedAtom*>& getRemovedProperties() const;
	
	void removeAddedProperty(const BoundedAtom& fact);
	
	void removeRemovedProperty(const BoundedAtom& fact);
	
private:
	const PropertySpace* property_space_;
	std::vector<const BoundedAtom*> properties_added_;
	std::vector<const BoundedAtom*> properties_deleted_;
	const std::vector<const Object*>* invariable_domain_;
	
	friend bool CompareBalancedPropertySet::operator()(const BalancedPropertySet& lhs, const BalancedPropertySet& rhs) const;
};

/**
 * The transition class marks a transition between two nodes in a DTG.
 */
class Transition
{
public:
	
	/**
	 * Migrate a transition from a pair of lifted nodes to their grounded equivalents.
	 */
	Transition* migrateTransition(const std::vector<const Atom*>& initial_facts, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node) const;
	
	/**
	 * Create a transitions between the two nodes. Note that from_node and to_node must be part of the same DTG!
	 * @param action The action which needs to be executed for the transition to work.
	 * @param from_node The start node of the transition.
	 * @param to_node The end node of the transition.
	 * @return The formed transition OR NULL if the transition was not possible.
	 */
	static Transition* createTransition(const Action& action, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts);
	
	/**
	 * Create a new transition which has the same bindings to the variables as this transition. But the
	 * from and to node are cloned as well.
	 */
	Transition* cloneWithNodes(const std::vector<const Atom*>& initial_facts) const;
	
	/**
	 * The step holds the action which makes the transition happen and the step id
	 * under which the action's variables are bounded.
	 */
	StepPtr getStep() const { return step_; }
	void setStep(const StepPtr step);

	/**
	 * Get the start node.
	 */
	DomainTransitionGraphNode& getFromNode() const { return *from_node_; }

	/**
	 * Get the end node.
	 */
	DomainTransitionGraphNode& getToNode() const { return *to_node_; }

	/**
	 * Get the effects which achieves to_node_.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getEffects() const { return *effects_; }

	/**
	 * The effects which deletes from_node_.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getAffected() const { return *affected_; }

	/**
	 * The preconditions which are present in from_node_.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getPreconditions() const { return *preconditions_; }
	
	/**
	 * Given an atom which is linked to this transition, return the index of the variable which is invariable.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getAllPreconditions() const { return *all_precondition_mappings_; }
	
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getAllPersistentPreconditions() const { return *persistent_preconditions_; }
	
	bool isPreconditionPersistent(const Atom&, InvariableIndex index) const;
	
	bool isPreconditionRemoved(const Atom& precondition, const Bindings& bindings) const;

	/**
	 * Check if a bounded atom is linked to this transition. I.e. does it share a variable domain with it?
	 */
	bool achieves(const BoundedAtom& bounded_atom) const;
	bool affects(const BoundedAtom& bounded_atom) const;
	
private:
	
	/**
	 * Create a transitions between the two nodes. Note that from_node and to_node must be part of the same DTG!
	 * @param step The bounded action which needs to be executed for the transition to work.
	 * @param from_node The start node of the transition.
	 * @param to_node The end node of the transition.
	 * @return The formed transition OR NULL if the transition was not possible.
	 */
	static Transition* createTransition(const StepPtr step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts);
	
	// TODO: Remove this function.
	static Transition* createSimpleTransition(const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts);

	/**
	 * Utility function to unify atoms from a dtg node with a set of (action) atoms (either effects or preconditions).
	 * @param facts_to_unify The set of atoms which need to be unified.
	 * @param dtg_node The DTG node the above set of facts are part of.
	 * @param action_atoms The set of atoms of the action it needs to be unified with.
	 * @param action_step_id The id the action's terms are bound to.
	 * @param action The action.
	 * @param bindings The set of bindings which contains the bindings of both the action and facts of the given DTG node.
	 * @param invariable_domain The domain which is considered to be invariable.
	 * @return True if all facts could be unified, false otherwise.
	 */
	static bool unifyDTGAtomsWithAction(const std::vector<const BoundedAtom*>& facts_to_unify, const DomainTransitionGraphNode& dtg_node, const std::vector<const Atom*>& action_atoms, StepID action_step_id, const Action& action, Bindings& bindings, const std::vector<const Object*>& invariable_domain);
	
	/**
	 * Check if the variable domains of the bounded atom and the atom linked to this transition are shared.
	 */
	bool shareVariableDomains(const BoundedAtom& bounded_atom, const Atom& atom) const;

	// A transition is not to be created manualy.
	Transition(MyPOP::StepPtr step, MyPOP::SAS_Plus::DomainTransitionGraphNode& from_node, MyPOP::SAS_Plus::DomainTransitionGraphNode& to_node, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& preconditions, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& effects, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& affected, const std::vector<std::pair<const Atom*, InvariableIndex> >& persistent_preconditions, const std::map< const MyPOP::SAS_Plus::PropertySpace*, const MyPOP::Variable* >& action_invariables, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& all_precondition_mappings);

	// The step contains:
	// 1) The action which needs to be executed to make the transition happen and,
	// 2) The step id under which the action's variables are bounded.
	StepPtr step_;

	// The node the transition is going from and to.
	DomainTransitionGraphNode* from_node_;
	DomainTransitionGraphNode* to_node_;

	// pair <atom of the Transition, bounded atom of the DTG node it is connected to>.
	// The preconditions which are linked to from_node_.
	const std::vector<std::pair<const Atom*, InvariableIndex> >* preconditions_;

	// The effects which achieves the facts of to_node_.
	const std::vector<std::pair<const Atom*, InvariableIndex> >* effects_;

	// The effect which deletes the facts from from_node_.
	const std::vector<std::pair<const Atom*, InvariableIndex> >* affected_;
	
	// A list of facts which remain unaltered.
	const std::vector<std::pair<const Atom*, InvariableIndex> >* persistent_preconditions_;
	
	// Per property space the variable which is invariable.
	const std::map<const PropertySpace*, const Variable*>* action_invariables_;
	
	// A list of all preconditions of the action, including the index of the term which is invariable.
	const std::vector<std::pair<const Atom*, InvariableIndex> >* all_precondition_mappings_;
};
/*
class RecursivePreconditions
{
	
private:
	const DomainTransitionGraphNode* from_node_;
	const DomainTransitionGraphNode* to_node_;
	const Action* action_;
	
	const std::map<std::pair<const Atom*, InvariableIndex>, std::pair<const Atom*, InvariableIndex> > dtg_node_atoms_to_terminate_conditions;
	
	// Atom's terms link to action variables.
	const std::map<const Atom*, InvariableIndex> dtg_node_atoms_to_recursive_terms;
};
*/
std::ostream& operator<<(std::ostream& os, const Transition& transition);

};

};

#endif // SAS_PLUS_TRANSITION_H
