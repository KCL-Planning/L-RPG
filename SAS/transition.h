#ifndef SAS_PLUS_TRANSITION_H
#define SAS_PLUS_TRANSITION_H

#include <map>
#include <vector>
#include <iostream>

#include "../plan_types.h"
#include "../pointers.h"
#include "dtg_types.h"

namespace MyPOP {

class Atom;
class Action;
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

/**
 * The transition class marks a transition between two nodes in a DTG.
 */
class Transition
{
public:
	
	/**
	 * Create a transitions between the two nodes. Note that from_node and to_node must be part of the same DTG!
	 * @param enablers The enablers for this action (e.g. dependencies on other DTGs for its preconditions).
	 * @param action The action which needs to be executed for the transition to work.
	 * @param from_node The start node of the transition.
	 * @param to_node The end node of the transition.
	 * @return The formed transition OR NULL if the transition was not possible.
	 */
	static Transition* createTransition(const std::vector<BoundedAtom>& enablers, const Action& action, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts);

	static Transition* createSimpleTransition(const std::vector<BoundedAtom>& enablers, const Action& action, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts);
	
	/**
	 * Create a transitions between the two nodes. Note that from_node and to_node must be part of the same DTG!
	 * @param enablers The enablers for this action (e.g. dependencies on other DTGs for its preconditions).
	 * @param step The bounded action which needs to be executed for the transition to work.
	 * @param from_node The start node of the transition.
	 * @param to_node The end node of the transition.
	 * @return The formed transition OR NULL if the transition was not possible.
	 */
	static Transition* createTransition(const std::vector<BoundedAtom>& enablers, const StepPtr step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts);
	
	static Transition* createSimpleTransition(const std::vector<BoundedAtom>& enablers, const StepPtr action_step, DomainTransitionGraphNode& from_node, DomainTransitionGraphNode& to_node, const std::vector<const Atom*>& initial_facts);

	/**
	 * Create a new transition which has the same bindings to the variables as this transition. But the
	 * from and to node are cloned as well.
	 */
	Transition* cloneWithNodes(const std::vector<const Atom*>& initial_facts) const;
	
	/**
	 * Get the enabler (i.e. external dependencies for this transition to execute).
	 */
	const std::vector<BoundedAtom>& getEnablers() const { return enablers_; }
	
	/**
	 * Add an enabler to this transition.
	 */
	void addEnabler(BoundedAtom bounded_atom);

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
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getEffects() const { return effects_; }

	/**
	 * The effects which deletes from_node_.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getAffected() const { return affected_; }

	/**
	 * The preconditions which are present in from_node_.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getPreconditions() const { return preconditions_; }
	
	/**
	 * Given an atom which is linked to this transition, return the index of the variable which is invariable.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getAllPreconditions() const { return all_precondition_mappings_; }
	
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getAllPersistentPreconditions() const { return persistent_preconditions_; }
	
	bool isPreconditionPersistent(const Atom&, InvariableIndex index) const;

	/**
	 * Check if a bounded atom is linked to this transition. I.e. does it share a variable domain with it?
	 */
	bool achieves(const BoundedAtom& bounded_atom) const;
	bool affects(const BoundedAtom& bounded_atom) const;

	///void getAllPreconditions(std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions) const;
	
private:
	
	/**
	 * Check if the variable domains of the bounded atom and the atom linked to this transition are shared.
	 */
	bool shareVariableDomains(const BoundedAtom& bounded_atom, const Atom& atom) const;

	// A transition is not to be created manualy.
	Transition(const std::vector< MyPOP::SAS_Plus::BoundedAtom >& enablers, MyPOP::StepPtr step, MyPOP::SAS_Plus::DomainTransitionGraphNode& from_node, MyPOP::SAS_Plus::DomainTransitionGraphNode& to_node, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& preconditions, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& effects, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& affected, const std::vector<std::pair<const Atom*, InvariableIndex> >& persistent_preconditions, const std::map< const MyPOP::SAS_Plus::PropertySpace*, const MyPOP::Variable* >& action_invariables, const std::vector< std::pair< const MyPOP::Atom*, InvariableIndex > >& all_precondition_mappings);

	// Some transaction require a fact from another DTG to be true before it can be excuted.
	std::vector<BoundedAtom> enablers_;

	// The step contains:
	// 1) The action which needs to be executed to make the transition happen and,
	// 2) The step id under which the action's variables are bounded.
	StepPtr step_;

	// The node the transition is going from and to.
	DomainTransitionGraphNode* from_node_;
	DomainTransitionGraphNode* to_node_;

	// pair <atom of the Transition, bounded atom of the DTG node it is connected to>.
	// The preconditions which are linked to from_node_.
	std::vector<std::pair<const Atom*, InvariableIndex> > preconditions_;

	// The effects which achieves the facts of to_node_.
	std::vector<std::pair<const Atom*, InvariableIndex> > effects_;

	// The effect which deletes the facts from from_node_.
	std::vector<std::pair<const Atom*, InvariableIndex> > affected_;
	
	// A list of facts which remain unaltered.
	std::vector<std::pair<const Atom*, InvariableIndex> > persistent_preconditions_;
	
	// Per property space the variable which is invariable.
	const std::map<const PropertySpace*, const Variable*>* action_invariables_;
	
	// A list of all preconditions of the action, including the index of the term which is invariable.
	const std::vector<std::pair<const Atom*, InvariableIndex> > all_precondition_mappings_;
};

std::ostream& operator<<(std::ostream& os, const Transition& transition);

};

};

#endif // SAS_PLUS_TRANSITION_H
