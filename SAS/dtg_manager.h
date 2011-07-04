#ifndef MYPOP_SAS_PLUS_DTG_MANAGER
#define MYPOP_SAS_PLUS_DTG_MANAGER

#include <vector>
#include <map>
#include <sstream>
#include <fstream>
#include <limits>
#include "dtg_graph.h"
#include "../VALfiles/ptree.h"
#include "../VALfiles/SASActions.h"
#include "../VALfiles/ToFunction.h"
#include "../manager.h"
#include "../plan_types.h"
#include "../plan.h"
#include "../action_manager.h"
#include "../plan_bindings.h"
#include "../formula.h"
#include <term_manager.h>

namespace MyPOP {

class TypeManager;
class PredicateManager;
class ActionManager;
class TermManager;
class Type;
class Action;
class VariableDomain;
class Object;
class Predicate;
class BindingsPropagator;

namespace SAS_Plus {

class DTGBindings;
class DomainTransitionGraphManager;
class DomainTransitionGraphNode;
class Transition;
class PropertyState;

/**
 * A bounded atom is an atom which has been bounded by a Bindings instance. The id is the id which has been
 * returned after bindings. On top of that the bounded atom can be part of multiple property / attribute spaces.
 * This means that one of the terms of the atom is marked as 'invariable' which means that that term is the same
 * for all properties / attributes within the designated space.
 *
 * For example, (at driver loc) \/ (driving driver truck) - driver is invariable for all walk, board and disembark 
 * actions. A bounded atom can be part of multiple property spaces with different invariables. E.g. a bounded atom
 * (driving driver truck) can also have truck as an invariable when combined with (at truck loc) in a DTG node which
 * has a driver transition. Driver does not change but truck does! To allow this kind of behaviour we allow a bounded
 * atom to have multiple properties.
 */
class BoundedAtom {

public:
	
	//static BoundedAtom& createBoundedAtom(const Atom& atom, const Property* property, Bindings& bindings);
	static BoundedAtom& createBoundedAtom(const Atom& atom, Bindings& bindings);
	static BoundedAtom& createBoundedAtom(const Atom& atom, const Property& property, Bindings& bindings);
	static BoundedAtom& createBoundedAtom(const Atom& atom, const std::vector<const Property*>& properties, Bindings& bindings);

	//BoundedAtom(StepID id, const Atom& atom, const Property* property);
	BoundedAtom(StepID id, const Atom& atom);
	BoundedAtom(StepID id, const Atom& atom, const std::vector<const Property*>& properties);

	~BoundedAtom();

	StepID getId() const;

	const Atom& getAtom() const;

	/**
	 * Get the index of the term bounded by the given id, the variable domains of the given term and the term of this bounded atom
	 * must be exactly the same.
	 * @param id The ID the term is bounded with.
	 * @param term The term which we are looking for.
	 * @param bindings The bindings where the term and the terms of this bounded atom are bounded by.
	 * @return The index of the term which shares the variable domain of the given term, id pair.
	 */
	InvariableIndex getIndex(StepID id, const Term& term, const Bindings& bindings) const;
	
	const std::vector<const Property*>& getProperties() const;
	
	/**
	 * Add a property this bounded atom is part of.
	 * @param property The property to add.
	 * @return True if the property was added, false otherwise; The latter indicates that property was already part of this bounded atom.
	 */
	bool addProperty(const Property& property);
	
	/**
	 * Check if this bounded atom is mutex with another bounded atom. This is only the case if there is an overlap in the property's 
	 * attribute space of both bounded atoms. If this is the case and the properties are not the same we can conclude that the bounded
	 * atoms must be mutex since only a single value can be true at any given time. Ofcourse we do need to check if the invariable - as
	 * indicated by the property - is equal or at least unifiable.
	 * @param other The BoundedAtom to compare the mutex relation against.
	 * @param bindings The binding class which binds both this bounded atom and @var other.
	 * @return True if the two bounded atoms are mutex, false otherwise.
	 */
	bool isMutexWith(const BoundedAtom& other, const Bindings& bindings) const;
	
	/**
	 * When checking if this bounded atom is mutex with the given atom we check if the given atom can be unified with any property of any
	 * property space this bounded atom is a member of. If this is the case and the invariable of that property space can be unified with 
	 * the invariable of this bounded atom we conclude that the given atom is mutex with this bounded atom. If - on the other hand - we can
	 * find a property space which matches the given atom and can be unified with this bounded atom we know that it cannot be mutex.
	 * @param atom The atom to check if it is mutex with this bounded atom.
	 * @param step_id The id the atom is bounded by.
	 * @param bindings The bindings instance the atom is bounded with, as well as this bounded atom.
	 * @param invariable_index The index the given atom is invariable at.
	 * @return True if the given atom and this bounded atom are mutex, false otherwise.
	 */
	bool isMutexWith (const MyPOP::Atom& atom, MyPOP::StepID step_id, const MyPOP::Bindings& bindings, InvariableIndex invariable_index) const;

	void print(std::ostream& os, const Bindings& bindings, bool verbal = true) const;

private:
	StepID id_;
	const Atom* atom_;
	std::vector<const Property*> properties_;
//	const Property* property_;
};

class DomainTransitionGraphManager : public Manager<DomainTransitionGraph>
{
public:
	DomainTransitionGraphManager(const PredicateManager& predicate_manager, const TypeManager& type_manager, const ActionManager& action_manager, const TermManager& term_manager, const std::vector<const Atom*>& initial_facts);

	virtual ~DomainTransitionGraphManager();
	
	/**
	 * Internally we can construct the DTG structures by using the TIM analysis. Instead of using the SAS+
	 * structure, we construct the DTG structures directly from the TIM analysis.
	 * @param initial_facts All facts which are true in the initial state.
	 * @param types All types as found by VAL.
	 * @param bindings The bindings used to bind the initial facts.
	 */
	void generateDomainTransitionGraphsTIM(const VAL::pddl_type_list& types, const Bindings& bindings);

	/**
	 * Get the DTGs which contains a node which actually unifies with the given atom and binding.
	 * @param found_dtgs All found DTGs are added to this list.
	 * @param binding_id The id which is used to bind atom's variables.
	 * @param atom The bounded atom all searched nodes must unify with.
	 * @param bindings The binding which hold the atom's bindings.
	 * @param index At which the given atom is invariable. This should match up with a DTG node contained by the returned DTGs.
	 */
	void getDTGs(std::vector<const DomainTransitionGraph*>& found_dtgs, StepID binding_id, const Atom& atom, const Bindings& bindings, unsigned int index = ALL_INVARIABLE_INDEXES) const;

	/**
	 * Get the DTG nodes which can be unified with the given atom and bindings.
	 * @param found_dtgs All found DTG nodes are added to this list.
	 * @param binding_id The id which is used to bind atom's variables.
	 * @param atom The bounded atom all searched nodes must unify with.
	 * @param bindings The binding which hold the atom's bindings.
	 * @param index The index at which the variable should be invariable in the found DTG node.
	 */
	void getDTGNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, StepID binding_id, const Atom& atom, const Bindings& bindings, unsigned int index = ALL_INVARIABLE_INDEXES) const;
	void getDTGNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const Bindings& bindings) const;
	
	/**
	 * Check if the given atom is supported by any of the DTG nodes.
	 */
	bool isSupported(unsigned int id, const MyPOP::Atom& atom, const MyPOP::Bindings& bindings) const;
	
	/**
	 * Get all the facts true in the initial state.
	 */
	const std::vector<const Atom*>& getInitialFacts() const { return *initial_facts_; }

private:
	
	void applyRules();
	
	void mergeIdenticalDTGs(Bindings& bindings);
	
	bool isTermStatic(const Atom& atom, StepID step_id, InvariableIndex term_index, const Bindings& bindings) const;

	// The predicate manager.
	const PredicateManager* predicate_manager_;

	// The type manager.
	const TypeManager* type_manager_;

	// The action manager.
	const ActionManager* action_manager_;

	// The term manager.
	const TermManager* term_manager_;

	// The SAS+ representation of all operators is contained in the SAS::FunctionStructure.
	SAS::FunctionStructure function_structure_;
	
	// The facts which are true in the initial state.
	const std::vector<const Atom*>* initial_facts_;
	
	void getProperties(std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state) const;

	bool removeDTG(const DomainTransitionGraph& dtg);
    void precondition_index_to_add_to_to_node();
    void precondition_index_to_add_to_to_node(ptrdiff_t arg1);
};

};

namespace Graphviz {

// Printing the DTG.
void printToDot(const SAS_Plus::DomainTransitionGraphManager& dtg_manager);
void printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg);
void printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraphNode& dtg_node);
void printToDot(std::ofstream& ofs, const SAS_Plus::Transition& transition, const Bindings& bindings);
void printPredicatesToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg);

};

};

#endif
