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

/**
 * Wrapper for the pair function, used to give it more sensible get methods.
 */
class BoundedAtom {

public:

	BoundedAtom(StepID id, const Atom& atom)
		: id_(id), atom_(&atom)
	{

	}

	~BoundedAtom()
	{
		//delete atom_;
	}

	StepID getId() const
	{
		return id_;
	}

	const Atom& getAtom() const
	{
		return *atom_;
	}

	void setId(StepID id) {
		id_ = id;
	}

	void setAtom(const Atom& atom)
	{
		atom_ = &atom;
	}
	
	unsigned int getIndex(const VariableDomain& variable_domain, const BindingsFacade& bindings) const
	{
		std::vector<const VariableDomain*> variable_domains;
		bindings.getVariableDomains(variable_domains, id_, *atom_);
		
		for (unsigned int i = 0; i < variable_domains.size(); i++)
		{
			if (variable_domains[i] == &variable_domain)
			{
				return i;
			}
		}
		
		assert (false);
	}

	void print(std::ostream& os, const BindingsFacade& bindings) const
	{
		atom_->print(os, bindings, id_);
	}

private:
	StepID id_;
	const Atom* atom_;
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
	void generateDomainTransitionGraphsTIM(const VAL::pddl_type_list& types, const BindingsFacade& bindings);

	/**
	 * Get the DTGs which contains a node which actually unifies with the given atom and binding.
	 * @param found_dtgs All found DTGs are added to this list.
	 * @param binding_id The id which is used to bind atom's variables.
	 * @param atom The bounded atom all searched nodes must unify with.
	 * @param bindings The binding which hold the atom's bindings.
	 * @param index At which the given atom is invariable. This should match up with a DTG node contained by the returned DTGs.
	 */
	void getDTGs(std::vector<const DomainTransitionGraph*>& found_dtgs, StepID binding_id, const Atom& atom, const BindingsFacade& bindings, unsigned int index = std::numeric_limits<unsigned int>::max()) const;

	/**
	 * Get the DTG nodes which can be unified with the given atom and bindings.
	 * @param found_dtgs All found DTG nodes are added to this list.
	 * @param binding_id The id which is used to bind atom's variables.
	 * @param atom The bounded atom all searched nodes must unify with.
	 * @param bindings The binding which hold the atom's bindings.
	 * @param index The index at which the variable should be invariable in the found DTG node.
	 */
	void getDTGNodes(std::vector<const DomainTransitionGraphNode*>& found_dtg_nodes, StepID binding_id, const Atom& atom, const BindingsFacade& bindings, unsigned int index = std::numeric_limits<unsigned int>::max()) const;
	void getDTGNodes(std::vector<const DomainTransitionGraphNode*>& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const BindingsFacade& bindings) const;
	
	/**
	 * Check if the given atom is supported by any of the DTG nodes.
	 */
	bool isSupported(unsigned int id, const MyPOP::Atom& atom, const MyPOP::BindingsFacade& bindings) const;
	
	/**
	 * Get all the facts true in the initial state.
	 */
	const std::vector<const Atom*>& getInitialFacts() const { return *initial_facts_; }

private:
	
	/**
	 * Process used as part of the generateDomainTransitionGraphsTIM function. This function merges DTGs together which
	 * are linked through the preconditions of the transitions and share the same invariable.
	 */
	void mergeDTGs();
	
	void splitDTGs();

	// The predicate manager.
	const PredicateManager* predicate_manager_;

	// The type manager.
	const TypeManager* type_manager_;

	// The action manager.
	const ActionManager* action_manager_;

	// The term manager.
	const TermManager* term_manager_;

	// Mapping of predicates to their respective domain transition graphs.
	//std::map<const Predicate*, std::vector<DomainTransitionGraph*>* > dtg_mappings_;

	// The SAS+ representation of all operators is contained in the SAS::FunctionStructure.
	SAS::FunctionStructure function_structure_;
	
	// The facts which are true in the initial state.
	const std::vector<const Atom*>* initial_facts_;
	
	// Add transitions to a DTG.
	void addTransitions(const SAS::ValuesUnion& value_union, MyPOP::SAS_Plus::DomainTransitionGraph& dtg) const;
	void addTransitions(MyPOP::SAS_Plus::DomainTransitionGraph& dtg) const;
	
	void getProperties(std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state) const;

	bool removeDTG(const DomainTransitionGraph& dtg);
};

};

namespace Graphviz {

// Printing the DTG.
void printToDot(const SAS_Plus::DomainTransitionGraphManager& dtg_manager);
void printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg);
void printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraphNode& dtg_node);
void printToDot(std::ofstream& ofs, const SAS_Plus::Transition& transition, const BindingsFacade& bindings);
void printPredicatesToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg);

};

};

#endif
