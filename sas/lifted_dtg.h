#ifndef MYPOP_SAS_PLUS_LIFTED_DTG
#define MYPOP_SAS_PLUS_LIFTED_DTG

#include <vector>
#include <set>
#include "../VALfiles/ptree.h"
#include "../VALfiles/SASActions.h"
#include "../VALfiles/ToFunction.h"
#include "causal_graph.h"

namespace MyPOP
{
class Atom;
class Action;
class TypeManager;
class PredicateManager;
class ActionManager;
class TermManager;
class Predicate;
class Object;

namespace HEURISTICS
{
class Fact;
class VariableDomain;
};
	
namespace SAS_Plus
{
class LiftedDTG;
class PropertyState;
class PropertySpace;
class MultiValuedValue;
class MultiValuedVariable;
class CausalGraph;

class MultiValuedTransition
{
public:
	MultiValuedTransition(const Action& action, MultiValuedValue& precondition, MultiValuedValue& effect, std::vector<std::vector<unsigned int>* >& precondition_to_action_variable_mappings_, std::vector<std::vector<unsigned int>* >& effect_to_action_variable_mappings, const TypeManager& type_manager);
	
	MultiValuedTransition(const MultiValuedTransition& transition, const std::vector<HEURISTICS::VariableDomain*>& action_variable_domains);
	
	~MultiValuedTransition();
	
	const Action& getAction() const { return *action_; }
	
	MultiValuedValue& getFromNode() const { return *precondition_; }
	MultiValuedValue& getToNode() const { return *effect_; }
	
	bool isPreconditionIgnored(const Atom& precondition) const;
	bool isEffectIgnored(const Atom& effect) const;
	
	void ignorePrecondition(const Atom& precondition);
	void ignoreEffect(const Atom& effect);
	
	MultiValuedTransition* migrateTransition(MultiValuedValue& from_node, MultiValuedValue& to_node, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager) const;
	
	void migrateTransition(std::vector<MultiValuedTransition*>& results, const std::multimap<const Object*, const Object*>& equivalent_relationships, MultiValuedValue& from_node, MultiValuedValue& to_node, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager) const;
	
	const HEURISTICS::VariableDomain& getActionVariableDomain(unsigned int index) const { return *action_variable_domains_[index]; }
	
	const std::vector<std::vector<unsigned int>* >& getPreconditionToActionVariableMappings() const { return *precondition_to_action_variable_mappings_; }
	const std::vector<std::vector<unsigned int>* >& getEffectToActionVariableMappings() const { return *effect_to_action_variable_mappings_; }
	
	const HEURISTICS::Fact* getEffectPersistentWith(const HEURISTICS::Fact& precondition) const;
	
	const HEURISTICS::Fact* getPreconditionPersistentWith(const HEURISTICS::Fact& effect) const;
	
private:
	
	const Action* action_;
	std::vector<HEURISTICS::VariableDomain*> action_variable_domains_;
	
	MultiValuedValue* precondition_;
	MultiValuedValue* effect_;
	
	// We map each term of each value of each precondition to the variables of the action.
	std::vector<std::vector<unsigned int>* >* precondition_to_action_variable_mappings_;
	
	// We map each action variable to each term of the effect.
	std::vector<std::vector<unsigned int>* >* effect_to_action_variable_mappings_;
	
	std::vector<std::pair<unsigned int, unsigned int> > persitent_precondition_to_effect_mappings_;
	
	std::vector<const Atom*> preconditions_to_ignore_;
	std::vector<const Atom*> effects_to_ignore_;
	
	friend std::ostream& operator<<(std::ostream& os, const MultiValuedTransition& transition);
};

std::ostream& operator<<(std::ostream& os, const MultiValuedTransition& transition);

class MultiValuedValue
{
public:
	MultiValuedValue(const LiftedDTG& lifted_dtg, std::vector<HEURISTICS::Fact*>& values, const PropertyState& property_state, bool is_copy = false);
	
	MultiValuedValue(const LiftedDTG& lifted_dtg, const MultiValuedValue& other, bool is_copy = false);
	
	~MultiValuedValue();
	
	void findMappings(std::vector< std::vector< const MyPOP::HEURISTICS::Fact* >* >& found_mappings, const std::vector< const MyPOP::HEURISTICS::Fact* >& facts, const MyPOP::PredicateManager& predicate_manager) const;
	
	void addTransition(const MultiValuedTransition& transition);
	
	const PropertyState& getPropertyState() const { return *property_state_; }
	
	const std::vector<HEURISTICS::Fact*>& getValues() const { return *values_; }
	
	const std::vector<const MultiValuedTransition*>& getTransitions() const { return transitions_; }
	
	bool isCopy() const { return is_copy_; }
	
	void split(std::vector<MultiValuedValue*>& split_nodes, const std::multimap<const Object*, const Object*>& equivalent_relationships, const PredicateManager& predicate_manager) const;
	
	/**
	 * In some cases we need to make copies of a lifted DTG node, such that we do not into too many
	 * dead ends. However, these copies are only used if the facts in the initial state map to a node
	 * for which copies have been made.
	 * Therefor we store all the copies for a node in a list, this way we know which one to 'active'.
	 */
	void addCopy(MultiValuedValue& copy);
	
	const std::vector<MultiValuedValue*>& getCopies() const { return created_copies_; }
	
	const LiftedDTG& getLiftedDTG() const { return *lifted_dtg_; }
	
	void printFacts(std::ostream& os) const;
	
private:
	void findMappings(std::vector<std::vector<const HEURISTICS::Fact*>* >& found_mappings, const std::vector<const HEURISTICS::Fact*>& current_mappings, const HEURISTICS::VariableDomain& invariable_domain, const std::vector<const HEURISTICS::Fact*>& facts, const PredicateManager& predicate_manager) const;
	
	void findAssignments(unsigned int fact_index, unsigned int term_index, std::vector<MultiValuedValue*>& created_nodes, std::vector<const HEURISTICS::VariableDomain*>& assignments_made, const std::multimap<const Object*, const Object*>& equivalent_relationships, const PredicateManager& predicate_manager) const;
	
	const LiftedDTG* lifted_dtg_;
	
	std::vector<HEURISTICS::Fact*>* values_;
	const PropertyState* property_state_;
	
	std::vector<const MultiValuedTransition*> transitions_;
	
	bool is_copy_;
	
	std::vector<MultiValuedValue*> created_copies_;
	
	friend std::ostream& operator<<(std::ostream& os, const MultiValuedValue& value);
};

std::ostream& operator<<(std::ostream& os, const MultiValuedValue& value);

class LiftedDTG
{
public:
	static void createLiftedDTGs(std::vector<LiftedDTG*>& created_lifted_dtgs, const VAL::pddl_type_list& types, const PredicateManager& predicate_manager, const TypeManager& type_manager, const ActionManager& action_manager, const TermManager& term_manager, const std::vector<const Atom*>& initial_facts);
	
	LiftedDTG(const PredicateManager& predicate_manager, const TypeManager& type_manager, const SAS_Plus::PropertySpace& property_space);
	
	LiftedDTG(const LiftedDTG& other, const PredicateManager& predicate_manager, const std::multimap<const Object*, const Object*>& equivalent_relationships, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager);
	
	LiftedDTG(const LiftedDTG& other, const std::vector<MultiValuedValue*>& node_set, const std::vector<const Atom*>& initial_fact, const TypeManager& type_manager, const PredicateManager& predicate_manager);
	
	~LiftedDTG();
	
	const std::vector<MultiValuedValue*>& getNodes() const { return nodes_; }
	
	/**
	 * Find all nodes which can unify with the given fact and store the matching nodes in found_nodes. This method will never return nodes
	 * that are copies, because these have another purpose.
	 */
	void getNodes(std::vector<const MultiValuedValue*>& found_nodes, const HEURISTICS::Fact& fact_to_find) const;
	
	//const SAS_Plus::PropertySpace& getPropertySpace() const { return *property_space_; }
	const std::vector<const Object*>& getInvariableObjects() const { return invariable_objects_; }
	
	void splitNodes(const std::multimap<const Object*, const Object*>& equivalent_relationships, const std::vector<const Atom*>& initial_facts, const PredicateManager& predicate_manager, const TypeManager& type_manager);
	
private:
	
	static void splitLiftedTransitionGraphs(std::vector<LiftedDTG*>& result, const std::vector< MyPOP::SAS_Plus::LiftedDTG* >& created_ltgs, const MyPOP::TermManager& term_manager, const std::vector< const MyPOP::Atom* >& initial_facts, const MyPOP::TypeManager& type_manager, const PredicateManager& predicate_manager);
	
	void createCopies(const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager);
	
	static void getProperties(const PredicateManager& predicate_manager, std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state);
	
	void createTransitions(const std::vector<LiftedDTG*>& all_lifted_dtgs, const TypeManager& type_manager);
	
	void ground(const std::vector<LiftedDTG*>& all_lifted_dtgs, const std::vector<const Atom*>& initial_facts, const TermManager& term_manager, const TypeManager& type_manager, const std::set<const Object*>& objects_not_to_ground);
	
	//MultiValuedValue* getMultiValuedValue(const PropertyState& property_state) const;
	void getMultiValuedValues(std::vector<MultiValuedValue*>& matching_nodes, const PropertyState& property_state) const;
	
	void findInvariableObjects(const std::vector<const Atom*>& initial_facts, const PredicateManager& predicate_manager);
	
	std::vector<MultiValuedValue*> nodes_;
	
	const SAS_Plus::PropertySpace* property_space_;
	
	std::vector<const Object*> invariable_objects_;
	
	//static std::vector<LiftedDTG*> all_lifted_dtgs_;
	
	friend std::ostream& operator<<(std::ostream& os, const LiftedDTG& lifted_dtg);
	
	friend void Graphviz::printToDot(const std::string& file_name, const SAS_Plus::CausalGraph& causal_graph);
};

std::ostream& operator<<(std::ostream& os, const LiftedDTG& lifted_dtg);

};

namespace Graphviz {
void printToDot(const std::vector<SAS_Plus::LiftedDTG*>& all_lifted_dtgs);

void printToDot(std::ofstream& ofs, const SAS_Plus::MultiValuedTransition& transition);

void printToDot(std::ofstream& ofs, const SAS_Plus::MultiValuedValue& dtg_node);

void printToDot(std::ofstream& ofs, const SAS_Plus::LiftedDTG& dtg);
};

};



#endif
