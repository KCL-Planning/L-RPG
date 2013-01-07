#ifndef MYPOP_SAS_PLUS_LIFTED_DTG
#define MYPOP_SAS_PLUS_LIFTED_DTG

#include <vector>
#include <set>
#include "../VALfiles/ptree.h"
#include "../VALfiles/SASActions.h"
#include "../VALfiles/ToFunction.h"

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

class PropertyState;
class PropertySpace;
class MultiValuedValue;
class MultiValuedVariable;

class MultiValuedTransition
{
public:
	MultiValuedTransition(const Action& action, MultiValuedValue& precondition, MultiValuedValue& effect, const std::vector<std::vector<unsigned int>* >& precondition_to_action_variable_mappings_, const std::vector<std::vector<unsigned int>* >& effect_to_action_variable_mappings, const TypeManager& type_manager);
	
	~MultiValuedTransition();
	
	const Action& getAction() const { return *action_; }
	
	MultiValuedValue& getFromNode() const { return *precondition_; }
	MultiValuedValue& getToNode() const { return *effect_; }
	
	void ignorePrecondition(const Atom& precondition);
	void ignoreEffect(const Atom& effect);
	
	MultiValuedTransition* migrateTransition(MultiValuedValue& from_node, MultiValuedValue& to_node, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager) const;
	
	const HEURISTICS::VariableDomain& getActionVariableDomain(unsigned int index) const { return *action_variable_domains_[index]; }
	
private:
	
	const Action* action_;
	std::vector<HEURISTICS::VariableDomain*> action_variable_domains_;
	
	MultiValuedValue* precondition_;
	MultiValuedValue* effect_;
	
	// We map each term of each value of each precondition to the variables of the action.
	const std::vector<std::vector<unsigned int>* >* precondition_to_action_variable_mappings_;
	
	// We map each action variable to each term of the effect.
	const std::vector<std::vector<unsigned int>* >* effect_to_action_variable_mappings_;
	
	std::vector<const Atom*> preconditions_to_ignore_;
	std::vector<const Atom*> effects_to_ignore_;
	
	friend std::ostream& operator<<(std::ostream& os, const MultiValuedTransition& transition);
};

std::ostream& operator<<(std::ostream& os, const MultiValuedTransition& transition);

class MultiValuedValue
{
public:
	MultiValuedValue(std::vector<HEURISTICS::Fact*>& values, const PropertyState& property_state, bool is_copy = false);
	
	MultiValuedValue(const MultiValuedValue& other, bool is_copy = false);
	
	~MultiValuedValue();
	
	void addTransition(const MultiValuedTransition& transition);
	
	const PropertyState& getPropertyState() const { return *property_state_; }
	
	const std::vector<HEURISTICS::Fact*>& getValues() const { return *values_; }
	
	const std::vector<const MultiValuedTransition*>& getTransitions() const { return transitions_; }
	
	bool isCopy() const { return is_copy_; }
	
	/**
	 * In some cases we need to make copies of a lifted DTG node, such that we do not into too many
	 * dead ends. However, these copies are only used if the facts in the initial state map to a node
	 * for which copies have been made.
	 * Therefor we store all the copies for a node in a list, this way we know which one to 'active'.
	 */
	void addCopy(MultiValuedValue& copy);
	
private:
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
	
	~LiftedDTG();
	
	const std::vector<MultiValuedValue*>& getNodes() const { return nodes_; }
	
	/**
	 * Find all nodes which can unify with the given fact and store the matching nodes in found_nodes. This method will never return nodes
	 * that are copies, because these have another purpose.
	 */
	void getNodes(std::vector<const MultiValuedValue*>& found_nodes, const HEURISTICS::Fact& fact_to_find) const;
	
	const SAS_Plus::PropertySpace& getPropertySpace() const { return *property_space_; }
	
private:
	
	void createCopies(const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager);
	
	static void getProperties(const PredicateManager& predicate_manager, std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state);
	
	void createTransitions(const std::vector<LiftedDTG*>& all_lifted_dtgs, const TypeManager& type_manager);
	
	void ground(const std::vector<LiftedDTG*>& all_lifted_dtgs, const std::vector<const Atom*>& initial_facts, const TermManager& term_manager, const TypeManager& type_manager, const std::set<const Object*>& objects_not_to_ground);
	
	MultiValuedValue* getMultiValuedValue(const PropertyState& property_state) const;
	
	std::vector<MultiValuedValue*> nodes_;
	
	const SAS_Plus::PropertySpace* property_space_;
	
	//static std::vector<LiftedDTG*> all_lifted_dtgs_;
	
	friend std::ostream& operator<<(std::ostream& os, const LiftedDTG& lifted_dtg);
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
