#ifndef MYPOP_SAS_PLUS_LIFTED_DTG
#define MYPOP_SAS_PLUS_LIFTED_DTG

#include <vector>
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

namespace HEURISTICS
{
class Fact;
};
	
namespace SAS_Plus
{

class PropertyState;
class PropertySpace;
class MultiValuedVariable;

struct MultiValuedVariableTermIndex
{
	unsigned int value_index_;
	unsigned int value_fact_index_;
	unsigned int value_fact_term_index_;
};


class MultiValuedTransition
{
public:
	MultiValuedTransition(const Action& action, const MultiValuedTransition& effect);
private:
	
	const Action* action_;
	
	std::vector<const MultiValuedVariable*> preconditions_;
	const MultiValuedTransition* effect_;
	
	// We map each term of each value of each precondition to the variables of the action.
	std::vector<std::pair<MultiValuedVariableTermIndex, unsigned int> > precondition_to_action_variable_mappings_;
	
	// We map each action variable to each term of the effect.
	std::vector<std::pair<unsigned int, MultiValuedVariableTermIndex> > effect_to_action_variable_;
};

class MultiValuedValue
{
public:
	MultiValuedValue(const std::vector<HEURISTICS::Fact*>& values, const PropertyState& property_state);
	
	~MultiValuedValue();
	
	void addTransition(const MultiValuedTransition& transition);
	
	const PropertyState& getPropertyState() const { return *property_state_; }
	
	const std::vector<HEURISTICS::Fact*>& getValues() const { return *values_; }
	
private:
	const std::vector<HEURISTICS::Fact*>* values_;
	const PropertyState* property_state_;
	
	std::vector<const MultiValuedTransition*> transitions_;
	
	friend std::ostream& operator<<(std::ostream& os, const MultiValuedValue& value);
};

std::ostream& operator<<(std::ostream& os, const MultiValuedValue& value);

class LiftedDTG
{
public:
	static void createLiftedDTGs(std::vector<LiftedDTG*>& created_lifted_dtgs, const VAL::pddl_type_list& types, const PredicateManager& predicate_manager, const TypeManager& type_manager, const ActionManager& action_manager, const TermManager& term_manager, const std::vector<const Atom*>& initial_facts);
	
	LiftedDTG(const PredicateManager& predicate_manager, const TypeManager& type_manager, const SAS_Plus::PropertySpace& property_space);
	
	~LiftedDTG();
	
private:
	
	static void getProperties(const PredicateManager& predicate_manager, std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state);
	
	void createTransitions(const std::vector<LiftedDTG*>& all_lifted_dtgs);
	
	MultiValuedValue* getMultiValuedValue(const PropertyState& property_state) const;
	
	std::vector<MultiValuedValue*> nodes_;
	
	const SAS_Plus::PropertySpace* property_space_;
	
	//static std::vector<LiftedDTG*> all_lifted_dtgs_;
	
	friend std::ostream& operator<<(std::ostream& os, const LiftedDTG& lifted_dtg);
};

std::ostream& operator<<(std::ostream& os, const LiftedDTG& lifted_dtg);

};

};



#endif
