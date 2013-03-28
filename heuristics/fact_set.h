#ifndef MYPOP_HEURISTICS_FACT_SET
#define MYPOP_HEURISTICS_FACT_SET

#include <ostream>
#include <map>
#include <vector>

namespace MyPOP {

class Atom;
class Action;
class Predicate;
class Object;
class PredicateManager;
class Term;
class Variable;
class TermManager;
class TypeManager;
class GroundedAtom;

namespace HEURISTICS {

class VariableDomain
{
public:
	VariableDomain();
	VariableDomain(const std::vector<const Object*>& variable_domain);
	
	~VariableDomain();
	
	void addObject(const Object& object);
	unsigned int size() const { return variable_domain_.size(); }
	const std::vector<const Object*>& getVariableDomain() const { return variable_domain_; }
	
	bool sharesObjectsWith(const VariableDomain& rhs) const;
	
	void getIntersection(VariableDomain& result, const VariableDomain& rhs) const;
	
	bool contains(const Object& object) const;
	
	void set(const Object& object);
	void set(const std::vector<const Object*>& set);
	
	bool operator==(const VariableDomain& rhs) const;
	bool operator!=(const VariableDomain& rhs) const;
	
private:
	std::vector<const Object*> variable_domain_;
	
	friend std::ostream& operator<<(std::ostream& os, const VariableDomain& variable_domain);
};

std::ostream& operator<<(std::ostream& os, const VariableDomain& variable_domain);

class Fact
{
public:
	Fact(const PredicateManager& predicate_manager, const Predicate& predicate, std::vector<const VariableDomain*>& variable_domains);
	
	Fact(const Fact& other);
	
	virtual ~Fact();
	
	const Predicate& getPredicate() const { return *predicate_; }
	
	const std::vector<const VariableDomain*>& getVariableDomains() const { return *variable_domains_; }
	
	void setVariableDomain(unsigned int term_index, const VariableDomain& variable_domain);
	
	bool canUnifyWith(const Fact& fact) const;
	
	bool canUnifyWith(const GroundedAtom& grounded_atom) const;
	
	bool operator==(const Fact& rhs) const;
	
protected:
	const Predicate* predicate_;
	std::vector<const VariableDomain*>* variable_domains_;
	
	friend std::ostream& operator<<(std::ostream& os, const Fact& fact);
};

std::ostream& operator<<(std::ostream& os, const Fact& fact);

class TransitionFact : public Fact
{
public:
	TransitionFact(const PredicateManager& predicate_manager, const Predicate& predicate, std::vector<const VariableDomain*>& variable_domains, const std::vector<const Term*>& variables);
	
	virtual ~TransitionFact();
	
	const std::vector<const Term*>& getActionVariables() const { return *action_variables_; }
	
	bool operator==(const TransitionFact& rhs) const;
	
private:
	const std::vector<const Term*>* action_variables_;
	
	friend std::ostream& operator<<(std::ostream& os, const TransitionFact& transition_fact);
};

std::ostream& operator<<(std::ostream& os, const TransitionFact& transition_fact);
	
/**
 * In order to reduce the overhead of computing a consistent set of preconditions we split the preconditions
 * into sets and ground those terms which can never be made equivalent.
 */
class FactSet
{
public:
	FactSet();
	
	~FactSet();
	
	const std::vector<const TransitionFact*>& getFacts() const { return facts_; }

	/**
	 * Test if the given fact set is equivalent to this one. This is the case iff:
	 * - both have the same number of facts.
	 * - there is a bijection between both sets that respects the action variable as well as the variable domain.
	 */
	const std::map<const TransitionFact*, const TransitionFact*>* findBijection(const FactSet& other) const;
	
	void addFact(const TransitionFact& fact);
private:
	std::vector<const TransitionFact*> facts_;
	
	const std::map<const TransitionFact*, const TransitionFact*>* findBijection(unsigned int current_fact_index, const FactSet& other, const std::map<const TransitionFact*, const TransitionFact*>& variable_domain_bijection, const std::map<const Term*, const Term*>& variable_bijection) const;
	
	friend std::ostream& operator<<(std::ostream& os, const FactSet& fact_set);
};

std::ostream& operator<<(std::ostream& os, const FactSet& fact_set);

/**
 * A lifted transition contains references to fact sets instead of the normal preconditions and effects in order
 * to speed up finding consistent sets.
 */
class LiftedTransition
{
public:
	~LiftedTransition();
	
	static void createLiftedTransitions(std::vector<LiftedTransition*>& created_lifted_transitions, const PredicateManager& predicate_manager, const TermManager& term_manager, const TypeManager& type_manager, const Action& action, const std::vector<const Atom*>& initial_facts, const std::vector<const Object*>& part_of_property_state);
	
	static void mergeFactSets(const std::vector<LiftedTransition*>& all_lifted_transitions);
	
	const Action& getAction() const { return *action_; }
	
	const std::vector<const VariableDomain*>& getActionVariables() const { return action_variable_domains_; }
	
	const std::vector<const FactSet*>& getPreconditions() const { return preconditions_; }
	
	const std::vector<const FactSet*>& getEffects() const { return effects_; }
	
	const std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* >& getPreconditionMappings() const { return precondition_variable_domains_to_action_parameters_; }
	
	const std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* >& getEffectMappings() const { return effect_variable_domains_to_action_parameters_; }

	/**
	 * Change the my_fact_set such that becomes equal to the merged_fact_set. This is done to reduce the number of facts sets we need to
	 * instantiate. The bijection tells us how the facts are mapped so we can update the bindings to the action variables.
	 */
	void updateFactSet(const FactSet& my_fact_set, const FactSet& merged_fact_set, const std::map<const TransitionFact*, const TransitionFact*>& bijection);
	
private:
	
	LiftedTransition(const Action& action, const std::vector<const VariableDomain*>& action_variable_domains, const std::vector<const FactSet*>& preconditions, const std::vector<const FactSet*>& effects);
	
	void mapFactsToActionVariables(std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* >& fact_variable_domains_to_action_parameters, const std::vector<const FactSet*>& fact_sets);
	const std::map<const TransitionFact*, const TransitionFact*>* findBijection(const FactSet& other, const std::map<const TransitionFact*, const TransitionFact*>& variable_domain_bijection, const std::map<const Term*, const Term*>& variable_bijection) const;
	
	static void split(std::vector<const FactSet*>& result, const std::vector<const TransitionFact*>& facts);
	
	const Action* action_;
	std::vector<const VariableDomain*> action_variable_domains_;
	std::vector<const VariableDomain*> precondition_mappings_;
	std::vector<const FactSet*> preconditions_;
	std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* > precondition_variable_domains_to_action_parameters_;
	std::vector<const FactSet*> effects_;
	std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* > effect_variable_domains_to_action_parameters_;
	
	friend std::ostream& operator<<(std::ostream& os, const LiftedTransition& lifted_transition);
};

std::ostream& operator<<(std::ostream& os, const LiftedTransition& lifted_transition);

};

};

#endif