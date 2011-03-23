#ifndef SAS_PLUS_RECURSIVE_FUNCTION_H
#define SAS_PLUS_RECURSIVE_FUNCTION_H
#include <vector>
#include <set>
#include <ostream>
#include "dtg_types.h"
#include "../plan_types.h"

namespace MyPOP {

class Atom;
class Action;
class Bindings;
class Term;

namespace SAS_Plus {

class Transition;

/**
 * A recursive function of the form: f(c): { set of termination clauses } OR { set of recursive clauses } \bigcup f(c').
 *
 * An example recursive function is constructed in the depots domain, between the DTG nodes:
 * { (on crate crate'), (on crate' surface) (at crate' place) } -> { (clear crate'), (on crate' crate), (at crate' place) }.
 *
 * The resulting fuction is: f(c): ( (clear c) AND (at c place) ) OR ( (on crate c) AND f(create) ).
 */
class RecursiveFunction
{
public:
	/**
	 * Create a recusive function which is linked to the given action. All predicate's terms will be 
	 * linked to this action's variables.
	 */
	RecursiveFunction(const Action& action);
	
	/**
	 * Add a predicate which will be part of the termination clause. The atom's terms will be linked to 
	 * the action's variables, it is assumed that these are linked by the given transition.
	 * @param atom The predicate to be added to the termination clause.
	 * @param parameter_index  The index of the atom which is linked to the function's parameter.
	 * @param transition The transition the atom is part of, it is assumed that the transition's action 
	 * is the same action as given in the constructor.
	 */
	void addTerminationClause(const Atom& atom, InvariableIndex parameter_index, const Transition& transition);
	
	/**
	 * Add a predicate which will be part of the termination clause. The atom's terms will be linked to 
	 * the action's variables, it is assumed that these are linked by the given transition.
	 * @param atom The predicate to be added to the termination clause.
	 * @param parameter_index  The index of the atom which is linked to the function's parameter.
	 * @param recursive_index The index of the atom which will be used as parameter for the recursive call.
	 * @param transition The transition the atom is part of, it is assumed that the transition's action 
	 * is the same action as given in the constructor.
	 */
	void addRecursiveClause(const Atom& atom, InvariableIndex parameter_index, InvariableIndex new_parameter_index, const Transition& transition);
	
	/**
	 * Execute the recursive action and report if the function holds for the given object.
	 * @param object The term fed into the recursive function.
	 * @param initial_state The initial state of the problem.
	 * @param action_id The StepID for the given action determines the value of every term.
	 * @return True if the function holds, false otherwise.
	 */
	bool execute(const Term& term, const std::vector<const Atom*>& initial_state, StepID action_id, const Bindings& bindings) const;
	
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getTerminationClause() const { return termination_clause; }
	
	const std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > >& getRecursiveClause() const { return recursive_clause; }
	
	const Action& getAction() const { return *action_; }
	
private:
	
	/**
	 * Internally called by execute, contains a closed list, to make sure it does not loop.
	 */
	bool execute(std::set<const Term*>& closed_list, const Term& term, const std::vector<const Atom*>& initial_state, StepID action_id, const Bindings& bindings) const;
	
	/**
	 * The predicates added to both clauses need to be transformed in such a way that the terms are equal to
	 * the action's variables. This way we can evaluate the function by providing a StepID the action is
	 * bounded to and evaluate the function without having to rediscover how the terms in the predicates
	 * are linked up.
	 * @param atom The atom which is part of a transition and needs to be transformed.
	 * @param action_id The id the action is bounded to.
	 * @param bindings All the bindings of the given atom.
	 * @return A new atom whos terms are linked to the action's variables.
	 */
	const Atom* mapAtomTerms(const Atom& atom, StepID action_id, const Bindings& bindings) const;
	
	/**
	 * The first clause that is checked is the termination clause. If this clause is true the recursive
	 * formula will return true and terminate. The Atom's terms are directly linked to the action variables
	 * so the bindings of the action directly influence the values of these atoms. The invariable index links
	 * to the index where the function's parameter should be placed.
	 */
	std::vector<std::pair<const Atom*, InvariableIndex> > termination_clause;
	
	/**
	 * If the termination clause if false, the recursive clause is called. If the recursive clause is found to
	 * be true, the recursive function is called again, but this time another parameter will be added to the 
	 * function. The double pair of invariables represent: < function's parameter, 
	 * invariable for the recursive call >.
	 */
	std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > > recursive_clause;
	
	const Action* action_;
};

std::ostream& operator<<(std::ostream& os, const RecursiveFunction& recursive_function);

};

};

#endif // SAS_PLUS_RECURSIVE_FUNCTION_H

