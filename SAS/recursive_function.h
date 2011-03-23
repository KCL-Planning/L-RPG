#ifndef SAS_PLUS_RECURSIVE_FUNCTION_H
#define SAS_PLUS_RECURSIVE_FUNCTION_H
#include <vector>
#include <ostream>
#include "dtg_types.h"
#include "../plan_types.h"

namespace MyPOP {

class Atom;
class Action;
class Bindings;

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
	RecursiveFunction(const Action& action);
	
	void addTerminationClause(const Atom& atom, InvariableIndex parameter_index, const Transition& transition);
	
	void addRecursiveClause(const Atom& atom, InvariableIndex parameter_index, InvariableIndex new_parameter_index, const Transition& transition);
	
	const std::vector<std::pair<const Atom*, InvariableIndex> >& getTerminationClause() const { return termination_clause; }
	
	const std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > >& getRecursiveClause() const { return recursive_clause; }
	
	const Action& getAction() const { return *action_; }
	
private:
	
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

