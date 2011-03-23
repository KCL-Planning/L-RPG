#include <iostream>

#include "recursive_function.h"
#include "action_manager.h"
#include "dtg_graph.h"
#include "transition.h"
#include "../formula.h"
#include "../plan.h"
#include "../term_manager.h"


namespace MyPOP {
	
namespace SAS_Plus {

RecursiveFunction::RecursiveFunction(const MyPOP::Action& action)
	: action_(&action)
{

}

void RecursiveFunction::addTerminationClause(const Atom& atom, InvariableIndex parameter_index, const Transition& transition)
{
	const Atom* new_atom = mapAtomTerms(atom, transition.getStep()->getStepId(), transition.getFromNode().getDTG().getBindings());
	termination_clause.push_back(std::make_pair(new_atom, parameter_index));
}
	
void RecursiveFunction::addRecursiveClause(const Atom& atom, InvariableIndex parameter_index, InvariableIndex new_parameter_index, const Transition& transition)
{
	const Atom* new_atom = mapAtomTerms(atom, transition.getStep()->getStepId(), transition.getFromNode().getDTG().getBindings());
	recursive_clause.push_back(std::make_pair(new_atom, std::make_pair(parameter_index, new_parameter_index)));
}

const Atom* RecursiveFunction::mapAtomTerms(const Atom& atom, StepID action_id, const Bindings& bindings) const
{
	// Map the atom's terms to the action's variables.
	std::vector<const Term*>* new_terms = new std::vector<const Term*>();
	for (std::vector<const Term*>::const_iterator ci = atom.getTerms().begin(); ci != atom.getTerms().end(); ci++)
	{
		const Term* atom_term = *ci;
		
		for (std::vector<const Variable*>::const_iterator ci = action_->getVariables().begin(); ci != action_->getVariables().end(); ci++)
		{
			const Variable* action_variable = *ci;
			if (atom_term->isTheSameAs(action_id, *action_variable, action_id, bindings))
			{
				new_terms->push_back(action_variable);
				std::cout << "%" << *action_variable;
			
				if (ci != action_->getVariables().end() - 1)
				{
					std::cout << ", ";
				}
				break;
			}
		}
	}
	return new Atom(atom.getPredicate(), *new_terms, atom.isNegative());
}
	
std::ostream& operator<<(std::ostream& os, const RecursiveFunction& recursive_function)
{
	const std::vector<std::pair<const Atom*, InvariableIndex> >& termination_clause = recursive_function.getTerminationClause();
	const std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > >& recursive_clause = recursive_function.getRecursiveClause();
	
	if (termination_clause.size() > 0 || recursive_clause.size() > 0)
	{
		os << recursive_function.getAction() << " - Recursive function: f(c): (";

		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = termination_clause.begin(); ci != termination_clause.end(); ci++)
		{
			const Atom* atom = (*ci).first;
			atom->print(os);
			os << "[" << (*ci).second << "]";
			if (ci != termination_clause.end() - 1)
			{
				os << " /\\ ";
			}
		}

		os << ") \\/ (";

		for (std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > >::const_iterator ci = recursive_clause.begin(); ci != recursive_clause.end(); ci++)
		{
			const Atom* atom = (*ci).first;
			std::pair<InvariableIndex, InvariableIndex> indexes = (*ci).second;
			
			atom->print(os);
			os << "(" << indexes.first << ")[" << indexes.second << "]";
			if (ci != recursive_clause.end() - 1)
			{
				os << " /\\ ";
			}
		}
		os << " /\\ f(c) )" << std::endl;
	}
	return os;
}
	
};

};