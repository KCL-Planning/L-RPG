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

bool RecursiveFunction::execute(const Term& term, const std::vector<const Atom*>& initial_state, StepID action_id, const Bindings& bindings) const
{
	std::set<const Term*> closed_list;
	return execute(closed_list, term, initial_state, action_id, bindings);
}

bool RecursiveFunction::execute(std::set<const Term*>& closed_list, const Term& term, const std::vector<const Atom*>& initial_state, StepID action_id, const Bindings& bindings) const
{
	if (closed_list.count(&term) != 0)
	{
		return false;
	}
	closed_list.insert(&term);
	
	std::cout << "Check the term: ";
	term.print(std::cout, bindings, Step::INITIAL_STEP);
	std::cout << std::endl;
	
	// Check if the terminating state is true.
	std::vector<const Atom*> termination_candidates = initial_state;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = termination_clause.begin(); ci != termination_clause.end(); ci++)
	{
		const Atom* termination_clause = (*ci).first;
		InvariableIndex index = (*ci).second;
		
		std::cout << "Check the termination clause: ";
		termination_clause->print(std::cout, bindings, action_id);
		std::cout << std::endl;
		
		// Terminate those which do not fit.
		for (std::vector<const Atom*>::reverse_iterator ri = termination_candidates.rbegin(); ri != termination_candidates.rend(); ri++)
		{
			const Atom* atom = *ri;
			
			if (!bindings.canUnify(*termination_clause, action_id, *atom, Step::INITIAL_STEP))
			{
				std::cout << "[" << termination_candidates.size() << "/" << initial_state.size() << "] The atom: ";
				atom->print(std::cout, bindings, Step::INITIAL_STEP);
				std::cout << "Cannot be a candidate because it cannot be unified!" << std::endl;
				termination_candidates.erase(ri.base() - 1);
			}
			else if (!atom->getTerms()[index]->containsAtLeastOneOf(term.getDomain(Step::INITIAL_STEP, bindings), Step::INITIAL_STEP, bindings))
			{
				std::cout << "[" << termination_candidates.size() << "/" << initial_state.size() << "] The atom: ";
				atom->print(std::cout, bindings, Step::INITIAL_STEP);
				std::cout << "Cannot be a candidate because the index " << index << " does not contain any of the required objects!" << std::endl;
				termination_candidates.erase(ri.base() - 1);
			}
			else
			{
				std::cout << "[" << termination_candidates.size() << "/" << initial_state.size() << "] The atom: ";
				atom->print(std::cout, bindings, Step::INITIAL_STEP);
				std::cout << " is a possible candidate!" << std::endl;
			}
		}
	}
	
	if (termination_candidates.size() > 0)
	{
		return true;
	}
	
	std::cout << "No termination clauses, continue!" << std::endl;
	
	// Check if we need to invoke the recursive function and for which objects.
	std::vector<std::pair<const Atom*, InvariableIndex> > recursive_candidates;
	for (std::vector<const Atom*>::const_iterator ci = initial_state.begin(); ci != initial_state.end(); ci++)
	{
		recursive_candidates.push_back(std::make_pair(*ci, NO_INVARIABLE_INDEX));
	}
	
	for (std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > >::const_iterator ci = recursive_clause.begin(); ci != recursive_clause.end(); ci++)
	{
		const Atom* recursive_clause = (*ci).first;
		InvariableIndex invariable_index = (*ci).second.first;
		InvariableIndex recursive_index = (*ci).second.second;
		
		std::cout << "Process the recursive clause: ";
		recursive_clause->print(std::cout, bindings, action_id);
		std::cout << std::endl;
		
		// Terminate those which do not fit.
		for (std::vector<std::pair<const Atom*, InvariableIndex> >::reverse_iterator ri = recursive_candidates.rbegin(); ri != recursive_candidates.rend(); ri++)
		{
			const Atom* atom = (*ri).first;
			InvariableIndex index = (*ri).second;
			
			if (bindings.canUnify(*recursive_clause, action_id, *atom, Step::INITIAL_STEP))
			{
				bool update_index = false;
				if (index == NO_INVARIABLE_INDEX)
				{
					index = recursive_index;
					update_index = true;
				}
				
				if (!atom->getTerms()[invariable_index]->containsAtLeastOneOf(term.getDomain(Step::INITIAL_STEP, bindings), Step::INITIAL_STEP, bindings))
				{
					std::cout << "Subsequent iteration, ";
					atom->print(std::cout, bindings, Step::INITIAL_STEP);
					std::cout << " cannot be an iteration, because the term ";
					term.print(std::cout, bindings, Step::INITIAL_STEP);
					std::cout << " is not part of the index " << invariable_index << std::endl;
					recursive_candidates.erase(ri.base() - 1);
				}
				else if (update_index)
				{
					std::cout << "First iteration, ";
					atom->print(std::cout, bindings, Step::INITIAL_STEP);
					std::cout << " can be a candidate!" << std::endl;
					recursive_candidates.erase(ri.base() - 1);
					recursive_candidates.push_back(std::make_pair(atom, recursive_index));
				}
				else
				{
					std::cout << "Subsequent iteration, ";
					atom->print(std::cout, bindings, Step::INITIAL_STEP);
					std::cout << " can be a candidate!" << std::endl;
				}
			}
			else
			{
				std::cout << "Subsequent iteration, ";
				atom->print(std::cout, bindings, Step::INITIAL_STEP);
				std::cout << " cannot be an iteration, because it cannot be unified." << std::endl;
				recursive_candidates.erase(ri.base() - 1);
			}
		}
	}
	
	// Call the function recursively for the lucky candidates.
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = recursive_candidates.begin(); ci != recursive_candidates.end(); ci++)
	{
		const Term* recursive_term = (*ci).first->getTerms()[(*ci).second];
		if (execute(closed_list, *recursive_term, initial_state, action_id, bindings))
		{
			return true;
		}
	}
	
	return false;
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