#include <iostream>

#include "recursive_function.h"
#include "action_manager.h"
#include "dtg_graph.h"
#include "transition.h"
#include "../formula.h"
#include "../plan.h"
#include "../term_manager.h"

///#define MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS

namespace MyPOP {
	
namespace SAS_Plus {

RecursiveFunction::RecursiveFunction(const MyPOP::Action& action, const TermManager& term_manager, const std::vector<const Object*>& applicable_objects)
	: action_(&action), term_manager_(&term_manager), applicable_objects_(&applicable_objects)
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
				break;
			}
		}
	}
	
	assert (new_terms->size() == atom.getArity());
	
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

#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
	std::cout << "Check the term: ";
	term.print(std::cout, bindings, Step::INITIAL_STEP);
	std::cout << std::endl;
	
	std::cout << "Applicable objects: ";
	for (std::vector<const Object*>::const_iterator ci = applicable_objects_->begin(); ci != applicable_objects_->end(); ci++)
	{
		std::cout << **ci << ", ";
	}
#endif

	std::vector<const Object*> domain = term.getDomain(Step::INITIAL_STEP, bindings);
	for (std::vector<const Object*>::reverse_iterator ri = domain.rbegin(); ri != domain.rend(); ri++)
	{
		const Object* domain_object = *ri;
		bool applicable = false;
		for (std::vector<const Object*>::const_iterator ci = applicable_objects_->begin(); ci != applicable_objects_->end(); ci++)
		{
			if (*ci == domain_object)
			{
				applicable = true;
				break;
			}
		}
		
		if (!applicable)
		{
			domain.erase(ri.base() - 1);
		}
	}
	
	if (domain.size() == 0)
	{
		return false;
	}
	
	
	std::vector<const Atom*> object_to_initial_facts;
	for (std::vector<const Atom*>::const_iterator ci = initial_state.begin(); ci != initial_state.end(); ci++)
	{
		const Atom* initial_fact = *ci;
		for (std::vector<const Term*>::const_iterator ci = initial_fact->getTerms().begin(); ci != initial_fact->getTerms().end(); ci++)
		{
			const Term* initial_term = *ci;
			if (initial_term->isTheSameAs(Step::INITIAL_STEP, term, Step::INITIAL_STEP, bindings))
			{
				object_to_initial_facts.push_back(initial_fact);
				break;
			}
		}
	}

	// Check if the terminating state is true.
	bool termination_clauses_satisfied = true;
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = termination_clause.begin(); ci != termination_clause.end(); ci++)
	{
		const Atom* termination_clause = (*ci).first;
		InvariableIndex index = (*ci).second;
		
#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
		std::cout << "Check the termination clause: ";
		termination_clause->print(std::cout, bindings, action_id);
		std::cout << "[" << index << "]" << std::endl;
#endif

		std::vector<const Object*> to_remove;
		
		bool clause_satisfied = false;

		for (std::vector<const Atom*>::const_iterator ci = object_to_initial_facts.begin(); ci != object_to_initial_facts.end(); ci++)
		{
			const Atom* atom = *ci;

			if (bindings.canUnify(*termination_clause, action_id, *atom, Step::INITIAL_STEP) &&
			    atom->getTerms()[index]->containsAtLeastOneOf(domain, Step::INITIAL_STEP, bindings))
			{
				clause_satisfied = true;
				break;
			}
		}
		
		if (!clause_satisfied)
		{
			termination_clauses_satisfied = false;
			break;
		}
	}
	
	if (termination_clauses_satisfied)
	{
		return true;
	}
	
#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
	std::cout << "No termination clauses, continue!" << std::endl;
#endif
	
	// Check if we need to invoke the recursive function and for which objects.
	std::set<const Term*> recursive_candidates;

	for (std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > >::const_iterator ci = recursive_clause.begin(); ci != recursive_clause.end(); ci++)
	{
		const Atom* recursive_atom = (*ci).first;
		InvariableIndex invariable_index = (*ci).second.first;
		InvariableIndex recursive_index = (*ci).second.second;
		
#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
		std::cout << "Process the recursive clause: ";
		recursive_atom->print(std::cout, bindings, action_id);
		std::cout << std::endl;
#endif
		
		std::set<const Term*> matching_candidates;
		
		for (std::vector<const Atom*>::const_iterator ci2 = object_to_initial_facts.begin(); ci2 != object_to_initial_facts.end(); ci2++)
		{
			const Atom* atom = *ci2;
			
#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
			std::cout << "Check the initial fact: ";
			atom->print(std::cout, bindings, Step::INITIAL_STEP);
#endif
			
			if (bindings.canUnify(*recursive_atom, action_id, *atom, Step::INITIAL_STEP))
			{
				if (!atom->getTerms()[invariable_index]->containsAtLeastOneOf(domain, Step::INITIAL_STEP, bindings))
				{
#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
					std::cout << " ... (Subsequent iteration): ";
					atom->print(std::cout, bindings, Step::INITIAL_STEP);
					std::cout << " cannot be an iteration, because the object(s) (";
					for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
					{
						std::cout << **ci;
						if (ci != domain.end() - 1)
						{
							std::cout << ", ";
						}
					}
					std::cout << ") is not part of the index " << invariable_index << std::endl;
#endif
				}
				else
				{
#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
					std::cout << " ... (Subsequent iteration): ";
					atom->print(std::cout, bindings, Step::INITIAL_STEP);
					std::cout << " can be a candidate!" << std::endl;
#endif
					matching_candidates.insert(atom->getTerms()[recursive_index]);
				}
			}
#ifdef MYPOP_SAS_PLUS_RECURSIVE_FUNCTION_COMMENTS
			else
			{
				std::cout << " ... (Subsequent iteration): ";
				atom->print(std::cout, bindings, Step::INITIAL_STEP);
				std::cout << " cannot be an iteration, because it cannot be unified." << std::endl;
			}
#endif
		}
		
		if (ci == recursive_clause.begin())
		{
			recursive_candidates.insert(matching_candidates.begin(), matching_candidates.end());
		}
		else
		{
			std::vector<const Term*> tmp(std::max(recursive_candidates.size(), matching_candidates.size()));
			std::vector<const Term*>::iterator i = std::set_intersection(recursive_candidates.begin(), recursive_candidates.end(), matching_candidates.begin(), matching_candidates.end(), tmp.begin());
			recursive_candidates.clear();
			recursive_candidates.insert(tmp.begin(), i);
		}
	}
	
	for (std::set<const Term*>::const_iterator ci = recursive_candidates.begin(); ci != recursive_candidates.end(); ci++)
	{
		const Term* term = *ci;
		if (execute(closed_list, *term, initial_state, action_id, bindings))
		{
			return true;
		}
	}
	return false;
}

/********************************
 *
 * BoundedRecursiveFunction
 *
 *******************************/

BoundedRecursiveFunction::BoundedRecursiveFunction(const Action& action, const TermManager& term_manager, const std::vector<const Object*>& applicable_objects, const std::vector<const Atom*>& initial_state, StepID action_id, const Bindings& bindings)
	: RecursiveFunction(action, term_manager, applicable_objects), initial_state_(&initial_state), action_id_(action_id), bindings_(new Bindings(bindings))
{
//	std::cout << "Created a bounded recursive function: " << *this << std::endl;
}

bool BoundedRecursiveFunction::evaluate(const Term& term) const
{
	return execute(term, *initial_state_, action_id_, *bindings_);
}

std::ostream& operator<<(std::ostream& os, const BoundedRecursiveFunction& function)
{
	const std::vector<std::pair<const Atom*, InvariableIndex> >& termination_clause = function.getTerminationClause();
	const std::vector<std::pair<const Atom*, std::pair<InvariableIndex, InvariableIndex> > >& recursive_clause = function.getRecursiveClause();
	
	if (termination_clause.size() > 0 || recursive_clause.size() > 0)
	{
		os << function.getAction() << " - Recursive function: f(c): (";

		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = termination_clause.begin(); ci != termination_clause.end(); ci++)
		{
			const Atom* atom = (*ci).first;
			atom->print(os, *function.bindings_, function.action_id_);
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
			
			atom->print(os, *function.bindings_, function.action_id_);
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

/********************************
 *
 * RecursiveFunctionManager
 *
 *******************************/

RecursiveFunctionManager::RecursiveFunctionManager()
{
	
}
	
void RecursiveFunctionManager::addRecursiveFunction(const BoundedRecursiveFunction& function)
{
//	std::cout << "Added the recursive function: " << function << std::endl;
	functions_.push_back(&function);
}
	
void RecursiveFunctionManager::evaluateObjects(std::map<const Object*, boost::dynamic_bitset<> >& result, const std::vector<const Object*>& objects) const
{
	for (unsigned int i = 0; i < objects.size(); i++)
	{
		const Object* object = objects[i];
		
		boost::dynamic_bitset<> bitset = evaluateObject(*object);
		result[object] = bitset;
	}
}
	
boost::dynamic_bitset<> RecursiveFunctionManager::evaluateObject(const Object& object) const
{
	boost::dynamic_bitset<> bitset(functions_.size());
//	std::cout << "Evaluate: " << object << std::endl;
	
	for (unsigned int i = 0; i < functions_.size(); i++)
	{
//		std::cout << "- " << *functions_[i] << " - ";
		if (functions_[i]->evaluate(object))
		{
//			std::cout << " YES!";
			bitset[i] = 1;
		}
		else
		{
//			std::cout << " NO!";
			bitset[i] = 0;
		}
//		std::cout << std::endl;
	}
	
	return bitset;
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