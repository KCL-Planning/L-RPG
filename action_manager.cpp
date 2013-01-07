#include "action_manager.h"
#include "type_manager.h"
#include "term_manager.h"
#include "predicate_manager.h"
#include "formula.h"
#include "parser_utils.h"
#include "plan_bindings.h"
#include "plan.h"

///#define MYPOP_ACTION_MANAGER_COMMENTS

namespace MyPOP {

/*************************
 * The Action class
 *************************/

Action* Action::dummy_action = new Action("", Formula::TRUE, NULL, NULL);

Action::Action(const std::string& predicate, const Formula& precondition, const std::vector<const Variable*>* variables, const std::vector<const Atom*>* effects)
	: predicate_(predicate), precondition_(&precondition), variables_(variables), effects_(effects)
{
	if (effects != NULL)
	{
		for (std::vector<const Atom*>::const_iterator ci = effects->begin(); ci != effects->end(); ++ci)
		{
			const Atom* effect = *ci;
			std::vector<unsigned int>* effect_mappings = new std::vector<unsigned int>();
			
			for (std::vector<const Term*>::const_iterator ci = effect->getTerms().begin(); ci != effect->getTerms().end(); ++ci)
			{
				const Term* effect_term = *ci;
				unsigned int action_variable_index = std::distance(variables->begin(), std::find(variables->begin(), variables->end(), effect_term));
				effect_mappings->push_back(action_variable_index);
			}
			effect_terms_to_action_variable_mappings_.push_back(effect_mappings);
		}
	}
}

Action::~Action()
{
	if (precondition_ != &Formula::TRUE &&
	    precondition_ != &Formula::FALSE)
	{
		delete precondition_;
	}

	for (std::vector<const Atom*>::const_iterator ci = effects_->begin(); ci != effects_->end(); ci++)
	{
		delete *ci;
	}
	
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = effect_terms_to_action_variable_mappings_.begin(); ci != effect_terms_to_action_variable_mappings_.end(); ++ci)
	{
		delete *ci;
	}

	delete effects_;
	delete variables_;
}

void Action::getAchievingEffects(const Atom& atom, std::vector<const Atom*>& achieving_effects) const
{
	for (std::vector<const Atom*>::const_iterator ci = effects_->begin(); ci != effects_->end(); ci++)
	{
		const Atom* effect = *ci;
		if (effect->getPredicate().getName() != atom.getPredicate().getName())
		//if (&effect->getPredicate() != &atom.getPredicate())
			continue;

		// Make sure the sign is correct.
		if (effect->isNegative() != atom.isNegative())
			continue;

		// Check if the terms have the same type.
		if (effect->getArity() != atom.getArity())
			continue;

		bool types_differ = false;
		for (unsigned int i = 0; i < effect->getArity(); i++)
		{
			const Type* effect_type = (effect->getTerms()[i])->getType();
			const Type* atom_type = (atom.getTerms()[i])->getType();
			if (((effect_type == NULL || atom_type == NULL) && effect_type != atom_type) ||
			(!effect_type->isSubtypeOf(*atom_type) && !atom_type->isSubtypeOf(*effect_type) && !atom_type->isEqual(*effect_type)))
			{
				types_differ = true;
				break;
			}
		}
		if (types_differ)
			continue;

		achieving_effects.push_back(effect);

		// Break here if there is only a single effect which can satisfy the action.
	}
}

unsigned int Action::getActionVariable(unsigned int effect_index, unsigned int effect_term_index) const
{
	return (*effect_terms_to_action_variable_mappings_[effect_index])[effect_term_index];
}

unsigned int Action::getActionVariable(const Term& term) const
{
	for (unsigned int action_variable_index = 0; action_variable_index < variables_->size(); ++action_variable_index)
	{
		if ((*variables_)[action_variable_index] == &term)
		{
			return action_variable_index;
		}
	}
	
	return std::numeric_limits<unsigned int>::max();
}

void Action::print(std::ostream& os, const Bindings& bindings, StepID step_id) const
{
	os << "(" << predicate_ << " ";

	for (std::vector<const Variable*>::const_iterator ci = variables_->begin(); ci != variables_->end(); ci++)
	{
		const VariableDomain& vd = bindings.getVariableDomain(step_id, **ci);
		if (vd.getDomain().size() > 1)
		{
			os << "{";
		}
		for (std::vector<const Object*>::const_iterator ci2 = vd.getDomain().begin(); ci2 != vd.getDomain().end(); ci2++)
		{
			os << **ci2;
			if (ci2 + 1 != vd.getDomain().end())
			{
				os << ", ";
			}
		}
		if (vd.getDomain().size() > 1)
		{
			os << "}";
		}
		
//		os << "[ADDR=" << *ci << "]";
//		os << "%" << &(vd.getDomain()) << "%";

		if (ci + 1 != variables_->end())
		{
			os << " ";
		}
	}
	os << ")";
}

std::ostream& operator<<(std::ostream& os, const Action& action)
{
	os << "(" << action.predicate_ << " ";

	for (std::vector<const Variable*>::const_iterator ci = action.variables_->begin(); ci != action.variables_->end(); ++ci)
	{
		os << **ci << "(" << *ci << ")";
		if (ci + 1 != action.variables_->end())
		{
			os << " ";
		}
	}
	os << ") effects " << std::endl;
	for (std::vector<const Atom*>::const_iterator ci = action.effects_->begin(); ci != action.effects_->end(); ++ci)
	{
		const Atom* effect = *ci;
		(*ci)->print(std::cout);
		for (std::vector<const Term*>::const_iterator ci = effect->getTerms().begin(); ci != effect->getTerms().end(); ++ci)
		{
			os << *ci << ",";
		}
		os << std::endl;
	}
	return os;
}

/*************************
 * The ActionManager class
 *************************/
ActionManager::ActionManager(const TypeManager& type_manager, TermManager& term_manager, const PredicateManager& predicate_manager)
	: type_manager_(&type_manager), term_manager_(&term_manager), predicate_manager_(&predicate_manager)
{

}

ActionManager::~ActionManager()
{
#ifdef MYPOP_ACTION_MANAGER_COMMENTS
	std::cout << "[Destructor] ActionManager" << std::endl;
#endif
}

void ActionManager::processActions(const VAL::operator_list& operators)
{
	for (VAL::operator_list::const_iterator ci = operators.begin(); ci != operators.end(); ci++)
	{
		const VAL::operator_* op = *ci;

	    const VAL::operator_symbol* name = op->name;
//		const VAL::var_symbol_table* symtab = op->symtab;
    	const VAL::var_symbol_list* parameters = op->parameters;
    	const VAL::goal* precondition = op->precondition;
    	const VAL::effect_lists* effects = op->effects;

		// Get the predicate.
		const std::string& predicate = name->getName();

		// Initialize the variables.
		std::vector<const Variable*>* action_variables = new std::vector<const Variable*>();
		for (VAL::var_symbol_list::const_iterator i = parameters->begin(); i != parameters->end(); i++)
		{
			VAL::var_symbol* parameter = *i;

			// Get the type of the parameter.
			const Type* type = type_manager_->getType(parameter->type->getName());
			Variable* var = new Variable(*type, parameter->getName());
			term_manager_->addTerm(*parameter, *var);
			
//			const Term* term = term_manager_->getTerm(*parameter);
//			assert (term != NULL && term->isVariable());
//			const Variable* var = term->asVariable();

			//variables[var_counter++] = var;
			action_variables->push_back(var);
		}

		// Parse the goals. The goal is a superclass of all possible goals.
		// Possible goals:
		// * disj_goal [not supported]
		// * imply_goal [not supported]
		// * neg_goal
		// * timed_goal [not supported]
		// * simple_goal
		// * con_goal [not supported]
		// * constraint_goal [not supported]
		// * preference [not supported]
		// * qfied_goal [not supported]
		// * conj_goal
		const Formula* action_precondition = Utility::convertGoal(*term_manager_, *predicate_manager_, precondition, false);

		// Parse the effects. All possible effects are:
		// * pc_list<simple_effect*> add_effects;
		// * pc_list<simple_effect*> del_effects;
		// * pc_list<forall_effect*> forall_effects; [not supported]
		// * pc_list<cond_effect*>   cond_effects; [not supported]
		// * pc_list<cond_effect*>   cond_assign_effects; [not supported]
		// * pc_list<assignment*>    assign_effects; [not supported]
		// * pc_list<timed_effect*>  timed_effects; [not supported]
		std::vector<const Atom*>* action_effects = new std::vector<const Atom*>();
		Utility::convertEffects(*term_manager_, *predicate_manager_,  *effects, *action_effects);
		
		Action* action = new Action(predicate, *action_precondition, action_variables, action_effects);
		addManagableObject(action);

		// Map the operator to the constructed action object for preprocessing purposes.
		action_indexing_[op] = action;
	}
}

void ActionManager::getAchievingActions(std::vector<std::pair<const Action*, const Atom*> >& actions, const Atom& atom) const
{
#ifdef MYPOP_ACTION_MANAGER_COMMENTS
	std::cout << "Find all the actions which can achieve ";
	atom.print(std::cout);
	std::cout << std::endl;
#endif

	// Create a list of all action which have the same predicate.
	for (unsigned int i = 0; i < highest_id_; i++)
	{
		const Action* action = objects_[i];
		std::vector<const Atom*> achieving_effects;
		action->getAchievingEffects(atom, achieving_effects);

		for (std::vector<const Atom*>::const_iterator ci = achieving_effects.begin(); ci != achieving_effects.end(); ci++)
		{
			actions.push_back(std::make_pair(action, *ci));
		}
	}
}

const Action& ActionManager::getAction(const VAL::operator_& val_operator) const
{
	std::map<const VAL::operator_*, const Action*>::const_iterator ci = action_indexing_.find(&val_operator);
	assert(ci != action_indexing_.end());
	return *(*ci).second;
}

void ActionManager::ground(Bindings& bindings, std::vector<const Step*>& grounded_actions, const Action& action) const
{
//	std::cout << "ground " << action << std::endl;
	
	// In succession, assing one of the objects in each of its variable domains.
	const std::vector<const Variable*>& action_variables = action.getVariables();
	unsigned int variable_counter[action_variables.size()];
	unsigned int max_variable_counter[action_variables.size()];
	
//	std::cout << " " << action_variables.size() << " variables!" << std::endl;

	// Initialise the maximum domain size of each action variable.
	for (unsigned int i = 0; i < action_variables.size(); i++)
	{
		std::vector<const Object*> values;
		term_manager_->getTypeManager().getObjectsOfType(values, *action_variables[i]->getType());
		variable_counter[i] = 0;
		max_variable_counter[i] = values.size();
		
//		std::cout << " Size of variable domain " << *action_variables[i] << " is: " << values.size() << std::endl;
	}

	
	while (true)
	{
//		std::cout << " process: ";
//		for (unsigned int i = 0; i < action_variables.size(); i++)
//		{
//			std::cout << variable_counter[i] << ", ";
//		}
//		std::cout << std::endl;
		
		// Create a new action binding.
		StepID action_id = bindings.createVariableDomains(action);

		// Assign the domains.
		for (unsigned int i = 0; i < action_variables.size(); i++)
		{
			VariableDomain& variable_domain = bindings.getNonConstVariableDomain(action_id, *action_variables[i]);
			variable_domain.makeEqualTo(*variable_domain.getDomain()[variable_counter[i]]);
//			std::cout << variable_domain << " [" << *variable_domain.getDomain()[variable_counter[i]] << "]" << std::endl;
		}

		// Store the grounded action.
		grounded_actions.push_back(new Step(action_id, action));

		// Iterate through all possible combinations of variable assignments, akin binary iterating.
		unsigned int variable_to_update = 0;
		while (variable_to_update < action_variables.size())
		{
			if (variable_counter[variable_to_update] + 1 != max_variable_counter[variable_to_update])
			{
				variable_counter[variable_to_update]++;
				break;
			}
			
			variable_counter[variable_to_update] = 0;
			variable_to_update++;
		}
		
		// If the variable_to_update equals action_variables we have exhausted all combinations, break.
		if (variable_to_update == action_variables.size())
		{
			break;
		}
	}
}

};
