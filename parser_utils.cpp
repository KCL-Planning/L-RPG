#include <string>
#include <assert.h>
#include "parser_utils.h"
#include "type_manager.h"
#include "term_manager.h"
#include "predicate_manager.h"
#include "formula.h"

///#define MYPOP_PARSER_UTILS_COMMENTS

namespace MyPOP {

const Formula* Utility::convertGoal(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::goal* precondition, bool make_negative)
{
	const VAL::neg_goal* ng = dynamic_cast<const VAL::neg_goal*>(precondition);
	if (ng)
	{
		const Formula* negFormula = convertGoal(term_manager, predicate_manager, ng->getGoal(), !make_negative);
		return negFormula;
	}

	const VAL::simple_goal* sg = dynamic_cast<const VAL::simple_goal*>(precondition);
	if (sg)
	{
		const VAL::proposition* prop = sg->getProp();
		return convertPrecondition(term_manager, predicate_manager, *prop, make_negative);
	}

	const VAL::conj_goal* cg = dynamic_cast<const VAL::conj_goal*>(precondition);
	if (cg)
	{
		Conjunction* con = new Conjunction();
		const VAL::goal_list* goals = cg->getGoals();
		for (VAL::goal_list::const_iterator ci = goals->begin(); ci != goals->end(); ci++)
		{
			const Formula* f = convertGoal(term_manager, predicate_manager, (*ci), make_negative);
			con->addFormula(*f);
		}
		return con;
	}
	/*
	const VAL::timed_goal* tg = dynamic_cast<const VAL::timed_goal*>(precondition);
	if (tg)
	{
		return convertGoal(term_manager, predicate_manager, tg->getGoal(), make_negative);
	}
	*/
	
	std::cout << "Unsupported goal detected, quiting!" << std::endl;
	precondition->write(std::cout);
	assert (false);
	exit(1);
}

Formula* Utility::convertPrecondition(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::proposition& prop, bool make_negative)
{
	VAL::pred_symbol* predicate = prop.head;
	VAL::parameter_symbol_list* action_parameters = prop.args;

	const std::string& action_predicate = predicate->getName();

	// If the predicate is equal to "=" it is an equal relationship between the two variables.
	if (action_predicate == "=")
	{
		assert (action_parameters->size() == 2);
		const Term* variable = term_manager.getTerm(*action_parameters->front());
		const Term* term = term_manager.getTerm(*action_parameters->back());
		return new Equality(*variable, *term, !make_negative);
	}
	else
	{
		return Utility::convertToAtom(term_manager, predicate_manager, prop, make_negative);
	}
}


Atom* Utility::convertToAtom(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::proposition& prop, bool make_negative)
{
	VAL::pred_symbol* predicate_symbol = prop.head;
	VAL::parameter_symbol_list* action_parameters = prop.args;

	const std::string& action_predicate = predicate_symbol->getName();

	// Constructiong an atom requires both a set of variables a predicate. All possible predicates have
	// already been constructed and are stored in the predicate manager. To retrieve an existing predicate
	// we must specify the name of the predicate and the types of the variables.
	std::vector<const Term*>* variables = new std::vector<const Term*>();
	std::vector<const Type*> types;
	for (VAL::parameter_symbol_list::const_iterator i = action_parameters->begin(); i != action_parameters->end(); i++)
	{
		VAL::parameter_symbol* parameter = *i;
		const Term* term = term_manager.getTerm(*parameter);
		variables->push_back(term);
		types.push_back(term->getType());
	}

	// Retrieve the predicate, this one must exist.
	const Predicate* predicate = predicate_manager.getPredicate(action_predicate, types);
	assert (predicate != NULL);

	return new Atom(*predicate, *variables, make_negative);
}

void Utility::convertEffects(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::effect_lists& effects, std::vector<const Atom*>& action_effects)
{
	for (VAL::pc_list<VAL::simple_effect*>::const_iterator ci = effects.add_effects.begin(); ci != effects.add_effects.end(); ci++)
	{
		action_effects.push_back(convertToAtom(term_manager, predicate_manager, *(*ci)->prop, false));
	}
	for (VAL::pc_list<VAL::simple_effect*>::const_iterator ci = effects.del_effects.begin(); ci != effects.del_effects.end(); ci++)
	{
		action_effects.push_back(convertToAtom(term_manager, predicate_manager, *(*ci)->prop, true));
	}
}

void Utility::convertFormula(std::vector<const Atom*>& atoms, const Formula* formula)
{
	assert (formula != NULL);
	const Atom* atom = dynamic_cast<const Atom*>(formula);
	if (atom != NULL)
	{
		atoms.push_back(atom);
		return;
	}

	const Conjunction* conjunction = dynamic_cast<const Conjunction*>(formula);
	if (conjunction != NULL)
	{
		for (std::vector<const Formula*>::const_iterator ci = conjunction->getFormulea().begin(); ci != conjunction->getFormulea().end(); ci++)
		{
			convertFormula(atoms, *ci);
		}
		return;
	}

	// Other cases ignored.
}

void Utility::convertFormula(std::vector<const Atom*>& atoms, std::vector<const Equality*>& equalities, const Formula* formula)
{
	assert (formula != NULL);
	const Atom* atom = dynamic_cast<const Atom*>(formula);
	if (atom != NULL)
	{
		atoms.push_back(atom);
		return;
	}

	const Conjunction* conjunction = dynamic_cast<const Conjunction*>(formula);
	if (conjunction != NULL)
	{
		for (std::vector<const Formula*>::const_iterator ci = conjunction->getFormulea().begin(); ci != conjunction->getFormulea().end(); ci++)
		{
			convertFormula(atoms, equalities, *ci);
		}
		return;
	}

	const Equality* equality = dynamic_cast<const Equality*>(formula);
	if (equality != NULL)
	{
		equalities.push_back(equality);
	}
}

const Predicate& Utility::getPredicate(const TypeManager& type_manager, const PredicateManager& predicate_manager, const TIM::Property& property)
{
	// A property only stored the predicate symbol and the variable number this property holds.
	// In order to get the predicate symbol and the types of the predicate we need to cast the
	// property into an extended_pred_symbol.
	const VAL::extended_pred_symbol* extended_property = property.root();

	const std::string& predicate_name = extended_property->getName();
	std::vector<const Type*> predicate_types;
	for(std::vector<VAL::pddl_typed_symbol*>::const_iterator esp_i = extended_property->tcBegin(); esp_i != extended_property->tcEnd(); ++esp_i)
	{
		const Type* type = type_manager.getType((*esp_i)->type->getName());
		assert (type != NULL);
		predicate_types.push_back(type);
	}

	// Now that we know the name and type, find the predicate.
	const Predicate* predicate = predicate_manager.getPredicate(predicate_name, predicate_types);
	assert (predicate != NULL);
	return *predicate;
}

};
