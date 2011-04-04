#include "formula.h"
#include "term_manager.h"
#include "logging.h"
#include "plan.h"
#include "pointers.h"
#include "plan_flaws.h"
#include "plan_bindings.h"
#include "predicate_manager.h"

namespace MyPOP {

// Instantiate default formulea for true and false.
const Formula& Formula::TRUE = Formula(false);
const Formula& Formula::FALSE = Formula(true);

/*************************
 * The Formula class
 *************************/
Formula::Formula(bool is_negative)
	: is_negative_(is_negative)
{
	
}

Formula::~Formula()
{

}

void Formula::addAsPrecondition(Plan& plan, StepPtr step) const
{

}

void Formula::print(std::ostream& os) const
{
	os << (is_negative_ ? "FALSE" : "TRUE");
}

void Formula::print(std::ostream& os, const Bindings& bindings, StepID step_id) const
{
	return print(os);
}

/*************************
 * The Atom class
 *************************/
Atom::Atom(const Predicate& predicate, const std::vector<const Term*>& terms, bool is_negative)
	: Formula(is_negative), predicate_(&predicate), terms_(&terms)
{
//	for (unsigned int i = 0; i < terms.size(); i++)
//	{
//		assert (terms[i]->getType() == predicate.getTypes()[i]);
//	}
}

Atom::~Atom()
{
	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << predicate_ << " is deleted!" << std::endl;
	}
	delete terms_;
}

void Atom::addAsPrecondition(Plan& plan, StepPtr step) const
{
	plan.addOpenCondition(OpenConditionPtr(new OpenCondition(step, *this)));
}

void Atom::print(std::ostream& os) const
{
	os << "\t";
	if (is_negative_)
	{
		os << "!";
	}
	os << "(" << predicate_->getName() << " ";
	for (std::vector<const Term*>::const_iterator ci = terms_->begin(); ci != terms_->end(); ci++)
	{
		os << **ci;
		if (ci + 1 != terms_->end())
			os << " ";
	}
	os << ")";
	if (predicate_->isStatic())
	{
		os << "[s]";
	}
}

void Atom::print(std::ostream& os, const Bindings& bindings, StepID step_id) const
{
	os << "\t";
	if (is_negative_)
	{
		os << "!";
	}
	os << "(" << predicate_->getName() << " ";
	for (std::vector<const Term*>::const_iterator ci = terms_->begin(); ci != terms_->end(); ci++)
	{
		const Term* term = *ci;
		term->print(os, bindings, step_id);
		os << "%" << &(term->getDomain(step_id, bindings)) << "%";
		if (ci + 1 != terms_->end())
			os << " ";
	}
	os << ")";
	if (predicate_->isStatic())
	{
		os << "[s]";
	}
}

/*************************
 * The Conjunction class
 *************************/
Conjunction::~Conjunction()
{
	for (std::vector<const Formula*>::iterator i = formula_list_.begin(); i != formula_list_.end(); i++)
	{
		delete *i;
	}
}

void Conjunction::addFormula(const Formula& formula)
{
	formula_list_.push_back(&formula);
}

void Conjunction::addAsPrecondition(Plan& plan, StepPtr step) const
{
	for (std::vector<const Formula*>::const_iterator ci = formula_list_.begin(); ci != formula_list_.end(); ci++)
	{
		(*ci)->addAsPrecondition(plan, step);
	}
}

void Conjunction::print(std::ostream& os) const
{
	for (std::vector<const Formula*>::const_iterator ci = formula_list_.begin(); ci != formula_list_.end(); ci++)
	{
		(*ci)->print(os);
		if (ci + 1 != formula_list_.end())
		{
			os << std::endl;
		}
	}
}

void Conjunction::print(std::ostream& os, const Bindings& bindings, StepID step_id) const
{
	for (std::vector<const Formula*>::const_iterator ci = formula_list_.begin(); ci != formula_list_.end(); ci++)
	{
		(*ci)->print(os, bindings, step_id);
		if (ci + 1 != formula_list_.end())
		{
			os << std::endl;
		}
	}	
}

/*************************
 * The Equality class
 *************************/
Equality::Equality(const Term& variable, const Term& term, bool make_equal)
	: variable_(&variable), term_(&term), make_equal_(make_equal)
{

}

void Equality::print(std::ostream& os) const
{
	os << *variable_ << (make_equal_ ? " == " : " != ") << *term_;
}

void Equality::print(std::ostream& os, const Bindings& bindings, StepID step_id) const
{
	print(os);
}

void Equality::addAsPrecondition(Plan& plan, StepPtr step) const
{
	if (make_equal_)
	{
//		variable_->unify(step->getStepId(), *term_, step->getStepId(), plan.getBindings());
	}
	else
	{
///		variable_->(step->getStepId(), *term_, step->getStepId(), plan.getBindings());
	}
/*
	if (term_->isObject())
	{
		ObjectBinding object_binding(step->getStepId(), *variable_, *term_->asObject(), make_equal_);
		plan.getBindings().addBinding(object_binding);
	}
	else
	{
		VariableBinding variable_binding(step->getStepId(), *variable_, step->getStepId(), *term_->asVariable(), make_equal_);
		plan.getBindings().addBinding(variable_binding);
	}
*/
}

};

