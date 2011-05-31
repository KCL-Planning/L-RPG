#ifndef MYPOP_FORMULA
#define MYPOP_FORMULA

#include <vector>
#include <string>
#include "pointers.h"
#include "plan_types.h"

namespace MyPOP {

class Bindings;
class Predicate;
class Variable;
class Term;
class Plan;

/**
 * The base class used to describe preconditions of actions.
 */
class Formula
{
public:
	// Default formulea.
	static const Formula& TRUE;
	static const Formula& FALSE;

	// By default all formulas are not negative.
	Formula(bool is_negative = false);

	virtual ~Formula();

	// Set this formula as a negative or possitive.
	void makeNegative(bool negative) { is_negative_ = negative; }

	// Add this formula to the plan as a precondition of the given plan.
	virtual void addAsPrecondition(Plan& plan, StepPtr step) const;

	// Print the formula to the ostream.
	virtual void print(std::ostream& os) const;
	
	// Print the formula to the ostream but with the variable printed
	// with the set of objects from their domains.
	virtual void print(std::ostream&os, const Bindings& bindings, StepID step_id) const;

	// Check if this formula has a negative sign.
	bool isNegative() const { return is_negative_; }

protected:
	// True if this atom is a negative atom.
	bool is_negative_;
};

/**
 * A base literal, can either be true or false.
 */
class Atom : public Formula
{
public:
	// Create a new atom.
	Atom(const Predicate& predicate, const std::vector<const Term*>& terms, bool is_negative);

	virtual ~Atom();

	// Add this formula to the plan as a precondition of the given plan. An atom will be added
	// by adding a new unsafe.
	virtual void addAsPrecondition(Plan& plan, StepPtr step) const;

	// Print the formula to the ostream.
	virtual void print(std::ostream& os) const;
	
	// Print the formula to the ostream but with the variable printed
	// with the set of objects from their domains.
	virtual void print(std::ostream& os, const Bindings& bindings, StepID step_id, bool verbal = true) const;

	// Get the predicate.
	const Predicate& getPredicate() const { return *predicate_; }

	// Get the arity of this atom.
	unsigned int getArity() const { return terms_->size(); }

	// Get the terms.
	const std::vector<const Term*>& getTerms() const { return *terms_; }

protected:
	// The predicate of this atom.
	const Predicate* predicate_;

	// A vector with all the terms of this atom.
	const std::vector<const Term*>* terms_;
};

/**
 * A conjunction of formulea.
 */
class Conjunction : public Formula
{
public:
	virtual ~Conjunction();

	// Add a formula to this conjunction.
	void addFormula(const Formula& formula);

	// Get the formulea in this conjunction.
	const std::vector<const Formula*>& getFormulea() const { return formula_list_; }

	// Add this formula to the plan as a precondition of the given plan. Loop over all formulea and
	// add them appropriately.
	virtual void addAsPrecondition(Plan& plan, StepPtr step) const;

	// Print the formula to the ostream.
	virtual void print(std::ostream& os) const;
	
	// Print the formula to the ostream but with the variable printed
	// with the set of objects from their domains.
	virtual void print(std::ostream&os, const Bindings& bindings, StepID step_id) const;

protected:
	// List to store all the formulea who are part of this conjunction.
	std::vector<const Formula*> formula_list_;
};

/**
 * An equal relationship between two action variables.
 */
class Equality : public Formula
{
public:
///	Equality(const Variable& variable, const Term& term, bool make_unequal);
	Equality(const Term& variable, const Term& term, bool make_unequal);

	// The variable to make equal or unequal to.
///	const Variable& getVariable() const { return *variable_; }

	// The term to assign to the variable.
///	const Term& getTerm() const { return *term_; }

	// Check if this relationship is a equal or unequal one.
	bool isMakeEqual() const { return make_equal_; }

	// Print the formula to the ostream.
	virtual void print(std::ostream& os) const;
	
	// Print the formula to the ostream but with the variable printed
	// with the set of objects from their domains.
	virtual void print(std::ostream&os, const Bindings& bindings, StepID step_id) const;

	// Add this formula to the plan as a precondition of the given plan. Loop over all formulea and
	// add them appropriately.
	virtual void addAsPrecondition(Plan& plan, StepPtr step) const;

private:
	// The variable which needs to be made equal or unequal.
///	const Variable* variable_;
	const Term* variable_;

	// The term the variable must be made equal or unequal to.
	const Term* term_;

	// Make the variable equal or unequal to the term.
	bool make_equal_;
};

};

#endif
