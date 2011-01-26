#ifndef MYPOP_FLAWS_H
#define MYPOP_FLAWS_H

#include <vector>

#include "formula.h"
#include "pointers.h"

namespace MyPOP {

class Planner;
class Plan;

class Flaw
{
public:
	virtual ~Flaw() {}

	/**
	 * In order to avoid having to dynamic cast in the Planner class after a flaw has
	 * been selected to be handled. Every flaw implements this function which will call
	 * the appropriate function for the planner.
	 * Suppose it's bit of a doggy design, but the best I could come up with for now.
	 * An alternative approach would be to add pointers to this class to every base class
	 * so we can probe Flaw which of the pointers isn't NULL as to determine the actual
	 * class and retrive a pointer to it, i.e.
	 *
	 * class Flaw
	 * {
	 * private:
	 *    const OpenCondition* oc_pointer_;
	 *    const Unsafe* us_pointer_;
	 *    const Mutex* m_pointer_;
	 * };
	 */
	virtual void handleFlaw(std::vector<const Plan*>& refinements, Planner& planner, const Plan& plan) const = 0;
};

/**
 * An open condition in a plan is a flaw caused by a precondition of an action
 * not being satisfied. The only way to resolve an open condition is by adding
 * a causal link to support the open condition.
 */
class OpenCondition : public Flaw
{

public:
	// Create a new open condition.
	OpenCondition(StepPtr step, const Atom& condition);

	// Get the step who has this open condition.
	StepPtr getStep() const { return step_; }

	// Get the actual open condition as an atom, if the open condition was not
	// an atom this function returns NULL.
	const Atom& getAtom() const { return *condition_; }

	// Call the function to handle open conditions in planner.
	virtual void handleFlaw(std::vector<const Plan*>& refinements, Planner& planner, const Plan& plan) const;

private:
	// The step which has an open condition.
	StepPtr step_;

	// The actual open conditions.
	const Atom* condition_;
};

/**
 * An unsafe relation exists when an effect of an action can negate a causal link
 * in which case we either have to promote, demote or separate the threatening action
 * (the clobberer).
 */
class Unsafe : public Flaw
{

public:
	// Create a new mutex relation.
	Unsafe(StepPtr clobberer, const Atom& effect, LinkPtr link);

	// Get the step which threatens the causal link.
	StepPtr getClobberer() const { return clobberer_; }

	// Get the effect which negates the supported atom.
	const Atom& getEffect() const { return *effect_; }

	//Get the link which is threatened.
	LinkPtr getLink() const { return link_; }

	// Call the function to handle unsafes in planner.
	virtual void handleFlaw(std::vector<const Plan*>& refinements, Planner& planner, const Plan& plan) const;

	friend std::ostream& operator<<(std::ostream& os, const Unsafe& other);
private:
	// The step which actually threatens the causal link.
	StepPtr clobberer_;
	
	// The effect which negates the atom supported by the causal link.
	const Atom* effect_;
	
	// The link which is treatened.
	LinkPtr link_;
};

std::ostream& operator<<(std::ostream& os, const Unsafe& other);

/**
 * A mutex relation exists between steps if they both achieve the same atom but one is the
 * negative of the other.
 */
class Mutex : public Flaw
{
public:
	Mutex(StepPtr step1, const Atom& effect1, StepPtr step2, const Atom& effect2);
	
	// Call the function to handle mutexes in planner.
	virtual void handleFlaw(std::vector<const Plan*>& refinements, Planner& planner, const Plan& plan) const;

private:
	StepPtr step1_;
	const Atom* effect1_;
	StepPtr step2_;
	const Atom* effect2_;
};


};

#endif
