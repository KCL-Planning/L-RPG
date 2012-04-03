#include "plan_flaws.h"
#include "plan.h"
#include "formula.h"
#include "planner.h"

namespace MyPOP {

OpenCondition::OpenCondition(StepPtr step, const Atom& condition)
	: step_(step), condition_(&condition)
{
//	if (step_->getStepId() > 100)
//	{
//		assert(false);
//	}
}

void OpenCondition::handleFlaw(std::vector<const Plan*>& refinements, Planner& planner, const Plan& plan) const 
{
	planner.handleOpenCondition(refinements, plan, *this);
}

Unsafe::Unsafe(StepPtr clobberer, const Atom& effect, LinkPtr link)
	: clobberer_(clobberer), effect_(&effect), link_(link)
{
	
}

void Unsafe::handleFlaw(std::vector<const Plan*>& refinements, Planner& planner, const Plan& plan) const
{
	planner.handleUnsafe(refinements, plan, *this);
}

std::ostream& operator<<(std::ostream& os, const Unsafe& other)
{
	os << "# " << *other.clobberer_ << "{";
	os << "} -> {" << (*other.link_) << "}";
	return os;
}

Mutex::Mutex(StepPtr step1, const Atom& effect1, StepPtr step2, const Atom& effect2)
	: step1_(step1), effect1_(&effect1), step2_(step2), effect2_(&effect2)
{
	
}

void Mutex::handleFlaw(std::vector<const Plan*>& refinements, Planner& planner, const Plan& plan) const
{
	planner.handleMutex(refinements, plan, *this);
}

};
