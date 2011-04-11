//
// C++ Implementation: planner
//
// Description: 
//
//
// Author: Bram Ridder <bram@pc-bram>, (C) 2010
//
// Copyright: See COPYING file that comes with this distribution
//
//
#include <iostream>

#include "planner.h"
#include "plan.h"
#include "plan_flaws.h"
#include "type_manager.h"
#include "term_manager.h"
#include "action_manager.h"
#include "predicate_manager.h"
#include "plan_bindings.h"


///#define MYPOP_PLANNER_COMMENTS

namespace MyPOP {

bool ComparePlans::operator()(const Plan* p1, const Plan* p2)
{
	return p1->getSteps().size() + p1->getOpenConditions().size() + p1->getUnsafes().size() > p2->getSteps().size() + p2->getOpenConditions().size() + p2->getUnsafes().size();
}


Planner::Planner(const Plan& initial_plan, const ActionManager& action_manager, const TermManager& term_manager, const TypeManager& type_manager, const FlawSelectionStrategy& flaw_selector)
	: action_manager_(&action_manager), term_manager_(&term_manager), type_manager_(&type_manager), flaw_selector_(&flaw_selector), dead_ends_(0), plans_visited_(0)
{
	plans_.push(&initial_plan);
}


Planner::~Planner()
{
	while (!plans_.empty())
	{
		const Plan* plan = plans_.top();
		delete plan;
#ifdef MYPOP_PLANNER_COMMENTS
		std::cout << "Delete plan!" << std::endl;
#endif
		plans_.pop();
	}
}

const Plan* Planner::getSolution()
{
	// Continue planning until we run out of plans to try.
	while (!plans_.empty())
	{
		const Plan* current_plan = plans_.top();
#ifdef MYPOP_PLANNER_COMMENTS
		std::cout << "*** Current plan:" << std::endl << *current_plan << std::endl;
#endif
		plans_.pop();

		// If there are no more flaws to work on, return the plan!
		if (current_plan->getOpenConditions().size() == 0 && current_plan->getUnsafes().size() == 0)
		{
			std::cout << std::endl;
			return current_plan;
		}

		++plans_visited_;

		// Select the flaw to work on.
		const Flaw& flaw = flaw_selector_->selectFlaw(*current_plan);

		// Get all the refinements on this plan and put them into the queue.
		std::vector<const Plan*> refinements;
		flaw.handleFlaw(refinements, *this, *current_plan);
#ifdef MYPOP_PLANNER_COMMENTS
		std::cout << "Possible refinements:" << std::endl;
		for (std::vector<const Plan*>::const_iterator ci = refinements.begin(); ci != refinements.end(); ci++)
		{
			std::cout << **ci << std::endl;
		}
#endif

		if (refinements.size() == 0)
		{
#ifdef MYPOP_PLANNER_COMMENTS
			std::cout << "Dead end..." << std::endl;
#endif
			++dead_ends_;
		}

		// Delete plan after processing.
		delete current_plan;

		// Add all the new refinements into the queue.
		int size = plans_.size();
		for (std::vector<const Plan*>::const_iterator ci = refinements.begin(); ci != refinements.end(); ci++)
		{
			plans_.push(*ci);
		}
		assert (plans_.size() == size + refinements.size());

		if (plans_visited_ % 1000 == 5)
		{
			std::cout << "." << std::flush;
		}
	}

	std::cout << std::endl;
	return NULL;
}

bool Planner::separate(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe)
{
	// The threatening step.
	StepPtr clobberer = unsafe.getClobberer();

	// The threatened step.
	StepPtr threatened_step = (*unsafe.getLink()).getToStep();

	// The effect.
	const Atom& effect = unsafe.getEffect();

	// The condition.
	const Atom& condition = (*unsafe.getLink()).getCondition();
	
	bool separatable = false;

	for (unsigned int i = 0; i < effect.getArity(); i++)
	{
		const Term* effect_term = effect.getTerms()[i];
		const Term* condition_term = condition.getTerms()[i];

		// The refinement.
		Plan* new_plan = new Plan(plan);
		Bindings& bindings = new_plan->getBindings();

		if (effect_term->makeDisjunct(clobberer->getStepId(), *condition_term, threatened_step->getStepId(), bindings))
		{
			separatable = true;
			new_plan->removeUnsafe(unsafe);
			refinements.push_back(new_plan);
		}
		else
		{
			delete new_plan;
		}
	}

/*
		// If both are objects, there is little we can do since we have tested that both atoms
		// do affect eachother so the objects must be the same.
		if (effect_term->isObject() && condition_term->isObject())
		{
			continue;
		}

		// If one of the two is a variable, remove the object from the variable's domain.
		const Variable* variable = NULL;
		const Object* object = NULL;
		const StepPtr* step = NULL;
		if (effect_term->isObject() && condition_term->isVariable())
		{
			object = effect_term->asObject();
			variable = condition_term->asVariable();
			step = &threatened_step;
		}
		else if (effect_term->isVariable() && condition_term->isObject())
		{
			object = condition_term->asObject();
			variable = effect_term->asVariable();
			step = &clobberer;
		}
	
		// Otherwise, both terms are variables, introduce a not equal restriction.
		else
		{
			VariableBinding vb(clobberer->getStepId(), *effect_term->asVariable(), threatened_step->getStepId(), *condition_term->asVariable(), false);
			if (bindings.addBinding(vb))
			{
				// Remove the unsafe from the new plan.
				new_plan->removeUnsafe(unsafe);
				refinements.push_back(new_plan);
			}
			else
			{
				delete new_plan;
			}
			continue;
		}

		ObjectBinding ob((*step)->getStepId(), *variable, *object, false);
		if (bindings.addBinding(ob))
		{
			// Remove the unsafe from the new plan.
			new_plan->removeUnsafe(unsafe);
			refinements.push_back(new_plan);
			separatable = true;
		}
		else
		{
			delete new_plan;
		}
	}*/

	return separatable;
}

bool Planner::demote(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe)
{
	// Try to impose an ordering constraint where the clobberer is ordered before the threatened step.
	Plan* new_plan = new Plan(plan);
	Orderings& o = new_plan->getOrderings();

	// The threatening step.
	StepPtr clobberer = unsafe.getClobberer();

	// The threatened step.
	StepPtr threatened_step = (*unsafe.getLink()).getFromStep();

	Ordering new_ordering((*clobberer).getStepId(), StepTime::dummy_step_time, (*threatened_step).getStepId(), StepTime::dummy_step_time);
	if (!o.addOrdering(new_ordering))
	{
		delete new_plan;
		return false;
	}

	// Remove the unsafe from the new plan.
	new_plan->removeUnsafe(unsafe);

	refinements.push_back(new_plan);
	return true;
}

bool Planner::promote(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe)
{
	// Try to impose an ordering constraint where the clobberer is ordered before the threatened step.
	Plan* new_plan = new Plan(plan);
	Orderings& o = new_plan->getOrderings();

	// The threatening step.
	StepPtr clobberer = unsafe.getClobberer();

	// The threatened step.
	StepPtr threatened_step = (*unsafe.getLink()).getToStep();

	Ordering new_ordering((*threatened_step).getStepId(), StepTime::dummy_step_time, (*clobberer).getStepId(), StepTime::dummy_step_time);
	if (!o.addOrdering(new_ordering))
	{
		delete new_plan;
		return false;
	}

	// Remove the unsafe from the new plan.
	new_plan->removeUnsafe(unsafe);

	refinements.push_back(new_plan);
	return true;
}

void Planner::handleMutex(std::vector<const Plan*>& refinement, const Plan& plan, const Mutex& mutex)
{
	std::cout << "Function not yet implemented!" << std::endl;
	assert(false);
}

void Planner::handleUnsafe(std::vector<const Plan*>& refinements, const Plan& plan, const Unsafe& unsafe)
{
	// Check all ways in which we can refine an unsafe.

	// The threatening step.
	StepPtr threatening_step = unsafe.getClobberer();

	// The threatened step.
	StepPtr threatened_step = (*unsafe.getLink()).getToStep();

	// The effect.
	//const Atom& effect = unsafe.getEffect();

#ifdef MYPOP_PLANNER_COMMENTS
	std::cout << unsafe << std::endl;
	//std::cout << "Refine unsafe: " << *threatening_step << " -> " << *threatened_step << " Effect: ";
	//effect.print(std::cout);
	//std::cout << std::endl;
#endif
	
	// Check if this unsafe is still valid, it might already been solved due to other orderings
	// and separations constraints added to the plan in an attempt to resolve other unsafes as well.
	if (!plan.isThreat(unsafe))
	{
		Plan* new_plan = new Plan(plan);
		new_plan->removeUnsafe(unsafe);
		refinements.push_back(new_plan);
		return;
	}

	// Try to promote and demote the plan.
	promote(refinements, plan, unsafe);
	demote(refinements, plan, unsafe);

	// The last option is to separate the variables so they do not interfere.
	separate(refinements, plan, unsafe);
}

void Planner::handleOpenCondition(std::vector<const Plan*>& refinements, const Plan& plan, const OpenCondition& oc)
{
	// Check all ways in which we can refine an open condition.
	// Since we are only considering open conditions, check which actions can resolve this problem.
	StepPtr step = oc.getStep();
	const Atom& atom = oc.getAtom();

#ifdef MYPOP_PLANNER_COMMENTS
	std::cout << "Refine [" << step->getStepId() << "] ";
	atom.print(std::cout);
	std::cout << std::endl;
#endif

	// Find all actions which can achieve the asked atom.
	std::vector<std::pair<const Action*, const Atom*> > actions;
	action_manager_->getAchievingActions(actions, atom);
	
#ifdef MYPOP_PLANNER_COMMENTS
	std::cout << "--- Possible achievers: " << std::endl;
#endif

	for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator ci = actions.begin(); ci != actions.end(); ci++)
	{
		const Action* achieving_action = (*ci).first;
		const Atom* achieving_action_effect = (*ci).second;

#ifdef MYPOP_PLANNER_COMMENTS
		std::cout << *achieving_action << std::endl;
#endif

		// The new step to be added.
		Plan* new_plan = new Plan(plan);
		StepPtr new_step = new_plan->createStep(*achieving_action);

		// Create a causal link.
		if (!new_plan->createCausalLink(new_step, *achieving_action_effect, oc, true))
		{
#ifdef MYPOP_PLANNER_COMMENTS
			std::cout << "Could not be impose causal link :(" << std::endl;
#endif
			delete new_plan;
			continue;
		}

#ifdef MYPOP_PLANNER_COMMENTS
		std::cout << *new_plan << std::endl;
#endif
		refinements.push_back(new_plan);
	}

	// Next check if we can reuse any of the actions from the plan.
	const std::vector<StepPtr>& steps = plan.getSteps();
#ifdef MYPOP_PLANNER_COMMENTS
	std::cout << "--- Possible actions to reuse: " << std::endl;
#endif
	for (std::vector<StepPtr>::const_iterator ci = steps.begin(); ci != steps.end(); ci++)
	{
		StepPtr existing_step = *ci;

		// Check if the step can be ordered before the step we want to support.
		if (!plan.getOrderings().canBeOrderedBefore((*existing_step).getStepId(), StepTime::dummy_step_time, (*step).getStepId(), StepTime::dummy_step_time))
		{
#ifdef MYPOP_PLANNER_COMMENTS
			std::cout << "We cannot order " << *existing_step << " before " << *step << std::endl;
#endif
			continue;
		}

		// Get the action.
		const Action& action = (*existing_step).getAction();
#ifdef MYPOP_PLANNER_COMMENTS
		std::cout << action << std::endl;
#endif

		// Check if any of the effects can satisfy the open condition.
		std::vector<const Atom*> achieving_effects;
		action.getAchievingEffects(atom, achieving_effects);

		// Check if any of these can be unified within the existing plan.
		for (std::vector<const Atom*>::const_iterator ci = achieving_effects.begin(); ci != achieving_effects.end(); ci++)
		{
			const Atom* achieving_effect = *ci;

			// Create a new plan with this action as the causal link.
			Plan* new_plan = new Plan(plan);
			if (!new_plan->createCausalLink(existing_step, *achieving_effect, oc, false))
			{
#ifdef MYPOP_PLANNER_COMMENTS
				std::cout << "Could not be impose causal link :(" << std::endl;
#endif
				delete new_plan;
				continue;
			}

#ifdef MYPOP_PLANNER_COMMENTS
			std::cout << *new_plan << std::endl;
#endif
			refinements.push_back(new_plan);
		}
	}
}

};

