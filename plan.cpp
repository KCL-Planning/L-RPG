#include <set>

#include "plan.h"
#include "action_manager.h"
#include "term_manager.h"
#include "type_manager.h"
#include "predicate_manager.h"
#include "plan_bindings.h"
#include "plan_orderings.h"
#include "formula.h"
#include "plan_flaws.h"
#include "logging.h"
#include "exceptions.h"

namespace MyPOP {

int Plan::plan_counter_ = -1;

/*************************
 * The Step class
 *************************/

const Step* Step::dummy_step = StepPtr(new Step(Step::INVALID_STEP, *Action::dummy_action)).get();

std::ostream& operator<<(std::ostream& os, const Step& step)
{
	os << "Step [" << step.stepId_ << "] " << *step.action_;
	// On the next lines print the preconditions which must be satisfied.
//	step.action_->getPrecondition().print(os);
	const Formula& precondition = step.action_->getPrecondition();
//	step.printFormula(os, precondition);
	precondition.print(os);
	os << std::endl;
	return os;
}

/*************************
 * The Link class
 *************************/
Link::Link (StepPtr from_step, StepPtr to_step, const Atom& condition)
	: from_step_(from_step), to_step_(to_step), condition_(&condition)
{

}

std::ostream& operator<<(std::ostream& os, const Link& other)
{
	os << *other.from_step_ << " -> {";
	other.condition_->print(os);
	os << "} " << *other.to_step_ << std::endl;
	return os;
}

/*************************
 * The Plan class
 *************************/
Plan::Plan(const ActionManager& action_manager, const TermManager& term_manager, const TypeManager& type_manager, const BindingsPropagator& propagator)
	: plan_id_(plan_counter_++), action_manager_(&action_manager), term_manager_(&term_manager), type_manager_(&type_manager), bindings_(new Bindings(term_manager, propagator)), orderings_(new BinaryOrderings())
{

}

/**
 * Currently we make deep copies for plans, this is NOT optimal nor even quick
 * but for testing it works for now...
 */
Plan::Plan(const Plan& plan)
	: plan_id_(plan_counter_++), action_manager_(plan.action_manager_), term_manager_(plan.term_manager_), type_manager_(plan.type_manager_)
{
	for (std::vector<StepPtr>::const_iterator ci = plan.steps_.begin(); ci != plan.steps_.end(); ci++)
		steps_.push_back(*ci);

	for (std::vector<OpenConditionPtr>::const_iterator ci = plan.open_conditions_.begin(); ci != plan.open_conditions_.end(); ci++)
		open_conditions_.push_back(*ci);

	for (std::vector<LinkPtr>::const_iterator ci = plan.causal_links_.begin(); ci != plan.causal_links_.end(); ci++)
		causal_links_.push_back(*ci);

	for (std::vector<UnsafePtr>::const_iterator ci = plan.unsafes_.begin(); ci != plan.unsafes_.end(); ci++)
		unsafes_.push_back(*ci);

	for (std::vector<MutexPtr>::const_iterator ci = mutexes_.begin(); ci != mutexes_.end(); ci++)
		mutexes_.push_back(*ci);

	bindings_ = new Bindings(*plan.bindings_);
	orderings_ = new BinaryOrderings(*plan.orderings_);
}

Plan::~Plan()
{
	delete bindings_;
	delete orderings_;
}

void Plan::makeInitialPlan(const Action& initial_action, const Action& goal_action)
{
	// Create the initial step, which is a custom action with the atoms of the initial state as its effects.
	StepPtr initial_step = createStep(initial_action);

	// Create the goal, which is a custom action with the goal atoms as preconditions.
	StepPtr goal_step = createStep(goal_action);

	// Order the initial step before the goal step.
	Ordering ordering((*initial_step).getStepId(), StepTime::dummy_step_time, (*goal_step).getStepId(), StepTime::dummy_step_time);
	assert (orderings_->addOrdering(ordering));
	orderings_->print(std::cout);
}

StepPtr Plan::createStep(const Action& new_action)
{
	//const Step* new_step = new Step(steps_.size(), new_action);
	StepID new_step_id = bindings_->createVariableDomains(new_action);
	StepPtr new_step(new Step(new_step_id, new_action));
	steps_.push_back(new_step);

	/*StepPtr new_step(new Step(steps_.size(), new_action));
	steps_.push_back(new_step);

	// Create a new variable domain for every variable in this step.
	const std::vector<const Variable*>& variables = new_action.getVariables();
	for (std::vector<const Variable*>::const_iterator ci = variables.begin(); ci != variables.end(); ci++)
	{
		bindings_->createVariableDomain(new_step->getStepId(), **ci);

		try
		{
			bindings_->getVariableDomain(new_step->getStepId(), **ci);
		}
		catch (RequestNonExistingVariableBindingException e)
		{
			assert(false);
		}
	}*/

	// Add all the preconditions new open conditions to the plan.
	// Note: The goal must be added after initializing the variable domain as the preconditions might impose
	// constraints between them.
	addGoal(new_action.getPrecondition(), new_step);

	// Order the step after the initial state and before the goal state.
	Ordering after_initial_state(0, StepTime::dummy_step_time, new_step_id, StepTime::dummy_step_time);
	orderings_->addOrdering(after_initial_state);

	Ordering before_goal_state(new_step_id, StepTime::dummy_step_time, 1, StepTime::dummy_step_time);
	orderings_->addOrdering(before_goal_state);

	return new_step;
}

bool Plan::createCausalLink(StepPtr from_step, const Atom& supporting_effect, const OpenCondition& open_condition, bool is_new_step)
{
	// Create the causal link.
	LinkPtr link(new Link(from_step, open_condition.getStep(), open_condition.getAtom()));

	// Remove the open condition from the plan.
	for (std::vector<OpenConditionPtr>::iterator i = open_conditions_.begin(); i != open_conditions_.end(); i++)
	{
		if ((*i).get() == &open_condition)
		{
			open_conditions_.erase(i);
			break;
		}
	}

	// Add the new link.
	causal_links_.push_back(link);

	// Add the orderings to the plan.
	Ordering order((*from_step).getStepId(), StepTime::dummy_step_time, (*open_condition.getStep()).getStepId(), StepTime::dummy_step_time);
	bool can_be_ordered = orderings_->addOrdering(order);
	if (!can_be_ordered)
	{
		return false;
	}

	// Check if the bindings can be enforced on the achieving action.
	const std::vector<const Term*>& bounded_terms = open_condition.getAtom().getTerms();
	const std::vector<const Term*>& supporting_action_terms = supporting_effect.getTerms();
			
	bool can_unify = true;
	for (unsigned int i = 0; i < bounded_terms.size(); i++)
	{
		const Term* bounded_term = bounded_terms[i];
		
		// Impose the same constraints on the achieving action.
		const Term* action_term = supporting_action_terms[i];

		// Check if these terms can be unified.
///		if (!bindings_->unify(*bounded_term, open_condition.getStep()->getStepId(), *action_term, from_step->getStepId()))
		if (!bounded_term->canUnify(open_condition.getStep()->getStepId(), *action_term, from_step->getStepId(), *bindings_))
		{
			can_unify = false;
			break;
		}
	}
		
	if (!can_unify)
	{
		if (Logging::verbosity <= Logging::INFO)
		{
			std::cout << "Could not be unified :(" << std::endl;
		}
		return false;
	}
	
	checkLinkThreats(link);

	// When we introduced a new step, make sure to check which causal links it threatens.
	if (is_new_step)
	{
		checkStepThreats(from_step);
	}

	return true;
}

void Plan::checkStepThreats(StepPtr step)
{
	// If the ordering can be imposed, we need to check if there are any threads to this newly established
	// causal link. The most basic one is when the effect of this causal link negates another effect which
	// could take place at the same time.
	for (std::vector<LinkPtr>::const_iterator ci = causal_links_.begin(); ci != causal_links_.end(); ci++)
	{
		LinkPtr link = *ci;
		checkThreat(step, link);
	}
}

void Plan::checkLinkThreats(LinkPtr link)
{
	// If the ordering can be imposed, we need to check if there are any threads to this newly established
	// causal link. The most basic one is when the effect of this causal link negates another effect which
	// could take place at the same time.
	for (std::vector<StepPtr>::const_iterator ci = steps_.begin(); ci != steps_.end(); ci++)
	{
		StepPtr step = *ci;
		checkThreat(step, link);
	}
}

bool Plan::isThreat(const Unsafe& unsafe) const
{
	StepPtr step = unsafe.getClobberer();
	StepPtr from_step = (*unsafe.getLink()).getFromStep();
	StepPtr to_step = (*unsafe.getLink()).getToStep();
	const Atom& condition = (*unsafe.getLink()).getCondition();

	// First of all check if this step could potentially interfere. I.e. it can be ordered before the
	// step related to the open condition or after the step which satisfies it.
	if (!orderings_->canBeOrderedBefore((*step).getStepId(), StepTime::dummy_step_time, (*to_step).getStepId(), StepTime::dummy_step_time) ||
		!orderings_->canBeOrderedAfter((*step).getStepId(), StepTime::dummy_step_time, (*from_step).getStepId(), StepTime::dummy_step_time))
	{
		if (Logging::verbosity <= Logging::DEBUG)
		{
			std::cout << "Ordering cannot be imposed for the step to be a threat!" << unsafe << std::endl;
		}
		return false;
	}

	// Also make sure the step is not the step supporting the link.

	const Action& action = (*step).getAction();

	// Check if one of its effects could delete the literal we try to support.
	for (std::vector<const Atom*>::const_iterator ci = action.getEffects().begin(); ci != action.getEffects().end(); ci++)
	{
		const Atom* effect = *ci;

		if (bindings_->affects(*effect, step->getStepId(), condition, to_step->getStepId()))
		{
			return true;
		}
	}

	return false;
}

void Plan::checkThreat(StepPtr step, LinkPtr link)
{
	StepPtr from_step = (*link).getFromStep();
	StepPtr to_step = (*link).getToStep();
	const Atom& condition = (*link).getCondition();

	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "Check treat by " << step->getStepId() << " to " << *link << std::endl;
	}

	// First of all check if this step could potentially interfere. I.e. it can be ordered before the
	// step related to the open condition or after the step which satisfies it.
	if (!orderings_->canBeOrderedBefore((*step).getStepId(), StepTime::dummy_step_time, (*to_step).getStepId(), StepTime::dummy_step_time) ||
		!orderings_->canBeOrderedAfter((*step).getStepId(), StepTime::dummy_step_time, (*from_step).getStepId(), StepTime::dummy_step_time))
	{
		if (Logging::verbosity <= Logging::DEBUG)
		{
			std::cout << "Ordering cannot be imposed for the step to be a threat!" << *link << std::endl;
		}
		return;
	}

	// Also make sure the step is not the step supporting the link.

	const Action& action = (*step).getAction();

	// Check if one of its effects could delete the literal we try to support.
	for (std::vector<const Atom*>::const_iterator ci = action.getEffects().begin(); ci != action.getEffects().end(); ci++)
	{
		const Atom* effect = *ci;

		if (bindings_->affects(*effect, step->getStepId(), condition, to_step->getStepId()))
		{
			// Found a new unsafe!
			UnsafePtr unsafe(new Unsafe(step, *effect, link));
			
			if (Logging::verbosity <= Logging::DEBUG)
			{
				std::cout << "Found an unsafe relation: " << *unsafe << std::endl;
			}
			
			unsafes_.push_back(unsafe);
		}
		else if (Logging::verbosity <= Logging::DEBUG)
		{
			std::cout << "Does not affect!" << *link << std::endl;
		}
	}
}

void Plan::addOpenCondition(OpenConditionPtr open_condition)
{
	open_conditions_.push_back(open_condition);
}

void Plan::addGoal(const Formula& goal, StepPtr step)
{
	goal.addAsPrecondition(*this, step);
}

void Plan::removeUnsafe(const Unsafe& unsafe)
{
	for (std::vector<UnsafePtr>::iterator i = unsafes_.begin(); i != unsafes_.end(); i++)
	{
		if ((*i).get() == &unsafe)
		{
			unsafes_.erase(i);
			return;
		}
	}

	// Don't allow the program to try to remove an unsafe which doesn't exist!
	assert(false);
}

void Plan::addUnsafe(UnsafePtr unsafe)
{
	unsafes_.push_back(unsafe);
}


std::ostream& operator<<(std::ostream& os, const Plan& plan)
{
	os << "Plan: [" << plan.plan_id_ << "]" << plan.getSteps().size() + plan.getOpenConditions().size() + plan.getUnsafes().size() << std::endl;
	
	// We want to print the plan in chronological order, starting with the initial state.
	std::set<int> closed_list;
	
	// Continue until we have printed all steps.
	while (closed_list.size() != plan.steps_.size())
	{
		for (std::vector<StepPtr>::const_iterator ci = plan.steps_.begin(); ci != plan.steps_.end(); ci++)
		{
			const Step* step = (*ci).get();
			
			// Check if this step has already been processed.
			if (closed_list.find(step->getStepId()) != closed_list.end())
				continue;
			
			// Check if all steps which support the preconditions of this step have already been printed.
			bool supporting_steps_printed = true;
			for (std::vector<LinkPtr>::const_iterator lci = plan.causal_links_.begin(); lci != plan.causal_links_.end(); lci++)
			{
				const Link& link = **lci;
				if ((*link.getToStep()).getStepId() == step->getStepId())
				{
					if (closed_list.find((*link.getFromStep()).getStepId()) == closed_list.end())
					{
						supporting_steps_printed = false;
						break;
					}
				}
			}

			// Check if all steps which are ordered before this step have already been printed.
			for (std::vector<StepPtr>::const_iterator ci2 = plan.steps_.begin(); ci2 != plan.steps_.end(); ci2++)
			{
				if (ci == ci2)
				{
					continue;
				}

				if (plan.getOrderings().canBeOrderedBefore((*ci2)->getStepId(), StepTime::dummy_step_time, (*ci)->getStepId(), StepTime::dummy_step_time) && !plan.getOrderings().canBeOrderedAfter((*ci2)->getStepId(), StepTime::dummy_step_time, (*ci)->getStepId(), StepTime::dummy_step_time))
				{
					if (closed_list.find((*ci2)->getStepId()) == closed_list.end())
					{
						supporting_steps_printed = false;
						break;
					}
				}
			}
			if (!supporting_steps_printed)
			{
				continue;
			}

			closed_list.insert(step->getStepId());
			
			os << "Step " << step->getStepId() << "\t: ";
			step->getAction().print(os, plan.getBindings(), step->getStepId());
			os << std::endl;

			// If this step is the initial action, show all the atoms which are true in the initial state.
			if (step->getStepId() == Step::INITIAL_STEP)
			{
				for (std::vector<const Atom*>::const_iterator aci = step->getAction().getEffects().begin(); aci != step->getAction().getEffects().end(); aci++)
				{
					(*aci)->print(os);
					if (aci + 1 != step->getAction().getEffects().end())
						os << ", ";
				}
				os << std::endl;
			}

			// Check if there are open conditions refering to this step.
			for (std::vector<OpenConditionPtr>::const_iterator oci = plan.open_conditions_.begin(); oci != plan.open_conditions_.end(); oci++)
			{
				const OpenCondition* oc = (*oci).get();
				// Check if the open condition referes to the same step.
				if (oc->getStep()->getStepId() == step->getStepId())
				{
					const Atom& atom = oc->getAtom();

					os << "\t";
					atom.print(os);
					os << " <- ???" << std::endl;
				}
			}

			// Do the same for causal links established to this step.
			for (std::vector<LinkPtr>::const_iterator lci = plan.causal_links_.begin(); lci != plan.causal_links_.end(); lci++)
			{
				const Link& link = **lci;

				if ((*link.getToStep()).getStepId() == step->getStepId())
				{
					const Atom& atom = link.getCondition();

					// This should only happen if we add more complex open conditions. Not much of a concern
					// at this moment.
					//if (atom != NULL)
					{
						os << "\t";
						atom.print(os);
						os << " <- " << (*link.getFromStep()).getStepId() << std::endl;
					}
				}
			}
		}
	}
	os << std::endl;

	// Print out all the unsafes.
	for (std::vector<UnsafePtr>::const_iterator ci = plan.unsafes_.begin(); ci != plan.unsafes_.end(); ci++)
	{
		os << **ci;
		if (ci + 1 != plan.unsafes_.end())
		{
			os << ", ";
		}
		os << std::endl;
	}

	// Print out the bindings.
	os << *plan.bindings_ << std::endl;
	os << "Orderings: { ";
	plan.orderings_->print(os);
	os << " }" << std::endl;
	return os;
}

};
