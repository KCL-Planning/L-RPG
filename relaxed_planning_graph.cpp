#include "relaxed_planning_graph.h"
#include "action_manager.h"
#include "bindings_propagator.h"
#include "plan.h"
#include "plan_bindings.h"
#include "parser_utils.h"
#include "formula.h"

namespace MyPOP {

namespace RPG {

FactLayer::FactLayer(const Bindings& bindings)
	: bindings_(&bindings)
{

}

FactLayer::FactLayer(const FactLayer& fact_layer)
	: bindings_(fact_layer.bindings_)
{
	facts_.insert(facts_.begin(), fact_layer.facts_.begin(), fact_layer.facts_.end());
}

bool FactLayer::addFact(const BoundedAtom& bounded_atom)
{
	// Check if any of the existing facts can be unified with the given bounded atom. If this is the case
	// this atom will not be added.
	for (std::vector<BoundedAtom>::const_iterator ci = facts_.begin(); ci != facts_.end(); ci++)
	{
		if (bounded_atom.second->isNegative() == (*ci).second->isNegative() && bindings_->canUnify(*bounded_atom.second, bounded_atom.first, *(*ci).second, (*ci).first))
		{
			return false;
		}
	}
	facts_.push_back(bounded_atom);
	return true;
}

RelaxedPlanningGraph::RelaxedPlanningGraph(const ActionManager& action_manager, const Plan& initial_plan)
	: bindings_(new Bindings(initial_plan.getBindings()))
{
	const Action& initial_state_action = initial_plan.getSteps()[0]->getAction();
	FactLayer* current_fact_layer = new FactLayer(*bindings_);
	//std::set<BoundedAtom, CompareBoundedAtoms> current_fact_layer(compare_bounded_atoms);
	
	for (std::vector<const Atom*>::const_iterator ci = initial_state_action.getEffects().begin(); ci != initial_state_action.getEffects().end(); ci++)
	{
		current_fact_layer->addFact(std::make_pair<StepID, const Atom*>(Step::INITIAL_STEP, *ci));
		//current_fact_layer.insert(std::make_pair<StepID, const Atom*>(Step::INITIAL_STEP, *ci));
	}
	FactLayer* next_fact_layer = new FactLayer(*current_fact_layer);
	FactLayer* initial_fact_layer = new FactLayer(*current_fact_layer);
	fact_layers_.push_back(initial_fact_layer);

	// First we will ground all the actions.
	std::vector<const Step*> all_grounded_actions;
	for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
	{
		const Action* action = *ci;
		std::vector<const Step*> grounded_actions;
		action_manager.ground(*bindings_, grounded_actions, *action);
		all_grounded_actions.insert(all_grounded_actions.end(), grounded_actions.begin(), grounded_actions.end());
	}

	// Now check for each grounded action which one is applicable in the current fact layer.
	while (true)
	{
		std::vector<const Step*>* new_action_layer = new std::vector<const Step*>();
		for (std::vector<const Step*>::const_iterator action_ci = all_grounded_actions.begin(); action_ci != all_grounded_actions.end(); action_ci++)
		{
			// Check if all preconditions are satisfied in the current layer.
			const Action& grounded_action = (*action_ci)->getAction();
			StepID grounded_action_id = (*action_ci)->getStepId();
			const Formula& precondition_formula = grounded_action.getPrecondition();
			std::vector<const Atom*> preconditions;
			Utility::convertFormula(preconditions, &precondition_formula);

			bool preconditions_are_satisfied = true;
			for (std::vector<const Atom*>::const_iterator precondition_ci = preconditions.begin(); precondition_ci != preconditions.end(); precondition_ci++)
			{
				const Atom* precondition = *precondition_ci;
				bool precondition_satisfied = false;

				for (std::vector<BoundedAtom>::const_iterator layer_ci = current_fact_layer->getFacts().begin(); layer_ci != current_fact_layer->getFacts().end(); layer_ci++)
				{
					if (precondition->isNegative() == (*layer_ci).second->isNegative() && bindings_->canUnify(*precondition, grounded_action_id, *(*layer_ci).second, (*layer_ci).first))
					{
						precondition_satisfied = true;
						break;
					}
				}

				if (!precondition_satisfied)
				{
					preconditions_are_satisfied = false;
					break;
				}
			}

			// If all preconditions are satisfied, add all the action's effects to the new layer.
			if (preconditions_are_satisfied)
			{
				//std::cout << "Add effects: ";
				for (std::vector<const Atom*>::const_iterator ci = grounded_action.getEffects().begin(); ci != grounded_action.getEffects().end(); ci++)
				{
					//std::cout << "* ";
					//(*ci)->print(std::cout, *bindings_, grounded_action_id);
					//std::cout << std::endl;
					next_fact_layer->addFact(std::make_pair(grounded_action_id, *ci));
				}
				std::cout << std::endl;

				// Add this action to the action layer.
				new_action_layer->push_back(new Step(grounded_action_id, grounded_action));
			}
		}

		// If the next and current layer are the same, we have reached the level off point and we can stop.
		if (current_fact_layer->getFacts().size() == next_fact_layer->getFacts().size())
		{
			for (std::vector<const Step*>::iterator step_ci = new_action_layer->begin(); step_ci != new_action_layer->end(); step_ci++)
			{
				delete *step_ci;
			}
			delete new_action_layer;
			break;
		}

		// Prepare the layers for the next iterator. Facts once achieved stay achieved.
		current_fact_layer = next_fact_layer;
		next_fact_layer = new FactLayer(*current_fact_layer);

		// Add the action and fact layer to the RPG:
		action_layers_.push_back(new_action_layer);
		fact_layers_.push_back(next_fact_layer);
	}
}


RelaxedPlanningGraph::~RelaxedPlanningGraph()
{

}

std::ostream& operator<<(std::ostream& os, const RelaxedPlanningGraph& rpg)
{
	// Start with the initial fact layer.
	const std::vector<FactLayer* >& fact_layers = rpg.getFactLayers();
	const std::vector<std::vector<const Step*>* >& action_layers = rpg.getActionLayers();

	if (fact_layers.size() - 1 != action_layers.size())
	{
		std::cout << "Fact layers: " << fact_layers.size() << std::endl;
		std::cout << "Action layers: " << action_layers.size() << std::endl;
		assert (false);
	}
	for (unsigned int i = 0; i < action_layers.size(); i++)
	{
		std::cout << "Fact layer " << i << std::endl;
		for (std::vector<BoundedAtom>::const_iterator facts_ci = fact_layers[i]->getFacts().begin(); facts_ci != fact_layers[i]->getFacts().end(); facts_ci++)
		{
			(*facts_ci).second->print(std::cout, rpg.getBindings(), (*facts_ci).first);
			std::cout << std::endl;
		}

		std::cout << "Action layer " << i << std::endl;
		for (std::vector<const Step*>::const_iterator actions_ci = action_layers[i]->begin(); actions_ci != action_layers[i]->end(); actions_ci++)
		{
			const Step* step = *actions_ci;
			step->getAction().print(std::cout, rpg.getBindings(), step->getStepId());
			std::cout << std::endl;
		}
	}

	// The last layer is the last fact layer.
	std::cout << "Fact layer " << fact_layers.size() - 1 << std::endl;
	for (std::vector<BoundedAtom>::const_iterator facts_ci = fact_layers[fact_layers.size() - 1]->getFacts().begin(); facts_ci != fact_layers[fact_layers.size() - 1]->getFacts().end(); facts_ci++)
	{
		(*facts_ci).second->print(std::cout, rpg.getBindings(), (*facts_ci).first);
		std::cout << std::endl;
	}
	return os;
}

};

};
