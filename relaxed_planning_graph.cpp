#include "relaxed_planning_graph.h"
#include "action_manager.h"
#include "bindings_propagator.h"
#include "plan.h"
#include "plan_bindings.h"
#include "parser_utils.h"
#include "formula.h"
#include "predicate_manager.h"
#include "SAS/dtg_manager.h"
#include "SAS/equivalent_object_group.h"
#include "SAS/dtg_reachability.h"

///#define MYPOP_RPG_RELAXED_PLANNING_GRAPH

namespace MyPOP {

namespace RPG {

	
ResolvedAction::ResolvedAction(const Action& action, StepID step_id, const Bindings& bindings, const SAS_Plus::EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
	: step_id_(step_id), action_(&action), bindings_(&bindings)
{
	const Formula& precondition_formula = action.getPrecondition();
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &precondition_formula);
	
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
	{
		const Atom* precondition = *ci;
		SAS_Plus::ResolvedBoundedAtom* resolved_precondition = new SAS_Plus::ResolvedBoundedAtom(step_id, *precondition, bindings, eog_manager, predicate_manager);
		preconditions_.push_back(resolved_precondition);
	}
	
	for (std::vector<const Atom*>::const_iterator ci = action.getEffects().begin(); ci != action.getEffects().end(); ci++)
	{
		SAS_Plus::ResolvedBoundedAtom* resolved_effect = new SAS_Plus::ResolvedBoundedAtom(step_id, **ci, bindings, eog_manager, predicate_manager);
		effects_.push_back(resolved_effect);
	}
}

ResolvedAction::~ResolvedAction()
{
	for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = preconditions_.begin(); ci != preconditions_.end(); ci++)
	{
		delete *ci;
	}
	
	for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
	{
		delete *ci;
	}
}

std::ostream& operator<<(std::ostream& os, const ResolvedAction& resolved_action)
{
	resolved_action.getAction().print(os, resolved_action.getBindings(), resolved_action.getStepID());
	return os;
}

FactLayer::FactLayer(bool delete_facts)
	: delete_facts_(delete_facts)
{
}
	
FactLayer::FactLayer(const FactLayer& fact_layer)
	: delete_facts_(false)
{
	facts_.insert(facts_.begin(), fact_layer.facts_.begin(), fact_layer.facts_.end());
	mapped_facts_.insert(fact_layer.mapped_facts_.begin(), fact_layer.mapped_facts_.end());
}

FactLayer::~FactLayer()
{
	for (std::vector<std::vector<const SAS_Plus::ResolvedBoundedAtom*>*>::const_iterator ci = mapped_facts_to_remove_.begin(); ci != mapped_facts_to_remove_.end(); ci++)
	{
		delete *ci;
	}
	
	if (delete_facts_)
	{
		for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = facts_.begin(); ci != facts_.end(); ci++)
		{
			delete *ci;
		}
	}
}

bool FactLayer::addFact(const SAS_Plus::ResolvedBoundedAtom& bounded_atom)
{
	// Check if any of the existing facts can be unified with the given bounded atom. If this is the case
	// this atom will not be added.
	std::string unique_name = getUniqueName(bounded_atom);
	
	std::map<std::string, std::vector<const SAS_Plus::ResolvedBoundedAtom*>* >::iterator i = mapped_facts_.find(unique_name);
	std::vector<const SAS_Plus::ResolvedBoundedAtom*>* mapping = NULL;
	if (i == mapped_facts_.end())
	{
		mapping = new std::vector<const SAS_Plus::ResolvedBoundedAtom*>();
		mapped_facts_[getUniqueName(bounded_atom)] = mapping;
		mapped_facts_to_remove_.push_back(mapping);
	}
	else
	{
		mapping = (*i).second;
		
		for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = mapping->begin(); ci != mapping->end(); ci++)
		{
			if (bounded_atom.getOriginalAtom().isNegative() == (*ci)->getOriginalAtom().isNegative() &&
			    bounded_atom.canUnifyWith(**ci))
			{
				return false;
			}
		}
	}
	
	facts_.push_back(&bounded_atom);
	mapping->push_back(&bounded_atom);
	
	return true;
}

const std::vector<const SAS_Plus::ResolvedBoundedAtom*>* FactLayer::getFacts(const SAS_Plus::ResolvedBoundedAtom& precondition) const
{
	std::map<std::string, std::vector<const SAS_Plus::ResolvedBoundedAtom*>* >::const_iterator i = mapped_facts_.find(getUniqueName(precondition));
	if (i == mapped_facts_.end())
	{
		return NULL;
	}
	return (*i).second;
}

std::string FactLayer::getUniqueName(const SAS_Plus::ResolvedBoundedAtom& atom) const
{
	return atom.getOriginalAtom().getPredicate().getName();
}


RelaxedPlanningGraph::RelaxedPlanningGraph(const ActionManager& action_manager, const Plan& initial_plan, const SAS_Plus::EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
	: bindings_(new Bindings(initial_plan.getBindings()))
{
	const Action& initial_state_action = initial_plan.getSteps()[0]->getAction();
	FactLayer* initial_fact_layer = new FactLayer(true);
	
	for (std::vector<const Atom*>::const_iterator ci = initial_state_action.getEffects().begin(); ci != initial_state_action.getEffects().end(); ci++)
	{
//		SAS_Plus::BoundedAtom* new_bounded_atom = new SAS_Plus::BoundedAtom(Step::INITIAL_STEP, **ci);
//		SAS_Plus::ResolvedBoundedAtom* resolved_bounded_atom = new SAS_Plus::ResolvedBoundedAtom(*new_bounded_atom, *bindings_, eog_manager, predicate_manager);
		SAS_Plus::ResolvedBoundedAtom* resolved_bounded_atom = new SAS_Plus::ResolvedBoundedAtom(Step::INITIAL_STEP, **ci, *bindings_, eog_manager, predicate_manager);
		initial_fact_layer->addFact(*resolved_bounded_atom);
	}
	FactLayer* next_fact_layer = new FactLayer(*initial_fact_layer);
	FactLayer* current_fact_layer = initial_fact_layer;
	//FactLayer* initial_fact_layer = new FactLayer(*current_fact_layer);
	fact_layers_.push_back(initial_fact_layer);

	// First we will ground all the actions.
	std::cerr << "Ground actions..." << std::endl;
	for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
	{
		const Action* action = *ci;
		std::vector<const Step*> grounded_actions;
		action_manager.ground(*bindings_, grounded_actions, *action);
		
		for (std::vector<const Step*>::const_iterator ci = grounded_actions.begin(); ci != grounded_actions.end(); ci++)
		{
			const Step* action_step = *ci;
			all_grounded_actions_.push_back(new ResolvedAction(action_step->getAction(), action_step->getStepId(), *bindings_, eog_manager, predicate_manager));
			delete action_step;
		}
	}
	std::cerr << "#" << all_grounded_actions_.size() << std::endl;

	// Now check for each grounded action which one is applicable in the current fact layer.
	while (true)
	{
		std::cerr << "Work on layer " << fact_layers_.size() << "..." << std::endl;
//		std::vector<const ResolvedAction*>* new_action_layer = new std::vector<const ResolvedAction*>();
		for (std::vector<const ResolvedAction*>::reverse_iterator action_ci = all_grounded_actions_.rbegin(); action_ci != all_grounded_actions_.rend(); action_ci++)
		{
			// Check if all preconditions are satisfied in the current layer.
			const ResolvedAction* resolved_action = *action_ci;

			bool preconditions_are_satisfied = true;
			for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator precondition_ci = resolved_action->getPreconditions().begin(); precondition_ci != resolved_action->getPreconditions().end(); precondition_ci++)
			{
				const SAS_Plus::ResolvedBoundedAtom* precondition = *precondition_ci;
				bool precondition_satisfied = false;
				
				const std::vector<const SAS_Plus::ResolvedBoundedAtom*>* supporting_facts = current_fact_layer->getFacts(*precondition);
				
				if (supporting_facts == NULL)
				{
					preconditions_are_satisfied = false;
					break;
				}
				
				for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator layer_ci = supporting_facts->begin(); layer_ci != supporting_facts->end(); layer_ci++)
				//for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator layer_ci = current_fact_layer->getFacts().begin(); layer_ci != current_fact_layer->getFacts().end(); layer_ci++)
				{
					if (precondition->getOriginalAtom().isNegative() == (*layer_ci)->getOriginalAtom().isNegative() && 
					    precondition->canUnifyWith(**layer_ci))
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
				for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = resolved_action->getEffects().begin(); ci != resolved_action->getEffects().end(); ci++)
				{
					next_fact_layer->addFact(**ci);
				}

				// Add this action to the action layer.
//				new_action_layer->push_back(resolved_action);
//				all_grounded_actions.erase(action_ci.base() - 1);
//				delete resolved_action;
			}
		}

		// If the next and current layer are the same, we have reached the level off point and we can stop.
		if (current_fact_layer->getFacts().size() == next_fact_layer->getFacts().size())
		{
//			for (std::vector<const ResolvedAction*>::iterator step_ci = new_action_layer->begin(); step_ci != new_action_layer->end(); step_ci++)
//			{
//				delete *step_ci;
//			}
//			delete new_action_layer;
			delete next_fact_layer;
			break;
		}

		// Prepare the layers for the next iterator. Facts once achieved stay achieved.
		current_fact_layer = next_fact_layer;
		next_fact_layer = new FactLayer(*current_fact_layer);

		// Add the action and fact layer to the RPG:
//		action_layers_.push_back(new_action_layer);
		fact_layers_.push_back(current_fact_layer);
	}
}


RelaxedPlanningGraph::~RelaxedPlanningGraph()
{
	for (std::vector<std::vector<const ResolvedAction*>* >::const_iterator ci = action_layers_.begin(); ci != action_layers_.end(); ci++)
	{
		delete *ci;
	}

	// The fact layers.
	for (std::vector<FactLayer*>::const_iterator ci = fact_layers_.begin(); ci != fact_layers_.end(); ci++)
	{
		delete *ci;
	}
	
	for (std::vector<const ResolvedAction*>::const_iterator action_ci = all_grounded_actions_.begin(); action_ci != all_grounded_actions_.end(); action_ci++)
	{
		delete *action_ci;
	}
	
	delete bindings_;
}

std::ostream& operator<<(std::ostream& os, const RelaxedPlanningGraph& rpg)
{
	// Start with the initial fact layer.
	const std::vector<FactLayer* >& fact_layers = rpg.getFactLayers();
	const std::vector<std::vector<const ResolvedAction*>* >& action_layers = rpg.getActionLayers();

	if (fact_layers.size() - 1 != action_layers.size())
	{
		std::cout << "Fact layers: " << fact_layers.size() << std::endl;
		std::cout << "Action layers: " << action_layers.size() << std::endl;
		assert (false);
	}
	for (unsigned int i = 0; i < action_layers.size(); i++)
	{
		std::cout << "Fact layer " << i << std::endl;
		for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator facts_ci = fact_layers[i]->getFacts().begin(); facts_ci != fact_layers[i]->getFacts().end(); facts_ci++)
		{
			std::cout << **facts_ci << std::endl;
		}

		std::cout << "Action layer " << i << std::endl;
		for (std::vector<const ResolvedAction*>::const_iterator actions_ci = action_layers[i]->begin(); actions_ci != action_layers[i]->end(); actions_ci++)
		{
			std::cout << **actions_ci << std::endl;
		}
	}

	// The last layer is the last fact layer.
	std::cout << "Fact layer " << fact_layers.size() - 1 << std::endl;
	for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator facts_ci = fact_layers[fact_layers.size() - 1]->getFacts().begin(); facts_ci != fact_layers[fact_layers.size() - 1]->getFacts().end(); facts_ci++)
	{
		std::cout << **facts_ci << std::endl;
	}
	return os;
}

};

};
