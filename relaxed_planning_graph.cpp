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
///#define MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG

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


std::ostream& operator<<(std::ostream& os, const ResolvedAction& resolved_action)
{
	resolved_action.getAction().print(os, resolved_action.getBindings(), resolved_action.getStepID());
	return os;
}

	
FactLayer::FactLayer()
{

}

FactLayer::FactLayer(const FactLayer& fact_layer)
{
	for (std::map<std::string, std::vector<const SAS_Plus::ResolvedBoundedAtom*>* >::const_iterator ci = fact_layer.mapped_facts_.begin(); ci != fact_layer.mapped_facts_.end(); ci++)
	{
		std::string name = (*ci).first;
		std::vector<const SAS_Plus::ResolvedBoundedAtom*>* list = (*ci).second;
		std::vector<const SAS_Plus::ResolvedBoundedAtom*>* new_list = new std::vector<const SAS_Plus::ResolvedBoundedAtom*>(list->begin(), list->end());
		
		mapped_facts_[name] = new_list;
	}
	facts_.insert(facts_.begin(), fact_layer.facts_.begin(), fact_layer.facts_.end());
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
	FactLayer* current_fact_layer = new FactLayer();
	
	for (std::vector<const Atom*>::const_iterator ci = initial_state_action.getEffects().begin(); ci != initial_state_action.getEffects().end(); ci++)
	{
		SAS_Plus::BoundedAtom* new_bounded_atom = new SAS_Plus::BoundedAtom(Step::INITIAL_STEP, **ci);
		SAS_Plus::ResolvedBoundedAtom* resolved_bounded_atom = new SAS_Plus::ResolvedBoundedAtom(*new_bounded_atom, *bindings_, eog_manager, predicate_manager);
		current_fact_layer->addFact(*resolved_bounded_atom);
	}
	FactLayer* next_fact_layer = new FactLayer(*current_fact_layer);
	fact_layers_.push_back(current_fact_layer);

	// First we will ground all the actions.
	std::cerr << "Ground actions..." << std::endl;
	std::vector<const ResolvedAction*> all_grounded_actions;
	for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
	{
		const Action* action = *ci;
		std::vector<const Step*> grounded_actions;
		action_manager.ground(*bindings_, grounded_actions, *action);
		
		for (std::vector<const Step*>::const_iterator ci = grounded_actions.begin(); ci != grounded_actions.end(); ci++)
		{
			const Step* action_step = *ci;
			all_grounded_actions.push_back(new ResolvedAction(action_step->getAction(), action_step->getStepId(), *bindings_, eog_manager, predicate_manager));
		}
	}
	std::cerr << "#" << all_grounded_actions.size() << std::endl;

	// Now check for each grounded action which one is applicable in the current fact layer.
	while (true)
	{
		std::cerr << "Work on layer " << fact_layers_.size() << "(" << current_fact_layer->getFacts().size() << ")" << std::endl;
		
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
		std::cout << "Work on layer " << fact_layers_.size() << "(" << current_fact_layer->getFacts().size() << ")" << std::endl;
		for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = current_fact_layer->getFacts().begin(); ci != current_fact_layer->getFacts().end(); ci++)
		{
			std::cout << "* " << **ci << std::endl;
		}
#endif
		std::vector<const ResolvedAction*>* new_action_layer = new std::vector<const ResolvedAction*>();
		
		for (std::vector<const ResolvedAction*>::reverse_iterator action_ci = all_grounded_actions.rbegin(); action_ci != all_grounded_actions.rend(); action_ci++)
		{
			// Check if all preconditions are satisfied in the current layer.
			const ResolvedAction* resolved_action = *action_ci;

			bool preconditions_are_satisfied = true;
			const SAS_Plus::ResolvedBoundedAtom* unsatisfied_precondition = NULL;
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
			string why = "";
#endif
			for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator precondition_ci = resolved_action->getPreconditions().begin(); precondition_ci != resolved_action->getPreconditions().end(); precondition_ci++)
			{
				const SAS_Plus::ResolvedBoundedAtom* precondition = *precondition_ci;
				bool precondition_satisfied = false;
				
				const std::vector<const SAS_Plus::ResolvedBoundedAtom*>* supporting_facts = current_fact_layer->getFacts(*precondition);
				
				if (supporting_facts == NULL)
				{
					preconditions_are_satisfied = false;
					unsatisfied_precondition = precondition;
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
					why = "supporting_facts == NULL; " + current_fact_layer->getUniqueName(*precondition);
#endif
					break;
				}
				
				for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator layer_ci = supporting_facts->begin(); layer_ci != supporting_facts->end(); layer_ci++)
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
					unsatisfied_precondition = precondition;
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
					why = "precondition not found == NULL" + current_fact_layer->getUniqueName(*precondition);
#endif
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
				new_action_layer->push_back(resolved_action);
				all_grounded_actions.erase(action_ci.base() - 1);
				
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
				std::cout << "Added action: " << *resolved_action << " to layer " << action_layers_.size() << std::endl;
#endif
			}
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
			else
			{
				std::cout << "Could not add action: " << *resolved_action << " because of the precondition: " << *unsatisfied_precondition << "; " << why << "; UID: " << current_fact_layer->getUniqueName(*unsatisfied_precondition) << std::endl;
			}
#endif
		}

		// If the next and current layer are the same, we have reached the level off point and we can stop.
		if (current_fact_layer->getFacts().size() == next_fact_layer->getFacts().size())
		{
			for (std::vector<const ResolvedAction*>::iterator step_ci = new_action_layer->begin(); step_ci != new_action_layer->end(); step_ci++)
			{
				delete *step_ci;
			}
			delete new_action_layer;
			break;
		}
		
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
		std::cout << "[END] Of layer " << fact_layers_.size() << "(" << current_fact_layer->getFacts().size() << ")" << " next layer: " << next_fact_layer->getFacts().size() << "(" << next_fact_layer->getFacts().size() << ")" << std::endl;
#endif
		
		// Add the action and fact layer to the RPG:
		action_layers_.push_back(new_action_layer);
		fact_layers_.push_back(next_fact_layer);
		
		// Prepare the layers for the next iterator. Facts once achieved stay achieved.
		current_fact_layer = next_fact_layer;
		next_fact_layer = new FactLayer(*current_fact_layer);
	}
}


RelaxedPlanningGraph::~RelaxedPlanningGraph()
{

}

int RelaxedPlanningGraph::calculateHeuristic(const std::vector<const SAS_Plus::BoundedAtom*>& goals, const Bindings& bindings) const
{
	// Get the facts in the last layer which can unify with the goals.
	std::vector<const SAS_Plus::ResolvedBoundedAtom*> current_facts;
	for (std::vector<const SAS_Plus::BoundedAtom*>::const_iterator ci = goals.begin(); ci != goals.end(); ci++)
	{
		const SAS_Plus::BoundedAtom* goal = *ci;
		FactLayer* last_fact_layer = fact_layers_[fact_layers_.size() - 1];
		for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = last_fact_layer->getFacts().begin(); ci != last_fact_layer->getFacts().end(); ci++)
		{
			const SAS_Plus::ResolvedBoundedAtom* resolved_bounded_atom = *ci;
			if (resolved_bounded_atom->canUnifyWith(*goal, bindings))
			{
				current_facts.push_back(resolved_bounded_atom);
				break;
			}
		}
	}
	
	// Not all goals are achieveable!
	if (current_facts.size() != goals.size())
	{
		return -1;
	}
	
	if (action_layers_.size() != fact_layers_.size() - 1)
	{
		std::cerr << "[RPG] Wrong number of action layers and fact layers!!! " << action_layers_.size() << " v.s. " << fact_layers_.size() << "." << std::endl;
		assert (false);
	}
	
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
	std::cerr << "[RPG] " << *this << std::endl;
#endif
	
	unsigned int heuristic = 0;
	for (int layer_nr = fact_layers_.size() - 1; layer_nr > 0; layer_nr--)
	{
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
		std::cerr << "[RPG] Working on fact layer: " << layer_nr << std::endl;
#endif

		std::vector<const SAS_Plus::ResolvedBoundedAtom*> next_set_of_facts;
		std::set<const ResolvedAction*> action_choosen;
		for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = current_facts.begin(); ci != current_facts.end(); ci++)
		{
			const SAS_Plus::ResolvedBoundedAtom* cur_fact = *ci;
			bool noop_action_available = false;
			
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
			std::cerr << "[RPG] * " << *cur_fact << std::endl;
#endif
			
			// Check at what layer the fact is reachable for the first time.
			for (int j = 0; j < layer_nr && !noop_action_available; j++)
			{
				const FactLayer* previous_fact_layer = fact_layers_[j];
				
				for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = previous_fact_layer->getFacts().begin(); ci != previous_fact_layer->getFacts().end(); ci++)
				{
					const SAS_Plus::ResolvedBoundedAtom* previous_atom = *ci;
					if (previous_atom->canUnifyWith(*cur_fact))
					{
						noop_action_available = true;
						break;
					}
				}
			}
			
			if (noop_action_available)
			{
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
				std::cerr << "[RPG] - Apply NOOP!" << std::endl;
#endif
				next_set_of_facts.push_back(cur_fact);
				continue;
			}
			
			// Find actions which can satisfy this fact and choose the one which will be 'easiest' to achieve.
			const std::vector<const ResolvedAction*>* action_layer = action_layers_[layer_nr - 1];
			std::vector<const ResolvedAction*> action_candidates;
			for (std::vector<const ResolvedAction*>::const_iterator ci = action_layer->begin(); ci != action_layer->end(); ci++)
			{
				const ResolvedAction* resolved_action = *ci;
				
				for(std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = resolved_action->getEffects().begin(); ci != resolved_action->getEffects().end(); ci++)
				{
					if (cur_fact->canUnifyWith(**ci))
					{
						action_candidates.push_back(resolved_action);
						break;
					}
				}
			}
			
			// Select the action which is least 'difficult'.
			const ResolvedAction* least_difficult_action = NULL;
			unsigned int least_difficulty = std::numeric_limits<unsigned int>::max();
			for (std::vector<const ResolvedAction*>::const_iterator ci = action_candidates.begin(); ci != action_candidates.end(); ci++)
			{
				const ResolvedAction* resolved_action = *ci;
				
				unsigned int difficulty = 0;
				std::vector<const SAS_Plus::ResolvedBoundedAtom*> preconditions = resolved_action->getPreconditions();
				
				for (int j = 0; j < layer_nr; j++)
				{
					const FactLayer* previous_fact_layer = fact_layers_[layer_nr];
					
					for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator ci = previous_fact_layer->getFacts().begin(); ci != previous_fact_layer->getFacts().end(); ci++)
					{
						const SAS_Plus::ResolvedBoundedAtom* previous_atom = *ci;
						
						for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::reverse_iterator ri = preconditions.rbegin(); ri != preconditions.rend(); ri++)
						{
							const SAS_Plus::ResolvedBoundedAtom* precondition = *ri;
							
							if (precondition->canUnifyWith(*previous_atom))
							{
								difficulty += j;
								preconditions.erase(ri.base() - 1);
								break;
							}
						}
					}
				}
				
				if (least_difficult_action == NULL || least_difficulty > difficulty)
				{
					least_difficult_action = resolved_action;
					least_difficulty = difficulty;
				}
			}
			
			if (least_difficult_action == NULL)
			{
				std::cerr << "[RPG] - No action found!? :((((" << std::endl;
				assert (false);
			}
			
#ifdef MYPOP_RPG_RELAXED_PLANNING_GRAPH_DEBUG
			std::cerr << "[RPG] - Apply " << *least_difficult_action << "!" << std::endl;
#endif
			
			if (action_choosen.count(least_difficult_action) == 0)
			{
				action_choosen.insert(least_difficult_action);
				++heuristic;
			}
			
			// Add the preconditions to the list of facts to achieve!
			next_set_of_facts.insert(next_set_of_facts.end(), least_difficult_action->getPreconditions().begin(), least_difficult_action->getPreconditions().end());
		}
		current_facts = next_set_of_facts;
	}
	
	return heuristic;
}

std::ostream& operator<<(std::ostream& os, const RelaxedPlanningGraph& rpg)
{
	// Start with the initial fact layer.
	const std::vector<FactLayer* >& fact_layers = rpg.getFactLayers();
	const std::vector<std::vector<const ResolvedAction*>* >& action_layers = rpg.getActionLayers();

	if (fact_layers.size() - 1 != action_layers.size())
	{
		os << "Fact layers: " << fact_layers.size() << std::endl;
		os << "Action layers: " << action_layers.size() << std::endl;
		assert (false);
	}
	for (unsigned int i = 0; i < action_layers.size(); i++)
	{
		os << "Fact layer " << i << std::endl;
		for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator facts_ci = fact_layers[i]->getFacts().begin(); facts_ci != fact_layers[i]->getFacts().end(); facts_ci++)
		{
			os << **facts_ci << std::endl;
		}

		os << "Action layer " << i << std::endl;
		for (std::vector<const ResolvedAction*>::const_iterator actions_ci = action_layers[i]->begin(); actions_ci != action_layers[i]->end(); actions_ci++)
		{
			os << **actions_ci << std::endl;
		}
	}

	// The last layer is the last fact layer.
	os << "Fact layer " << fact_layers.size() - 1 << std::endl;
	for (std::vector<const SAS_Plus::ResolvedBoundedAtom*>::const_iterator facts_ci = fact_layers[fact_layers.size() - 1]->getFacts().begin(); facts_ci != fact_layers[fact_layers.size() - 1]->getFacts().end(); facts_ci++)
	{
		os << **facts_ci << std::endl;
	}
	return os;
}

};

};
