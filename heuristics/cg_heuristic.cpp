#include "cg_heuristic.h"

#include "formula.h"
#include "sas/lifted_dtg.h"
#include "sas/causal_graph.h"
#include "fc_planner.h"
#include "fact_set.h"
#include <sas/property_space.h>
#include <queue>
#include <parser_utils.h>
#include <action_manager.h>
#include "term_manager.h"
#include <predicate_manager.h>

namespace MyPOP {

namespace HEURISTICS {

bool CompareLCGSearchNodes::operator()(const LCGSearchNode* lhs_node, const LCGSearchNode* rhs_node)
{
	return lhs_node->getPlan() > rhs_node->getPlan();
}

LCGSearchNode::LCGSearchNode(const std::vector<const GroundedAtom*>& assignments, const SAS_Plus::MultiValuedValue& node, std::vector<const GroundedAction*>& plan)
	: assignments_(&assignments), node_(&node), plan_(&plan)
{
	
}

LCGSearchNode::LCGSearchNode(const std::vector<const GroundedAtom*>& assignments, const SAS_Plus::MultiValuedValue& node)
	: assignments_(&assignments), node_(&node), plan_(new std::vector<const GroundedAction*>())
{
	
}

LCGSearchNode::LCGSearchNode(const LCGSearchNode& other)
	: assignments_(new std::vector<const GroundedAtom*>(*other.assignments_)), node_(other.node_), plan_(new std::vector<const GroundedAction*>(*other.plan_))
{
	
}
	
LCGSearchNode::~LCGSearchNode()
{
	delete assignments_;
	delete plan_;
}

	
LiftedCausalGraphHeuristic::LiftedCausalGraphHeuristic(const std::vector<SAS_Plus::LiftedDTG*>& lifted_dtgs, const ActionManager& action_manager, const PredicateManager& predicate_manager, const std::vector< const GroundedAtom* >& goal_facts)
	: lifted_dtgs_(&lifted_dtgs), predicate_manager_(&predicate_manager)
{
	causal_graph_ = new SAS_Plus::CausalGraph(lifted_dtgs, action_manager, predicate_manager);
	Graphviz::printToDot("cg", *causal_graph_);
	causal_graph_->breakCycles(goal_facts);
	Graphviz::printToDot("broken-cg", *causal_graph_);
}

void LiftedCausalGraphHeuristic::setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& goal_facts, bool find_helpful_actions, bool allow_new_goals_to_be_added)
{
	unsigned int h = getHeuristic(state, goal_facts);
	state.setDistanceToGoal(h);
}

unsigned int LiftedCausalGraphHeuristic::getHeuristic(const State& state, const std::vector< const GroundedAtom* >& bounded_goal_facts)
{
	unsigned int h = 0;
	
	// For every goal we try to find a plan in the abstract space.
	for (std::vector<const GroundedAtom*>::const_iterator ci = bounded_goal_facts.begin(); ci != bounded_goal_facts.end(); ++ci)
	{
		const GroundedAtom* goal = *ci;
		
		std::vector<const VariableDomain*> variable_domains;
		
		for (unsigned int term_index = 0; term_index < goal->getPredicate().getArity(); ++term_index)
		{
			VariableDomain* vd = new VariableDomain();
			vd->addObject(goal->getObject(term_index));
			variable_domains.push_back(vd);
		}
		
		HEURISTICS::Fact goal_fact(*predicate_manager_, goal->getPredicate(), variable_domains);
		const SAS_Plus::MultiValuedValue* best_node = findNode(goal_fact);
		
		// Check which term is invariable.
		HEURISTICS::VariableDomain invariable_domain;
		for (unsigned int fact_index = 0; fact_index < best_node->getValues().size(); ++fact_index)
		{
			if (goal_fact.canUnifyWith(*best_node->getValues()[fact_index]))
			{
				const SAS_Plus::Property* property = best_node->getPropertyState().getProperties()[fact_index];
				if (property->getIndex() != std::numeric_limits<unsigned int>::max())
				{
					invariable_domain.addObject(goal->getObject(property->getIndex()));
					break;
				}
			}
		}
		
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const HEURISTICS::Fact*>* > > goal_nodes;
		std::vector<const HEURISTICS::Fact*> goal_facts;
		goal_facts.push_back(&goal_fact);
		goal_nodes.push_back(std::make_pair(best_node, &goal_facts));
		
		std::cout << "Goal: " << goal_fact << "Invariable domain: " << invariable_domain << std::endl;
		std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
		
		std::cout << "Find nodes for the initial state: " << state << std::endl;
		
		// Find the value of the initial state.
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > > assignments;
		getNodes(assignments, best_node->getLiftedDTG(), invariable_domain, state);
		
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > >::const_iterator ci = assignments.begin(); ci != assignments.end(); ++ci)
		{
			std::cout << "Node: " << *(*ci).first << std::endl;
			std::vector<const GroundedAtom*>* values = (*ci).second;
			for (std::vector<const GroundedAtom*>::const_iterator ci = values->begin(); ci != values->end(); ++ci)
			{
				std::cout << "* " << **ci << std::endl;
			}
		}
		
		const LCGSearchNode* result = getCost(state, assignments, goal_nodes);
		if (result == NULL)
		{
			h = std::numeric_limits<unsigned int>::max();
			break;
		}
		h += result->getPlan().size();
	}
	return h;
}

const LCGSearchNode* LiftedCausalGraphHeuristic::getCost(const State& state, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > >& from_nodes, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const HEURISTICS::Fact*>* > >& to_nodes) const
{
	// A multi source, multi destination pathfinding algorithm.
	std::priority_queue<const LCGSearchNode*, std::vector<const LCGSearchNode*>, CompareLCGSearchNodes> open_list;
	
	for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > >::const_iterator ci = from_nodes.begin(); ci != from_nodes.end(); ++ci)
	{
		LCGSearchNode* node = new LCGSearchNode(*(*ci).second, *(*ci).first);
		open_list.push(node);
	}
	
	std::set<const SAS_Plus::MultiValuedValue*> closed_list;
	while (!open_list.empty())
	{
		const LCGSearchNode* current_node = open_list.top();
		open_list.pop();
		
		if (closed_list.find(&current_node->getNode()) != closed_list.end())
		{
			delete current_node;
			continue;
		}
		closed_list.insert(&current_node->getNode());
		
		// Check if this node satisfies one of the goals!
		bool goal_satisfied = false;
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = to_nodes.begin(); ci != to_nodes.end(); ++ci)
		{
			const std::vector<const HEURISTICS::Fact*>* goals = (*ci).second;
			for (std::vector<const GroundedAtom*>::const_iterator ci = current_node->getAssignments().begin(); ci != current_node->getAssignments().end(); ++ci)
			{
				const GroundedAtom* grounded_atom = *ci;
				for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = goals->begin(); ci != goals->end(); ++ci)
				{
					const HEURISTICS::Fact* goal = *ci;
					if (goal->canUnifyWith(*grounded_atom))
					{
						goal_satisfied = true;
						break;
					}
				}
				if (goal_satisfied)
				{
					break;
				}
			}
			if (goal_satisfied)
			{
				break;
			}
		}
		
		// Return heuristic value!
		if (goal_satisfied)
		{
			return new LCGSearchNode(*current_node);
		}
		
		for (std::vector<const SAS_Plus::MultiValuedTransition*>::const_iterator ci = current_node->getNode().getTransitions().begin(); ci != current_node->getNode().getTransitions().end(); ++ci)
		{
			const SAS_Plus::MultiValuedTransition* transition = *ci;
			
			if (closed_list.find(&transition->getToNode()) != closed_list.end())
			{
				continue;
			}
			
			unsigned int transition_cost = 1;
			
			std::vector<HEURISTICS::VariableDomain*> action_variable_domains;
			for (unsigned int action_variable_index = 0; action_variable_index < transition->getAction().getVariables().size(); ++action_variable_index)
			{
				const HEURISTICS::VariableDomain& variable_domain = transition->getActionVariableDomain(action_variable_index);
				action_variable_domains.push_back(new HEURISTICS::VariableDomain(variable_domain.getVariableDomain()));
			}
			
			//for (std::vector<HEURISTICS::Fact*>::const_iterator ci = current_node->getNode().getValues().begin(); ci != current_node->getNode().getValues().end(); ++ci)
			for (unsigned int fact_index = 0; fact_index < current_node->getNode().getValues().size(); ++fact_index)
			{
				//const HEURISTICS::Fact* fact = current_node->getNode().getValues()[fact_index];
				std::vector<unsigned int>* mappings_to_action_variables = transition->getPreconditionToActionVariableMappings()[fact_index];
				
				 const GroundedAtom* mapped_fact = current_node->getAssignments()[fact_index];
				 for (unsigned int term_index = 0; term_index < mapped_fact->getPredicate().getArity(); ++term_index)
				 {
					action_variable_domains[(*mappings_to_action_variables)[term_index]]->set(mapped_fact->getObject(term_index));
				 }
			}
		
			// Update the variable domains based on the values of the node.
			
			// Check its preconditions!
			std::vector<const Atom*> preconditions;
			Utility::convertFormula(preconditions, &transition->getAction().getPrecondition());
			
			std::vector<const GroundedAtom*> found_preconditions;
			
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
			{
				const Atom* precondition = *ci;
				if (transition->isPreconditionIgnored(*precondition))
				{
					found_preconditions.push_back(NULL);
					continue;
				}
				
				// Resolve this precondition.
				std::vector<const VariableDomain*> variable_domains;
				for (unsigned int term_index = 0; term_index < precondition->getArity(); ++term_index)
				{
					for (unsigned int action_index = 0; action_index < transition->getAction().getVariables().size(); ++action_index)
					{
						if (precondition->getTerms()[term_index] == transition->getAction().getVariables()[action_index])
						{
							variable_domains.push_back(&transition->getActionVariableDomain(action_index));
							break;
						}
					}
				}
				
				HEURISTICS::Fact precondition_fact(*predicate_manager_, precondition->getPredicate(), variable_domains);
				
				// Check if this precondition is part of the from node.
				bool precondition_is_part_of_from_node = false;
				//for (std::vector<HEURISTICS::Fact*>::const_iterator ci = current_node->getNode().getValues().begin(); ci != current_node->getNode().getValues().end(); ++ci)
				for (unsigned int fact_index = 0; fact_index < current_node->getNode().getValues().size(); ++fact_index)
				{
					if (precondition_fact.canUnifyWith(*current_node->getNode().getValues()[fact_index]))
					{
						const GroundedAtom* mapped_fact = current_node->getAssignments()[fact_index];
						found_preconditions.push_back(mapped_fact);
						precondition_is_part_of_from_node = true;
						break;
					}
				}
				
				if (precondition_is_part_of_from_node)
				{
					continue;
				}
				
				// If the fact is not part of the from node, then we look for the DTG it does belong to.
				const SAS_Plus::MultiValuedValue* best_node = findNode(precondition_fact);
				
				// Check which term is invariable.
				HEURISTICS::VariableDomain invariable_domain;
				for (unsigned int fact_index = 0; fact_index < best_node->getValues().size(); ++fact_index)
				{
					if (precondition_fact.canUnifyWith(*best_node->getValues()[fact_index]))
					{
						const SAS_Plus::Property* property = best_node->getPropertyState().getProperties()[fact_index];
						if (property->getIndex() != std::numeric_limits<unsigned int>::max())
						{
							invariable_domain.set(precondition_fact.getVariableDomains()[property->getIndex()]->getVariableDomain());
							break;
						}
					}
				}
				
				std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const HEURISTICS::Fact*>* > > goal_nodes;
				std::vector<const HEURISTICS::Fact*> goal_facts;
				goal_facts.push_back(&precondition_fact);
				goal_nodes.push_back(std::make_pair(best_node, &goal_facts));
				
				std::cout << "Goal: " << precondition_fact << "Invariable domain: " << invariable_domain << std::endl;
				std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
				
				std::cout << "Find nodes for the initial state: " << state << std::endl;
				
				// Find the value of the initial state.
				std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > > assignments;
				getNodes(assignments, best_node->getLiftedDTG(), invariable_domain, state);
/*
				for (std::vector<std::pair<SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > >::const_iterator ci = assignments.begin(); ci != assignments.end(); ++ci)
				{
					std::cout << "Node: " << *(*ci).first << std::endl;
					std::vector<const GroundedAtom*>* values = (*ci).second;
					for (std::vector<const GroundedAtom*>::const_iterator ci = values->begin(); ci != values->end(); ++ci)
					{
						std::cout << "* " << **ci << std::endl;
					}
				}
*/
				const LCGSearchNode* result = getCost(state, assignments, goal_nodes);
				if (result == NULL)
				{
					transition_cost = std::numeric_limits<unsigned int>::max();
					break;
				}
				else
				{
					transition_cost += result->getPlan().size();
					
					for (std::vector<const GroundedAtom*>::const_iterator ci = result->getAssignments().begin(); ci != result->getAssignments().end(); ++ci)
					{
						if (precondition_fact.canUnifyWith(**ci))
						{
							const GroundedAtom* matching_grounded_fact = *ci;
							found_preconditions.push_back(matching_grounded_fact);
							
							// Update the action variables of the action domains.
							std::vector<HEURISTICS::VariableDomain*> action_variable_domains;
							for (unsigned int term_index = 0; term_index < precondition_fact.getVariableDomains().size(); ++term_index)
							{
								for (unsigned int action_index = 0; action_index < transition->getAction().getVariables().size(); ++action_index)
								{
									if (precondition->getTerms()[term_index] == transition->getAction().getVariables()[action_index])
									{
										action_variable_domains[action_index]->set(matching_grounded_fact->getObject(term_index));
										break;
									}
								}
							}
							
							break;
						}
					}
				}
			}
			
			if (transition_cost == std::numeric_limits<unsigned int>::max())
			{
				continue;
			}
			
			std::vector<const GroundedAction*>* plan = new std::vector<const GroundedAction*>();
			
			// Find the assignments to the to node.
			std::vector<const GroundedAtom*>* assignments_to_to_node = new std::vector<const GroundedAtom*>();
			const std::vector<std::vector<unsigned int>* >& effect_to_action_variable_mappings = transition->getEffectToActionVariableMappings();
			
			for (unsigned int to_fact_index = 0; to_fact_index < transition->getToNode().getValues().size(); ++to_fact_index)
			{
				const HEURISTICS::Fact* to_fact = transition->getToNode().getValues()[to_fact_index];
				
				const Object** to_fact_variable = new const Object*[to_fact->getPredicate().getArity()];
				std::vector<unsigned int>* effect_to_action_variable_mapping = effect_to_action_variable_mappings[to_fact_index];
				for (unsigned int term_index = 0; term_index < to_fact->getPredicate().getArity(); ++term_index)
				{
					assert (action_variable_domains[(*effect_to_action_variable_mapping)[term_index]]->getVariableDomain().size() == 1);
					const Object* object = action_variable_domains[(*effect_to_action_variable_mapping)[term_index]]->getVariableDomain()[0];
					to_fact_variable[term_index] = object;
				}
				
				const GroundedAtom& grounded_atom = GroundedAtom::getGroundedAtom(to_fact->getPredicate(), to_fact_variable);
				assignments_to_to_node->push_back(&grounded_atom);
			}
			
			LCGSearchNode* new_node = new LCGSearchNode(*assignments_to_to_node ,transition->getToNode(), *plan);
			open_list.push(new_node);
		}
	}
	
	return NULL;
}

void LiftedCausalGraphHeuristic::getNodes(std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > >& assignments, const SAS_Plus::LiftedDTG& lifted_dtg, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const
{
//	std::cout << "Get nodes." << std::endl;
//	std::cout << state << std::endl;
//	std::cout << "Invariable domain: " << invariable_domain << std::endl;
	
	for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = lifted_dtg.getNodes().begin(); ci != lifted_dtg.getNodes().end(); ++ci)
	{
		const SAS_Plus::MultiValuedValue* node = *ci;
//		std::cout << "Process: " << *node << std::endl;
		std::vector<const GroundedAtom*> empty_mapping;
		std::vector<std::vector<const GroundedAtom*>* > found_mappings;
		findMappings(found_mappings, empty_mapping, *node, invariable_domain, state);
		
		for (std::vector<std::vector<const GroundedAtom*>* >::const_iterator ci = found_mappings.begin(); ci != found_mappings.end(); ++ci)
		{
			assignments.push_back(std::make_pair(node, *ci));
		}
	}
}

void LiftedCausalGraphHeuristic::findMappings(std::vector<std::vector<const GroundedAtom*>* >& found_mappings, const std::vector<const GroundedAtom*>& current_mappings, const SAS_Plus::MultiValuedValue& node, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const
{
	unsigned int fact_index = current_mappings.size();
//	std::cout << "[LiftedCausalGraphHeuristic::findMappings] Index: " << fact_index << std::endl;
//	for (std::vector<const GroundedAtom*>::const_iterator ci = current_mappings.begin(); ci != current_mappings.end(); ++ci)
//	{
//		std::cout << "* " << **ci << std::endl;
//	}
	
	// Found a full assignment!
	if (fact_index == node.getValues().size())
	{
		std::vector<const GroundedAtom*>* new_found_mapping = new std::vector<const GroundedAtom*>(current_mappings);
		found_mappings.push_back(new_found_mapping);
		return;
	}
	
	const HEURISTICS::Fact* fact = node.getValues()[fact_index];
	const SAS_Plus::Property* property = node.getPropertyState().getProperties()[fact_index];
	
	// Check which facts from the state can be mapped to this fact.
	for (std::vector<const GroundedAtom*>::const_iterator ci = state.getFacts().begin(); ci != state.getFacts().end(); ++ci)
	{
		const GroundedAtom* atom = *ci;
		if (!fact->canUnifyWith(*atom))
		{
			continue;
		}
		
		// Check if the invariable matches as well.
		if (property->getIndex() != std::numeric_limits<unsigned int>::max() && !invariable_domain.contains(atom->getObject(property->getIndex())))
		{
			continue;
		}
		
		// Found an assignment!
		std::vector<const GroundedAtom*> new_current_mappings(current_mappings);
		new_current_mappings.push_back(atom);
		findMappings(found_mappings, new_current_mappings, node, invariable_domain, state);
	}
}
/*
unsigned int LiftedCausalGraphHeuristic::getCost()
{
	
}
*/
const SAS_Plus::MultiValuedValue* LiftedCausalGraphHeuristic::findNode(const HEURISTICS::Fact& fact) const
{
	// Find the set of nodes this goal is part of.
	std::vector<const SAS_Plus::MultiValuedValue*> found_nodes;
	for (std::vector<SAS_Plus::LiftedDTG*>::const_iterator ci = lifted_dtgs_->begin(); ci != lifted_dtgs_->end(); ++ci)
	{
		const SAS_Plus::LiftedDTG* lifted_dtg = *ci;
		lifted_dtg->getNodes(found_nodes, fact);
	}
	
	// Next we select the node whose lifted DTG has the least number of dependencies (preferably none!).
	const SAS_Plus::MultiValuedValue* best_node = NULL;
	std::vector<const SAS_Plus::LiftedDTG*> best_node_dependencies;
	for (std::vector<const SAS_Plus::MultiValuedValue*>::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ++ci)
	{
		const SAS_Plus::MultiValuedValue* node = *ci;
		std::vector<const SAS_Plus::LiftedDTG*> node_dependencies;
		causal_graph_->getAllDependencies(node_dependencies, node->getLiftedDTG());
		
		if (best_node == NULL || best_node_dependencies.size() > node_dependencies.size())
		{
			best_node = node;
			best_node_dependencies.clear();
			best_node_dependencies.insert(best_node_dependencies.end(), node_dependencies.begin(), node_dependencies.end());
		}
	}
	
	return best_node;
}

};

};
