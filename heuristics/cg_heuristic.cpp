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

//#define LIFTED_CAUSAL_GRAPH_COMMENTS

namespace MyPOP {

namespace HEURISTICS {

bool CompareLCGSearchNodes::operator()(const LCGSearchNode* lhs_node, const LCGSearchNode* rhs_node)
{
	return lhs_node->getCost() > rhs_node->getCost();
}

LCGSearchNode::LCGSearchNode(const std::vector<const HEURISTICS::Fact*>& assignments, const SAS_Plus::MultiValuedValue& node, const std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& assignments_to_lower_variables, unsigned int cost)
	: starting_node_(this), assignments_(&assignments), node_(&node), assignments_to_lower_variables_(&assignments_to_lower_variables), cost_(cost)
{
	
}

LCGSearchNode::LCGSearchNode(const LCGSearchNode& starting_node, const std::vector<const HEURISTICS::Fact*>& assignments, const SAS_Plus::MultiValuedValue& node, const std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& assignments_to_lower_variables, unsigned int cost)
	: starting_node_(&starting_node), assignments_(&assignments), node_(&node), assignments_to_lower_variables_(&assignments_to_lower_variables), cost_(cost)
{
	
}

LCGSearchNode::LCGSearchNode(const LCGSearchNode& other)
	: starting_node_(other.starting_node_), assignments_(new std::vector<const HEURISTICS::Fact*>(*other.assignments_)), node_(other.node_), assignments_to_lower_variables_(new std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >(*other.assignments_to_lower_variables_)), cost_(other.cost_)
{
	
}
	
LCGSearchNode::~LCGSearchNode()
{
	delete assignments_;
}

const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& LCGSearchNode::getAssignmentsToLowerVariables(const SAS_Plus::LiftedDTG& lifted_dtg) const
{
	std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >::const_iterator ci = assignments_to_lower_variables_->find(&lifted_dtg);
	if (ci == assignments_to_lower_variables_->end())
	{
		std::cerr << "Cannot find the assignments of the lifted dtg: " << std::endl;
		std::cerr << lifted_dtg << std::endl;
		std::cerr << "Node: " << std::endl;
		std::cerr << *this << std::endl;
		assert (false);
	}
	return *(*ci).second;
}

std::ostream& operator<<(std::ostream& os, const LCGSearchNode& search_node)
{
	os << "[LCGSearchNode] Node: Cost=" << search_node.cost_ << std::endl;
	search_node.getNode().printFacts(os);
	os << "Assignments:" << std::endl;
	for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = search_node.assignments_->begin(); ci != search_node.assignments_->end(); ++ci)
	{
		os << **ci << std::endl;
	}
	
	os << "Assignments to lower variables:" << std::endl;
	for (std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >::const_iterator ci = search_node.assignments_to_lower_variables_->begin(); ci != search_node.assignments_to_lower_variables_->end(); ++ci)
	{
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* assignments = (*ci).second;
		os << "- Lower assignments:" << std::endl;
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = assignments->begin(); ci != assignments->end(); ++ci)
		{
			(*ci).first->printFacts(os);
			os << "Assignments: " << std::endl;
			const std::vector<const HEURISTICS::Fact*>* node_assignments = (*ci).second;
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = node_assignments->begin(); ci != node_assignments->end(); ++ci)
			{
				os << "* " << **ci << std::endl;
			}
		}
	}
	return os;
}
	
LiftedCausalGraphHeuristic::LiftedCausalGraphHeuristic(const std::vector<SAS_Plus::LiftedDTG*>& lifted_dtgs, const ActionManager& action_manager, const PredicateManager& predicate_manager, const std::vector< const GroundedAtom* >& goal_facts)
	: lifted_dtgs_(&lifted_dtgs), predicate_manager_(&predicate_manager)
{
	causal_graph_ = new SAS_Plus::CausalGraph(lifted_dtgs, action_manager, predicate_manager);
	Graphviz::printToDot("cg", *causal_graph_);
	causal_graph_->breakCycles(goal_facts);
	Graphviz::printToDot("broken-cg", *causal_graph_);
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	//std::cout << *causal_graph_ << std::endl;
#endif
}

void LiftedCausalGraphHeuristic::setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& goal_facts, bool find_helpful_actions, bool allow_new_goals_to_be_added)
{
	unsigned int h = getHeuristic(state, goal_facts);
	state.setDistanceToGoal(h);
}

unsigned int LiftedCausalGraphHeuristic::getHeuristic(const State& state, const std::vector< const GroundedAtom* >& bounded_goal_facts)
{
	std::vector<const SAS_Plus::LiftedDTG*> all_lifted_dtgs;
	for (std::vector<SAS_Plus::LiftedDTG*>::const_iterator ci = lifted_dtgs_->begin(); ci != lifted_dtgs_->end(); ++ci)
	{
		all_lifted_dtgs.push_back(*ci);
	}
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
//	for (std::vector<SAS_Plus::LiftedDTG*>::const_iterator ci = lifted_dtgs_->begin(); ci != lifted_dtgs_->end(); ++ci)
//	{
//		std::cout << **ci << std::endl;
//	}
	
	std::cout << "LiftedCausalGraphHeuristic::getHeuristic" << std::endl;
	std::cout << state << std::endl;
	std::cout << "Goals: " << std::endl;
	for (std::vector<const GroundedAtom*>::const_iterator ci = bounded_goal_facts.begin(); ci != bounded_goal_facts.end(); ++ci)
	{
		std::cout << "* " << **ci << std::endl;
	}
#endif
	unsigned int h = 0;
	
	// For every goal we try to find a plan in the abstract space.
	for (std::vector<const GroundedAtom*>::const_iterator ci = bounded_goal_facts.begin(); ci != bounded_goal_facts.end(); ++ci)
	{
		const GroundedAtom* goal = *ci;
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Process the goal: " << *goal << std::endl;
#endif
		
		std::vector<const VariableDomain*> variable_domains;
		
		for (unsigned int term_index = 0; term_index < goal->getPredicate().getArity(); ++term_index)
		{
			VariableDomain* vd = new VariableDomain();
			vd->addObject(goal->getObject(term_index));
			variable_domains.push_back(vd);
		}
		
		HEURISTICS::Fact goal_fact(*predicate_manager_, goal->getPredicate(), variable_domains);
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Transformed into: " << goal_fact << std::endl;
#endif
		const SAS_Plus::MultiValuedValue* best_node = findNode(goal_fact, all_lifted_dtgs);
		
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
		
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > > goal_nodes;
		std::vector<const HEURISTICS::Fact*> goal_facts;
		goal_facts.push_back(&goal_fact);
		goal_nodes.push_back(std::make_pair(best_node, &goal_facts));
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Goal: " << goal_fact << "Invariable domain: " << invariable_domain << std::endl;
//		std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
#endif
		
		// Find the value of the initial state.
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > > assignments;
		getNodes(assignments, best_node->getLiftedDTG(), invariable_domain, state);
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Find nodes for the initial state: " << state << std::endl;
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = assignments.begin(); ci != assignments.end(); ++ci)
		{
			std::cout << "Node: " ;
			(*ci).first->printFacts(std::cout);
			const std::vector<const HEURISTICS::Fact*>* values = (*ci).second;
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = values->begin(); ci != values->end(); ++ci)
			{
				std::cout << "* " << **ci << std::endl;
			}
		}
#endif
		
		const LCGSearchNode* result = getCost(state, best_node->getLiftedDTG(), assignments, goal_nodes);
		if (result == NULL)
		{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "Could not achieve the goal: " << goal_fact << "Invariable domain: " << invariable_domain << std::endl;
//			std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
#endif
			h = std::numeric_limits<unsigned int>::max();
			break;
		}
		h += result->getCost();
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Achieve the goal: " << goal_fact << "Invariable domain: " << invariable_domain << ". Costs = " << result->getCost() << "." << std::endl;
//		std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
#endif
	}
	return h;
}

const LCGSearchNode* LiftedCausalGraphHeuristic::getCost(const State& state, const SAS_Plus::LiftedDTG& lifted_dtg, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& from_nodes, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& to_nodes) const
{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	std::cout << "[LiftedCausalGraphHeuristic::getCost] " << std::endl;
	std::cout << "State: " << state << std::endl;
	std::cout << "Initial facts: " << std::endl;
	for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = from_nodes.begin(); ci != from_nodes.end(); ++ci)
	{
		const std::vector<const HEURISTICS::Fact*>* initial_facts = (*ci).second;
		for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = initial_facts->begin(); ci != initial_facts->end(); ++ci)
		{
			std::cout << "* " << **ci << std::endl;
		}
	}
	
	std::cout << "Goals: " << std::endl;
	for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = to_nodes.begin(); ci != to_nodes.end(); ++ci)
	{
		const std::vector<const HEURISTICS::Fact*>* goals = (*ci).second;
		for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = goals->begin(); ci != goals->end(); ++ci)
		{
			std::cout << "* " << **ci << std::endl;
		}
	}
#endif
	
	const std::set<const SAS_Plus::LiftedDTG*>& dependencies_set = causal_graph_->getAllDirectDependencies(lifted_dtg);
	std::vector<const SAS_Plus::LiftedDTG*> dependencies(dependencies_set.begin(), dependencies_set.end());
	
	// A multi source, multi destination pathfinding algorithm.
	std::priority_queue<const LCGSearchNode*, std::vector<const LCGSearchNode*>, CompareLCGSearchNodes> open_list;
	std::set<const SAS_Plus::MultiValuedValue*> closed_list;
	
	// Disable any copies of nodes, we will not be using them.
	for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = lifted_dtg.getNodes().begin(); ci != lifted_dtg.getNodes().end(); ++ci)
	{
		if ((*ci)->isCopy())
		{
			closed_list.insert(*ci);
		}
	}
	
	for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = from_nodes.begin(); ci != from_nodes.end(); ++ci)
	{
		const SAS_Plus::MultiValuedValue* node = (*ci).first;
		const std::vector<const HEURISTICS::Fact*>* assignments_to_node = (*ci).second;
		
		// Enable any copies of this node.
		for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = node->getCopies().begin(); ci != node->getCopies().end(); ++ci)
		{
			closed_list.erase(*ci);
		}
		
		std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >* assignments_per_lifted_dtg = new std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >();
		
		// Initialise the values of the dependencies.
		for (std::vector<const SAS_Plus::LiftedDTG*>::const_iterator ci = dependencies.begin(); ci != dependencies.end(); ++ci)
		{
			const SAS_Plus::LiftedDTG* lifted_dtg = *ci;
			HEURISTICS::VariableDomain invariable_domain(lifted_dtg->getPropertySpace().getObjects());
			
			std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* assignments = new std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >();
			getNodes(*assignments, *lifted_dtg, invariable_domain, state);
			(*assignments_per_lifted_dtg)[lifted_dtg] = assignments;
		}
		
		std::vector<const HEURISTICS::Fact*>* from_node_assignments = new std::vector<const HEURISTICS::Fact*>(*assignments_to_node);
		LCGSearchNode* starting_node = new LCGSearchNode(*from_node_assignments, *node, *assignments_per_lifted_dtg);
		open_list.push(starting_node);
		
		assert (assignments_per_lifted_dtg->size() == dependencies.size());
	}
	
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
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = to_nodes.begin(); ci != to_nodes.end(); ++ci)
		{
			const std::vector<const HEURISTICS::Fact*>* goals = (*ci).second;
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = current_node->getAssignments().begin(); ci != current_node->getAssignments().end(); ++ci)
			{
				const HEURISTICS::Fact* grounded_atom = *ci;
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
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "Found a goal: Cost = " << current_node->getCost() << std::endl;
			current_node->getNode().printFacts(std::cout);
#endif
			LCGSearchNode* goal_node = new LCGSearchNode(*current_node);
			while (!open_list.empty())
			{
				const LCGSearchNode* current_node = open_list.top();
				open_list.pop();
				delete current_node;
			}
			return goal_node;
		}
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Process the node: " << std::endl;
		std::cout << *current_node << std::endl;
#endif
		
		for (std::vector<const SAS_Plus::MultiValuedTransition*>::const_iterator ci = current_node->getNode().getTransitions().begin(); ci != current_node->getNode().getTransitions().end(); ++ci)
		{
			const SAS_Plus::MultiValuedTransition* transition = *ci;
			
			if (closed_list.find(&transition->getToNode()) != closed_list.end())
			{
				continue;
			}
			
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "Process the transition: " << *transition << std::endl;
#endif
			
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
				if (mappings_to_action_variables == NULL)
				{
					continue;
				}
				
				const HEURISTICS::Fact* mapped_fact = current_node->getAssignments()[fact_index];
				for (unsigned int term_index = 0; term_index < mapped_fact->getPredicate().getArity(); ++term_index)
				{
					action_variable_domains[(*mappings_to_action_variables)[term_index]]->set(mapped_fact->getVariableDomains()[term_index]->getVariableDomain());
				}
			}
		
			// Update the variable domains based on the values of the node.
			
			// Check its preconditions!
			std::vector<const Atom*> preconditions;
			Utility::convertFormula(preconditions, &transition->getAction().getPrecondition());
			
			std::vector<const HEURISTICS::Fact*> found_preconditions;
			
			std::vector<const LCGSearchNode*> assignments_made;
			
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
//							variable_domains.push_back(&transition->getActionVariableDomain(action_index));
							variable_domains.push_back(action_variable_domains[action_index]);
							break;
						}
					}
				}
				
				HEURISTICS::Fact precondition_fact(*predicate_manager_, precondition->getPredicate(), variable_domains);
				
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
				std::cout << "Handle the precondition: " << precondition_fact << std::endl;
#endif
				
				// Check if this precondition is part of the from node.
				bool precondition_is_part_of_from_node = false;
				//for (std::vector<HEURISTICS::Fact*>::const_iterator ci = current_node->getNode().getValues().begin(); ci != current_node->getNode().getValues().end(); ++ci)
				for (unsigned int fact_index = 0; fact_index < current_node->getNode().getValues().size(); ++fact_index)
				{
					if (precondition_fact.canUnifyWith(*current_node->getNode().getValues()[fact_index]))
					{
						const HEURISTICS::Fact* mapped_fact = current_node->getAssignments()[fact_index];
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
				const SAS_Plus::MultiValuedValue* best_node = findNode(precondition_fact, dependencies);
				
				assert (best_node != NULL);
				
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
				
				std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > > goal_nodes;
				std::vector<const HEURISTICS::Fact*> goal_facts;
				goal_facts.push_back(&precondition_fact);
				goal_nodes.push_back(std::make_pair(best_node, &goal_facts));
				
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
				std::cout << "Goal: " << precondition_fact << "Invariable domain: " << invariable_domain << std::endl;
//				std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
				
				std::cout << "Find nodes for the initial state: " << state << std::endl;
#endif
				
				std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > > from_assignments = current_node->getAssignmentsToLowerVariables(best_node->getLiftedDTG());
				
				// Prune those from nodes which do not match the invariable.
				for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::reverse_iterator ri = from_assignments.rbegin(); ri != from_assignments.rend(); ++ri)
				{
					const SAS_Plus::MultiValuedValue* node = (*ri).first;
					const std::vector<const HEURISTICS::Fact*>* assignments = (*ri).second;
					
					const HEURISTICS::VariableDomain* node_invariable_domain = NULL;
					
					const SAS_Plus::PropertyState& property_state = node->getPropertyState();
					for (unsigned int fact_index = 0; fact_index < node->getValues().size(); ++fact_index)
					{
						const SAS_Plus::Property* property = property_state.getProperties()[fact_index];
						if (property->getIndex() != std::numeric_limits<unsigned int>::max())
						{
							node_invariable_domain = (*assignments)[fact_index]->getVariableDomains()[property->getIndex()];
							break;
						}
					}
					
					if (node_invariable_domain != NULL && !node_invariable_domain->sharesObjectsWith(invariable_domain))
					{
						from_assignments.erase(ri.base() - 1);
					}
				}
				
				const LCGSearchNode* result = getCost(state, best_node->getLiftedDTG(), from_assignments, goal_nodes);
				assignments_made.push_back(result);
				
				if (result == NULL)
				{
					transition_cost = std::numeric_limits<unsigned int>::max();
					break;
				}
				else
				{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
					std::cout << "Achieved the precondition: " << precondition_fact << std::endl;
					std::cout << "With cost: " << result->getCost() << std::endl;
					std::cout << "Initial facts: " << std::endl;
					for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = from_assignments.begin(); ci != from_assignments.end(); ++ci)
					{
						const std::vector<const HEURISTICS::Fact*>* initial_facts = (*ci).second;
						for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = initial_facts->begin(); ci != initial_facts->end(); ++ci)
						{
							std::cout << "* " << **ci << std::endl;
						}
					}
					
					std::cout << "Goals: " << std::endl;
					for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = goal_nodes.begin(); ci != goal_nodes.end(); ++ci)
					{
						const std::vector<const HEURISTICS::Fact*>* goals = (*ci).second;
						for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = goals->begin(); ci != goals->end(); ++ci)
						{
							std::cout << "* " << **ci << std::endl;
						}
					}
					
					std::cout << "Assignments of the preconditions: " << std::endl;
					for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = result->getAssignments().begin(); ci != result->getAssignments().end(); ++ci)
					{
						std::cout << **ci << std::endl;
					}
#endif
					transition_cost += result->getCost();
					
					for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = result->getAssignments().begin(); ci != result->getAssignments().end(); ++ci)
					{
						if (precondition_fact.canUnifyWith(**ci))
						{
							const HEURISTICS::Fact* matching_grounded_fact = *ci;
							found_preconditions.push_back(matching_grounded_fact);
							
							assert (matching_grounded_fact->getPredicate().getArity() == precondition_fact.getVariableDomains().size());
							assert (action_variable_domains.size() == transition->getAction().getVariables().size());
							
							// Update the action variables of the action domains.
							for (unsigned int term_index = 0; term_index < precondition_fact.getVariableDomains().size(); ++term_index)
							{
								for (unsigned int action_index = 0; action_index < transition->getAction().getVariables().size(); ++action_index)
								{
									if (precondition->getTerms()[term_index] == transition->getAction().getVariables()[action_index])
									{
										action_variable_domains[action_index]->set(matching_grounded_fact->getVariableDomains()[term_index]->getVariableDomain());
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
			
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "All preconditions satisfied!" << std::endl;
			std::cout << transition->getAction().getPredicate() << " ";
			for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_domains.begin(); ci != action_variable_domains.end(); ++ci)
			{
				std::cout << **ci << " ";
			}
			std::cout << "." << std::endl;
#endif
			
			// Find the assignments to the to node.
			std::vector<const HEURISTICS::Fact*>* assignments_to_to_node = new std::vector<const HEURISTICS::Fact*>();
			const std::vector<std::vector<unsigned int>* >& effect_to_action_variable_mappings = transition->getEffectToActionVariableMappings();
			
			for (unsigned int to_fact_index = 0; to_fact_index < transition->getToNode().getValues().size(); ++to_fact_index)
			{
				const HEURISTICS::Fact* to_fact = transition->getToNode().getValues()[to_fact_index];
				
				// Check if this fact is persistent.
				const HEURISTICS::Fact* precondition_persistent_with_to_fact = transition->getPreconditionPersistentWith(*to_fact);
				std::vector<const HEURISTICS::VariableDomain*>* to_node_variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
				if (precondition_persistent_with_to_fact != NULL)
				{
					for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = precondition_persistent_with_to_fact->getVariableDomains().begin(); ci != precondition_persistent_with_to_fact->getVariableDomains().end(); ++ci)
					{
						to_node_variable_domains->push_back(new HEURISTICS::VariableDomain((*ci)->getVariableDomain()));
					}
				}
				else
				{
					for (unsigned int term_index = 0; term_index < to_fact->getPredicate().getArity(); ++term_index)
					{
						// If no mapping is specified it is identical to the precondition.
						// TODO: Handle persistent facts.
						if (effect_to_action_variable_mappings[to_fact_index] == NULL)
						{
							assert (false);
						}
						else
						{
							to_node_variable_domains->push_back(new HEURISTICS::VariableDomain(*action_variable_domains[(*effect_to_action_variable_mappings[to_fact_index])[term_index]]));
						}
					}
				}
				assignments_to_to_node->push_back(new HEURISTICS::Fact(*predicate_manager_, to_fact->getPredicate(), *to_node_variable_domains));
			}
			
			const std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& current_assignments_to_lower_variables = current_node->getAssignmentsToLowerVariables();
			std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >* new_assignments_to_lower_variables = new std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >();
			
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << " UPDATED ASSIGNMENTS!!! [#=" << assignments_made.size() << "]" << std::endl;
			for (std::vector<const LCGSearchNode*>::const_iterator ci = assignments_made.begin(); ci != assignments_made.end(); ++ci)
			{
				std::cout << "START:" << std::endl;
				std::cout << (*ci)->getStartingNode() << std::endl;
				std::cout << " *** TO *** " << std::endl;
				std::cout << **ci << std::endl;
			}
#endif
			
			for (std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >::const_iterator ci = current_assignments_to_lower_variables.begin(); ci != current_assignments_to_lower_variables.end(); ++ci)
			{
				const SAS_Plus::LiftedDTG* lifted_dtg = (*ci).first;
				std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* mappings = (*ci).second;
				std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* new_mappings = new std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >();
				
				// Check if any assignments have been made by the transitions.
				for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
				{
					const SAS_Plus::MultiValuedValue* node = (*ci).first;
					const std::vector<const HEURISTICS::Fact*>* previous_assignments = (*ci).second;
					
					// Check which previous assignments have been altered.
					bool node_has_been_altered = false;
					for (std::vector<const LCGSearchNode*>::const_iterator ci = assignments_made.begin(); ci != assignments_made.end(); ++ci)
					{
						const LCGSearchNode* search_node = *ci;
						if (&search_node->getStartingNode().getNode() == node)
						{
							bool facts_match = true;
							for (unsigned int fact_index = 0; fact_index < node->getValues().size(); ++fact_index)
							{
								if (!search_node->getStartingNode().getAssignments()[fact_index]->canUnifyWith(*(*previous_assignments)[fact_index]))
								{
									facts_match = false;
									break;
								}
							}
							
							if (facts_match)
							{
								node_has_been_altered = true;
								new_mappings->push_back(std::make_pair(&search_node->getNode(), &search_node->getAssignments()));
								break;
							}
						}
					}
					
					if (!node_has_been_altered)
					{
						new_mappings->push_back(std::make_pair(node, new std::vector<const HEURISTICS::Fact*>(*previous_assignments)));
					}
				}
				(*new_assignments_to_lower_variables)[lifted_dtg] = new_mappings;
			}
			
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "Found a new achiever for the node: " << std::endl;
			transition->getToNode().printFacts(std::cout);
			std::cout << "Assignments: " << std::endl;
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = assignments_to_to_node->begin(); ci != assignments_to_to_node->end(); ++ci)
			{
				std::cout << "* " << **ci << "." << std::endl;
			}
			std::cout << "Cost: " << current_node->getCost() + transition_cost << std::endl;
#endif
			LCGSearchNode* new_node = new LCGSearchNode(current_node->getStartingNode(), *assignments_to_to_node, transition->getToNode(), *new_assignments_to_lower_variables, current_node->getCost() + transition_cost);
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << *new_node << std::endl;
#endif
			open_list.push(new_node);
			assert (new_assignments_to_lower_variables->size() == dependencies.size());
		}
	}
	
	return NULL;
}
/*
void LiftedCausalGraphHeuristic::solveSASPlusMinusOneProblem(const State& current_state, const SAS_Plus::LiftedDTG& lifted_dtg, const std::vector<const HEURISTICS::Fact*>& initial_assignments, const std::vector<const HEURISTICS::Fact*>& goals)
{
	// Initialise the high and low level variables.
	std::vector<const SAS_Plus::LiftedDTG*> dependencies;
	causal_graph_->getAllDependencies(dependencies, lifted_dtg);
	
	
	
	// For now we ignore any preconditions of the lower level variables.
	
}
*/
void LiftedCausalGraphHeuristic::getNodes(std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& assignments, const SAS_Plus::LiftedDTG& lifted_dtg, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const
{
//	std::cout << "Get nodes." << std::endl;
//	std::cout << state << std::endl;
//	std::cout << "Invariable domain: " << invariable_domain << std::endl;
	
	for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = lifted_dtg.getNodes().begin(); ci != lifted_dtg.getNodes().end(); ++ci)
	{
		const SAS_Plus::MultiValuedValue* node = *ci;
		if (node->isCopy())
		{
			continue;
		}
//		std::cout << "Process: " << *node << std::endl;
		std::vector<const HEURISTICS::Fact*> empty_mapping;
		std::vector<std::vector<const HEURISTICS::Fact*>* > found_mappings;
		findMappings(found_mappings, empty_mapping, *node, invariable_domain, state);
		
		for (std::vector<std::vector<const HEURISTICS::Fact*>* >::const_iterator ci = found_mappings.begin(); ci != found_mappings.end(); ++ci)
		{
			assignments.push_back(std::make_pair(node, *ci));
		}
	}
}

void LiftedCausalGraphHeuristic::findMappings(std::vector<std::vector<const HEURISTICS::Fact*>* >& found_mappings, const std::vector<const HEURISTICS::Fact*>& current_mappings, const SAS_Plus::MultiValuedValue& node, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const
{
	unsigned int fact_index = current_mappings.size();
/*#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	std::cout << "[LiftedCausalGraphHeuristic::findMappings] Index: " << fact_index << std::endl;
	for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = current_mappings.begin(); ci != current_mappings.end(); ++ci)
	{
		std::cout << "* " << **ci << std::endl;
	}
#endif*/
	
	// Found a full assignment!
	if (fact_index == node.getValues().size())
	{
		std::vector<const HEURISTICS::Fact*>* new_found_mapping = new std::vector<const HEURISTICS::Fact*>();
		for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = current_mappings.begin(); ci != current_mappings.end(); ++ci)
		{
			const HEURISTICS::Fact* grounded_atom = *ci;
			std::vector<const HEURISTICS::VariableDomain*>* variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
			for (unsigned int i = 0; i < grounded_atom->getPredicate().getArity(); ++i)
			{
				HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
				vd->set(grounded_atom->getVariableDomains()[i]->getVariableDomain());
				variable_domains->push_back(vd);
			}
			new_found_mapping->push_back(new HEURISTICS::Fact(*predicate_manager_, grounded_atom->getPredicate(), *variable_domains));
		}
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
		
		std::vector<const HEURISTICS::VariableDomain*> variable_domain;
		for (unsigned int term_index = 0; term_index < atom->getPredicate().getArity(); ++term_index)
		{
			HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
			vd->set(atom->getObject(term_index));
			variable_domain.push_back(vd);
		}
		HEURISTICS::Fact fact(*predicate_manager_, atom->getPredicate(), variable_domain);
		
		// Found an assignment!
		std::vector<const HEURISTICS::Fact*> new_current_mappings(current_mappings);
		new_current_mappings.push_back(&fact);
		HEURISTICS::VariableDomain new_invariable_domain;
		if (property->getIndex() != std::numeric_limits<unsigned int>::max())
		{
			new_invariable_domain.set(atom->getObject(property->getIndex()));
			findMappings(found_mappings, new_current_mappings, node, new_invariable_domain, state);
		}
		else
		{
			findMappings(found_mappings, new_current_mappings, node, invariable_domain, state);
		}
	}
}
/*
unsigned int LiftedCausalGraphHeuristic::getCost()
{
	
}
*/
const SAS_Plus::MultiValuedValue* LiftedCausalGraphHeuristic::findNode(const HEURISTICS::Fact& fact, const std::vector<const SAS_Plus::LiftedDTG*>& possible_lifted_dtgs) const
{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	std::cout << "[LiftedCausalGraphHeuristic::findNode] " << fact << std::endl;
#endif
	// Find the set of nodes this goal is part of.
	std::vector<const SAS_Plus::MultiValuedValue*> found_nodes;
	for (std::vector<const SAS_Plus::LiftedDTG*>::const_iterator ci = possible_lifted_dtgs.begin(); ci != possible_lifted_dtgs.end(); ++ci)
	{
		const SAS_Plus::LiftedDTG* lifted_dtg = *ci;
		lifted_dtg->getNodes(found_nodes, fact);
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Check " << *lifted_dtg << "." << std::endl;
		std::cout << "Found: " << std::endl;
		for (std::vector<const SAS_Plus::MultiValuedValue*>::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ++ci)
		{
			std::cout << "* " << **ci << std::endl;
		}
#endif
	}
	
	// Next we select the node whose lifted DTG has the least number of dependencies (preferably none!).
	const SAS_Plus::MultiValuedValue* best_node = NULL;
	std::vector<const SAS_Plus::LiftedDTG*> best_node_dependencies;
	for (std::vector<const SAS_Plus::MultiValuedValue*>::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ++ci)
	{
		const SAS_Plus::MultiValuedValue* node = *ci;
		
		// Copies are never initialised!
		if (node->isCopy())
		{
			continue;
		}
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
