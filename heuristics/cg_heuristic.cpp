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

///#define LIFTED_CAUSAL_GRAPH_COMMENTS

namespace MyPOP {

namespace HEURISTICS {

bool CompareLCGSearchNodes::operator()(const LCGSearchNode* lhs_node, const LCGSearchNode* rhs_node)
{
	return lhs_node->getCost() > rhs_node->getCost();
}

LCGSearchNode::LCGSearchNode(std::vector<const HEURISTICS::Fact*>& assignments, const SAS_Plus::MultiValuedValue& node, std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& assignments_to_lower_variables, unsigned int cost)
	: starting_node_(this), assignments_(&assignments), node_(&node), assignments_to_lower_variables_(&assignments_to_lower_variables), cost_(cost)
{
	
}

LCGSearchNode::LCGSearchNode(const LCGSearchNode& starting_node, std::vector<const HEURISTICS::Fact*>& assignments, const SAS_Plus::MultiValuedValue& node, std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& assignments_to_lower_variables, unsigned int cost)
	: starting_node_(&starting_node), assignments_(&assignments), node_(&node), assignments_to_lower_variables_(&assignments_to_lower_variables), cost_(cost)
{
	
}

LCGSearchNode::LCGSearchNode(const LCGSearchNode& other)
	: starting_node_(other.starting_node_), node_(other.node_), cost_(other.cost_)
{
	assignments_ = new std::vector<const HEURISTICS::Fact*>();
	for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = other.assignments_->begin(); ci != other.assignments_->end(); ++ci)
	{
		assignments_->push_back(new HEURISTICS::Fact(**ci));
	}
	
	assignments_to_lower_variables_ = new std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >();
	for (std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >::const_iterator ci = other.assignments_to_lower_variables_->begin(); ci != other.assignments_to_lower_variables_->end(); ++ci)
	{
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* new_assignments = new std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >();
		
		const SAS_Plus::LiftedDTG* lifted_dtg = (*ci).first;
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* current_facts = (*ci).second;
		
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = current_facts->begin(); ci != current_facts->end(); ++ci)
		{
			const SAS_Plus::MultiValuedValue* mvv = (*ci).first;
			const std::vector<const HEURISTICS::Fact*>* org_facts = (*ci).second;
			
			std::vector<const HEURISTICS::Fact*>* new_facts = new std::vector<const HEURISTICS::Fact*>();
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = org_facts->begin(); ci != org_facts->end(); ++ci)
			{
				new_facts->push_back(new HEURISTICS::Fact(**ci));
			}
			new_assignments->push_back(std::make_pair(mvv, new_facts));
		}
		(*assignments_to_lower_variables_)[lifted_dtg] = new_assignments;
	}
}

LCGSearchNode& LCGSearchNode::createDeepCopy() const
{
	LCGSearchNode* copy = new LCGSearchNode(*this);
	copy->starting_node_ = new LCGSearchNode(*starting_node_);
	return *copy;
}

LCGSearchNode::~LCGSearchNode()
{
	for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = assignments_->begin(); ci != assignments_->end(); ++ci)
	{
		delete *ci;
	}
	delete assignments_;
	for (std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >::const_iterator ci = assignments_to_lower_variables_->begin(); ci != assignments_to_lower_variables_->end(); ++ci)
	{
		std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* assignments = (*ci).second;
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = assignments->begin(); ci != assignments->end(); ++ci)
		{
			const std::vector<const HEURISTICS::Fact*>* given_facts = (*ci).second;
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = given_facts->begin(); ci != given_facts->end(); ++ci)
			{
				delete *ci;
			}
			delete given_facts;
		}
		delete assignments;
	}
	delete assignments_to_lower_variables_;
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

LiftedCausalGraphHeuristic::~LiftedCausalGraphHeuristic()
{
	delete causal_graph_;
	for (std::map<const SAS_Plus::MultiValuedValue*, std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* >::const_iterator ci = cache_.begin(); ci != cache_.end(); ++ci)
	{
		std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* cache_item = (*ci).second;
		
		for (std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >::const_iterator ci = cache_item->begin(); ci != cache_item->end(); ++ci)
		{
			delete (*ci).first;
			delete &(*ci).second->getStartingNode();
			delete (*ci).second;
		}
		
		delete cache_item;
	}
}

void LiftedCausalGraphHeuristic::setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager, bool find_helpful_actions, bool allow_new_goals_to_be_added)
{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	std::cout << "LiftedCausalGraphHeuristic::setHeuristicForState" << std::endl;
	std::cout << state << std::endl;
#endif
	deleteHelpfulActions();
	std::vector<const GroundedAtom*> facts_in_state;
	state.getFacts(initial_facts, facts_in_state);
	unsigned int h = getHeuristic(facts_in_state, initial_facts, goal_facts);
	state.setDistanceToGoal(h);
}

unsigned int LiftedCausalGraphHeuristic::getHeuristic(const std::vector<const GroundedAtom*>& facts_in_state, const std::vector<const GroundedAtom*>& initial_facts, const std::vector< const GroundedAtom* >& bounded_goal_facts)
{
	for (std::map<const SAS_Plus::MultiValuedValue*, std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* >::const_iterator ci = cache_.begin(); ci != cache_.end(); ++ci)
	{
		std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* cache_item = (*ci).second;
		
		for (std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >::const_iterator ci = cache_item->begin(); ci != cache_item->end(); ++ci)
		{
			delete (*ci).first;
			delete &(*ci).second->getStartingNode();
			delete (*ci).second;
		}
		
		delete cache_item;
	}
	cache_.clear();
	
//	std::vector<const Fact*> all_created_facts;
	
//	std::cerr << ";";
	std::vector<const SAS_Plus::LiftedDTG*> all_lifted_dtgs;
	for (std::vector<SAS_Plus::LiftedDTG*>::const_iterator ci = lifted_dtgs_->begin(); ci != lifted_dtgs_->end(); ++ci)
	{
		all_lifted_dtgs.push_back(*ci);
	}

	unsigned int h = 0;

	// For every goal we try to find a plan in the abstract space.
	for (std::vector<const GroundedAtom*>::const_iterator ci = bounded_goal_facts.begin(); ci != bounded_goal_facts.end(); ++ci)
	{
		const GroundedAtom* goal = *ci;
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Process the goal: " << *goal << std::endl;
#endif
//		std::cerr << "Process the goal: " << *goal << std::endl;
		
		std::vector<const VariableDomain*>* variable_domains = new std::vector<const VariableDomain*>();
		
		for (unsigned int term_index = 0; term_index < goal->getPredicate().getArity(); ++term_index)
		{
			VariableDomain* vd = new VariableDomain();
			vd->addObject(goal->getObject(term_index));
			variable_domains->push_back(vd);
		}
		
		HEURISTICS::Fact goal_fact(*predicate_manager_, goal->getPredicate(), *variable_domains);
/*
		for (std::vector<const VariableDomain*>::const_iterator ci = variable_domains.begin(); ci != variable_domains.end(); ++ci)
		{
			delete *ci;
		}
*/
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Transformed into: " << goal_fact << std::endl;
#endif
		
		const LCGSearchNode* result = getCost(facts_in_state, all_lifted_dtgs, goal_fact, NULL, initial_facts);
		
		if (result == NULL)
		{
//#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			//std::cerr << state << std::endl;
			for (std::vector<const GroundedAtom*>::const_iterator ci = facts_in_state.begin(); ci != facts_in_state.end(); ++ci)
			{
				std::cerr << "* " << **ci << std::endl;
			}
//		std::cerr << "Could not achieve the goal: " << goal_fact << "Invariable domain: " << invariable_domain << std::endl;
			std::cerr << "Could not achieve the goal: " << goal_fact << std::endl;
//		std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
//#endif
			h = std::numeric_limits<unsigned int>::max();
			assert (false);
			break;
		}
		h += result->getCost();
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
//		std::cout << "Achieve the goal: " << goal_fact << "Invariable domain: " << invariable_domain << ". Costs = " << result->getCost() << "." << std::endl;
		std::cout << "Achieve the goal: " << goal_fact << "; Costs = " << result->getCost() << "." << std::endl;
//		std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
#endif
		delete &result->getStartingNode();
		delete result;
	}
	return h;
}

const LCGSearchNode* LiftedCausalGraphHeuristic::getCost(const std::vector<const GroundedAtom*>& facts_in_state, const std::vector<const SAS_Plus::LiftedDTG*>& lifted_dtgs, const HEURISTICS::Fact& goal, const LCGSearchNode* current_search_node, const std::vector<const GroundedAtom*>& initial_facts)
{
	// Check if we have this solution cached.
	const SAS_Plus::MultiValuedValue* current_node = NULL;
	if (current_search_node != NULL)
	{
		current_node = &current_search_node->getNode();
	}
	
	std::map<const SAS_Plus::MultiValuedValue*, std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* >::const_iterator cache_ci = cache_.find(current_node);
	if (cache_ci != cache_.end())
	{
		std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* cached_solutions = (*cache_ci).second;
		for (std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >::const_iterator ci = cached_solutions->begin(); ci != cached_solutions->end(); ++ci)
		{
			if ((*ci).first->canUnifyWith(goal))
			{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
				std::cout << "Found cached solution: " << *(*ci).second << std::endl;
#endif
				return &(*ci).second->createDeepCopy();
			}
		}
	}

	// If the fact is not part of the from node, then we look for the DTG it does belong to.
	const SAS_Plus::MultiValuedValue* best_node = findNode(goal, lifted_dtgs);
	
	if (best_node == NULL)
	{
		std::cerr << "Could not find a node for the precondition: " << goal << std::endl;
		std::cerr << "#nodes considered: " << lifted_dtgs.size() << std::endl;
		for (std::vector<const SAS_Plus::LiftedDTG*>::const_iterator ci = lifted_dtgs.begin(); ci != lifted_dtgs.end(); ++ci)
		{
			std::cerr << **ci << std::endl;
		}
		assert (best_node != NULL);
	}
	
	// Check which term is invariable.
	HEURISTICS::VariableDomain invariable_domain;
	for (unsigned int fact_index = 0; fact_index < best_node->getValues().size(); ++fact_index)
	{
		if (goal.canUnifyWith(*best_node->getValues()[fact_index]))
		{
			const SAS_Plus::Property* property = best_node->getPropertyState().getProperties()[fact_index];
			if (property->getIndex() != std::numeric_limits<unsigned int>::max())
			{
				invariable_domain.set(goal.getVariableDomains()[property->getIndex()]->getVariableDomain());
				break;
			}
		}
	}
	
	std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > > goal_nodes;
	std::vector<const HEURISTICS::Fact*> goal_facts;
	goal_facts.push_back(&goal);
	goal_nodes.push_back(std::make_pair(best_node, &goal_facts));
	
//				std::cerr << "Process the precondition: " << goal << std::endl;
	
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	std::cout << "Goal: " << goal << "Invariable domain: " << invariable_domain << std::endl;
//				std::cout << "Lifted DTG: " << best_node->getLiftedDTG() << std::endl;
	/*
	std::cout << "Find nodes for the initial state: ";
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts_in_state.begin(); ci != facts_in_state.end(); ++ci)
	{
		std::cerr << "* " << **ci << std::endl;
	}
	if (current_search_node != NULL)
	{
		std::cout << "Search node: " << *current_search_node << std::endl;
	}
	else
	{
		std::cout << "Need to find the node!" << std::endl;
	}
	*/
#endif
	
	std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > > new_from_assignments;
	if (current_search_node != NULL)
	{
		const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& org_from_assignments = current_search_node->getAssignmentsToLowerVariables(best_node->getLiftedDTG());
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Initial assignments to the lower variables: " << std::endl;
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = org_from_assignments.begin(); ci != org_from_assignments.end(); ++ci)
		{
			std::cout << *(*ci).first << std::endl;
			const std::vector<const HEURISTICS::Fact*>* facts = (*ci).second;
			
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = facts->begin(); ci != facts->end(); ++ci)
			{
				std::cout << "* " << **ci << "." << std::endl;
			}
		}
#endif
		
		//std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* new_from_assignments = new std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >();
		
		// Prune those from nodes which do not match the invariable.
		for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = org_from_assignments.begin(); ci != org_from_assignments.end(); ++ci)
		{
			const SAS_Plus::MultiValuedValue* node = (*ci).first;
			const std::vector<const HEURISTICS::Fact*>* assignments = (*ci).second;
			
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
			
			if (node_invariable_domain == NULL || node_invariable_domain->sharesObjectsWith(invariable_domain))
			{
				std::vector<const HEURISTICS::Fact*>* new_assignments = new std::vector<const HEURISTICS::Fact*>();
				for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = assignments->begin(); ci != assignments->end(); ++ci)
				{
					new_assignments->push_back(new HEURISTICS::Fact(**ci));
				}
				//new_from_assignments->push_back(std::make_pair(node, new_assignments));
				new_from_assignments.push_back(std::make_pair(node, new_assignments));
			}
		}
	}
	// If no current node is specified, then we are finding a plan from the state.
	else
	{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "[getCost]: No initial node specified. Search for it!" << std::endl;
#endif
		// Find the value of the initial state.
		getNodes(new_from_assignments, best_node->getLiftedDTG(), invariable_domain, facts_in_state, initial_facts);
	}
	
	if (current_search_node != NULL)
	{
		assert (&best_node->getLiftedDTG() != &current_search_node->getNode().getLiftedDTG());
	}
	
	const LCGSearchNode* result = getCost(facts_in_state, best_node->getLiftedDTG(), new_from_assignments, goal_nodes, initial_facts);

	// Store the cached value.
	if (result != NULL)
	{
		std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* cached_items = NULL;
		if (cache_ci != cache_.end())
		{
			cached_items = (*cache_ci).second;
		}
		else
		{
			cached_items = new std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >();
			cache_[current_node] = cached_items;
		}
		
		cached_items->push_back(std::make_pair(new HEURISTICS::Fact(goal), &result->createDeepCopy()));
	}

	for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = new_from_assignments.begin(); ci != new_from_assignments.end(); ++ci)
	{
		delete (*ci).second;
	}
	
	return result;
}

const LCGSearchNode* LiftedCausalGraphHeuristic::getCost(const std::vector<const GroundedAtom*>& facts_in_state, const SAS_Plus::LiftedDTG& lifted_dtg, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& from_nodes, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& to_nodes, const std::vector<const GroundedAtom*>& initial_facts)
{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	std::cout << "[LiftedCausalGraphHeuristic::getCost] " << std::endl;
	std::cout << "State: " << std::endl;
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts_in_state.begin(); ci != facts_in_state.end(); ++ci)
	{
		std::cerr << "* " << **ci << std::endl;
	}
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
	
/*	std::cout << "The dependencies of " << lifted_dtg << " are: " << std::endl;
	
	for (std::vector<const SAS_Plus::LiftedDTG*>::const_iterator ci = dependencies.begin(); ci != dependencies.end(); ++ci)
	{
		std::cout << " === DEP === " << std::endl;
		std::cout << **ci << std::endl;
		std::cout << " === PED === " << std::endl;
	}*/
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
	
	std::set<const LCGSearchNode*> starting_nodes;
	
	for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = from_nodes.begin(); ci != from_nodes.end(); ++ci)
	{
		const SAS_Plus::MultiValuedValue* node = (*ci).first;
		const std::vector<const HEURISTICS::Fact*>* assignments_to_node = (*ci).second;
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "Start node: " << *node << (node->isCopy() ? "(COPY)" : "(REAL)") << std::endl;
#endif
		
		// Enable any copies of this node.
		for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = node->getCopies().begin(); ci != node->getCopies().end(); ++ci)
		{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "Enable the copy: " << **ci << std::endl;
#endif
			closed_list.erase(*ci);
		}
		
		std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >* assignments_per_lifted_dtg = new std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >();
		
		// Initialise the values of the dependencies.
		for (std::vector<const SAS_Plus::LiftedDTG*>::const_iterator ci = dependencies.begin(); ci != dependencies.end(); ++ci)
		{
			const SAS_Plus::LiftedDTG* lifted_dtg = *ci;
			HEURISTICS::VariableDomain invariable_domain(lifted_dtg->getInvariableObjects());
			
			std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* assignments = new std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >();
			getNodes(*assignments, *lifted_dtg, invariable_domain, facts_in_state, initial_facts);
			(*assignments_per_lifted_dtg)[lifted_dtg] = assignments;
		}
		
		std::vector<const HEURISTICS::Fact*>* from_node_assignments = new std::vector<const HEURISTICS::Fact*>(*assignments_to_node);
		LCGSearchNode* starting_node = new LCGSearchNode(*from_node_assignments, *node, *assignments_per_lifted_dtg);
		starting_nodes.insert(starting_node);
		open_list.push(starting_node);
		
		assert (assignments_per_lifted_dtg->size() == dependencies.size());
	}
	
	while (!open_list.empty())
	{
		const LCGSearchNode* current_node = open_list.top();
		open_list.pop();
		
		if (closed_list.find(&current_node->getNode()) != closed_list.end())
		{
			if (starting_nodes.find(current_node) == starting_nodes.end())
			{
				delete current_node;
			}
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
			
			if (current_node != &goal_node->getStartingNode())
			{
				delete current_node;
			}
			
			while (!open_list.empty())
			{
				const LCGSearchNode* current_node = open_list.top();
				open_list.pop();
				
				if (starting_nodes.find(current_node) == starting_nodes.end())
				{
					delete current_node;
				}
			}
			
			for (std::set<const LCGSearchNode*>::const_iterator ci = starting_nodes.begin(); ci != starting_nodes.end(); ++ci)
			{
				if (*ci != &goal_node->getStartingNode())
				{
					delete *ci;
				}
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
//			std::cerr << "Process the transition: " << transition->getAction().getPredicate() << std::endl;
			
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
				std::vector<const VariableDomain*>* variable_domains = new std::vector<const VariableDomain*>();
				for (unsigned int term_index = 0; term_index < precondition->getArity(); ++term_index)
				{
					for (unsigned int action_index = 0; action_index < transition->getAction().getVariables().size(); ++action_index)
					{
						if (precondition->getTerms()[term_index] == transition->getAction().getVariables()[action_index])
						{
//							variable_domains.push_back(&transition->getActionVariableDomain(action_index));
							variable_domains->push_back(new VariableDomain(action_variable_domains[action_index]->getVariableDomain()));
							break;
						}
					}
				}
				
				HEURISTICS::Fact precondition_fact(*predicate_manager_, precondition->getPredicate(), *variable_domains);
				
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

				const LCGSearchNode* result = getCost(facts_in_state, dependencies, precondition_fact, current_node, initial_facts);
				assignments_made.push_back(result);

				if (result == NULL)
				{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
					std::cout << "Could not find an achiever for the precondition: " << precondition_fact << std::endl;
#endif
					transition_cost = std::numeric_limits<unsigned int>::max();
					break;
				}
				else
				{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
					std::cout << "Achieved the precondition: " << precondition_fact << std::endl;
					
					std::cout << *result << std::endl;
					
/*
					std::cout << "With cost: " << result->getCost() << std::endl;
					std::cout << "Initial facts: " << std::endl;
					for (std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >::const_iterator ci = org_from_assignments.begin(); ci != org_from_assignments.end(); ++ci)
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
*/
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
										HEURISTICS::VariableDomain intersection;
										action_variable_domains[action_index]->getIntersection(intersection, *matching_grounded_fact->getVariableDomains()[term_index]);
										action_variable_domains[action_index]->set(intersection.getVariableDomain());
										
										//action_variable_domains[action_index]->set(matching_grounded_fact->getVariableDomains()[term_index]->getVariableDomain());
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
				for (std::vector<const LCGSearchNode*>::const_iterator ci = assignments_made.begin(); ci != assignments_made.end(); ++ci)
				{
					const LCGSearchNode* search_node = *ci;
					if (search_node == NULL)
					{
						continue;
					}
					if (&search_node->getStartingNode() != search_node)
					{
						delete &search_node->getStartingNode();
					}
					delete search_node;
				}
				
				for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_domains.begin(); ci != action_variable_domains.end(); ++ci)
				{
					delete *ci;
				}
				
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
						if (effect_to_action_variable_mappings[to_fact_index] == NULL)
						{
							std::cerr << "Could not find the mapping of the " << to_fact_index << "th fact of the to node: " << transition->getToNode() << std::endl;
							std::cerr << *transition << std::endl;
							assert (false);
						}
						else
						{
							to_node_variable_domains->push_back(new HEURISTICS::VariableDomain(*action_variable_domains[(*effect_to_action_variable_mappings[to_fact_index])[term_index]]));
						}
					}
				}
				assignments_to_to_node->push_back(new HEURISTICS::Fact(*predicate_manager_, to_fact->getPredicate(), *to_node_variable_domains));
/*
				for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = to_node_variable_domains.begin(); ci != to_node_variable_domains.end(); ++ci)
				{
					delete *ci;
				}
*/
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
//								new_mappings->push_back(std::make_pair(&search_node->getNode(), &search_node->getAssignments()));
								//new_mappings->push_back(std::make_pair(&search_node->getNode(), new std::vector<const HEURISTICS::Fact*>(search_node->getAssignments())));
								
								std::vector<const HEURISTICS::Fact*>* new_facts_for_search_node = new std::vector<const HEURISTICS::Fact*>();
								for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = search_node->getAssignments().begin(); ci != search_node->getAssignments().end(); ++ci)
								{
									new_facts_for_search_node->push_back(new HEURISTICS::Fact(**ci));
								}
								new_mappings->push_back(std::make_pair(&search_node->getNode(), new_facts_for_search_node));
								break;
							}
						}
					}
					
					if (!node_has_been_altered)
					{
						std::vector<const HEURISTICS::Fact*>* new_facts_for_search_node = new std::vector<const HEURISTICS::Fact*>();
						for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = previous_assignments->begin(); ci != previous_assignments->end(); ++ci)
						{
							new_facts_for_search_node->push_back(new HEURISTICS::Fact(**ci));
						}
						new_mappings->push_back(std::make_pair(node, new_facts_for_search_node));
					}
				}
				(*new_assignments_to_lower_variables)[lifted_dtg] = new_mappings;
			}
			
			for (std::vector<const LCGSearchNode*>::const_iterator ci = assignments_made.begin(); ci != assignments_made.end(); ++ci)
			{
				const LCGSearchNode* search_node = *ci;
				if (&search_node->getStartingNode() != search_node)
				{
					delete &search_node->getStartingNode();
				}
				delete search_node;
			}
			
			for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_domains.begin(); ci != action_variable_domains.end(); ++ci)
			{
				delete *ci;
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
			
//			std::cerr << "DONE Processing the transition..." << std::endl;
		}
		
		if (starting_nodes.find(current_node) == starting_nodes.end())
		{
			delete current_node;
		}
	}
	
	assert (open_list.empty());
	
 	for (std::set<const LCGSearchNode*>::const_iterator ci = starting_nodes.begin(); ci != starting_nodes.end(); ++ci)
	{
		delete *ci;
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
void LiftedCausalGraphHeuristic::getNodes(std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& assignments, const SAS_Plus::LiftedDTG& lifted_dtg, const HEURISTICS::VariableDomain& invariable_domain, const std::vector<const GroundedAtom*>& facts_in_state, const std::vector<const GroundedAtom*>& initial_state) const
{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
	std::cout << "Get nodes. Invariable domain: " << invariable_domain << std::endl;
#endif
	
	for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = lifted_dtg.getNodes().begin(); ci != lifted_dtg.getNodes().end(); ++ci)
	{
		const SAS_Plus::MultiValuedValue* node = *ci;
		if (node->isCopy())
		{
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			std::cout << "Skip: " << *node << " because it is a copy." << std::endl;
#endif
			continue;
		}
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
		std::cout << "Process: " << *node << std::endl;
#endif
		std::vector<const HEURISTICS::Fact*> empty_mapping;
		std::vector<std::vector<const HEURISTICS::Fact*>* > found_mappings;
		findMappings(found_mappings, empty_mapping, *node, invariable_domain, facts_in_state, initial_state);
		
		for (std::vector<std::vector<const HEURISTICS::Fact*>* >::const_iterator ci = found_mappings.begin(); ci != found_mappings.end(); ++ci)
		{
			assignments.push_back(std::make_pair(node, *ci));
			
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
			const std::vector<const HEURISTICS::Fact*>* facts = *ci;
			for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = facts->begin(); ci != facts->end(); ++ci)
			{
				std::cout << "* " << **ci << std::endl;
			}
#endif
			
		}
	}
}

void LiftedCausalGraphHeuristic::findMappings(std::vector<std::vector<const HEURISTICS::Fact*>* >& found_mappings, const std::vector<const HEURISTICS::Fact*>& current_mappings, const SAS_Plus::MultiValuedValue& node, const HEURISTICS::VariableDomain& invariable_domain, const std::vector<const GroundedAtom*>& facts_in_state, const std::vector<const GroundedAtom*>& initial_facts) const
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
/*
			for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = variable_domains.begin(); ci != variable_domains.end(); ++ci)
			{
				delete *ci;
			}
*/
		}
		found_mappings.push_back(new_found_mapping);
		return;
	}
	
	const HEURISTICS::Fact* fact = node.getValues()[fact_index];
	const SAS_Plus::Property* property = node.getPropertyState().getProperties()[fact_index];
	
//	std::vector<const GroundedAtom*> state_facts;
//	state.getFacts(initial_facts, state_facts);
	
	// Check which facts from the state can be mapped to this fact.
	///for (std::vector<const GroundedAtom*>::const_iterator ci = state.getFacts().begin(); ci != state.getFacts().end(); ++ci)
	for (std::vector<const GroundedAtom*>::const_iterator ci = facts_in_state.begin(); ci != facts_in_state.end(); ++ci)
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
		
		std::vector<const HEURISTICS::VariableDomain*>* variable_domain = new std::vector<const HEURISTICS::VariableDomain*>();
		for (unsigned int term_index = 0; term_index < atom->getPredicate().getArity(); ++term_index)
		{
			HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
			vd->set(atom->getObject(term_index));
			variable_domain->push_back(vd);
		}
		HEURISTICS::Fact fact(*predicate_manager_, atom->getPredicate(), *variable_domain);
/*
		for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ++ci)
		{
			delete *ci;
		}
*/
		
		// Found an assignment!
		std::vector<const HEURISTICS::Fact*> new_current_mappings(current_mappings);
		new_current_mappings.push_back(&fact);
		HEURISTICS::VariableDomain new_invariable_domain;
		if (property->getIndex() != std::numeric_limits<unsigned int>::max())
		{
			new_invariable_domain.set(atom->getObject(property->getIndex()));
			findMappings(found_mappings, new_current_mappings, node, new_invariable_domain, facts_in_state, initial_facts);
		}
		else
		{
			findMappings(found_mappings, new_current_mappings, node, invariable_domain, facts_in_state, initial_facts);
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
//	std::cout << "[LiftedCausalGraphHeuristic::findNode] " << fact << std::endl;
#endif
	// Find the set of nodes this goal is part of.
	std::vector<const SAS_Plus::MultiValuedValue*> found_nodes;
	for (std::vector<const SAS_Plus::LiftedDTG*>::const_iterator ci = possible_lifted_dtgs.begin(); ci != possible_lifted_dtgs.end(); ++ci)
	{
		const SAS_Plus::LiftedDTG* lifted_dtg = *ci;
		lifted_dtg->getNodes(found_nodes, fact);
		
#ifdef LIFTED_CAUSAL_GRAPH_COMMENTS
//		std::cout << "Check " << *lifted_dtg << "." << std::endl;
//		std::cout << "Found: " << std::endl;
//		for (std::vector<const SAS_Plus::MultiValuedValue*>::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ++ci)
//		{
//			std::cout << "* " << **ci << std::endl;
//		}
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
