#include "causal_graph.h"

#include <fstream>

#include "heuristics/dtg_reachability.h"
#include "fc_planner.h"

#include "../action_manager.h"
#include "../formula.h"
#include "../parser_utils.h"

//#define MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
#include "predicate_manager.h"
#include "lifted_dtg.h"
#include "heuristics/fact_set.h"
#include "type_manager.h"
#include "term_manager.h"
#include "property_space.h"

namespace MyPOP {
	
namespace SAS_Plus {

CausalGraph::CausalGraph(const std::vector<LiftedDTG*>& all_lifted_dtgs, const MyPOP::ActionManager& action_manager, const PredicateManager& predicate_manager)
	: all_lifted_dtgs_(&all_lifted_dtgs), action_manager_(&action_manager), cached_dependencies_(NULL), predicate_manager_(&predicate_manager)
{
	// Initialise the data structures.
	for (std::vector<LiftedDTG*>::const_iterator dtg_ci = all_lifted_dtgs.begin(); dtg_ci != all_lifted_dtgs.end(); dtg_ci++)
	{
		const LiftedDTG* dtg = *dtg_ci;
		std::set<const LiftedDTG*>* dtg_set = new std::set<const LiftedDTG*>();
		transitions_.insert(std::make_pair(dtg, dtg_set));
		std::set<const LiftedDTG*>* reverse_dtg_set = new std::set<const LiftedDTG*>();
		reverse_transitions_.insert(std::make_pair(dtg, reverse_dtg_set));
		
		for (std::vector<LiftedDTG*>::const_iterator dtg_ci = all_lifted_dtgs.begin(); dtg_ci != all_lifted_dtgs.end(); dtg_ci++)
		{
			std::set<const MultiValuedTransition*>* supported_transitions = new std::set<const MultiValuedTransition*>();
			arc_weights_[std::make_pair(dtg, *dtg_ci)] = supported_transitions;
		}
	}
	
	/**
	 * A edge exists in the CG in the following cases:
	 * 1) A transition in one of the DTGs has a precondition which is linked to an external DTG.
	 * 2) A transition exists which affects the values of two or more DTGs.
	 * 
	 * In this system all actions are contained in DTGs (even if it only concerns a fact which can either be true or false).
	 */
	for (std::vector<LiftedDTG*>::const_iterator dtg_ci = all_lifted_dtgs.begin(); dtg_ci != all_lifted_dtgs.end(); dtg_ci++)
	{
		const LiftedDTG* dtg = *dtg_ci;
		
		// Go through all transitions and check the external dependencies.
		for (std::vector<MultiValuedValue*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ++ci)
		{
			const MultiValuedValue* node = *ci;
			for (std::vector<const MultiValuedTransition*>::const_iterator ci = node->getTransitions().begin(); ci != node->getTransitions().end(); ++ci)
			{
				const MultiValuedTransition* transition = *ci;
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
				std::cout << "Process: " << *transition << "." << std::endl;
#endif
				std::vector<const Atom*> preconditions;
				Utility::convertFormula(preconditions, &transition->getAction().getPrecondition());
				
				for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
				{
					const Atom* precondition = *ci;
					bool is_external_precondition = true;
					
					std::vector<const HEURISTICS::VariableDomain*> precondition_variable_domains;
					for (unsigned int term_index = 0; term_index < precondition->getPredicate().getArity(); ++term_index)
					{
						precondition_variable_domains.push_back(new HEURISTICS::VariableDomain(transition->getActionVariableDomain(transition->getAction().getActionVariable(*precondition->getTerms()[term_index])).getVariableDomain()));
					}
					HEURISTICS::Fact precondition_fact(predicate_manager, precondition->getPredicate(), precondition_variable_domains);
					
					for (std::vector<HEURISTICS::Fact*>::const_iterator ci = node->getValues().begin(); ci != node->getValues().end(); ++ci)
					{
						HEURISTICS::Fact* fact = *ci;
						
						if (precondition_fact.canUnifyWith(*fact))
						{
							is_external_precondition = false;
							break;
						}
					}
					if (!is_external_precondition) continue;
					
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
					std::cout << "External precondition: ";
					precondition->print(std::cout);
					std::cout << std::endl;
#endif
					for (std::vector<LiftedDTG*>::const_iterator dtg_ci = all_lifted_dtgs.begin(); dtg_ci != all_lifted_dtgs.end(); dtg_ci++)
					{
						const LiftedDTG* other_dtg = *dtg_ci;
						if (other_dtg == dtg)
						{
							continue;
						}
						std::vector<const MultiValuedValue*> matching_lifted_dtgs;
						other_dtg->getNodes(matching_lifted_dtgs, precondition_fact);
						
						if (matching_lifted_dtgs.size() > 0)
						{
							addTransition(*dtg, *other_dtg, *transition);
						}
					}
				}
				
				// Check if there exists a pair of effects which affects more than two different DTGs.
				for (std::vector<const Atom*>::const_iterator ci = transition->getAction().getEffects().begin(); ci != transition->getAction().getEffects().end() - 1; ++ci)
				{
					const Atom* lhs_effect = *ci;
					
					std::vector<const HEURISTICS::VariableDomain*> lhs_effect_variable_domains;
					for (unsigned int term_index = 0; term_index < lhs_effect->getPredicate().getArity(); ++term_index)
					{
						lhs_effect_variable_domains.push_back(new HEURISTICS::VariableDomain(transition->getActionVariableDomain(transition->getAction().getActionVariable(*lhs_effect->getTerms()[term_index])).getVariableDomain()));
					}
					HEURISTICS::Fact lhs_effect_fact(predicate_manager, lhs_effect->getPredicate(), lhs_effect_variable_domains);
					
					
					std::vector<const LiftedDTG*> dtgs_affected_by_lhs_effect;
					for (std::vector<LiftedDTG*>::const_iterator lifted_dtgs_ci = all_lifted_dtgs.begin(); lifted_dtgs_ci != all_lifted_dtgs.end(); ++lifted_dtgs_ci)
					{
						std::vector<const MultiValuedValue*> matching_lifted_dtgs;
						(*lifted_dtgs_ci)->getNodes(matching_lifted_dtgs, lhs_effect_fact);
						
						if (matching_lifted_dtgs.size() > 0)
						{
							dtgs_affected_by_lhs_effect.push_back(*lifted_dtgs_ci);
						}
					}
					
					for (std::vector<const Atom*>::const_iterator ci2 = ci + 1; ci2 != transition->getAction().getEffects().end(); ++ci2)
					{
						const Atom* rhs_effect = *ci2;
						
						std::vector<const HEURISTICS::VariableDomain*> rhs_effect_variable_domains;
						for (unsigned int term_index = 0; term_index < rhs_effect->getPredicate().getArity(); ++term_index)
						{
							rhs_effect_variable_domains.push_back(new HEURISTICS::VariableDomain(transition->getActionVariableDomain(transition->getAction().getActionVariable(*rhs_effect->getTerms()[term_index])).getVariableDomain()));
						}
						HEURISTICS::Fact rhs_effect_fact(predicate_manager, rhs_effect->getPredicate(), rhs_effect_variable_domains);
						
						std::vector<const LiftedDTG*> dtgs_affected_by_rhs_effect;
						for (std::vector<LiftedDTG*>::const_iterator lifted_dtgs_ = all_lifted_dtgs.begin(); lifted_dtgs_ != all_lifted_dtgs.end(); ++lifted_dtgs_)
						{
							std::vector<const MultiValuedValue*> matching_lifted_dtgs;
							(*lifted_dtgs_)->getNodes(matching_lifted_dtgs, rhs_effect_fact);
							
							if (matching_lifted_dtgs.size() > 0)
							{
								dtgs_affected_by_rhs_effect.push_back(*lifted_dtgs_);
							}
						}
						
						for (std::vector<const LiftedDTG*>::const_iterator ci = dtgs_affected_by_rhs_effect.begin(); ci != dtgs_affected_by_rhs_effect.end(); ++ci)
						{
							const LiftedDTG* rhs_dtgs = *ci;
							for (std::vector<const LiftedDTG*>::const_iterator ci = dtgs_affected_by_lhs_effect.begin(); ci != dtgs_affected_by_lhs_effect.end(); ++ci)
							{
								const LiftedDTG* lhs_dtgs = *ci;
								/*if (rhs_dtgs == lhs_dtgs)
								{
									continue;
								}*/
								
								addTransition(*rhs_dtgs, *lhs_dtgs, *transition);
								addTransition(*lhs_dtgs, *rhs_dtgs, *transition);
							}
						}
					}
				}
			}
		}
	}
//	cacheDependencies();
}

CausalGraph::~CausalGraph()
{
	for (DTGtoDTG::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
	{
		delete (*ci).second;
	}
	
	for (DTGtoDTG::const_iterator ci = reverse_transitions_.begin(); ci != reverse_transitions_.end(); ci++)
	{
		delete (*ci).second;
	}
	
	for (TransitionToWeightMapping::const_iterator ci = arc_weights_.begin(); ci != arc_weights_.end(); ci++)
	{
		delete (*ci).second;
	}
/*
	if (cached_dependencies_ != NULL)
	{
		
		for (unsigned int i = 0; i < dtg_manager_->getManagableObjects().size(); ++i)
		{
			delete[] cached_dependencies_[i];
		}
		delete[] cached_dependencies_;
	}
*/
}

void CausalGraph::breakCycles(const std::vector<const GroundedAtom*>& goals)
{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
	std::cout << "[CausalGraph::breakCycles] " << goals.size() << std::endl;
#endif
/*
	// First of all we remove all the lifted DTGs the goals do not depend on.
	std::set<const LiftedDTG*> relevant_dtgs;

	for (std::vector<const GroundedAtom*>::const_iterator ci = goals.begin(); ci != goals.end(); ++ci)
	{
		const GroundedAtom* goal = *ci;
		std::vector<const HEURISTICS::VariableDomain*> variable_domains;
		
		for (unsigned int term_index = 0; term_index < goal->getAtom().getArity(); ++term_index)
		{
			HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
			vd->addObject(goal->getObject(term_index));
			variable_domains.push_back(vd);
		}
		
		HEURISTICS::Fact goal_fact(*predicate_manager_, goal->getAtom().getPredicate(), variable_domains);
		for (std::vector<LiftedDTG*>::const_iterator ci = all_lifted_dtgs_->begin(); ci != all_lifted_dtgs_->end(); ci++)
		{
			const LiftedDTG* dtg = *ci;
			
			std::vector<const MultiValuedValue*> found_nodes;
			dtg->getNodes(found_nodes, goal_fact);
			
			if (found_nodes.size() > 0)
			{
				relevant_dtgs.insert(dtg);
			}
		}
	}
	
	unsigned int relevant_set_size = 0;
	while (relevant_set_size != relevant_dtgs.size())
	{
		relevant_set_size = relevant_dtgs.size();
		std::set<const LiftedDTG*> to_add;
		for (std::set<const LiftedDTG*>::const_iterator ci = relevant_dtgs.begin(); ci != relevant_dtgs.end(); ++ci)
		{
			std::set<const LiftedDTG*>* depenencies = transitions_[*ci];
			if (depenencies != NULL)
			{
				to_add.insert(depenencies->begin(), depenencies->end());
			}
		}
		
		relevant_dtgs.insert(to_add.begin(), to_add.end());
	}

	// Any lifted DTG that is not in the relevant set can be removed.
	for (std::vector<LiftedDTG*>::const_iterator dtg_ci = all_lifted_dtgs_->begin(); dtg_ci != all_lifted_dtgs_->end(); dtg_ci++)
	{
		const LiftedDTG* dtg = *dtg_ci;
		if (relevant_dtgs.find(dtg) == relevant_dtgs.end())
		{
			std::vector<std::pair<const LiftedDTG*, const LiftedDTG*> > connections_to_severe;
			std::set<const LiftedDTG*>* to_facts = transitions_[dtg];
			std::set<const LiftedDTG*>* from_facts = reverse_transitions_[dtg];
			
			for (std::set<const LiftedDTG*>::const_iterator ci = to_facts->begin(); ci != to_facts->end(); ++ci)
			{
				connections_to_severe.push_back(std::make_pair(dtg, *ci));
			}
			
			for (std::set<const LiftedDTG*>::const_iterator ci = from_facts->begin(); ci != from_facts->end(); ++ci)
			{
				connections_to_severe.push_back(std::make_pair(*ci, dtg));
			}
			
			for (std::vector<std::pair<const LiftedDTG*, const LiftedDTG*> >::const_iterator ci = connections_to_severe.begin(); ci != connections_to_severe.end(); ++ci)
			{
				removeEdge(*(*ci).first, *(*ci).second);
			}
		}
	}
*/
	// Apply Tarjan's algorithm for finding the stronly connected components of the CG. Only in strongly connected components can cycles arrise.
	bool cg_contains_cycles = true;
	while (cg_contains_cycles)
	{
		cg_contains_cycles = false;
		std::vector<std::vector<const LiftedDTG*>* > strongly_connected_components;
		findStronglyConnectedComponents(strongly_connected_components);
		for (std::vector<std::vector<const LiftedDTG*>* >::const_iterator ci = strongly_connected_components.begin(); ci != strongly_connected_components.end(); ci++)
		{
			std::vector<const LiftedDTG*>* strongly_connected_component = *ci;
			
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
			std::cout << "[CausalGraph::breakCycles] Stronglyl connected component:" << std::endl;
			for (std::vector<const DomainTransitionGraph*>::const_iterator ci = strongly_connected_component->begin(); ci != strongly_connected_component->end(); ci++)
			{
				std::cout << ** ci << std::endl;
			}
#endif
			
			if (strongly_connected_component->size() < 2)
			{
				delete strongly_connected_component;
				continue;
			}
			cg_contains_cycles = true;
			
			// Remove all the transitions (v, v') for which v < v', where the value of a vertex is defined as the sum of the weight of all the transitions which are dependend on it.
			bool removedTransition = false;
			for (std::vector<const LiftedDTG*>::const_iterator ci = strongly_connected_component->begin(); ci != strongly_connected_component->end(); ci++)
			{
				const LiftedDTG* from_dtg = *ci;
				std::set<const LiftedDTG*>* connected_dtgs = transitions_[from_dtg];
				
				for (std::set<const LiftedDTG*>::const_iterator ci = connected_dtgs->begin(); ci != connected_dtgs->end(); ci++)
				{
					const LiftedDTG* to_dtg = *ci;
					// Make sure they are part of the same stronly connected component!
					if (std::find(strongly_connected_component->begin(), strongly_connected_component->end(), to_dtg) == strongly_connected_component->end()) continue;
					
					if (getWeight(*from_dtg) >= getWeight(*to_dtg) && from_dtg != to_dtg)
					{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
						std::cout << "Remove the transition from: " << *from_dtg << " to " << *to_dtg << std::endl;
#endif
						removeEdge(*from_dtg, *to_dtg);
						removedTransition = true;
						break;
					}
				}
				
				if (removedTransition) break;
			}
			
			delete strongly_connected_component;
		}
		
		unsigned int nr_transitions = 0;
		for (DTGtoDTG::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
		{
			nr_transitions += (*ci).second->size();
		}
	}
	
	// Also remove any dependencies on graphs themselves.
	for (DTGtoDTG::const_iterator transition_ci = transitions_.begin(); transition_ci != transitions_.end(); transition_ci++)
	{
		const LiftedDTG* graph = (*transition_ci).first;
		std::set<const LiftedDTG*>* dependencies = (*transition_ci).second;
		
		while (dependencies->count(graph) > 0)
		{
			removeEdge(*graph, *graph);
		}
	}

#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
	std::cout << "[CausalGraph::breakCycles] Remove inrelevant transitions!" << std::endl;
#endif
	// After breaking the cycles, update the DTG and remove all preconditions from the transitions which are no longer relevant.
	for (std::vector<LiftedDTG*>::const_iterator dtg_ci = all_lifted_dtgs_->begin(); dtg_ci != all_lifted_dtgs_->end(); dtg_ci++)
	{
		LiftedDTG* dtg = *dtg_ci;
		
		for (std::vector<MultiValuedValue*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ++ci)
		{
			MultiValuedValue* node = *ci;
			
			for (std::vector<const MultiValuedTransition*>::const_iterator ci = node->getTransitions().begin(); ci != node->getTransitions().end(); ++ci)
			{
				MultiValuedTransition* transition = const_cast<MultiValuedTransition*>(*ci);
				
				std::vector<const Atom*> preconditions;
				Utility::convertFormula(preconditions, &transition->getAction().getPrecondition());
				
				for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
				{
					const Atom* precondition = *ci;
					
					std::vector<const HEURISTICS::VariableDomain*> precondition_variable_domains;
					for (unsigned int term_index = 0; term_index < precondition->getPredicate().getArity(); ++term_index)
					{
						precondition_variable_domains.push_back(new HEURISTICS::VariableDomain(transition->getActionVariableDomain(transition->getAction().getActionVariable(*precondition->getTerms()[term_index])).getVariableDomain()));
					}
					HEURISTICS::Fact* precondition_fact = new HEURISTICS::Fact(*predicate_manager_, precondition->getPredicate(), precondition_variable_domains);
					
					//std::vector<const MultiValuedValue*> found_nodes;
					//dtg->getNodes(found_nodes, *precondition_fact);
					bool is_part_of_node = false;
					for (std::vector<HEURISTICS::Fact*>::const_iterator ci = node->getValues().begin(); ci != node->getValues().end(); ++ci)
					{
						if ((*ci)->canUnifyWith(*precondition_fact))
						{
							is_part_of_node = true;
							break;
						}
					}
					
					// Don't remove preconditions which are part of its own DTG.
					//if (found_nodes.size() > 0)
					if (is_part_of_node)
					{
						delete precondition_fact;
						continue;
					}
					
					bool is_connected = false;
					std::vector<const MultiValuedValue*> found_nodes;
					for (std::vector<LiftedDTG*>::const_iterator ci = all_lifted_dtgs_->begin(); ci != all_lifted_dtgs_->end(); ++ci)
					{
						LiftedDTG* rhs_dtg = *ci;
						if (rhs_dtg == dtg)
						{
							continue;
						}
						
						found_nodes.clear();
						rhs_dtg->getNodes(found_nodes, *precondition_fact);
						
						if (found_nodes.size() > 0 && containsDependency(*dtg, *rhs_dtg, false))
						{
							is_connected = true;
							break;
						}
					}
					
					if (!is_connected)
					{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
						std::cout << "Remove the precondition: ";
						precondition->print(std::cout, dtg->getBindings(), transition->getStepId());
						std::cout << ". Achieving transitions: " << nr_transitions << std::endl;
#endif
						transition->ignorePrecondition(*precondition);
					}
				}
				
				// Do the same for the effects.
				for (std::vector<const Atom*>::const_iterator ci = transition->getAction().getEffects().begin(); ci != transition->getAction().getEffects().end(); ++ci)
				{
					const Atom* effect = *ci;
					
					std::vector<const HEURISTICS::VariableDomain*> effect_variable_domains;
					for (unsigned int term_index = 0; term_index < effect->getPredicate().getArity(); ++term_index)
					{
						effect_variable_domains.push_back(new HEURISTICS::VariableDomain(transition->getActionVariableDomain(transition->getAction().getActionVariable(*effect->getTerms()[term_index])).getVariableDomain()));
					}
					HEURISTICS::Fact* effect_fact = new HEURISTICS::Fact(*predicate_manager_, effect->getPredicate(), effect_variable_domains);
					
					std::vector<const MultiValuedValue*> found_nodes;
					dtg->getNodes(found_nodes, *effect_fact);
					
					// Don't remove preconditions which are part of its own DTG.
					if (found_nodes.size() > 0)
					{
						continue;
					}
					
					bool is_connected = false;
					for (std::vector<LiftedDTG*>::const_iterator ci = all_lifted_dtgs_->begin(); ci != all_lifted_dtgs_->end(); ++ci)
					{
						LiftedDTG* rhs_dtg = *ci;
						if (rhs_dtg == dtg)
						{
							continue;
						}
						
						found_nodes.clear();
						rhs_dtg->getNodes(found_nodes, *effect_fact);
						
						if (found_nodes.size() > 0 && containsDependency(*dtg, *rhs_dtg, false))
						{
							is_connected = true;
							break;
						}
					}
					
					if (!is_connected)
					{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
						std::cout << "Remove the precondition: ";
						precondition->print(std::cout, dtg->getBindings(), transition->getStepId());
						std::cout << ". Achieving transitions: " << nr_transitions << std::endl;
#endif
						transition->ignoreEffect(*effect);
					}
				}
			}
		}
	}
	//cacheDependencies();
}

unsigned int CausalGraph::getWeight(const LiftedDTG& dtg) const
{
	unsigned int weight = 0;
	for (TransitionToWeightMapping::const_iterator ci = arc_weights_.begin(); ci != arc_weights_.end(); ci++)
	{
		if ((*ci).first.second == &dtg) weight += (*ci).second->size();
	}
	return weight;
}

void CausalGraph::removeEdge(const LiftedDTG& from_dtg, const LiftedDTG& to_dtg)
{
	transitions_[&from_dtg]->erase(&to_dtg);
	reverse_transitions_[&to_dtg]->erase(&from_dtg);
	arc_weights_[std::make_pair(&from_dtg, &to_dtg)]->clear();
}

/*
void CausalGraph::cacheDependencies()
{
	if (cached_dependencies_ == NULL)
	{
		cached_dependencies_ = new bool*[dtg_manager_->getManagableObjects().size()];
		for (unsigned int i = 0; i < dtg_manager_->getManagableObjects().size(); ++i)
		{
			cached_dependencies_[i] = new bool[dtg_manager_->getManagableObjects().size()];
		}
	}
	
	for (unsigned int i = 0; i < dtg_manager_->getManagableObjects().size(); ++i)
	{
		DTGtoDTG::const_iterator ci = transitions_.find(dtg_manager_->getManagableObjects()[i]);
		for (unsigned int j = 0; j < dtg_manager_->getManagableObjects().size(); ++j)
		{
			if (ci == transitions_.end()) 
			{
				cached_dependencies_[i][j] = false;
			}
			else
			{
				cached_dependencies_[i][j] = (*ci).second->count(dtg_manager_->getManagableObjects()[j]) == 1;
			}
		}
	}
}
*/
void CausalGraph::findStronglyConnectedComponents(std::vector<std::vector<const LiftedDTG*>* >& strongly_connected_components) const
{
	std::map<const LiftedDTG*, std::pair<unsigned int, unsigned int> > dtg_to_indexes;
	for (DTGtoDTG::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
	{
		dtg_to_indexes[(*ci).first] = std::make_pair(std::numeric_limits<unsigned int>::max(), std::numeric_limits<unsigned int>::max());
	}
	
	for (DTGtoDTG::const_iterator ci = reverse_transitions_.begin(); ci != reverse_transitions_.end(); ci++)
	{
		dtg_to_indexes[(*ci).first] = std::make_pair(std::numeric_limits<unsigned int>::max(), std::numeric_limits<unsigned int>::max());
	}
	
	std::vector<const LiftedDTG*> stack;
	unsigned int lowest_index = 0;
	for (std::map<const LiftedDTG*, std::pair<unsigned int, unsigned int> >::const_iterator ci = dtg_to_indexes.begin(); ci != dtg_to_indexes.end(); ci++)
	{
		const LiftedDTG* dtg = (*ci).first;
		unsigned int index = (*ci).second.first;

		if (index == std::numeric_limits<unsigned int>::max())
		{
			strongConnect(strongly_connected_components, stack, *dtg, dtg_to_indexes, lowest_index);
		}
	}
}
	
void CausalGraph::strongConnect(std::vector<std::vector<const LiftedDTG*>* >& strongly_connected_components, std::vector<const LiftedDTG*>& stack, const LiftedDTG& dtg, std::map<const LiftedDTG*, std::pair<unsigned int, unsigned int> >& indexes, unsigned int& lowest_index) const
{
	indexes[&dtg] = std::make_pair(lowest_index, lowest_index);
	lowest_index += 1;
	stack.push_back(&dtg);
	
	DTGtoDTG::const_iterator ci = transitions_.find(&dtg);
	if (ci != transitions_.end())
	{
		std::set<const LiftedDTG*>* transitions = (*transitions_.find(&dtg)).second;
		for (std::set<const LiftedDTG*>::const_iterator ci = transitions->begin(); ci != transitions->end(); ci++)
		{
			if (indexes[*ci].first == std::numeric_limits<unsigned int>::max())
			{
				strongConnect(strongly_connected_components, stack, **ci, indexes, lowest_index);
				indexes[&dtg] = std::make_pair(indexes[&dtg].first, std::min(indexes[&dtg].second, indexes[*ci].second));
			}
			else if (std::find(stack.begin(), stack.end(), *ci) != stack.end())
			{
				indexes[&dtg] = std::make_pair(indexes[&dtg].first, std::min(indexes[&dtg].second, indexes[*ci].first));
			}
		}
	}
	
	if (indexes[&dtg].first == indexes[&dtg].second)
	{
		std::vector<const LiftedDTG*>* new_connected_component = new std::vector<const LiftedDTG*>();
		const LiftedDTG* last_added_dtg = NULL;
		do
		{
			last_added_dtg = *(stack.end() - 1);
			stack.erase(stack.end() - 1);
			new_connected_component->push_back(last_added_dtg);
		} while (last_added_dtg != &dtg);
		strongly_connected_components.push_back(new_connected_component);
	}
}
/*
void CausalGraph::getDTGs(std::vector<const DomainTransitionGraph*>& dtgs, const StepID step_id, const Atom& fact, const Bindings& bindings) const
{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
//	std::cout << "[CausalGraph::getDTGs] Find the DTG for the fact: ";
//	fact.print(std::cout, bindings, step_id);
//	std::cout << "." << std::endl;
#endif
	std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_dtg_nodes;
	dtg_manager_->getDTGNodes(found_dtg_nodes, step_id, fact, bindings);
	
	for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_dtg_nodes.begin(); ci != found_dtg_nodes.end(); ci++)
	{
		const DomainTransitionGraphNode* matching_dtg_node = (*ci).first;
		const BoundedAtom* matching_fact = (*ci).second;
		
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
//		std::cout << "Found a matching node: " << *matching_dtg_node << std::endl;
#endif
		
		std::vector<const std::vector<const Object*>* > other_invariable_terms;
		matching_dtg_node->getBalancedVariableDomains(other_invariable_terms);
		
		// Check if the invariable of the DTG node is present in the fact we are looking at.
		bool contains_matching_variable_domain = other_invariable_terms.empty();
		for (std::vector<const std::vector<const Object*>*>::const_iterator ci = other_invariable_terms.begin(); ci != other_invariable_terms.end(); ci++)
		{
			if (matching_fact->containsVariableDomain(**ci, matching_dtg_node->getDTG().getBindings()) != std::numeric_limits<unsigned int>::max())
			{
				contains_matching_variable_domain = true;
				break;
			}
		}
		
		if (contains_matching_variable_domain)
		{
			dtgs.push_back(&matching_dtg_node->getDTG());
		}
	}
}
*/

bool CausalGraph::containsDependency(const SAS_Plus::LiftedDTG& from, const SAS_Plus::LiftedDTG& to, bool use_cache) const
{
	//if (use_cache)
	//{
	//	return cached_dependencies_[from.getId()][to.getId()];
	//}
	DTGtoDTG::const_iterator ci = transitions_.find(&from);
	if (ci == transitions_.end()) return false;
	return (*ci).second->count(&to) == 1;
}

void CausalGraph::getAllDependencies(std::vector<const LiftedDTG*>& dependencies, const LiftedDTG& lifted_dtg) const
{
// First of all we remove all the lifted DTGs the goals do not depend on.
	std::set<const LiftedDTG*> relevant_dtgs;
	relevant_dtgs.insert(&lifted_dtg);
	
	unsigned int relevant_set_size = 0;
	while (relevant_set_size != relevant_dtgs.size())
	{
		relevant_set_size = relevant_dtgs.size();
		std::set<const LiftedDTG*> to_add;
		for (std::set<const LiftedDTG*>::const_iterator ci = relevant_dtgs.begin(); ci != relevant_dtgs.end(); ++ci)
		{
			std::set<const LiftedDTG*>* depenencies = (*transitions_.find(*ci)).second;
			if (depenencies != NULL)
			{
				to_add.insert(depenencies->begin(), depenencies->end());
			}
		}
		
		relevant_dtgs.insert(to_add.begin(), to_add.end());
	}
	
	dependencies.insert(dependencies.end(), relevant_dtgs.begin(), relevant_dtgs.end());
}

const std::set<const LiftedDTG*>& CausalGraph::getAllDirectDependencies(const LiftedDTG& lifted_dtg) const
{
	return *(*transitions_.find(&lifted_dtg)).second;
}

void CausalGraph::getTransitionsFrom(std::vector<const LiftedDTG*>& transitions, const LiftedDTG& dtg) const
{
	DTGtoDTG::const_iterator ci = transitions_.find(&dtg);
	if (ci == transitions_.end())
	{
		return;
	}
	
	for (std::set<const LiftedDTG*>::const_iterator dtg_ci = (*ci).second->begin(); dtg_ci != (*ci).second->end(); dtg_ci++)
	{
		transitions.push_back(*dtg_ci);
	}
}

void CausalGraph::getTransitionsTo(std::vector<const LiftedDTG*>& transitions, const LiftedDTG& dtg) const
{
//	std::cout << dtg.getId() << std::endl;
	DTGtoDTG::const_iterator ci = reverse_transitions_.find(&dtg);
	if (ci == reverse_transitions_.end())
	{
		return;
	}
	
	for (std::set<const LiftedDTG*>::const_iterator dtg_ci = (*ci).second->begin(); dtg_ci != (*ci).second->end(); dtg_ci++)
	{
		transitions.push_back(*dtg_ci);
	}
}

void CausalGraph::addTransition(const LiftedDTG& from_dtg, const LiftedDTG& to_dtg, const MultiValuedTransition& transition)
{
	std::set<const LiftedDTG*>* dtg_set = transitions_[&from_dtg];
	dtg_set->insert(&to_dtg);
	std::set<const LiftedDTG*>* reverse_dtg_set = reverse_transitions_[&to_dtg];
	reverse_dtg_set->insert(&from_dtg);
/*
	std::set<const LiftedDTG*>* dtg_set = NULL;
	DTGtoDTG::iterator i = transitions_.find(&from_dtg);
	if (i == transitions_.end())
	{
		dtg_set = new std::set<const LiftedDTG*>();
		transitions_.insert(std::make_pair(&from_dtg, dtg_set));
	}
	else
	{
		dtg_set = (*i).second;
	}
	dtg_set->insert(&to_dtg);

	std::set<const LiftedDTG*>* reverse_dtg_set = NULL;
	DTGtoDTG::iterator ri = reverse_transitions_.find(&to_dtg);
	if (ri == reverse_transitions_.end())
	{
		reverse_dtg_set = new std::set<const LiftedDTG*>();
		reverse_transitions_.insert(std::make_pair(&to_dtg, reverse_dtg_set));
	}
	else
	{
		reverse_dtg_set = (*ri).second;
	}
	reverse_dtg_set->insert(&from_dtg);
*/
	
	TransitionToWeightMapping::iterator weight_i = arc_weights_.find(std::make_pair(&from_dtg, &to_dtg));
	std::set<const MultiValuedTransition*>* supported_transitions = (*weight_i).second;
/*	std::set<const MultiValuedTransition*>* supported_transitions = NULL;
	if (weight_i == arc_weights_.end())
	{
		supported_transitions = new std::set<const MultiValuedTransition*>();
		arc_weights_[std::make_pair(&from_dtg, &to_dtg)] = supported_transitions;
	}
	else
	{
		supported_transitions = (*weight_i).second;
	}*/
	supported_transitions->insert(&transition);
}

std::ostream& operator<<(std::ostream& os, const CausalGraph& cg)
{
	os << "Printing causal graph: " << cg.getAllLiftedDTGs().size() << std::endl;
	for (std::vector<LiftedDTG*>::const_iterator ci = cg.getAllLiftedDTGs().begin(); ci != cg.getAllLiftedDTGs().end(); ++ci)
	{
		const LiftedDTG* lifted_dtg = *ci;
		std::vector<const LiftedDTG*> connected_dtgs;
		cg.getTransitionsFrom(connected_dtgs, *lifted_dtg);
		
		for (std::vector<const LiftedDTG*>::const_iterator dtg_ci = connected_dtgs.begin(); dtg_ci != connected_dtgs.end(); dtg_ci++)
		{
			os << *lifted_dtg << " is connected to " << **dtg_ci << std::endl;
		}
	}
	
	return os;
}

};

void Graphviz::printToDot(const std::string& file_name, const SAS_Plus::CausalGraph& causal_graph)
{
	std::ofstream ofs;
	ofs.open(std::string(file_name + ".dot").c_str(), std::ios::out);
	
	ofs << "digraph {" << std::endl;

	// Print all DTG nodes.
	for (std::vector<SAS_Plus::LiftedDTG*>::const_iterator ci = causal_graph.getAllLiftedDTGs().begin(); ci != causal_graph.getAllLiftedDTGs().end(); ++ci)
	{
		const SAS_Plus::LiftedDTG* lifted_dtg = *ci;
		printToDot(ofs, *lifted_dtg->property_space_, *lifted_dtg);
	}

	// Create the edges.
	for (std::vector<SAS_Plus::LiftedDTG*>::const_iterator ci = causal_graph.getAllLiftedDTGs().begin(); ci != causal_graph.getAllLiftedDTGs().end(); ++ci)
	{
		std::vector<const SAS_Plus::LiftedDTG*> transitions;
		causal_graph.getTransitionsFrom(transitions, **ci);
		
		for (std::vector<const SAS_Plus::LiftedDTG*>::const_iterator transition_ci = transitions.begin(); transition_ci != transitions.end(); transition_ci++)
		{
			printToDot(ofs, *(*ci)->property_space_, **ci);
			ofs << " -> ";
			printToDot(ofs, *(*transition_ci)->property_space_, **transition_ci);
			ofs << std::endl;
		}
	}
	ofs << "}" << std::endl;
	ofs.close();
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::PropertySpace& property_space, const SAS_Plus::LiftedDTG& ltg)
{
	ofs << "\"";
	for (std::vector<SAS_Plus::PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ++ci)
	{
		SAS_Plus::PropertyState* property_state = *ci;
		ofs << "(";
		for (std::vector<const SAS_Plus::Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
		{
			const SAS_Plus::Property* property = *ci;
			
			ofs << property->getPredicate().getName() << "_" << property->getIndex();
			if (ci + 1 != property_state->getProperties().end())
			{
				ofs << ", ";
			}
		}
		ofs << ")\\n";
	}
	ofs << &ltg << "\"";
}

};
