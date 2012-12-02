#include "causal_graph.h"

#include "dtg_manager.h"
#include "dtg_node.h"
#include "transition.h"
#include "heuristics/dtg_reachability.h"
#include "fc_planner.h"

#include "../action_manager.h"
#include "../formula.h"
#include "../parser_utils.h"

//#define MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
#include <predicate_manager.h>

namespace MyPOP {
	
namespace SAS_Plus {

CausalGraph::CausalGraph(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::ActionManager& action_manager)
	: dtg_manager_(&dtg_manager), action_manager_(&action_manager), cached_dependencies_(NULL)
{
	/**
	 * A edge exists in the CG in the following cases:
	 * 1) A transition in one of the DTGs has a precondition which is linked to an external DTG.
	 * 2) A transition exists which affects the values of two or more DTGs.
	 * 
	 * In this system all actions are contained in DTGs (even if it only concerns a fact which can either be true or false).
	 */
	for (std::vector<DomainTransitionGraph*>::const_iterator dtg_ci = dtg_manager.getManagableObjects().begin(); dtg_ci != dtg_manager.getManagableObjects().end(); dtg_ci++)
	{
		const DomainTransitionGraph* dtg = *dtg_ci;
		
		// Go through all transitions and check the external dependencies.
		for (std::vector<DomainTransitionGraphNode*>::const_iterator dtg_node_ci = dtg->getNodes().begin(); dtg_node_ci != dtg->getNodes().end(); dtg_node_ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *dtg_node_ci;
			for (std::vector<Transition*>::const_iterator transition_ci = dtg_node->getTransitions().begin(); transition_ci != dtg_node->getTransitions().end(); transition_ci++)
			{
				const Transition* transition = *transition_ci;
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
				std::cout << "Process: " << *transition << "." << std::endl;
#endif
				
				// Only those preconditions which are contained by the transition are external preconditions.
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getAllPreconditions().begin(); ci != transition->getAllPreconditions().end(); ci++)
				{
					const Atom* precondition = (*ci).first;
					bool is_external_precondition = true;
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getFromNodePreconditions().begin(); ci != transition->getFromNodePreconditions().end(); ci++)
					{
						if ((*ci).first == precondition)
						{
							is_external_precondition = false;
							break;
						}
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
						std::cout << std::endl;
#endif
					}
					if (!is_external_precondition) continue;
					
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
					std::cout << "External precondition: ";
					precondition->print(std::cout, dtg_node->getDTG().getBindings(), transition->getStepId());
					std::cout << std::endl;
#endif
					
					std::vector<const DomainTransitionGraph*> matching_dtgs;
					getDTGs(matching_dtgs, transition->getStepId(), *precondition, dtg->getBindings());
					
					for (std::vector<const DomainTransitionGraph*>::const_iterator ci = matching_dtgs.begin(); ci != matching_dtgs.end(); ci++)
					{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
						std::cout << "DTG nr: " << dtg->getId() << " affects DTG nr: " << (*ci)->getId() << std::endl;
#endif
						
						addTransition(*dtg, **ci, *transition);
					}
				}
				
				// Check if there exists a pair of effects which affects more than two different DTGs.
				const std::vector<std::pair<const Atom*, InvariableIndex> >& effects = transition->getAllEffects();
				
				//for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator effect_ci_1 = effects.begin(); effect_ci_1 != effects.end(); effect_ci_1++)
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator effect_ci_1 = effects.begin(); effect_ci_1 != effects.end() - 1; effect_ci_1++)
				{
					const Atom& effect1 = *(*effect_ci_1).first;
					std::vector<const DomainTransitionGraph*> effect_dtgs_1;
					getDTGs(effect_dtgs_1, transition->getStepId(), effect1, dtg->getBindings());
					//for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator effect_ci_2 = effects.begin(); effect_ci_2 != effects.end(); effect_ci_2++)
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator effect_ci_2 = effect_ci_1 + 1; effect_ci_2 != effects.end(); effect_ci_2++)
					{
						const Atom& effect2 = *(*effect_ci_2).first;
						std::vector<const DomainTransitionGraph*> effect_dtgs_2;
						getDTGs(effect_dtgs_2, transition->getStepId(), effect2, dtg->getBindings());
						
						for (std::vector<const DomainTransitionGraph*>::const_iterator ci = effect_dtgs_1.begin(); ci != effect_dtgs_1.end(); ci++)
						{
							const DomainTransitionGraph* dtg_1 = *ci;
							for (std::vector<const DomainTransitionGraph*>::const_iterator ci = effect_dtgs_2.begin(); ci != effect_dtgs_2.end(); ci++)
							{
								const DomainTransitionGraph* dtg_2 = *ci;
								if (dtg_1 != dtg_2)
								{
									
									dtg_1->getNodes();
									// Make sure that the bindings of the effects are the same in the matching dtgs.
									std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > effect_1_nodes;
									dtg_1->getNodes(effect_1_nodes, transition->getStepId(), effect1, dtg->getBindings());
									
									std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > effect_2_nodes;
									dtg_2->getNodes(effect_2_nodes, transition->getStepId(), effect2, dtg->getBindings());
									
									bool dtg_nodes_match = false;
									for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = effect_1_nodes.begin(); ci != effect_1_nodes.end(); ++ci)
									{
										const BoundedAtom* bounded_atom1 = (*ci).second;
											
										for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = effect_2_nodes.begin(); ci != effect_2_nodes.end(); ++ci)
										{
											const BoundedAtom* bounded_atom2 = (*ci).second;
											
											// Check if the bindings on bounded atom and bounded atom 2 reflect those of the effects.
											for (unsigned int term1_index = 0; term1_index < effect1.getArity(); ++term1_index)
											{
												const std::vector<const Object*>& variable_domain1 = bounded_atom1->getVariableDomain(term1_index, dtg->getBindings());

												for (unsigned int term2_index = 0; term2_index < effect2.getArity(); ++term2_index)
												{
													const std::vector<const Object*>& variable_domain2 = bounded_atom2->getVariableDomain(term2_index, dtg->getBindings());
													if (effect1.getTerms()[term1_index] == effect2.getTerms()[term2_index])
													{
														// Make sure the terms overlap.
														bool terms_overlap = false;
														for (std::vector<const Object*>::const_iterator ci = variable_domain1.begin(); ci != variable_domain1.end(); ++ci)
														{
															const Object* object1 = *ci;
															
															if (std::find(variable_domain2.begin(), variable_domain2.end(), object1) != variable_domain2.end())
															{
																terms_overlap = true;
																break;
															}
														}
														
														// If the terms do not overlap than these effects do not affect two different dtgs.
														if (terms_overlap)
														{
															dtg_nodes_match = true;
															break;
														}
													}
												}
												if (dtg_nodes_match) break;
											}
											if (dtg_nodes_match) break;
										}
										if (dtg_nodes_match) break;
									}
									
									if (!dtg_nodes_match) continue;
									
									addTransition(*dtg_1, *dtg_2, *transition);
									addTransition(*dtg_2, *dtg_1, *transition);
									
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
									std::cout << "The effects: ";
									(*effect_ci_1).first->print(std::cout, dtg->getBindings(), transition->getStepId());
									std::cout << ", ";
									(*effect_ci_2).first->print(std::cout, dtg->getBindings(), transition->getStepId());
									std::cout << " affect dtgs: " << dtg_1->getId() << " and " << dtg_2->getId() << std::endl;
									std::cout << std::endl;
#endif
									
								}
							}
						}
					}
				}
			}
		}
	}
	cacheDependencies();
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
	
	if (cached_dependencies_ != NULL)
	{
		
		for (unsigned int i = 0; i < dtg_manager_->getManagableObjects().size(); ++i)
		{
			delete[] cached_dependencies_[i];
		}
		delete[] cached_dependencies_;
	}
}

void CausalGraph::breakCycles(const std::vector<const GroundedAtom*>& goals, const MyPOP::Bindings& bindings)
{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
	std::cout << "[CausalGraph::breakCycles] " << goals.size() << std::endl;
#endif
	// Apply Tarjan's algorithm for finding the stronly connected components of the CG. Only in strongly connected components can cycles arrise.
	bool cg_contains_cycles = true;
	while (cg_contains_cycles)
	{
		cg_contains_cycles = false;
		std::vector<std::vector<const DomainTransitionGraph*>* > strongly_connected_components;
		findStronglyConnectedComponents(strongly_connected_components);
		for (std::vector<std::vector<const DomainTransitionGraph*>* >::const_iterator ci = strongly_connected_components.begin(); ci != strongly_connected_components.end(); ci++)
		{
			std::vector<const DomainTransitionGraph*>* strongly_connected_component = *ci;
			
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
			for (std::vector<const DomainTransitionGraph*>::const_iterator ci = strongly_connected_component->begin(); ci != strongly_connected_component->end(); ci++)
			{
				const DomainTransitionGraph* from_dtg = *ci;
				std::set<const DomainTransitionGraph*>* connected_dtgs = transitions_[from_dtg];
				
				for (std::set<const DomainTransitionGraph*>::const_iterator ci = connected_dtgs->begin(); ci != connected_dtgs->end(); ci++)
				{
					const DomainTransitionGraph* to_dtg = *ci;
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
		const DomainTransitionGraph* graph = (*transition_ci).first;
		std::set<const DomainTransitionGraph*>* dependencies = (*transition_ci).second;
		
		while (dependencies->count(graph) > 0)
		{
			removeEdge(*graph, *graph);
		}
	}
	
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
	std::cout << "[CausalGraph::breakCycles] Remove inrelevant transitions!" << std::endl;
#endif
	// After breaking the cycles, update the DTG and remove all preconditions from the transitions which are no longer relevant.
	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		SAS_Plus::DomainTransitionGraph* dtg = *ci;
		for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
			std::cout << "Process: " << *dtg_node << std::endl;
#endif
			for (std::vector<SAS_Plus::Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
			{
				SAS_Plus::Transition* transition = *ci;
				std::vector<const Atom*> preconditions_to_remove;
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
				std::cout << "Process the transition: " << *transition << "." << std::endl;
#endif
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getAllPreconditions().begin(); ci != transition->getAllPreconditions().end(); ci++)
				{
					if (std::find(transition->getFromNodePreconditions().begin(), transition->getFromNodePreconditions().end(), *ci) != transition->getFromNodePreconditions().end()) continue;
					
					const Atom* precondition = (*ci).first;
					if (precondition->getPredicate().isStatic()) continue;
					
					std::vector<const MyPOP::SAS_Plus::DomainTransitionGraph*> invariant_dtgs;
					getDTGs(invariant_dtgs, transition->getStepId(), *precondition, dtg->getBindings());
					unsigned int nr_transitions = 0;
					
					// Check if this precondition is in any way connected after breaking the cycles.
					bool is_connected = false;
					for (std::vector<const MyPOP::SAS_Plus::DomainTransitionGraph*>::const_iterator ci = invariant_dtgs.begin(); ci != invariant_dtgs.end(); ci++)
					{
						const MyPOP::SAS_Plus::DomainTransitionGraph* rhs_dtg = *ci;
						std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > achieving_dtg_nodes;
						rhs_dtg->getNodes(achieving_dtg_nodes, transition->getStepId(), *precondition, dtg->getBindings());
						
						for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = achieving_dtg_nodes.begin(); ci != achieving_dtg_nodes.end(); ++ci)
						{
							const MyPOP::SAS_Plus::DomainTransitionGraphNode* rhs_dtg_node = (*ci).first;
							std::vector<const Transition*> achieving_transitions;
							rhs_dtg_node->getAchievingTransitions(achieving_transitions);
							
							nr_transitions += achieving_transitions.size();
						}
						
						if (constainsDependency(*dtg, *rhs_dtg, false))
						{
							is_connected = true;
							break;
						}
					}
					
					if (!is_connected && nr_transitions > 0)
					{
#ifdef MYPOP_SAS_PLUS_CAUSAL_GRAPH_COMMENTS
						std::cout << "Remove the precondition: ";
						precondition->print(std::cout, dtg->getBindings(), transition->getStepId());
						std::cout << ". Achieving transitions: " << nr_transitions << std::endl;
#endif
						preconditions_to_remove.push_back(precondition);
					}
				}
				
				for (std::vector<const Atom*>::const_iterator ci = preconditions_to_remove.begin(); ci != preconditions_to_remove.end(); ci++)
				{
					transition->removePrecondition(**ci);
				}
			}
		}
	}
	
	cacheDependencies();
}

unsigned int CausalGraph::getWeight(const DomainTransitionGraph& dtg) const
{
	unsigned int weight = 0;
	for (TransitionToWeightMapping::const_iterator ci = arc_weights_.begin(); ci != arc_weights_.end(); ci++)
	{
		if ((*ci).first.second == &dtg) weight += (*ci).second->size();
	}
	return weight;
}

void CausalGraph::removeEdge(const DomainTransitionGraph& from_dtg, const DomainTransitionGraph& to_dtg)
{
	transitions_[&from_dtg]->erase(&to_dtg);
	reverse_transitions_[&to_dtg]->erase(&from_dtg);
	arc_weights_[std::make_pair(&from_dtg, &to_dtg)]->clear();
}

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

void CausalGraph::findStronglyConnectedComponents(std::vector<std::vector<const DomainTransitionGraph*>* >& strongly_connected_components) const
{
	std::map<const DomainTransitionGraph*, std::pair<unsigned int, unsigned int> > dtg_to_indexes;
	for (DTGtoDTG::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
	{
		dtg_to_indexes[(*ci).first] = std::make_pair(std::numeric_limits<unsigned int>::max(), std::numeric_limits<unsigned int>::max());
	}
	
	for (DTGtoDTG::const_iterator ci = reverse_transitions_.begin(); ci != reverse_transitions_.end(); ci++)
	{
		dtg_to_indexes[(*ci).first] = std::make_pair(std::numeric_limits<unsigned int>::max(), std::numeric_limits<unsigned int>::max());
	}
	
	std::vector<const DomainTransitionGraph*> stack;
	unsigned int lowest_index = 0;
	for (std::map<const DomainTransitionGraph*, std::pair<unsigned int, unsigned int> >::const_iterator ci = dtg_to_indexes.begin(); ci != dtg_to_indexes.end(); ci++)
	{
		const DomainTransitionGraph* dtg = (*ci).first;
		unsigned int index = (*ci).second.first;

		if (index == std::numeric_limits<unsigned int>::max())
		{
			strongConnect(strongly_connected_components, stack, *dtg, dtg_to_indexes, lowest_index);
		}
	}
}
	
void CausalGraph::strongConnect(std::vector<std::vector<const DomainTransitionGraph*>* >& strongly_connected_components, std::vector<const DomainTransitionGraph*>& stack, const DomainTransitionGraph& dtg, std::map<const DomainTransitionGraph*, std::pair<unsigned int, unsigned int> >& indexes, unsigned int& lowest_index) const
{
	indexes[&dtg] = std::make_pair(lowest_index, lowest_index);
	lowest_index += 1;
	stack.push_back(&dtg);
	
	DTGtoDTG::const_iterator ci = transitions_.find(&dtg);
	if (ci != transitions_.end())
	{
		std::set<const DomainTransitionGraph*>* transitions = (*transitions_.find(&dtg)).second;
		for (std::set<const DomainTransitionGraph*>::const_iterator ci = transitions->begin(); ci != transitions->end(); ci++)
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
		std::vector<const DomainTransitionGraph*>* new_connected_component = new std::vector<const DomainTransitionGraph*>();
		const DomainTransitionGraph* last_added_dtg = NULL;
		do
		{
			last_added_dtg = *(stack.end() - 1);
			stack.erase(stack.end() - 1);
			new_connected_component->push_back(last_added_dtg);
		} while (last_added_dtg != &dtg);
		strongly_connected_components.push_back(new_connected_component);
	}
}

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

bool CausalGraph::constainsDependency(const SAS_Plus::DomainTransitionGraph& from, const SAS_Plus::DomainTransitionGraph& to, bool use_cache) const
{
	if (use_cache)
	{
		return cached_dependencies_[from.getId()][to.getId()];
	}
	DTGtoDTG::const_iterator ci = transitions_.find(&from);
	if (ci == transitions_.end()) return false;
	return (*ci).second->count(&to) == 1;
}

void CausalGraph::getTransitionsFrom(std::vector<const DomainTransitionGraph*>& transitions, const MyPOP::SAS_Plus::DomainTransitionGraph& dtg) const
{
	DTGtoDTG::const_iterator ci = transitions_.find(&dtg);
	if (ci == transitions_.end())
	{
		return;
	}
	
	for (std::set<const DomainTransitionGraph*>::const_iterator dtg_ci = (*ci).second->begin(); dtg_ci != (*ci).second->end(); dtg_ci++)
	{
		transitions.push_back(*dtg_ci);
	}
}

void CausalGraph::getTransitionsTo(std::vector<const DomainTransitionGraph*>& transitions, const MyPOP::SAS_Plus::DomainTransitionGraph& dtg) const
{
//	std::cout << dtg.getId() << std::endl;
	DTGtoDTG::const_iterator ci = reverse_transitions_.find(&dtg);
	if (ci == reverse_transitions_.end())
	{
		return;
	}
	
	for (std::set<const DomainTransitionGraph*>::const_iterator dtg_ci = (*ci).second->begin(); dtg_ci != (*ci).second->end(); dtg_ci++)
	{
		transitions.push_back(*dtg_ci);
	}
}

void CausalGraph::addTransition(const DomainTransitionGraph& from_dtg, const DomainTransitionGraph& to_dtg, const Transition& transition)
{
	std::set<const DomainTransitionGraph*>* dtg_set = NULL;
	DTGtoDTG::iterator i = transitions_.find(&from_dtg);
	if (i == transitions_.end())
	{
		dtg_set = new std::set<const DomainTransitionGraph*>();
		transitions_.insert(std::make_pair(&from_dtg, dtg_set));
	}
	else
	{
		dtg_set = (*i).second;
	}
	dtg_set->insert(&to_dtg);
	
	std::set<const DomainTransitionGraph*>* reverse_dtg_set = NULL;
	DTGtoDTG::iterator ri = reverse_transitions_.find(&to_dtg);
	if (ri == reverse_transitions_.end())
	{
		reverse_dtg_set = new std::set<const DomainTransitionGraph*>();
		reverse_transitions_.insert(std::make_pair(&to_dtg, reverse_dtg_set));
	}
	else
	{
		reverse_dtg_set = (*ri).second;
	}
	reverse_dtg_set->insert(&from_dtg);
	
	TransitionToWeightMapping::iterator weight_i = arc_weights_.find(std::make_pair(&from_dtg, &to_dtg));
	std::set<const Transition*>* supported_transitions = NULL;
	if (weight_i == arc_weights_.end())
	{
		supported_transitions = new std::set<const Transition*>();
		arc_weights_[std::make_pair(&from_dtg, &to_dtg)] = supported_transitions;
	}
	else
	{
		supported_transitions = (*weight_i).second;
	}
	supported_transitions->insert(&transition);
}

std::ostream& operator<<(std::ostream& os, const CausalGraph& cg)
{
	os << "Printing causal graph: " << cg.getDTGManager().getManagableObjects().size() << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = cg.getDTGManager().getManagableObjects().begin(); ci != cg.getDTGManager().getManagableObjects().end(); ci++)
	{
		const DomainTransitionGraph* dtg = *ci;
		assert (dtg != NULL);
//		std::cout << "Process: " << *dtg << std::endl;
		std::vector<const DomainTransitionGraph*> connected_dtgs;
		cg.getTransitionsFrom(connected_dtgs, *dtg);
		
		for (std::vector<const DomainTransitionGraph*>::const_iterator dtg_ci = connected_dtgs.begin(); dtg_ci != connected_dtgs.end(); dtg_ci++)
		{
			os << *dtg << " is connected to " << **dtg_ci << std::endl;
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
	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = causal_graph.getDTGManager().getManagableObjects().begin(); ci != causal_graph.getDTGManager().getManagableObjects().end(); ci++)
	{
		printPredicatesToDot(ofs, **ci);
	}

	// Create the edges.
	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = causal_graph.getDTGManager().getManagableObjects().begin(); ci != causal_graph.getDTGManager().getManagableObjects().end(); ci++)
	{
		std::vector<const SAS_Plus::DomainTransitionGraph*> transitions;
		causal_graph.getTransitionsFrom(transitions, **ci);
		
		for (std::vector<const SAS_Plus::DomainTransitionGraph*>::const_iterator transition_ci = transitions.begin(); transition_ci != transitions.end(); transition_ci++)
		{
			printPredicatesToDot(ofs, **ci);
			ofs << " -> ";
			printPredicatesToDot(ofs, **transition_ci);
			ofs << std::endl;
		}
	}
	ofs << "}" << std::endl;
	ofs.close();
}

};
