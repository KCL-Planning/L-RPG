#include "relaxed_reachability_analyst.h"

#include "../formula.h"
#include "dtg_manager.h"
#include <predicate_manager.h>
#include <term_manager.h>
#include <type_manager.h>
#include <parser_utils.h>
#include "transition.h"
#include "property_space.h"

namespace MyPOP {

namespace SAS_Plus {

RelaxedReachabilityAnalyst::RelaxedReachabilityAnalyst(const DomainTransitionGraphManager& dtg_manager)
	: dtg_manager_(&dtg_manager)
{
	
}
	
void RelaxedReachabilityAnalyst::performReachabilityAnalysis(const std::vector<const Atom*>& initial_facts)
{
/*	// Initialize the data structures.
	// Every node in every DTG is assigned a bitset which tells us which nodes are reachable.
	boost::dynamic_bitset<>* reachable_nodes[dtg_manager_->getManagableObjects().size()];
	unsigned int counter = 0;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		reachable_nodes[counter] = new boost::dynamic_bitset<>((*ci)->getNodes().size());
		++counter;
	}
*/
	
	Type null_type("dummy_type", NULL);
	Object null_object(null_type, "dummy");
	
	std::set<DomainTransitionGraphNode*> open_list;
	std::set<std::pair<const DomainTransitionGraphNode*, const Transition*> > closed_list;

	/**
	 * We conjecture that the only information we need per DTG node is the list of invariables which are supported. The values of
	 * the other variables should be derived from looking at the DTGs where these are invariable.
	 * This means we only need to keep track of a single list of values per DTG node and greatly improves the runtime of the analysis.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<const Object*>* > reachable_invariables_per_dtg_node;

	/**
	 * Per DTG node, map which DTGs are reachable.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >* > reachability_graph;
	
	/**
	 * The first step in the algorithm is to initialize the list of values of each DTG node with the initial state.
	 * Per atom in a DTG node we group all initial facts which can unify with it, than we take the intersection of
	 * the variable which matches with the atom's invariable and mark this set.
	 */
	for (unsigned int dtg_nr = 0; dtg_nr < dtg_manager_->getManagableObjects().size(); dtg_nr++)
	{
		const DomainTransitionGraph* dtg = dtg_manager_->getManagableObjects()[dtg_nr];
		for (unsigned int node_nr = 0; node_nr < dtg->getNodes().size(); node_nr++)
		{
			DomainTransitionGraphNode* dtg_node = dtg->getNodes()[node_nr];
			
			std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >* reachable_dtg_nodes = new std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >();
			reachability_graph[dtg_node] = reachable_dtg_nodes;
			
			std::vector<const Object*>* reachable_invariables = new std::vector<const Object*>();
			reachable_invariables_per_dtg_node[dtg_node] = reachable_invariables;
			
			// Check if all atoms can unify with the initial state. For each candidate we store the invariable object. This way we can check if
			// the candidate also matches the other atoms in this node with respect to the invariable.
			std::map<const Term*, std::vector<const Atom*>*> candidates;
			
			unsigned int counter = 1;
			for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
			{
				const BoundedAtom* bounded_atom = *ci;
				
				// Check if the given invariable is supported by the initial state.
				for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
				{
					const Atom* initial_fact = *ci;

					if (dtg->getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), *initial_fact, Step::INITIAL_STEP))
					{
						// Check which candidate is supported.
						const Term* invariable = NULL;
						if (dtg_node->getIndex(*bounded_atom) == NO_INVARIABLE_INDEX)
						{
							invariable = &null_object;
						}
						else
						{
							invariable = initial_fact->getTerms()[dtg_node->getIndex(*bounded_atom)];
						}
						
						std::map<const Term*, std::vector<const Atom*>*>::const_iterator matched_ci = candidates.find(invariable);
						
						if (matched_ci != candidates.end())
						{
							(*matched_ci).second->push_back(initial_fact);
						}
						else if (counter == 1)
						{
							std::vector<const Atom*>* candidate_list = new std::vector<const Atom*>();
							candidates[invariable] = candidate_list;
							candidate_list->push_back(initial_fact);
						}
					}
				}
				
				// Remove all invariables which could not unify with every atom in the dtg node.
				std::vector<const Term*> to_remove;
				for (std::map<const Term*, std::vector<const Atom*>*>::const_iterator ci = candidates.begin(); ci != candidates.end(); ci++)
				{
					if ((*ci).second->size() != counter && (*ci).first != &null_object)
					{
						std::cout << "Could not find: " << *(*ci).first << " " << (*ci).second->size() << " != " << counter << std::endl;
						to_remove.push_back((*ci).first);
					}
				}
				
				for (std::vector<const Term*>::const_iterator ci = to_remove.begin(); ci != to_remove.end(); ci++)
				{
					candidates.erase(*ci);
				}
				++counter;
			}
			
			std::cout << "Possible initial states for: ";
			dtg_node->print(std::cout);
			std::cout << std::endl;

			// Store all found matching initial facts per dtg_node.
			std::vector<std::vector<const Atom*>* >* initial_facts_per_bounded_atom = new std::vector<std::vector<const Atom*>* >();
			for (std::map<const Term*, std::vector<const Atom*>*>::const_iterator ci = candidates.begin(); ci != candidates.end(); ci++)
			{
				std::vector<const Atom*>* atoms = (*ci).second;
				initial_facts_per_bounded_atom->push_back(atoms);
				
				/**
				 * Static nodes are stored in a single vector.
				 */
				if (atoms->size() != dtg_node->getAtoms().size())
				{
					for (unsigned int i = 0; i < atoms->size(); i++)
					{
						const Atom* atom = (*atoms)[i];
						std::cout << "* ";
						atom->print(std::cout, dtg->getBindings(), Step::INITIAL_STEP);
						std::cout << std::endl;
					}
				}
				
				for (unsigned int i = 0; i < atoms->size(); i++)
				{
					const Atom* atom = (*atoms)[i];
					atom->print(std::cout, dtg->getBindings(), Step::INITIAL_STEP);
					
					if (atom->getPredicate().isStatic())
					{
						continue;
					}
					
					const BoundedAtom* bounded_atom = dtg_node->getAtoms()[i];
					if (dtg_node->getDTG().isValidPredicateIndex(bounded_atom->getAtom().getPredicate(), dtg_node->getIndex(*bounded_atom)))
					{
						std::cout << "[" << dtg_node->getIndex(*bounded_atom) << "]";
						const Term* invariable_term = bounded_atom->getAtom().getTerms()[dtg_node->getIndex(*bounded_atom)];
						const std::vector<const Object*>& domain = invariable_term->getDomain(bounded_atom->getId(), dtg->getBindings());
						
						for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
						{
							const Object* object_to_add = *ci;
							bool object_already_present = false;
							for (std::vector<const Object*>::const_iterator ci = reachable_invariables->begin(); ci != reachable_invariables->end(); ci++)
							{
								const Object* existing_object = *ci;
								if (object_to_add == existing_object)
								{
									object_already_present = true;
									break;
								}
							}
							
							if (!object_already_present)
							{
								reachable_invariables->push_back(object_to_add);
							}
						}
					}
					else
					{
						std::cout << "[NO INVARIABLE!]";
					}
					std::cout << ", ";
				}
			}
			std::cout << std::endl;
			
			// If more than a single initial fact has been found add the node to the open list so we know we need to work on it!
			if (initial_facts_per_bounded_atom->size() > 0)
			{
				open_list.insert(dtg_node);
			}
		}
	}
	
	/**
	 * Store a copy of the objects true in the intial state for printing out the facts that can be achieved.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<const Object*>* > reachable_invariables_in_initial_state(reachable_invariables_per_dtg_node);
	
	/**
	 * After initialising the reachable invariables per DTG node, we now move on to the actual analysis. Per marked DTG node 
	 * he following operations are performed:
	 *
	 * 1) Forall transitions \in DTG node:
	 * 1.1) Copy the transition and bind the variables linked to the invariable to the values known to be true. This will initially
	 * only be the values true in the initial state.
	 * 1.2) Forall preconditions:
	 * 1.2.1) If the precondition is static, check if it is true in the initial state.
	 * 1.2.2) Else find the DTG node(s) the precondition is supported by. Then check if the invariable of the found DTG node(s) can be
	 * unified with the precondition. If so the precondition is supported.
	 * 1.3) If the transition is supported, add the invariable of the from node to the to node's list of invariables and mark in the
	 * from node all nodes reachable from the to node, including the to node itself. Mark the to node.
	 * 1.4) Propagate all reachable nodes until the graph stabilises.
	 *
	 * This process is repeated until there are no more marked nodes.
	 */
	std::set<DomainTransitionGraphNode*> achieved_nodes;
	std::vector<DomainTransitionGraphNode*> nodes_with_unsatisfied_transitions;
	unsigned int iteration = 0;
	while (open_list.size() > 0)
	{
		DomainTransitionGraphNode* from_dtg_node = *open_list.begin();
		open_list.erase(open_list.begin());
		
		/**
		 * Check for each transition if the preconditions have been met.
		 */
		bool all_transitions_processed = true;
		for (std::vector<const Transition*>::const_iterator ci = from_dtg_node->getTransitions().begin(); ci != from_dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			
			if (closed_list.count(std::make_pair(from_dtg_node, transition)) != 0)
			{
				continue;
			}
			
			// Sanity test.
			unsigned int from_transitions_number = from_dtg_node->getTransitions().size();
			
			std::cout << "Test transition from: " << transition->getFromNode() << " to " << transition->getToNode() << "; Action: " << transition->getStep()->getAction() << std::endl;
			
			/**
			 * Instantiate the transition for every possible value of the dtg node.
			 */
			std::map<const DomainTransitionGraphNode*, std::vector<const Object*>* >::iterator supporting_facts_i = reachable_invariables_per_dtg_node.find(from_dtg_node);;
			
			if (supporting_facts_i == reachable_invariables_per_dtg_node.end())
			{
				all_transitions_processed = false;
				continue;
			}

			std::vector<const Object*>* from_node_invariables = (*supporting_facts_i).second;
			DomainTransitionGraphNode* new_from_dtg_node = new DomainTransitionGraphNode(*from_dtg_node, from_dtg_node->getDTG());
			DomainTransitionGraphNode* new_to_dtg_node = new DomainTransitionGraphNode(transition->getToNode(), from_dtg_node->getDTG());
			
			/**
			 * Make the invariables of this node equal to the invariables which are found to be true.
			 */
			for (std::vector<BoundedAtom*>::const_iterator ci = new_from_dtg_node->getAtoms().begin(); ci != new_from_dtg_node->getAtoms().end(); ci++)
			{
				const BoundedAtom* bounded_atom = *ci;
				
				// Make sure this bounded atom is part of te balanced set of the DTG and not an external atom which has been merged.
				if (bounded_atom->getProperty() == NULL)
				{
					continue;
				}
				
				if (!new_from_dtg_node->getDTG().containsPropertySpace(bounded_atom->getProperty()->getPropertyState().getPropertySpace()))
				{
					continue;
				}
				
				InvariableIndex index = new_from_dtg_node->getIndex(*bounded_atom);
				
				std::cout << "Bind the " << index << "th term of the from node to: {";
				
				for (std::vector<const Object*>::const_iterator ci = from_node_invariables->begin(); ci != from_node_invariables->end(); ci++)
				{
					std::cout << **ci << ", ";
				}
				std::cout << "}" << std::endl;
				
				if (index == NO_INVARIABLE_INDEX)
				{
					continue;
				}
				
				bounded_atom->getAtom().getTerms()[index]->makeDomainEqualTo(bounded_atom->getId(), *from_node_invariables, from_dtg_node->getDTG().getBindings());
			}

			std::cout << "Test transition from: " << *new_from_dtg_node << " to " << *new_to_dtg_node << "; Action: " << transition->getStep()->getAction() << std::endl;
			
			// Make the actual transition.
			std::vector<BoundedAtom>* enabler_dummy = new std::vector<BoundedAtom>();
			Transition* new_transition = Transition::createTransition(*enabler_dummy, transition->getStep()->getAction(), *new_from_dtg_node, *new_to_dtg_node, initial_facts);
			
			assert (new_transition != NULL);

			bool transition_is_supported = true;
			std::vector<std::pair<const Atom*, InvariableIndex> > preconditions = new_transition->getAllPreconditions();

			for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = (*ci).first;
				InvariableIndex invariable_precondition_index = (*ci).second;
				bool precondition_is_supported = false;
				
				std::cout << "Check if the precondition: ";
				precondition->print(std::cout, new_from_dtg_node->getDTG().getBindings(), new_transition->getStep()->getStepId());
				std::cout << "[" << invariable_precondition_index << "] is supported..." << std::endl;
				
				if (precondition->getPredicate().isStatic())
				{
					// Check if the precondition is true in the initial state.
					for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
					{
						const Atom* initial_fact = *ci;
						if (from_dtg_node->getDTG().getBindings().canUnify(*precondition, new_transition->getStep()->getStepId(), *initial_fact, Step::INITIAL_STEP))
						{
							precondition_is_supported = true;
							break;
						}
					}
				}
				
				else
				{
					// Check which DTGs could support this precondition.
					std::vector<const DomainTransitionGraphNode*> supporting_nodes;
					dtg_manager_->getDTGNodes(supporting_nodes, new_transition->getStep()->getStepId(), *precondition, new_from_dtg_node->getDTG().getBindings());
					
					for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = supporting_nodes.begin(); ci != supporting_nodes.end(); ci++)
					{
						const DomainTransitionGraphNode* supporting_dtg_node = *ci;
						
						// Figure out which bounded atom matched.
						InvariableIndex invariable_supporting_index = NO_INVARIABLE_INDEX;
						for (std::vector<BoundedAtom*>::const_iterator ci = supporting_dtg_node->getAtoms().begin(); ci != supporting_dtg_node->getAtoms().end(); ci++)
						{
							const BoundedAtom* bounded_atom = *ci;
							if (new_from_dtg_node->getDTG().getBindings().canUnify(*precondition, new_transition->getStep()->getStepId(), bounded_atom->getAtom(), bounded_atom->getId(), &supporting_dtg_node->getDTG().getBindings()))
							{
								assert (invariable_supporting_index == NO_INVARIABLE_INDEX);
								invariable_supporting_index = supporting_dtg_node->getIndex(*bounded_atom);
							}
						}
						
						assert (invariable_supporting_index != NO_INVARIABLE_INDEX);
						
						std::cout << "Supporting DTG Node: ";
						supporting_dtg_node->print(std::cout);
						std::cout << std::endl;
						
						// Check if any of these nodes can reach the looked for precondition.
						std::map<const DomainTransitionGraphNode*, std::vector<const Object*>* >::iterator supporting_facts_i = reachable_invariables_per_dtg_node.find(supporting_dtg_node);
			
						if (supporting_facts_i == reachable_invariables_per_dtg_node.end())
						{
							std::cout << "The DTG node: ";
							supporting_dtg_node->print(std::cout);
							std::cout << " has no valid initial facts." << std::endl;
							continue;
						}
						
						// Check if any of the supported facts can be unified with the sought after precondition.
						std::vector<const Object*>* valid_invariables = (*supporting_facts_i).second;

						assert (precondition->getTerms()[invariable_supporting_index] != NULL);
						assert (valid_invariables != NULL);
						if (precondition->getTerms()[invariable_supporting_index]->containsAtLeastOneOf(*valid_invariables, new_transition->getStep()->getStepId(), from_dtg_node->getDTG().getBindings()))
						{
							precondition_is_supported = true;
							break;
						}
					}
					
					if (!precondition_is_supported)
					{
						std::cout << "The transition from ";
						new_from_dtg_node->print(std::cout);
						std::cout << " to ";
						new_to_dtg_node->print(std::cout);
						std::cout << " is NOT possible because the precondition: ";
						precondition->print(std::cout, new_from_dtg_node->getDTG().getBindings(), new_transition->getStep()->getStepId());
						std::cout << " is not supported!!!" << std::endl;

						all_transitions_processed = false;
						transition_is_supported = false;
						break;
					}
				}
			}
			
			/**
			 * If a transition is supported, add it to the open list and update the reachable domains of all nodes
			 * which can reach the from node of this transition.
			 */
			if (transition_is_supported)
			{
				std::cout << "[" << iteration << "] The transition from ";
				new_transition->getFromNode().print(std::cout);
				std::cout << " to ";
				new_transition->getToNode().print(std::cout);
				std::cout << " is possible!!!" << std::endl;
				
				closed_list.insert(std::make_pair(from_dtg_node, transition));
				achieved_nodes.insert(&transition->getToNode());
				
				std::vector<const Object*>* to_node_invariables = reachable_invariables_per_dtg_node[&transition->getToNode()];
				
				for (std::vector<const Object*>::const_iterator ci = from_node_invariables->begin(); ci != from_node_invariables->end(); ci++)
				{
					const Object* from_node_invariable = *ci;
					bool exists = false;
					for (std::vector<const Object*>::const_iterator ci = to_node_invariables->begin(); ci != to_node_invariables->end(); ci++)
					{
						const Object* to_node_invariable = *ci;
						if (from_node_invariable == to_node_invariable)
						{
							exists = true;
							break;
						}
					}
					
					if (!exists)
					{
						to_node_invariables->push_back(from_node_invariable);
					}
				}
				
				// TODO: Values below need to be propagated.
				std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >* reachable_nodes = reachability_graph[from_dtg_node];
				reachable_nodes->push_back(std::make_pair(&transition->getToNode(), transition));
			}
			
			assert (from_transitions_number == from_dtg_node->getTransitions().size());
		}
		
		if (!all_transitions_processed)
		{
			nodes_with_unsatisfied_transitions.push_back(from_dtg_node);
		}
		
		/**
		 * If all nodes in the open list have been processed, we add the newly marked node.
		 */
		if (open_list.empty())
		{
			if (achieved_nodes.empty())
			{
				break;
			}
			
			open_list.insert(achieved_nodes.begin(), achieved_nodes.end());
			open_list.insert(nodes_with_unsatisfied_transitions.begin(), nodes_with_unsatisfied_transitions.end());
			achieved_nodes.clear();
			++iteration;
		}
	}
	
	/**
	 * After running the reachabiliy analysis, we have recorded for each DTG node which transitions are possible and which
	 * other DTG nodes can be reached, but only for those for which a direct edge exists. To determine which nodes can be
	 * reached we propagate this information so every DTG node knows which other nodes it can reach.
	 */
	bool graph_has_changed = true;
	while (graph_has_changed)
	{
		graph_has_changed = false;
		
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
		{
			const DomainTransitionGraph* dtg = *ci;
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
			{
				DomainTransitionGraphNode* dtg_node = *ci;
				std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> > new_reachable_nodes;
				
				std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >* reachable_nodes = reachability_graph[dtg_node];
				for (std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >::const_iterator ci = reachable_nodes->begin(); ci != reachable_nodes->end(); ci++)
				{
					const DomainTransitionGraphNode* reachable_dtg_node = (*ci).first;
					
					std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >* indirect_reachable_nodes = reachability_graph[reachable_dtg_node];
					
					// Merge both sets.
					for (std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >::const_iterator ci = indirect_reachable_nodes->begin(); ci != indirect_reachable_nodes->end(); ci++)
					{
						const DomainTransitionGraphNode* indirect_reachable_node = (*ci).first;
						const Transition* indirect_reachable_node_transition = (*ci).second;
						
						// Check if this already exists.
						bool exists = false;
						for (std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >::const_iterator ci = reachable_nodes->begin(); ci != reachable_nodes->end(); ci++)
						{
							if ((*ci).first == indirect_reachable_node && (*ci).second == indirect_reachable_node_transition)
							{
								exists = true;
								break;
							}
						}
						
						if (!exists)
						{
							new_reachable_nodes.push_back(std::make_pair(indirect_reachable_node, indirect_reachable_node_transition));
						}
					}
				}
				
				if (new_reachable_nodes.size() > 0)
				{
					graph_has_changed = true;
					reachable_nodes->insert(reachable_nodes->end(), new_reachable_nodes.begin(), new_reachable_nodes.end());
				}
			}
		}
	}
	
	/**
	 * Print all the reachable facts.
	 */
	for (std::map<const DomainTransitionGraphNode*, std::vector<const Object*>* >::const_iterator ci = reachable_invariables_in_initial_state.begin(); ci != reachable_invariables_in_initial_state.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		std::vector<const Object*>* invariables = (*ci).second;
		std::cout << "Process: ";
		dtg_node->print(std::cout);
		std::cout << std::endl;
		
		std::cout << "True in the initial state for DTG node: {";
		for (std::vector<const Object*>::const_iterator ci = invariables->begin(); ci != invariables->end(); ci++)
		{
			std::cout << **ci;
			if (ci != invariables->end() - 1)
			{
				std::cout << ", ";
			}
		}
		std::cout << "}" << std::endl;
		
		std::cout << "Nodes reachable from here: " << std::endl;;
		std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >* reachable_nodes = reachability_graph[dtg_node];
		for (std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >::const_iterator ci = reachable_nodes->begin(); ci != reachable_nodes->end(); ci++)
		{
			const DomainTransitionGraphNode* reachable_dtg_node = (*ci).first;
			const Transition* transition = (*ci).second;
			std::cout << "* ";
			reachable_dtg_node->print(std::cout);
			std::cout << "; Action: ";
			transition->getStep()->getAction().print(std::cout, reachable_dtg_node->getDTG().getBindings(), transition->getStep()->getStepId());
			std::cout << std::endl;
		}
	}
}

};
	
};

