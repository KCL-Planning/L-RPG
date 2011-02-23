#include "relaxed_reachability_analyst.h"

#include "../formula.h"
#include "dtg_manager.h"
#include <predicate_manager.h>
#include <term_manager.h>
#include <type_manager.h>
#include <parser_utils.h>
#include "transition.h"

namespace MyPOP {

namespace SAS_Plus {

RelaxedReachabilityAnalyst::RelaxedReachabilityAnalyst(const DomainTransitionGraphManager& dtg_manager)
	: dtg_manager_(&dtg_manager)
{
	
}
	
void RelaxedReachabilityAnalyst::performReachabilityAnalysis(const std::vector<const Atom*>& initial_facts)
{
	// Initialize the data structures.
	// Every node in every DTG is assigned a bitset which tells us which nodes are reachable.
	boost::dynamic_bitset<>* reachable_nodes[dtg_manager_->getManagableObjects().size()];
	unsigned int counter = 0;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		reachable_nodes[counter] = new boost::dynamic_bitset<>((*ci)->getNodes().size());
		++counter;
	}
	
	Type null_type("dummy_type", NULL);
	Object null_object(null_type, "dummy");
	
	std::set<DomainTransitionGraphNode*> open_list;
	std::set<std::pair<const DomainTransitionGraphNode*, const Transition*> > closed_list;
	
	std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const Atom*>*>* > supported_facts_per_dtg_node;
	
	// Mark all nodes which are true in the initial state.
	for (unsigned int dtg_nr = 0; dtg_nr < dtg_manager_->getManagableObjects().size(); dtg_nr++)
	{
		const DomainTransitionGraph* dtg = dtg_manager_->getManagableObjects()[dtg_nr];
		for (unsigned int node_nr = 0; node_nr < dtg->getNodes().size(); node_nr++)
		{
			DomainTransitionGraphNode* dtg_node = dtg->getNodes()[node_nr];
			
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
				for (std::vector<const Atom*>::const_iterator ci = atoms->begin(); ci != atoms->end(); ci++)
				{
					(*ci)->print(std::cout, dtg->getBindings(), Step::INITIAL_STEP);
					std::cout << ", ";
				}
			}
			std::cout << std::endl;
			
			supported_facts_per_dtg_node[dtg_node] = initial_facts_per_bounded_atom;
			
			// If more than a single initial fact has been found add the node to the open list so we know we need to work on it!
			if (initial_facts_per_bounded_atom->size() > 0)
			{
				open_list.insert(dtg_node);
			}
		}
	}
	
	/**
	 * Map the action variables to the bounded atom terms of the DTG nodes. The mapping is as follows:
	 * transition -> per indexed action variable (the position in the vector) we store a term of the dtg_node
	 * indexed by < the bounded atom, the index of the term of that bounded atom >.
	 */
	///std::map<const Transition*, std::vector<std::pair<InvariableIndex, InvariableIndex> > >* transition_to_dtg_node_bounded_atoms;
	
	/**
	 * Start the actual analysis!
	 */
	while (open_list.size() > 0)
	{
		DomainTransitionGraphNode* dtg_node = *open_list.begin();
		open_list.erase(open_list.begin());
		
		/**
		 * Check for each transition if the preconditions have been met.
		 */
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			if (closed_list.count(std::make_pair(dtg_node, transition)) != 0)
			{
				continue;
			}
			
			/**
			 * Instantiate the transition for every possible value of the dtg node.
			 */
			std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const Atom*>* >* >::iterator supporting_facts_i = supported_facts_per_dtg_node.find(dtg_node);
			
			if (supporting_facts_i == supported_facts_per_dtg_node.end())
			{
				continue;
			}

			std::vector<std::vector<const Atom*>* >* possible_values = (*supporting_facts_i).second;
			for (std::vector<std::vector<const Atom*>* >::const_iterator ci = possible_values->begin(); ci != possible_values->end(); ci++)
			{
				std::vector<const Atom*>* assignments_to_bounded_atoms = *ci;
				DomainTransitionGraphNode* new_from_dtg_node = new DomainTransitionGraphNode(*dtg_node, dtg_node->getDTG());
				DomainTransitionGraphNode* new_to_dtg_node = new DomainTransitionGraphNode(transition->getToNode(), dtg_node->getDTG());
				
				for (unsigned int i = 0; i < assignments_to_bounded_atoms->size(); i++)
				{
					std::cout << "[" << i << "] ";
					new_from_dtg_node->getAtoms()[i]->print(std::cout, new_from_dtg_node->getDTG().getBindings());
					std::cout << " -> ";
					(*assignments_to_bounded_atoms)[i]->print(std::cout, new_from_dtg_node->getDTG().getBindings(), Step::INITIAL_STEP);
					std::cout << std::endl;
					dtg_node->getDTG().getBindings().makeEqual(new_from_dtg_node->getAtoms()[i]->getAtom(), new_from_dtg_node->getAtoms()[i]->getId(), *(*assignments_to_bounded_atoms)[i], Step::INITIAL_STEP);
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
					bool precondition_is_supported = false;
					
					std::cout << "Check if the precondition: ";
					precondition->print(std::cout, new_from_dtg_node->getDTG().getBindings(), new_transition->getStep()->getStepId());
					std::cout << " is supported..." << std::endl;
					
					// Check which DTGs could support this precondition.
					std::vector<const DomainTransitionGraphNode*> supporting_nodes;
					dtg_manager_->getDTGNodes(supporting_nodes, new_transition->getStep()->getStepId(), *precondition, new_from_dtg_node->getDTG().getBindings());
					
					for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = supporting_nodes.begin(); ci != supporting_nodes.end(); ci++)
					{
						const DomainTransitionGraphNode* supporting_dtg_node = *ci;
						
						std::cout << "Supporting DTG Node: ";
						supporting_dtg_node->print(std::cout);
						std::cout << std::endl;
						
						// Check if any of these nodes can reach the looked for precondition.
						std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const Atom*>* >* >::iterator supporting_facts_i = supported_facts_per_dtg_node.find(supporting_dtg_node);
						
						if (supporting_facts_i == supported_facts_per_dtg_node.end())
						{
							std::cout << "The DTG node: ";
							supporting_dtg_node->print(std::cout);
							std::cout << " has no valid initial facts." << std::endl;
							continue;
						}
						
						// Check if any of the supported facts can be unified with the sought after precondition.
						std::vector<std::vector<const Atom*>* >* all_facts = (*supporting_facts_i).second;
						for (std::vector<std::vector<const Atom*>* >::const_iterator ci = all_facts->begin(); ci != all_facts->end(); ci++)
						{
							const std::vector<const Atom*>* possible_supported_fact = *ci;
							for (std::vector<const Atom*>::const_iterator ci = possible_supported_fact->begin(); ci != possible_supported_fact->end(); ci++)
							{
								const Atom* fact = *ci;
								
								std::cout << " ... compare against: ";
								fact->print(std::cout, dtg_node->getDTG().getBindings(), Step::INITIAL_STEP);
								std::cout << std::endl;
								
								if (dtg_node->getDTG().getBindings().canUnify(*fact, Step::INITIAL_STEP, *precondition, new_transition->getStep()->getStepId()))
								{
									precondition_is_supported = true;
									break;
								}
							}
							
							if (precondition_is_supported)
							{
								break;
							}
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

						transition_is_supported = false;
///						assert (false);
						break;
					}
				}
				
				/**
				* If a transition is supported, add it to the open list and update the reachable domains of all nodes
				* which can reach the from node of this transition.
				*/
				if (transition_is_supported)
				{
					std::cout << "The transition from ";
					new_transition->getFromNode().print(std::cout);
					std::cout << " to ";
					new_transition->getToNode().print(std::cout);
					std::cout << " is possible!!!" << std::endl;
				}
			}
		}
	}
}

};
	
};

