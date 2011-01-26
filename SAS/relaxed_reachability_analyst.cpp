#include "relaxed_reachability_analyst.h"

#include "../formula.h"
#include "dtg_manager.h"
#include <predicate_manager.h>
#include <term_manager.h>

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
	
	Object null_object;
	
	// Mark all nodes which are true in the initial state.
	for (unsigned int dtg_nr = 0; dtg_nr < dtg_manager_->getManagableObjects().size(); dtg_nr++)
	{
		const DomainTransitionGraph* dtg = dtg_manager_->getManagableObjects()[dtg_nr];
		for (unsigned int node_nr = 0; node_nr < dtg->getNodes().size(); node_nr++)
		{
			const DomainTransitionGraphNode* dtg_node = dtg->getNodes()[node_nr];
			
			// Check if all atoms can unify with the initial state. For each candidate we store the invariable object. This way we can check if
			// the candidate also matches the other atoms in this node with respect to the invariable.
			std::map<const Object*, std::vector<const Atom*>*> candidates;
			
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
						const Object* invariable = NULL;
						if (initial_fact->getArity() < dtg_node->getIndex(*bounded_atom))
						{
							invariable = &null_object;
						}
						else
						{
							invariable = initial_fact->getTerms()[dtg_node->getIndex(*bounded_atom)]->asObject();
						}
						
						std::map<const Object*, std::vector<const Atom*>*>::const_iterator matched_ci = candidates.find(invariable);
						
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
				std::vector<const Object*> to_remove;
				for (std::map<const Object*, std::vector<const Atom*>*>::const_iterator ci = candidates.begin(); ci != candidates.end(); ci++)
				{
					if ((*ci).second->size() != counter && (*ci).first != &null_object)
					{
//						std::cout << "Could not find: " << *(*ci).first << " " << (*ci).second->size() << " != " << counter << std::endl;
						to_remove.push_back((*ci).first);
					}
				}
				
				for (std::vector<const Object*>::const_iterator ci = to_remove.begin(); ci != to_remove.end(); ci++)
				{
					candidates.erase(*ci);
				}
				++counter;
			}
			
			std::cout << "Possible initial states for: ";
			dtg_node->print(std::cout);
			std::cout << std::endl;
			
			for (std::map<const Object*, std::vector<const Atom*>*>::const_iterator ci = candidates.begin(); ci != candidates.end(); ci++)
			{
				const std::vector<const Atom*>* atoms = (*ci).second;
				for (std::vector<const Atom*>::const_iterator ci = atoms->begin(); ci != atoms->end(); ci++)
				{
					(*ci)->print(std::cout, dtg->getBindings(), Step::INITIAL_STEP);
					std::cout << ", ";
				}
			}
			std::cout << std::endl;
		}
	}
}

};
	
};

