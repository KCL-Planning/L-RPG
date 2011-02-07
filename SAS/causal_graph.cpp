#include "causal_graph.h"

#include "dtg_manager.h"
#include "dtg_node.h"
#include "transition.h"

#include "../action_manager.h"
#include "../formula.h"
#include "../parser_utils.h"

namespace MyPOP {
	
namespace SAS_Plus {

CausalGraph::CausalGraph(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::ActionManager& action_manager)
	: dtg_manager_(&dtg_manager), action_manager_(&action_manager)
{
/*
	// First check if there are any actions which affects the separate state variables.
	for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
	{
		for (std::vector<const Atom*>::const_iterator effect_ci = (*ci)->getEffects().begin(); effect_ci != (*ci)->getEffects().end(); effect_ci++)
		{
			const Atom* effect = *effect_ci;
			
			// Check out which state variable this affects.
			//const std::vector<DomainTransitionGraph*>* effect_dtgs = dtg_manager.getDTGs(effect->getPredicate());
			const std::vector<DomainTransitionGraph*> effect_dtgs;
			dtg_manager.getDTGs(effect_dtgs,  effect->getPredicate());
			if (effect_dtgs == NULL)
			{
				continue;
			}
			std::vector<DomainTransitionGraph*> effect_dtgs_copy(*effect_dtgs);
			std::sort(effect_dtgs_copy.begin(), effect_dtgs_copy.end());
			
			for (std::vector<const Atom*>::const_iterator effect_to_ci = effect_ci + 1; effect_to_ci != (*ci)->getEffects().end(); effect_to_ci++)
			{
				const Atom* other_effect = *effect_to_ci;
				
				// Check if they affect a different state variable.
				const std::vector<DomainTransitionGraph*>* other_effect_dtgs = dtg_manager.getDTGs(other_effect->getPredicate());
				if (other_effect_dtgs == NULL)
				{
					continue;
				}
				std::vector<DomainTransitionGraph*> other_effect_dtgs_copy(*other_effect_dtgs);
				
				// Create a link between each state variable if they are not the same.
				std::vector<DomainTransitionGraph*> difference(other_effect_dtgs->size() + effect_dtgs->size());
				std::sort(other_effect_dtgs_copy.begin(), other_effect_dtgs_copy.end());
				std::vector<DomainTransitionGraph*>::const_iterator difference_end = std::set_symmetric_difference(effect_dtgs_copy.begin(), effect_dtgs_copy.end(), other_effect_dtgs_copy.begin(), other_effect_dtgs_copy.end(), difference.begin());
				
				// Create a edge between all the state variables in the above set.
				for (std::vector<DomainTransitionGraph*>::const_iterator diff_ci = difference.begin(); diff_ci != difference_end; diff_ci++)
				{
					for (std::vector<DomainTransitionGraph*>::const_iterator diff_ci2 = diff_ci; diff_ci2 != difference_end; diff_ci2++)
					{
						// Check if these DTGs are the same, if not we add an edge between these two.
						if (*diff_ci != *diff_ci2)
						{
							const DomainTransitionGraph& test_dtg = dtg_manager.getManagableObject((*diff_ci)->getId());
							assert (&test_dtg == *diff_ci);

							const DomainTransitionGraph& test_dtg2 = dtg_manager.getManagableObject((*diff_ci2)->getId());
							assert (&test_dtg2 == *diff_ci2);

							
//							std::cout << "Create an edge between " << (*diff_ci)->getId() << " and " << (*diff_ci2)->getId() << std::endl;
//							std::cout << "Create an edge between " << **diff_ci << " and " << **diff_ci2 << std::endl;
							addTransition(*diff_ci, *diff_ci2);
							addTransition(*diff_ci2, *diff_ci);
						}
					}
				}
			}
		}
	}
*/

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
			
			for (std::vector<const Transition*>::const_iterator transition_ci = dtg_node->getTransitions().begin(); transition_ci != dtg_node->getTransitions().end(); transition_ci++)
			{
				Transition* transition = const_cast<Transition*>(*transition_ci);
				const Action& action = transition->getStep()->getAction();
				std::vector<const Atom*> preconditions;
				MyPOP::Utility::convertFormula(preconditions, &action.getPrecondition());
				
				/**
				 * For all preconditions, check if they belong to this or an external DTG. In the latter case we add the precondition as an enabler of this transition
				 * and put an edge in the CG.
				 */
				for (std::vector<const Atom*>::const_iterator precondition_ci = preconditions.begin(); precondition_ci != preconditions.end(); precondition_ci++)
				{
					const Atom* precondition = *precondition_ci;
					//InvariableDTGIndex invariable_index = dtg_node->getIndex(transition->getStep()->getStepId(), *precondition);
					
					std::vector<const DomainTransitionGraph*> precondition_dtgs;
					dtg_manager.getDTGs(precondition_dtgs, transition->getStep()->getStepId(), *precondition, dtg->getBindings()); //, invariable_index);
					
					// If this precondition is not part of the same DTG add an edge.
					for (std::vector<const DomainTransitionGraph*>::const_iterator precondition_dtg_ci = precondition_dtgs.begin(); precondition_dtg_ci != precondition_dtgs.end(); precondition_dtg_ci++)
					{
						if (*precondition_dtg_ci != dtg)
						{
//							std::cout << "Create an edge between " << (*precondition_dtg_ci)->getId() << " and " << dtg->getId() << std::endl;
							//transitions_.insert(std::make_pair(*precondition_dtg_ci, dtg));
							addTransition(*precondition_dtg_ci, dtg);
							
							
							transition->addEnabler(BoundedAtom(transition->getStep()->getStepId(), **precondition_ci, NULL));
						}
					}
				}
			}
		}
	}
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

void CausalGraph::addTransition(const DomainTransitionGraph* from_dtg, const DomainTransitionGraph* to_dtg)
{
	std::set<const DomainTransitionGraph*>* dtg_set = NULL;
	DTGtoDTG::iterator i = transitions_.find(from_dtg);
	if (i == transitions_.end())
	{
		dtg_set = new std::set<const DomainTransitionGraph*>();
		transitions_.insert(std::make_pair(from_dtg, dtg_set));
	}
	else
	{
		dtg_set = (*i).second;
	}
	dtg_set->insert(to_dtg);
	
	std::set<const DomainTransitionGraph*>* reverse_dtg_set = NULL;
	DTGtoDTG::iterator ri = reverse_transitions_.find(to_dtg);
	if (ri == reverse_transitions_.end())
	{
		reverse_dtg_set = new std::set<const DomainTransitionGraph*>();
		reverse_transitions_.insert(std::make_pair(to_dtg, reverse_dtg_set));
	}
	else
	{
		reverse_dtg_set = (*ri).second;
	}
	
	reverse_dtg_set->insert(from_dtg);
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

void Graphviz::printToDot(const SAS_Plus::CausalGraph& causal_graph)
{
	std::ofstream ofs;
	ofs.open("causal_graph.dot", std::ios::out);
	
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
