#include "reachability.h"

#include <vector>
#include <queue>

#include "dtg_manager.h"
#include "dtg_node.h"
#include "transition.h"
#include "landmarks.h"

#include "../parser_utils.h"
#include "../formula.h"
#include "../term_manager.h"
#include "../predicate_manager.h"

namespace MyPOP {
	
namespace SAS_Plus {



Pathfinder::Pathfinder(const DomainTransitionGraph& dtg)
	: dtg_(&dtg)
{

}

bool Pathfinder::isReachable(const DomainTransitionGraphNode& from, const DomainTransitionGraphNode& to) const
{
//	std::cout << "Find a path from " << from << " to " << to << std::endl;
	std::vector<const DomainTransitionGraphNode*> open_list;
	open_list.push_back(&from);

	std::set<const DomainTransitionGraphNode*> closed_list(ignore_list_);

	while (!open_list.empty())
	{
		const DomainTransitionGraphNode* dtg_node = open_list.back();
		open_list.pop_back();

		// Check if this dtg node has already been processed.
		if (closed_list.find(dtg_node) != closed_list.end())
		{
			// If it has, continue to the next node.
			continue;
		}

		// Add this node to the closed list.
		closed_list.insert(dtg_node);

		// Check if this node is the node we are looking for.
		if (dtg_node == &to)
		{
			return true;
		}

		// Add all the end points of all possible transitions to the open list.
		const std::vector<const Transition*>& transitions = dtg_node->getTransitions();
		for (std::vector<const Transition*>::const_iterator ci = transitions.begin(); ci != transitions.end(); ci++)
		{
			const Transition* transition = *ci;
			open_list.push_back(&transition->getToNode());
		}
	}

	// The node we were looking for was not found.
	return false;
}

bool Pathfinder::getPath(std::vector<const DomainTransitionGraphNode*>& path, const std::vector<const DomainTransitionGraphNode*>& from, const std::vector<const DomainTransitionGraphNode*>& to) const
{
	// Fill the priority queue with the from nodes and assign them a value of 0.
	std::priority_queue<const PathfinderNode*, std::vector<const PathfinderNode*>, PathfinderNodeComparer> open_list;
	for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = from.begin(); ci != from.end(); ci++)
	{
		open_list.push(new PathfinderNode(NULL, **ci));
	}

	std::set<const DomainTransitionGraphNode*> closed_list(ignore_list_);

	while (!open_list.empty())
	{
		const PathfinderNode* node = open_list.top();
		open_list.pop();
		const DomainTransitionGraphNode* dtg_node = node->node_;

		// Check if this dtg node has already been processed.
		if (closed_list.find(dtg_node) != closed_list.end())
		{
			// If it has, continue to the next node.
			continue;
		}

		// Add this node to the closed list.
		closed_list.insert(dtg_node);

		// Check if this is one of the nodes we have been looking for.
		for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = to.begin(); ci != to.end(); ci++)
		{
			if (*ci == dtg_node)
			{
				// Reconstruct the path.
				const PathfinderNode* current_node = node;
				while (current_node != NULL)
				{
					path.push_back(current_node->node_);
					current_node = current_node->parent_;
				}
				std::reverse(path.begin(), path.end());
				return true;
			}
		}

		// Add all the end points of all possible transitions to the open list.
		const std::vector<const Transition*>& transitions = dtg_node->getTransitions();
		for (std::vector<const Transition*>::const_iterator ci = transitions.begin(); ci != transitions.end(); ci++)
		{
/*			const Transition* transition = *ci;
			
			// Check if the predicates index of both nodes are equal.
			int from_predicate_index = dtg_node->getDTG().getPredicateInvariableIndex(dtg_node->getAtom().getPredicate());
			int to_predicate_index = transition->getToNode().getDTG().getPredicateInvariableIndex(transition->getToNode().getAtom().getPredicate());
			//std::cout << "Check: " << transition->getFromNode() << " to " << transition->getToNode() << std::endl;
			
			if (!dtg_node->getDTG().getBindings().canUnify(*dtg_node->getAtom().getTerms()[from_predicate_index], dtg_node->getId(), *transition->getToNode().getAtom().getTerms()[to_predicate_index], transition->getToNode().getId()))
			{
				continue;
			}
	
			open_list.push(new PathfinderNode(node, transition->getToNode()));
*/
		}
	}
	return false;
}
	
void Pathfinder::ignoreNode(const DomainTransitionGraphNode& dtg_node)
{
	ignore_list_.insert(&dtg_node);
}
	
void Pathfinder::clearIgnoreList()
{
	ignore_list_.clear();
}

/*************************
 * The ReachableDTGNode class
 *************************/

ReachableDTGNode::ReachableDTGNode(MyPOP::SAS_Plus::ReachabilityAnalist& reachability_analist, const MyPOP::SAS_Plus::DomainTransitionGraphNode& dtg_node)
	: reachability_analist_(&reachability_analist), dtg_node_(&dtg_node)
{

}

ReachableDTGNode::ReachableDTGNode(ReachabilityAnalist& reachability_analist, const MyPOP::SAS_Plus::DomainTransitionGraphNode& dtg_node, const std::vector< const std::vector< std::pair<const MyPOP::SAS_Plus::BoundedAtom*, InvariableIndex> >* >& init_assignments)
	: reachability_analist_(&reachability_analist), dtg_node_(&dtg_node)
{
	/**
	 * Assert that all atoms in the dtg node are assigned a value.
	 */
	for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >::const_iterator ci = init_assignments.begin(); ci != init_assignments.end(); ci++)
	{
		const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* assignments = (*ci);
		if (assignments->size() != dtg_node.getAtoms().size())
		{
			std::cout << "Trying the assign the following values: " << std::endl;
			for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = assignments->begin(); ci != assignments->end(); ci++)
			{
				const BoundedAtom* bounded_atom = (*ci).first;
				bounded_atom->print(std::cout, dtg_node.getDTG().getBindings());
				std::cout << std::endl;
			}
			
			std::cout << "To the DTG: ";
			dtg_node.print(std::cout);
			std::cout << std::endl;
			assert (false);
		}
		
		// Check if the order of the atoms corresponds with that of the DTG node.
		//for (std::vector<const BoundedAtom*>::const_iterator ci = assignments->begin(); ci != assignments->end(); ci++)
		for (unsigned int j = 0; j < assignments->size(); j++)
		{
			const BoundedAtom* assignment = (*assignments)[j].first;
			const BoundedAtom* dtg_atom = dtg_node.getAtoms()[j];
			if (!dtg_node_->getDTG().getBindings().canUnify(assignment->getAtom(), assignment->getId(), dtg_atom->getAtom(), dtg_atom->getId()))
			{
				std::cout << "The " << j << "th atom does not match, did you try to add the atoms in the wrong order?" << std::endl;
				assignment->print(std::cout, dtg_node.getDTG().getBindings());
				std::cout << " v.s. ";
				dtg_atom->print(std::cout, dtg_node.getDTG().getBindings());
				std::cout << std::endl;
				assert (false);
			}

		}
	}
	reachable_facts_.insert(reachable_facts_.end(), init_assignments.begin(), init_assignments.end());
}

void ReachableDTGNode::addFromNode(const ReachableDTGNode& dtg_node)//, const std::vector<const BoundedAtom*>& reachable_facts)
{
	for (std::vector<const ReachableDTGNode*>::const_iterator ci = reachable_from_.begin(); ci != reachable_from_.end(); ci++)
	{
		if (*ci == &dtg_node)
			return;
	}
	
	// Add new values to its variable domains!
//	assert (reachable_facts.size() > 0);
//	reachable_facts_.push_back(&reachable_facts);
	reachable_from_.push_back(&dtg_node);
}

void ReachableDTGNode::addReachableNode(const ReachableDTGNode& dtg_node)
{
	// TODO: Tomorrow: Check if we do not generate more of these nodes and end up in an infinite loop...
	for (std::vector<const ReachableDTGNode*>::const_iterator ci = reachable_.begin(); ci != reachable_.end(); ci++)
	{
		if (*ci == &dtg_node)
			return;
	}
	reachable_.push_back(&dtg_node);
}

void ReachableDTGNode::addTransition(ReachabilityTransition& reachable_transition)
{
	transitions_.push_back(&reachable_transition);
}

bool ReachableDTGNode::addReachableFacts(const std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >& new_reachable_facts)
{
 	std::cout << "[ReachableDTGNode::addReachableFacts] " << std::endl;
	std::cout << *this << std::endl;
	std::cout << "Current reachable facts (" << reachable_facts_.size() << "): " << std::endl;
	for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* reachable_facts = *ci;
		for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = reachable_facts->begin(); ci != reachable_facts->end(); ci++)
		{
			std::cout << "* ";
			(*ci).first->print(std::cout, dtg_node_->getDTG().getBindings());
			std::cout << std::endl;
		}
	}

	std::cout << "Reachable facts to add: (" << new_reachable_facts.size() << ")" << std::endl;
	for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >::const_iterator ci = new_reachable_facts.begin(); ci != new_reachable_facts.end(); ci++)
	{
		const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* reachable_facts = *ci;
		for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = reachable_facts->begin(); ci != reachable_facts->end(); ci++)
		{
			std::cout << "* ";
			(*ci).first->print(std::cout, dtg_node_->getDTG().getBindings());
			std::cout << std::endl;
		}
	}
	
	bool reachable_facts_have_changed = false;

	// Make sure we do not add double entries. If an existing value is a super set of a tupple of values we want
	// to add, don't add it. Or - the other way around - if a new value is a super set of a existing tupple we
	// replace the old one(s) with the new one.
	for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> > *>::const_iterator ci = new_reachable_facts.begin(); ci != new_reachable_facts.end(); ci++)
	{
		const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* facts_to_add = *ci;
		
		// For the facts such that the order corresponds with the way they are stored internally.
		std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* ordered_facts_to_add = new std::vector<std::pair<const BoundedAtom*, InvariableIndex> >();

		for (unsigned int i = 0; i < dtg_node_->getAtoms().size(); i++)
		{
			bool entry_found = false;
			for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = facts_to_add->begin(); ci != facts_to_add->end(); ci++)
			{
				const Predicate& predicate = (*ci).first->getAtom().getPredicate();
				InvariableIndex index = (*ci).second;

				std::cout << "Compare: " << predicate << " (" << index << ") v.s. " << dtg_node_->getAtoms()[i]->getAtom().getPredicate() << " (" << dtg_node_->getIndex(*dtg_node_->getAtoms()[i]) << ")" << std::endl;
				
				if (dtg_node_->getAtoms()[i]->getAtom().getPredicate().getName() == predicate.getName() &&
				    dtg_node_->getIndex(*dtg_node_->getAtoms()[i]) == index)
				{
					ordered_facts_to_add->push_back(*ci);
					entry_found = true;
					break;
				}
			}
			
			assert (entry_found);
		}
		
		bool add_new_fact = true;

		for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> > *>::reverse_iterator ri = reachable_facts_.rbegin(); ri != reachable_facts_.rend(); ri++)
		{
			const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* stored_facts = *ri;
			
			if (ordered_facts_to_add->size() != stored_facts->size())
			{
				std::cout << "Existing fact (" << stored_facts->size() << "): " << std::endl;
				for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = stored_facts->begin(); ci != stored_facts->end(); ci++)
				{
					std::cout << "* ";
					(*ci).first->print(std::cout, dtg_node_->getDTG().getBindings());
					std::cout << std::endl;
				}
				std::cout << "New fact (" << ordered_facts_to_add->size() << "): " << std::endl;
				for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = ordered_facts_to_add->begin(); ci != ordered_facts_to_add->end(); ci++)
				{
					std::cout << "* ";
					(*ci).first->print(std::cout, dtg_node_->getDTG().getBindings());
					std::cout << std::endl;
				}
				assert (false);
			}
			
			bool facts_to_add_is_a_super_set = true;
			bool facts_to_add_is_a_sub_set = true;

			// Check for individually if they are a sub or super set of each other.
			for (unsigned int i = 0; i < ordered_facts_to_add->size(); i++)
			{
				const BoundedAtom* new_bounded_atom = (*ordered_facts_to_add)[i].first;
				const BoundedAtom* existing_bounded_atom = (*stored_facts)[i].first;

				std::cout << "Atom to add to this node: ";
				new_bounded_atom->print(std::cout, dtg_node_->getDTG().getBindings());
				std::cout << " (" << (*ordered_facts_to_add)[i].second << ")" << std::endl;
				
				// All reachable facts submitted for inclusion must have the same predicate or be able to overlap with it.
				assert (new_bounded_atom->getAtom().getArity() == existing_bounded_atom->getAtom().getArity());
				assert (new_bounded_atom->getAtom().getPredicate().canSubstitute(existing_bounded_atom->getAtom().getPredicate()) ||
				        existing_bounded_atom->getAtom().getPredicate().canSubstitute(new_bounded_atom->getAtom().getPredicate()));

				/**
				 * If the current fact we want to add cannot be unified with the current reachable node, we break of and try the next existing node.
				 */
				if (!dtg_node_->getDTG().getBindings().canUnify(new_bounded_atom->getAtom(), new_bounded_atom->getId(), existing_bounded_atom->getAtom(), existing_bounded_atom->getId()))
				{
					std::cout << "Cannot unify.." << std::endl;
					facts_to_add_is_a_super_set = false;
					facts_to_add_is_a_sub_set = false;
					//continue;
					break;
				}
				
				for (unsigned int j = 0; j < existing_bounded_atom->getAtom().getArity(); j++)
				{
					const Term* new_atoms_term = new_bounded_atom->getAtom().getTerms()[j];
					const Term* existing_atoms_term = existing_bounded_atom->getAtom().getTerms()[j];
					
					// If both terms are objects they need to be the same.
					if (new_atoms_term->isObject() && existing_atoms_term->isObject())
					{
						std::cout << "Both are objects!" << std::endl;
						if (new_atoms_term->asObject() != existing_atoms_term->asObject())
						{
							std::cout << "Both are objects and disjunct!" << std::endl;
							facts_to_add_is_a_sub_set = false;
							facts_to_add_is_a_super_set = false;
						}
					}
					
					/**
					 * If the existing bounded atom is a single object and the new atom is a
					 * variable domain there are the following possibilities:
					 * 1) The object is included and is the only object in the domain.
					 * -> The new atom can be the sub and super set.
					 * 2) The object is not included.
					 * -> Cannot be a sub set or super set, they are distinct.
					 * 3) The object is included and is not the only object in the domain.
					 * -> The new atom cannot be the sub set, but can be a super set.
					 */
					else if (new_atoms_term->isVariable() && existing_atoms_term->isObject())
					{
						std::cout << "New is variable other is object." << std::endl;
						const VariableDomain& new_atom_variable_domain = dtg_node_->getDTG().getBindings().getVariableDomain(new_bounded_atom->getId(), *new_atoms_term->asVariable());
						
						std::cout << new_atom_variable_domain << " v.s. " << *existing_atoms_term->asObject() << std::endl;
						
						if (new_atom_variable_domain.contains(*existing_atoms_term->asObject()))
						{
							if (new_atom_variable_domain.getDomain().size() > 1)
							{
								std::cout << "New is variable other is object. New.size() > 1." << std::endl;
								facts_to_add_is_a_sub_set = false;
							}						
						}
						else
						{
							std::cout << "New is variable other is object. Disjunct." << std::endl;
							facts_to_add_is_a_sub_set = false;
							facts_to_add_is_a_super_set = false;
						}
					}
					
					/**
					 * If the new atom is a single object and the existing bounded atom is a
					 * variable domain there are the following possibilities:
					 * 1) The object is included and is the only object in the domain.
					 * -> The new atom can be the sub and super set.
					 * 2) The object is not included.
					 * -> Cannot be a sub set or super set, they are distinct.
					 * 3) The object is included and is not the only object in the domain.
					 * -> The new atom cannot be the super set, but can be a sub set.
					 */
					else if (new_atoms_term->isObject() && existing_atoms_term->isVariable())
					{
						std::cout << "Existing is variable other is object." << std::endl;
						const VariableDomain& existing_atom_variable_domain = dtg_node_->getDTG().getBindings().getVariableDomain(existing_bounded_atom->getId(), *existing_atoms_term->asVariable());
						
						if (existing_atom_variable_domain.contains(*new_atoms_term->asObject()))
						{
							if (existing_atom_variable_domain.getDomain().size() > 1)
							{
								std::cout << "Existing is variable other is object. Existing.size() > 1." << std::endl;
								facts_to_add_is_a_super_set = false;
							}						
						}
						else
						{
							std::cout << "Existing is variable other is object. Disjunct." << std::endl;
							facts_to_add_is_a_sub_set = false;
							facts_to_add_is_a_super_set = false;
						}
					}
					
					/**
					 * If both are a variable domain, we need to check if there are
					 * objects in either which are not present which are not in the
					 * other.
					 */
					else
					{
						std::cout << "Both variable." << std::endl;
						const VariableDomain& new_atom_variable_domain = dtg_node_->getDTG().getBindings().getVariableDomain(new_bounded_atom->getId(), *new_atoms_term->asVariable());
						const VariableDomain& existing_atom_variable_domain = dtg_node_->getDTG().getBindings().getVariableDomain(existing_bounded_atom->getId(), *existing_atoms_term->asVariable());
						
						// Check if the new facts are a subset of existing nodes.
						if (facts_to_add_is_a_sub_set)
						{
							// The complement must be empty, so all values in the other domain must be contained in this domain for it to be a sub set.
							std::vector<const Object*> complement;
							existing_atom_variable_domain.getComplement(complement, new_atom_variable_domain.getDomain());
							if (complement.size() != 0)
							{
								std::cout << "Both variable, new contains atoms not in existing. New cannot be a sub set." << std::endl;
								facts_to_add_is_a_sub_set = false;
							}
						}
						
						if (facts_to_add_is_a_super_set)
						{
							// The complement must be empty, so all values in the other domain must be contained in this domain for it to be a sub set.
							std::vector<const Object*> complement;
							new_atom_variable_domain.getComplement(complement, existing_atom_variable_domain.getDomain());
							if (complement.size() != 0)
							{
								std::cout << "Both variable, existing contains atoms not in new. New cannot be a super set." << std::endl;
								facts_to_add_is_a_super_set = false;
							}
						}
					}
				}
			}
			
			// If the fact to add is a sub set of an existing node, we do not need to add it, move on to the next one.
			if (facts_to_add_is_a_sub_set)
			{
				std::cout << "New is a subset, ignore!" << std::endl;
				add_new_fact = false;
				break;
			}
			
			// If the fact to add is a superset of an existing node, we remove the existing node in favour of this one.
			else if (facts_to_add_is_a_super_set)
			{
				std::cout << "New is a superset, ignore!" << std::endl;
				reachable_facts_.erase(ri.base() - 1);
				reachable_facts_.push_back(ordered_facts_to_add);
				add_new_fact = false;
				reachable_facts_have_changed = true;
				break;
			}
		}
		
		if (add_new_fact)
		{
			std::cout << "New is a new fact, ADD!" << std::endl;
			reachable_facts_.push_back(ordered_facts_to_add);
			reachable_facts_have_changed = true;
		}
	}
	
	std::cout << "Result for adding reachable facts: " << *this << std::endl;
	
	return reachable_facts_have_changed;
}

std::ostream& operator<<(std::ostream& os, const ReachableDTGNode& reachable_dtg_node)
{
	os << "-= Reachability node for the DTG =-" << std::endl;
	reachable_dtg_node.getDTGNode().print(os);
	os << std::endl;
	
	
	const std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >& reachable_facts = reachable_dtg_node.getReachableFacts();
	for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
	{
		const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* facts = *ci;
		for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = facts->begin(); ci != facts->end(); ci++)
		{
			os << "* ";
			(*ci).first->print(os, reachable_dtg_node.getDTGNode().getDTG().getBindings());
			os << std::endl;
		}
		os << " -=*=- " << std::endl;
	}
	
	return os;
}

/*************************
 * The ReachabilityTransition class
 *************************/

ReachabilityTransition::ReachabilityTransition(MyPOP::SAS_Plus::ReachabilityAnalist& reachability_analist, const MyPOP::SAS_Plus::Transition& transition)
	: reachability_analist_(&reachability_analist), transition_(&transition)
{

}

bool ReachabilityTransition::propagateEffects(const std::vector< const MyPOP::LANDMARKS::Landmark* >& landmarks, const std::vector<const Atom*>& initial_facts)
{
	// Check if any transition is possible (i.e. are the variable domains not empty).
	const DomainTransitionGraph& dtg = transition_->getFromNode().getDTG();

	StepID transition_action_id = transition_->getStep()->getStepId();
	const Action& transition_action = transition_->getStep()->getAction();

	std::cout << " -=  propagateEffects =- " << std::endl;
	std::cout << "Explore transition:" << std::endl;
	std::cout << "FROM: " << transition_->getFromNode() << std::endl;
	std::cout << "TO: " << transition_->getToNode() << std::endl;
	std::cout << "ACTION: ";
	transition_action.print(std::cout, dtg.getBindings(), transition_action_id);
	std::cout << std::endl;

	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &transition_action.getPrecondition());
	
	/**
	 * To determine all the assignments the values of the 'to node' can take we have to consider all assignments
	 * of the 'from node' and propagate the effect of the transition.
	 */
	const ReachableDTGNode* reachable_from_node = reachability_analist_->getReachableDTGNode(transition_->getFromNode());
	assert (reachable_from_node != NULL);

	const std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >& possible_from_assignments = reachable_from_node->getReachableFacts();
	
/*	if (possible_from_assignments.size() == 0)
	{
		std::cout << "No possible assignments from this node: " << *reachable_from_node << std::endl;
	}
*/
	bool to_node_changed = false;
	for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >::const_iterator ci = possible_from_assignments.begin(); ci != possible_from_assignments.end(); ci++)
	{
		const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* possible_assignment = (*ci);
		
		/**
		 * Create a copy of the transition and the both nodes. This allows us to change the transition itself by unifying
		 * the variables of the to and / or from nodes.
		 */
		Transition* base_transition_for_possible_assignment = transition_->cloneWithNodes(initial_facts);

		// Apply the possible assignment of the from node.
		assert (base_transition_for_possible_assignment->getFromNode().getAtoms().size() == possible_assignment->size());
		for (unsigned int i = 0; i < base_transition_for_possible_assignment->getFromNode().getAtoms().size(); i++)
		{
			const BoundedAtom* bounded_atom = base_transition_for_possible_assignment->getFromNode().getAtoms()[i];
			const BoundedAtom* reachable_bounded_atom = (*possible_assignment)[i].first;
			
			dtg.getBindings().unify(bounded_atom->getAtom(), bounded_atom->getId(), reachable_bounded_atom->getAtom(), reachable_bounded_atom->getId());
		}
		
		std::cout << "Base transition for possible assignments: " << base_transition_for_possible_assignment->getFromNode() << " -> " << base_transition_for_possible_assignment->getToNode() << std::endl;
		
		
		/**
		 * Remove the landmarks as possible preconditions for this transition.
		 *
		 * When searching for the first achievers of a landmark, the landmark itself cannot appear in
		 * any of the preconditions of the transitions. Therefor we check each preconditions against
		 * the landmark(s) we're trying to find. If the precondition can be unified with one of the
		 * landmarks, we limit its variable domains so it cannot be equal to the landmark(s).
		 */
		std::vector<const std::vector<const BoundedAtom*>* > all_possible_assignments;
		
	/*
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* transition_precondition = *ci;
			for (std::vector<const LANDMARKS::Landmark*>::const_iterator ci = landmarks.begin(); ci != landmarks.end(); ci++)
			{
				const LANDMARKS::Landmark* landmark = *ci;

				**
				 * If a landmark matches with any of the preconditions we need to split the possible assignments such 
				 * that they cannot unify with the landmark anymore.
				 *
				if (dtg.getBindings().canUnify(*transition_precondition, transition_action_id, landmark->getAtom(), landmark->getStepId(), &landmark->getLandmarkGraph().getBindings()))
				{
					
					std::cout << "The precondition: ";
					transition_precondition->print(std::cout, dtg.getBindings(), transition_action_id);
					std::cout << " can be unified with the landmark: " << *landmark << " prune the values it can take!" << std::endl;
					
					// Check which effects are affected by restricting this precondition.
					std::vector<const VariableDomain*> precondition_variable_domains;
					dtg.getBindings().getVariableDomains(precondition_variable_domains, transition_action_id, *transition_precondition);
					std::sort(precondition_variable_domains.begin(), precondition_variable_domains.end());
					
					std::vector<const VariableDomain*> effect_variable_domains;
					for (std::vector<const Atom*>::const_iterator ci = new_transition->getEffects().begin(); ci != new_transition->getEffects().end(); ci++)
					{
						const Atom* transition_effect = *ci;
						dtg.getBindings().getVariableDomains(effect_variable_domains, transition_action_id, *transition_effect);
					}
					std::sort(effect_variable_domains.begin(), effect_variable_domains.end());
					
					// By taking the intersection of both vectors of variable domains we will find all the variable domain which are shared among the two.
					std::vector<const VariableDomain*> affected_variable_domains(std::max(precondition_variable_domains.size(), effect_variable_domains.size()));
					std::vector<const VariableDomain*>::iterator end_of_intersection = std::set_intersection(precondition_variable_domains.begin(), precondition_variable_domains.end(), effect_variable_domains.begin(), effect_variable_domains.end(), affected_variable_domains.begin());
					
					std::set<const VariableDomain*> ordered_affected_variable_domains;
					ordered_affected_variable_domains.insert(affected_variable_domains.begin(), end_of_intersection);
					
					std::cout << "The preconditions and effects share: " << ordered_affected_variable_domains.size() << " variable domains!" << std::endl;
					
					**
					 * Construct the fact which cannot be made true due to the given landmark.
					 *
					for (std::vector<const Atom*>::const_iterator ci = new_transition->getEffects().begin(); ci != new_transition->getEffects().end(); ci++)
					{
						effect_variable_domains.clear();
						
						const Atom* transition_effect = *ci;
						dtg.getBindings().getVariableDomains(effect_variable_domains, transition_action_id, *transition_effect);
						
						for (std::vector<const VariableDomain*>::const_iterator ci = effect_variable_domains.begin(); ci != effect_variable_domains.end(); ci++)
						{
							const VariableDomain* effect_variable_domain = *ci;
							if (ordered_affected_variable_domains.count(effect_variable_domain) != 0)
							{
								precondition_variable_domains.clear();
								dtg.getBindings().getVariableDomains(precondition_variable_domains, transition_action_id, *transition_precondition);
								assert (landmark->getAtom().getTerms().size() == precondition_variable_domains.size());
								for (unsigned int i = 0; i < precondition_variable_domains.size(); i++)
								{
									if (effect_variable_domain == precondition_variable_domains[i])
									{
										std::cout << "Limit " << *precondition_variable_domains[i] << std::endl;
										StepID achievable_fact_id = dtg.getBindings().createVariableDomains(*transition_effect);
										dtg.getBindings().makeEqual(*transition_effect, achievable_fact_id, *transition_effect, transition_action_id);
										
										if (landmark->getAtom().getTerms()[i]->isObject())
										{
											dtg.getBindings().unassign(achievable_fact_id, *transition_effect->getTerms()[i]->asVariable(), *landmark->getAtom().getTerms()[i]->asObject());
										}
										else
										{
											const VariableDomain& landmark_variable_domain = landmark->getLandmarkGraph().getBindings().getVariableDomain(landmark->getStepId(), *landmark->getAtom().getTerms()[i]->asVariable());
											dtg.getBindings().unassign(achievable_fact_id, *transition_effect->getTerms()[i]->asVariable(), landmark_variable_domain.getDomain());
										}
										
										std::cout << "The following fact can be made true with this transition: ";
										//transition_effect->print(std::cout, dtg.getBindings(), achievable_fact_id);
										std::cout << std::endl;
										
										std::vector<const BoundedAtom*>* possible_assignments_for_landmark = new std::vector<const BoundedAtom*>();
										// Figure out which atom in the to node achievable_fact_id refers to.
										for (std::vector<BoundedAtom*>::const_iterator ci = new_transition->getToNode().getAtoms().begin(); ci != new_transition->getToNode().getAtoms().end(); ci++)
										{
											const BoundedAtom* to_node_fact = *ci;

											**
											 * For the restricted atoms we add the one constructed above. For those who are not restricted, they are added as copies of the original.
											 *
											if (dtg.getBindings().canUnify(to_node_fact->getAtom(), to_node_fact->getId(), *transition_effect, transition_action_id))
											{
												const VariableDomain& to_node_variable_domain = dtg.getBindings().getVariableDomain(to_node_fact->getId(), *to_node_fact->getAtom().getTerms()[i]->asVariable());
												if (&to_node_variable_domain == effect_variable_domain)
												{
													std::cout << "* ";
													transition_effect->print(std::cout, dtg.getBindings(), achievable_fact_id);
													std::cout << std::endl;
													possible_assignments_for_landmark->push_back(new BoundedAtom(achievable_fact_id, *transition_effect));
													continue;
												}
											}
											
											// Make copies of the original and add them too.
											StepID effect_copy_fact_id = dtg.getBindings().createVariableDomains(to_node_fact->getAtom());
											dtg.getBindings().makeEqual(to_node_fact->getAtom(), effect_copy_fact_id, to_node_fact->getAtom(), to_node_fact->getId());
											possible_assignments_for_landmark->push_back(new BoundedAtom(effect_copy_fact_id, to_node_fact->getAtom()));
											
											std::cout << "* ";
											to_node_fact->getAtom().print(std::cout, dtg.getBindings(), effect_copy_fact_id);
											std::cout << std::endl;
										}
										
										std::cout << std::endl;
										
										assert (possible_assignments_for_landmark->size() == new_transition->getToNode().getAtoms().size());
										all_possible_assignments.push_back(possible_assignments_for_landmark);
										break;
									}
								}
							}
						}
					}
				}
			}
		}
		*/
		
		/**
		 * If the transition wasn't constrained by any of the landmarks, add the original assignments of the variables.
		 */
		if (all_possible_assignments.size() == 0)
		{
//			std::cout << "Not affected by landmarks!" << std::endl;
//			all_possible_assignments.push_back(possible_assignment);
			std::vector<const BoundedAtom*>* bounded_atoms = new std::vector<const BoundedAtom*>();
			bounded_atoms->insert(bounded_atoms->end(), base_transition_for_possible_assignment->getFromNode().getAtoms().begin(), base_transition_for_possible_assignment->getFromNode().getAtoms().end());
			all_possible_assignments.push_back(bounded_atoms);
		}
//		else
//		{
//			std::cout << "Affected by landmarks!" << std::endl;
//		}
		
		/**
		 * For all possible assignments, make a new transition and apply them storing the result afterwards.
		 */
		for (std::vector<const std::vector<const BoundedAtom*>* >::const_iterator ci = all_possible_assignments.begin(); ci != all_possible_assignments.end(); ci++)
		{
			const std::vector<const BoundedAtom*>* possible_assignment = *ci;
			
			/**
			 * Create a copy of the transition and the both nodes. This allows us to change the transition itself by unifying
			 * the variables of the to and / or from nodes.
			 */
			Transition* new_transition = base_transition_for_possible_assignment->cloneWithNodes(initial_facts);
			assert (new_transition != NULL);
			
/*			std::cout << " -=  Explore the following possible assignment =- " << std::endl;
			std::cout << "Explore transition:" << std::endl;
			std::cout << "FROM: " << new_transition->getFromNode() << std::endl;
			std::cout << "TO: " << new_transition->getToNode() << std::endl;
			std::cout << "ACTION: ";
			transition_action.print(std::cout, dtg.getBindings(), new_transition->getStep()->getStepId());
			std::cout << std::endl;
*/

			// Apply the possible assignment of the from node.
			assert (new_transition->getFromNode().getAtoms().size() == possible_assignment->size());

			for (unsigned int i = 0; i < new_transition->getFromNode().getAtoms().size(); i++)
			{
				const BoundedAtom* bounded_atom = new_transition->getFromNode().getAtoms()[i];
				const BoundedAtom* reachable_bounded_atom = (*possible_assignment)[i];
				
				dtg.getBindings().unify(bounded_atom->getAtom(), bounded_atom->getId(), reachable_bounded_atom->getAtom(), reachable_bounded_atom->getId());
			}

/*
			std::cout << "Before checking the preconditions, possible assignments: " << std::endl;
			for (unsigned int i = 0; i < new_transition->getToNode().getAtoms().size(); i++)
			{
				new_transition->getToNode().getAtoms()[i]->print(std::cout, dtg.getBindings());
				std::cout << std::endl;
			}
			std::cout << " -= END =- " << std::endl;
*/

			/**
			 * We need to keep track of the bindings made to the variables of the transition prior to assigning them
			 * to the preconditions. This way, we can try all possible assignments of the preconditions. When we try
			 * a different assignment assignment for a precondition (i.e. we backtrack) we can restore the saved transition
			 * prior to making the assignment, make a copy of it and try again.
			 * 
			 * Per preconditions we might end up with multiple transitions, because the assignments of the variables might
			 * be completely non-intersection. E.g. a node might have the following assignments:
			 *
			 * (at truck1 s1) OR (at truck2 s2), which we cannot combine in the bindings made to a single transition.
			 *
			 * The result would be something like (at {truck1, truck2} {s1, s2}) which does not capture the correct constraints,
			 * therefor we need two separate ones.
			 */
			std::vector<const Transition*> open_list;
			open_list.push_back(new_transition);

			/**
			 * new_transition is the transition for the current assignments to the variable domains. Per precondition check which assignments
			 * are supported and add it as new possible assignments.
			 */
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = *ci;
				std::vector<const Transition*> possible_transitions;
				
				for (std::vector<const Transition*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
				{
					const Transition* current_transition = *ci;
					
	//				std::cout << "Check precondition: ";
	//				precondition->print(std::cout, dtg.getBindings(), new_transition->getStep()->getStepId());
	//				std::cout << std::endl;
					
					for (std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>::const_iterator ci = reachability_analist_->getReachableDTGNodes().begin(); ci != reachability_analist_->getReachableDTGNodes().end(); ci++)
					{
						const ReachableDTGNode* reachable_dtg_node = (*ci).second;
						
						const std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >& reachable_facts = reachable_dtg_node->getReachableFacts();
						
						for (std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
						{
							const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* reachables = *ci;
							for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = reachables->begin(); ci != reachables->end(); ci++)
							{
	//							std::cout << " v.s. reachable: ";
	//							(*ci)->print(std::cout, reachable_dtg_node->getDTGNode().getDTG().getBindings());
	//							std::cout << std::endl;

								/**
								 * Before trying to unify the transition we make a copy of it so the other transitions are not affected.
								 */
								if (!dtg.getBindings().canUnify(*precondition, current_transition->getStep()->getStepId(), (*ci).first->getAtom(), (*ci).first->getId(), &reachable_dtg_node->getDTGNode().getDTG().getBindings()))
								{
									continue;
								}
								
								Transition* transition_clone = current_transition->cloneWithNodes(initial_facts);
								assert (transition_clone != NULL);
								
								if (dtg.getBindings().unify(*precondition, transition_clone->getStep()->getStepId(), (*ci).first->getAtom(), (*ci).first->getId(), &reachable_dtg_node->getDTGNode().getDTG().getBindings()))
								{
									possible_transitions.push_back(transition_clone);
								}
								else
								{
									delete transition_clone;
								}
							}
						}
					}
				}
				
				/**
				 * All possible transitions are added in the list possible_transitions. After checking all possible
				 * assignments for the ith precondition we add the new possible transitions to the open list and these
				 * will be evaluated for the (i + 1)th precondition.
				 */
				open_list.clear();
				open_list.insert(open_list.begin(), possible_transitions.begin(), possible_transitions.end());
				
				// Test, make sure the order in which the nodes are stored in the transition isn't changed.
				for (std::vector<const Transition*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
				{
					const Transition* transition = *ci;
					
					const DomainTransitionGraphNode& from_dtg_node = transition->getFromNode();
					const DomainTransitionGraphNode& to_dtg_node = transition->getToNode();

					for (unsigned int i = 0; i < from_dtg_node.getAtoms().size(); i++)
					{
						const BoundedAtom* from_bounded_atom = from_dtg_node.getAtoms()[i];
						assert (from_dtg_node.getDTG().getBindings().canUnify(from_bounded_atom->getAtom(), from_bounded_atom->getId(), transition_->getFromNode().getAtoms()[i]->getAtom(), transition_->getFromNode().getAtoms()[i]->getId()));
					}
					
					for (unsigned int i = 0; i < to_dtg_node.getAtoms().size(); i++)
					{
						const BoundedAtom* to_bounded_atom = to_dtg_node.getAtoms()[i];
						assert (from_dtg_node.getDTG().getBindings().canUnify(to_bounded_atom->getAtom(), to_bounded_atom->getId(), transition_->getToNode().getAtoms()[i]->getAtom(), transition_->getToNode().getAtoms()[i]->getId()));
					}
				}
			}
			
			/**
			* If the current assignment of the variable domains contains an unsupported precondition we skip to the next one
			* (if any).
			*/
			if (open_list.size() == 0)
			{
				std::cout << "Preconditions are not supported :(" << std::endl;
				continue;
			}
			
			/**
			 * Add all resulting - valid - transitions to the reachable node.
			 */
			std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >* valid_assignment = new std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >();
			std::cout << "Possible assignments: " << std::endl;
			for (std::vector<const Transition*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
			{
				const Transition* possible_transition = *ci;

				std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* effects = new std::vector<std::pair<const BoundedAtom*, InvariableIndex> >();
				for (std::vector<BoundedAtom*>::const_iterator ci = possible_transition->getToNode().getAtoms().begin(); ci != possible_transition->getToNode().getAtoms().end(); ci++)
				{
					const BoundedAtom* to_node_atom = *ci;
					
					// Add this stuff to the valid assignments! :)
					effects->push_back(std::make_pair(to_node_atom, possible_transition->getToNode().getIndex(*to_node_atom)));
					std::cout << "** ";
					to_node_atom->print(std::cout, possible_transition->getFromNode().getDTG().getBindings());
					std::cout << std::endl;
				}
/*
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = possible_transition->getEffects().begin(); ci != possible_transition->getEffects().end(); ci++)
				{
					const Atom* effect = (*ci).first;
					InvariableIndex invariable_index = (*ci).second;
					effects->push_back(std::make_pair(new BoundedAtom(possible_transition->getStep()->getStepId(), *effect), invariable_index));
					std::cout << "** ";
					effect->print(std::cout, possible_transition->getFromNode().getDTG().getBindings(), possible_transition->getStep()->getStepId());
					std::cout << std::endl;
				}
*/

				valid_assignment->push_back(effects);
				std::cout << " -= ** =- " << std::endl;
			}
			
			std::cout << " -= END =- " << std::endl;
			
			ReachableDTGNode& reachable_to_node = reachability_analist_->createReachableDTGNode(transition_->getToNode(), NULL);
			if (reachable_to_node.addReachableFacts(*valid_assignment))
			{
				to_node_changed = true;
				std::cout << "* The node: " << reachable_to_node << " can be achieved! :D" << std::endl;
			}
//			else
//			{
//				std::cout << "* The node: " << reachable_to_node << " can be achieved! But this was already known!" << std::endl;
//			}

			ReachableDTGNode* reachable_from_node = reachability_analist_->getReachableDTGNode(transition_->getFromNode());
			reachable_from_node->addReachableNode(reachable_to_node);
		}
	}
	
//	exit(0);

	return to_node_changed;
}


/*************************
 * The ReachabilityAnalist class
 *************************/

ReachabilityAnalist::ReachabilityAnalist(const DomainTransitionGraphManager& dtg_manager)
	: dtg_manager_(&dtg_manager)
{

}

void ReachabilityAnalist::ignoreNode(const DomainTransitionGraphNode& dtg_node)
{
	std::cout << "Ignore: " << dtg_node << std::endl;
	ignore_list_.insert(&dtg_node);
}

void ReachabilityAnalist::addTransitionConstraint(const BoundedAtom& bounded_atom)
{
	transition_constrains_.push_back(&bounded_atom);
}

void ReachabilityAnalist::clearIgnoreList()
{
	ignore_list_.clear();
}

ReachableDTGNode* ReachabilityAnalist::getReachableDTGNode(const DomainTransitionGraphNode& dtg_node)
{
	std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>::const_iterator ci = reachable_nodes_.find(&dtg_node);
	if (ci == reachable_nodes_.end())
	{
		return NULL;
	}
	else
	{
		return (*ci).second;
	}
}

ReachableDTGNode& ReachabilityAnalist::createReachableDTGNode(const DomainTransitionGraphNode& dtg_node, const std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* >* possible_assignments)
{
	std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>::const_iterator ci = reachable_nodes_.find(&dtg_node);
	
	// Sanity, make sure only to build reachability nodes for the nodes from the DTGs!
	bool part_of_dtgs = false;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		const DomainTransitionGraph* dtg = *ci;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			if (*ci == &dtg_node)
			{
				part_of_dtgs = true;
				break;
			}
		}
		
		if (part_of_dtgs) break;
	}
	
	assert (part_of_dtgs);
	
	ReachableDTGNode* node = NULL;
	if (ci == reachable_nodes_.end())
	{
		if (possible_assignments == NULL)
		{
			node = new ReachableDTGNode(*this, dtg_node);
		}
		else
		{
			node = new ReachableDTGNode(*this, dtg_node, *possible_assignments);
		}
		reachable_nodes_[&dtg_node] = node;
//		std::cout << "New reachable node: " << dtg_node << std::endl;
	}
	else
	{
		node = (*ci).second;
		if (possible_assignments != NULL)
		{
			node->addReachableFacts(*possible_assignments);
		}
	}
	
//	std::cout << "Created the following DTG node: " << *node << std::endl;
	
	return *node;
}

void ReachabilityAnalist::initialiseReachablilityGraph(const std::vector<const Atom*>& initial_facts, const Bindings& bindings)
{
	std::cout << "[ReachabilityAnalist::initialiseReachablilityGraph] START" << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		const DomainTransitionGraph* dtg = *ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;

			// Keep track of the last tried combination.
			unsigned int counters[dtg_node->getAtoms().size()];
			memset(&counters[0], 0, sizeof(unsigned int));
			
			unsigned int current_bounded_atom = 0;
			
			// Explore all possible combinations of initial facts.
			std::vector<const std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* > all_possible_assignments;
			std::vector<std::pair<const BoundedAtom*, InvariableIndex> >* current_assignments = new std::vector<std::pair<const BoundedAtom*, InvariableIndex> >();
			const Object* invariable_initial_object = NULL;
			while (true)
			{
				const BoundedAtom* bounded_atom = dtg_node->getAtoms()[current_bounded_atom];

				std::cout << "Check node: ";
				bounded_atom->getAtom().print(std::cout, dtg->getBindings(), dtg_node->getAtoms()[current_bounded_atom]->getId());
				std::cout << std::endl;

				// Try to find an assignment for this node.
				bool found_assignment = false;
				for (unsigned int j = counters[current_bounded_atom]; j < initial_facts.size(); j++)
				{
					if (bindings.canUnify(*initial_facts[j], Step::INITIAL_STEP, bounded_atom->getAtom(), bounded_atom->getId(), &dtg->getBindings()))
					{
						assert (current_assignments->size() == current_bounded_atom);
						std::cout << "Possible fact which unifies: ";
						initial_facts[j]->print(std::cout, bindings, Step::INITIAL_STEP);
						std::cout << std::endl;
						
						/**
						 * If we have selected an assignment for the first variable, we must make sure that for subsequent choices the invariable
						 * domain is the same. If this is not the case the combination will not be considered.
						 */
						if (invariable_initial_object != NULL)
						{
							const Object* invariable = initial_facts[j]->getTerms()[dtg_node->getIndex(*bounded_atom)]->asObject();
							if (invariable_initial_object != invariable)
							{
								std::cout << "Invariable object does not match!" << std::endl;
								continue;
							}
						}
						
						/**
						 * If it is the first assignment we set the invariable domain.
						 */
						else
						{
							invariable_initial_object = initial_facts[j]->getTerms()[dtg_node->getIndex(*bounded_atom)]->asObject();
						}
						
						// Store the counter information so next time we revisit the node we start with the initial fact which comes after 
						// the one just selected.
						counters[current_bounded_atom] = j + 1;

						const BoundedAtom* reachable_node = new BoundedAtom(Step::INITIAL_STEP, *initial_facts[j]);
						
						/**
						 * If the assignment is made to the last node. We continue to search for further assignments for this
						 * atom given the previous assignments. Otherwise we store the assignment and continue to find assignments
						 * for the next bounded atom.
						 */
						if (current_bounded_atom != dtg_node->getAtoms().size() - 1)
						{
							current_bounded_atom++;
							current_assignments->push_back(std::make_pair(reachable_node, dtg_node->getIndex(*bounded_atom)));
						}
						else
						{
							current_assignments->push_back(std::make_pair(reachable_node, dtg_node->getIndex(*bounded_atom)));
							
							assert (current_assignments->size() == dtg_node->getAtoms().size());
							
							all_possible_assignments.push_back(current_assignments);
							
							for (std::vector<std::pair<const BoundedAtom*, InvariableIndex> >::const_iterator ci = current_assignments->begin(); ci != current_assignments->end(); ci++)
							{
								std::cout << "-> ";
								(*ci).first->print(std::cout, bindings);
								std::cout << std::endl;
							}

							// For the next possible assignments, we keep all assignments made so for except for the last one.
							current_assignments = new std::vector<std::pair<const BoundedAtom*, InvariableIndex> >(*current_assignments);
							current_assignments->pop_back();
						}
						found_assignment = true;
						break;
 					}
				}
				
				// If no assignment was found and we are looking at the first atom, we can conclude that no further assignment will be found.
				if (!found_assignment && current_bounded_atom == 0)
				{
					break;
				}
				
				// If it is not the first node, but we found no assignments we backtrack and try to find another assignment for the previous
				// bounded atom.
				else if(!found_assignment)
				{
					counters[current_bounded_atom] = 0;
					current_bounded_atom--;
					
					// If we couldn't not find an assignment we backtrack by trying a different assignment for the last assigned variable.
					current_assignments = new std::vector<std::pair<const BoundedAtom*, InvariableIndex> >(*current_assignments);
					current_assignments->pop_back();
				}
								
				// Reset the invariable object if we either:
				// 1) Revoke the first assignment.
				// 2) Found an assignment for the first atom, but it is the only one in the atom.
				if (current_bounded_atom == 0)
				{
					invariable_initial_object = NULL;
				}
			}

			createReachableDTGNode(*dtg_node, &all_possible_assignments);
		}
	}
	std::cout << "[ReachabilityAnalist::initialiseReachablilityGraph] Done!" << std::endl;
	
	std::cout << "[ReachabilityAnalist::initialiseReachablilityGraph] Result!" << std::endl;
	for (std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		std::cout << *(*ci).second << std::endl;
	}
	std::cout << "[ReachabilityAnalist::initialiseReachablilityGraph] END Result!" << std::endl;
//	initialiseTransitions();
}

void ReachabilityAnalist::initialiseTransitions()
{
	for (std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		ReachableDTGNode* reachable_dtg_node = (*ci).second;
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			ReachabilityTransition* reachable_transition = new ReachabilityTransition(*this, *transition);
			reachable_dtg_node->addTransition(*reachable_transition);
		}
	}
}

void ReachabilityAnalist::constructReachablilityGraph(const std::vector<const LANDMARKS::Landmark*>& landmarks, const std::vector<const Atom*>& initial_facts)
{
	std::cout << "[ReachabilityAnalist::constructReachablilityGraph] Start!" << std::endl;
	for (std::vector<const LANDMARKS::Landmark*>::const_iterator ci = landmarks.begin(); ci != landmarks.end(); ci++)
	{
		std::cout << "Landmark: " << **ci << std::endl;
	}
	
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		const DomainTransitionGraph* dtg = *ci;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			ReachableDTGNode& reachable_node = createReachableDTGNode(*dtg_node, NULL);
					
			for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;
				ReachabilityTransition* reachable_transition = new ReachabilityTransition(*this, *transition);
				reachable_node.addTransition(*reachable_transition);
			}
		}
	}

	// Brute force!
	bool has_changed = true;
	while(has_changed)
	{
		has_changed = false;
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
		{
			const DomainTransitionGraph* dtg = *ci;
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
			{
				ReachableDTGNode& reachable_node = createReachableDTGNode(**ci, NULL);
				
				for (std::vector<ReachabilityTransition*>::const_iterator ci = reachable_node.getTransitions().begin(); ci != reachable_node.getTransitions().end(); ci++)
				{
					ReachabilityTransition* reachability_transition = *ci;
					if (reachability_transition->propagateEffects(landmarks, initial_facts))
					{
						has_changed = true;
						
						std::cout << "The transition from ";
						reachability_transition->getTransition().getFromNode().print(std::cout);
						std::cout << " to ";
						reachability_transition->getTransition().getToNode().print(std::cout);
						std::cout << " is possible!" << std::endl;
					}
				}
			}
		}
		
		std::cout << "Done with the Xth iteration, results so far: " << std::endl;
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
		{
			const DomainTransitionGraph* dtg = *ci;
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
			{
				ReachableDTGNode& reachable_node = createReachableDTGNode(**ci, NULL);
				
				if (reachable_node.getReachableFacts().size() != 0)
				{
					std::cout << "@ " << reachable_node << std::endl;
				}
			}
		}
	}
	
	std::cout << "Found all possible reachable nodes!" << std::endl;
/*	std::set<ReachabilityTransition*> open_list;

	// Load all the nodes we need to process.
	std::cout << "[ReachabilityAnalist::constructReachablilityGraph] Start nodes:" << std::endl;
	for (std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		ReachableDTGNode* reachable_dtg_node = (*ci).second;
		open_list.insert(reachable_dtg_node->getTransitions().begin(), reachable_dtg_node->getTransitions().end());
		
		std::cout << "* " << *reachable_dtg_node << std::endl;
	}
	
	while (open_list.size() > 0)
	{
		bool changed = false;
		std::set<ReachabilityTransition*> to_process;
		for (std::set<ReachabilityTransition*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
		{
			ReachabilityTransition* reachability_transition = *ci;
			if (reachability_transition->propagateEffects(landmarks, initial_facts))
			{
				const std::vector<ReachabilityTransition*>& new_transitions = reachable_nodes_[&reachability_transition->getTransition().getToNode()]->getTransitions();
				to_process.insert(new_transitions.begin(), new_transitions.end());
				changed = true;
			}
		}
		
		open_list.clear();
		
		if (changed)
		{
			for (std::map<const DomainTransitionGraphNode*, ReachableDTGNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
			{
				open_list.insert((*ci).second->getTransitions().begin(), (*ci).second->getTransitions().end());
			}
		}
		//open_list.insert(to_process.begin(), to_process.end());
	}
*/
	
	Graphviz::printToDot(*this, landmarks);
}

};


void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::ReachableDTGNode& reachability_node)
{
	const SAS_Plus::DomainTransitionGraphNode& dtg_node = reachability_node.getDTGNode();
		
	// Print the node.
	Graphviz::printToDot(ofs, dtg_node);
	
	ofs << "\"[" << &dtg_node << "] ";
	for (std::vector<SAS_Plus::BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
	{
		(*ci)->print(ofs, dtg_node.getDTG().getBindings());
	}
	
	const std::vector<const std::vector<std::pair<const SAS_Plus::BoundedAtom*, InvariableIndex> >* >& reachable_facts = reachability_node.getReachableFacts();
	
	for (std::vector<const std::vector<std::pair<const SAS_Plus::BoundedAtom*, InvariableIndex> >* >::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
	{
		const std::vector<std::pair<const SAS_Plus::BoundedAtom*, InvariableIndex> >* reachable_fact = *ci;
		ofs << "(";
		
		for (std::vector<std::pair<const SAS_Plus::BoundedAtom*, InvariableIndex> >::const_iterator ci = reachable_fact->begin(); ci != reachable_fact->end(); ci++)
		{
			const SAS_Plus::BoundedAtom* bounded_atom = (*ci).first;
			bounded_atom->print(ofs, dtg_node.getDTG().getBindings());
			if (ci != reachable_fact->end() - 1)
			{
				ofs << ", ";
			}
		}
		ofs << ") ";
	}
	ofs << "\"";
}

// Printing the reachability graph.
void Graphviz::printToDot(const SAS_Plus::ReachabilityAnalist& reachability_analysis, const std::vector<const LANDMARKS::Landmark*>& landmarks)
{
	std::ofstream ofs;
	
	std::stringstream ss;
	ss << "reachability";
	
	for (std::vector<const LANDMARKS::Landmark*>::const_iterator ci = landmarks.begin(); ci != landmarks.end(); ci++)
	{
		const LANDMARKS::Landmark* landmark = *ci;
		landmark->getAtom().print(ss, landmark->getLandmarkGraph().getBindings(), landmark->getStepId());
	}
	ss << ".dot";
	
	std::string filename = ss.str();
	filename.erase(std::remove(filename.begin(), filename.end(), '\t'));
	std::replace(filename.begin(), filename.end(), '(', '_');
	std::replace(filename.begin(), filename.end(), ')', '_');
	std::replace(filename.begin(), filename.end(), '{', '_');
	std::replace(filename.begin(), filename.end(), '}', '_');
	
	ofs.open(filename.c_str(), std::ios::out);

	ofs << "digraph {" << std::endl;
	const std::map<const SAS_Plus::DomainTransitionGraphNode*, SAS_Plus::ReachableDTGNode*>& reachable_nodes = reachability_analysis.getReachableDTGNodes();
	
	for (std::map<const SAS_Plus::DomainTransitionGraphNode*, SAS_Plus::ReachableDTGNode*>::const_iterator ci = reachable_nodes.begin(); ci != reachable_nodes.end(); ci++)
	{
		const SAS_Plus::ReachableDTGNode* reachable_node = (*ci).second;
		
		// Print the node.
		Graphviz::printToDot(ofs, *reachable_node);
		ofs << std::endl;
		
		// Print all its transitions.
		const std::vector<const SAS_Plus::ReachableDTGNode*>& reachable_nodes = reachable_node->getReachableNodes();
		
		for (std::vector<const SAS_Plus::ReachableDTGNode*>::const_iterator ci = reachable_nodes.begin(); ci != reachable_nodes.end(); ci++)
		{
			const SAS_Plus::ReachableDTGNode* reachable_dtg_node = *ci;
			
			Graphviz::printToDot(ofs, *reachable_node);
			ofs << " -> ";
			Graphviz::printToDot(ofs, *reachable_dtg_node);
			ofs << std::endl;
		}
	}
	ofs << "}" << std::endl;
	ofs.close();
}

};
