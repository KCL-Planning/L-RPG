#include "dtg_node.h"

#include <boost/lambda/lambda.hpp>
#include <boost/lambda/bind.hpp>

#include "dtg_graph.h"
#include "dtg_manager.h"
#include "transition.h"
#include "property_space.h"

#include "../type_manager.h"
#include "../predicate_manager.h"
#include "../action_manager.h"
#include "../term_manager.h"
#include "../formula.h"
#include "../parser_utils.h"
#include "../plan_bindings.h"
#include "../bindings_propagator.h"
#include "../plan.h"

namespace MyPOP {

namespace SAS_Plus {

DomainTransitionGraphNode::DomainTransitionGraphNode(DomainTransitionGraph& dtg, unsigned int unique_id)
	: dtg_(&dtg)
{
	unique_ids_.push_back(unique_id);
}

DomainTransitionGraphNode::DomainTransitionGraphNode(const DomainTransitionGraphNode& dtg_node, bool copy_transitions)
{
	// We take the same atom and bindings as the template we copy all the information from.
	// NOTE: This needs to change, the clone might not be linked to the same DTG!
	dtg_ = dtg_node.dtg_;
	unique_ids_.insert(unique_ids_.end(), dtg_node.unique_ids_.begin(), dtg_node.unique_ids_.end());
	possible_actions_= dtg_node.possible_actions_;
	
	copyAtoms(dtg_node);

	// Copy all the transitions, but make sure the source and destination are altered to this node.
	if (copy_transitions)
	{
//		std::cout << "Copy transitions..." << std::endl;
		for (std::vector<const Transition*>::const_iterator ci = dtg_node.transitions_.begin(); ci != dtg_node.transitions_.end(); ci++)
		{
			const Transition* transition = *ci;
			
			// Make sure to copy circular references correctly.
			DomainTransitionGraphNode* to_node = NULL;
			if (&transition->getToNode() == &dtg_node)
			{
				to_node = this;
			}
			else
			{
				to_node = &transition->getToNode();
			}

			addTransition(transition->getEnablers(), transition->getStep()->getAction(), *to_node);
		}

		// Search for all nodes which have a transitions to this node.
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_->getNodes().begin(); ci != dtg_->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* existing_dtg_node = *ci;
			if (existing_dtg_node == &dtg_node)
			{
				continue;
			}

			std::vector<const Transition*> existing_transitions = existing_dtg_node->getTransitions();
			for (std::vector<const Transition*>::const_iterator ci = existing_transitions.begin(); ci != existing_transitions.end(); ci++)
			{
				const Transition* existing_transition = *ci;

				if (&existing_transition->getToNode() == &dtg_node)
				{
//					std::cout << "Add a new transition from " << *existing_dtg_node << " to " << *this << std::endl;
					existing_dtg_node->addTransition(existing_transition->getEnablers(), existing_transition->getStep()->getAction(), *this);
//					std::cout << "Result: " << *existing_dtg_node << std::endl;
				}
			}
		}
//		std::cout << "Done copying transitions..." << std::endl;
	}
}

DomainTransitionGraphNode::DomainTransitionGraphNode(const DomainTransitionGraphNode& dtg_node, DomainTransitionGraph& dtg)
{
	dtg_ = &dtg;
	unique_ids_.insert(unique_ids_.end(), dtg_node.unique_ids_.begin(), dtg_node.unique_ids_.end());
	possible_actions_ = dtg_node.possible_actions_;
	copyAtoms(dtg_node);
}

void DomainTransitionGraphNode::copyAtoms(const DomainTransitionGraphNode& dtg_node)
{
	// Construct a new atoms equal to the atoms used by dtg node. We make a copy of the terms as
	// this makes it easier to clean up afterwards (delete all terms in the destructor).
	for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.atoms_.begin(); ci != dtg_node.atoms_.end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		dtg_node.getIndex(*bounded_atom);
		StepID org_step_id = (*ci)->getId();
		const Atom& org_atom = (*ci)->getAtom();

		std::vector<const Term*>* new_terms = new std::vector<const Term*>();
		for (std::vector<const Term*>::const_iterator ci = org_atom.getTerms().begin(); ci != org_atom.getTerms().end(); ci++)
		{
			// We know that all terms are variables, so this is just a sanity check.
			const Term* term = *ci;
//			assert(term->asVariable());
			
			new_terms->push_back(new Variable(*term->getType(), term->getName()));
		}
		const Atom* new_atom = new Atom(org_atom.getPredicate(), *new_terms, org_atom.isNegative());
		StepID new_step_id = dtg_->getBindings().createVariableDomains(*new_atom);

		addAtom(new BoundedAtom(new_step_id, *new_atom, bounded_atom->getProperty()), dtg_node.getIndex(*bounded_atom));

		// Update the variable domains.
		// NOTE: Due to the nature of this function we cannot update the equal to variables as we do not copy these
		// relations. While this means this copy will be completely unaffected by any changes to the original and visa
		// versa we do loose this amount of information.
		for (unsigned int i = 0; i < new_atom->getTerms().size(); i++)
		{
			const Term* term = new_atom->getTerms()[i];
			const Term* old_term = org_atom.getTerms()[i];
//			assert (term->isVariable());
//			assert (old_term->isVariable());
			
			// Make sure the new domain transition graph is not connected to the same variable domain, but 
			// have the same objects in their domain.
			term->makeDomainEqualTo(new_step_id, *old_term, org_step_id, dtg_->getBindings());
//			VariableDomain& variable_domain = dtg_->getBindings().getNonConstVariableDomain(new_step_id, *term->asVariable());
//			variable_domain.makeEqualTo(dtg_->getBindings().getVariableDomain(org_step_id, *old_term->asVariable()).getDomain());
		}	
	}
}

DomainTransitionGraphNode::~DomainTransitionGraphNode()
{
	// Delete the transitions.
	for (std::vector<const Transition*>::iterator i = transitions_.begin(); i != transitions_.end(); i++)
	{
		delete *i;
	}
	
	// Delete all transaction to this node.
	const std::vector<DomainTransitionGraphNode*>& dtg_nodes = dtg_->getNodes();
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes.begin(); ci != dtg_nodes.end(); ci++)
	{
		DomainTransitionGraphNode* existing_dtg_node = *ci;
		if (existing_dtg_node == this)
		{
			continue;
		}

		// Very inefficient, but don't care for now!
		bool is_deleted = true;
		while (is_deleted)
		{
			is_deleted = false;
			std::vector<const Transition*>& existing_dtg_node_transitions = existing_dtg_node->transitions_;
			for (std::vector<const Transition*>::iterator transitions_ci = existing_dtg_node_transitions.begin(); transitions_ci != existing_dtg_node_transitions.end(); transitions_ci++)
			{
				const Transition* existing_transition = *transitions_ci;
				if (&existing_transition->getToNode() == this)
				{
					delete existing_transition;
					existing_dtg_node_transitions.erase(transitions_ci);
					is_deleted = true;
					break;
				}
			}
		}
	}

	for (std::vector<BoundedAtom*>::iterator i = atoms_.begin(); i != atoms_.end(); i++)
	{
		delete *i;
	}
}

void DomainTransitionGraphNode::addAtom(BoundedAtom* bounded_atom, InvariableIndex index)
{
	std::cout << "Add the atom: ";
	bounded_atom->print(std::cout, dtg_->getBindings());
	std::cout << " to : " << *this << std::endl;
	
	// Testing...
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		if (bounded_atom->isMutexWith(**ci))
		{
			bounded_atom->getAtom().print(std::cout);
			std::cout << "(" << index << ") and ";
			(*ci)->getAtom().print(std::cout);
			std::cout << "(" << getIndex(**ci) << ") are mutex!" << std::endl;
			assert (false);
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		const BoundedAtom* existing_bounded_atom = *ci;
		if (getIndex(*existing_bounded_atom) == index)
		{
			if (dtg_->getBindings().canUnify(existing_bounded_atom->getAtom(), existing_bounded_atom->getId(), bounded_atom->getAtom(), bounded_atom->getId()))
			{
				std::cout << "Adding the atom: ";
				bounded_atom->print(std::cout, dtg_->getBindings());
				std::cout << " inpossible, because it intersects with existing atom: ";
				existing_bounded_atom->print(std::cout, dtg_->getBindings());
				std::cout << std::endl;
				
				assert (false);
			}
		}
	}

	// Check if the variable domain  of the i'th variable is bounded to the others. Do this only if they form part of the same
	// property space.
	if (bounded_atom->getProperty() != NULL)
	{
		for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
		{
			const BoundedAtom* reference_bounded_atom = *ci;
			if (reference_bounded_atom->getProperty() != NULL)
			{
				if (&reference_bounded_atom->getProperty()->getPropertyState().getPropertySpace() == &bounded_atom->getProperty()->getPropertyState().getPropertySpace())
				{
					const Term* reference_term = reference_bounded_atom->getAtom().getTerms()[getIndex(*reference_bounded_atom)];
					const Term* domain_term = bounded_atom->getAtom().getTerms()[index];
					
					if (!reference_term->isTheSameAs(reference_bounded_atom->getId(), *domain_term, bounded_atom->getId(), dtg_->getBindings()))
					{
			//			std::cout << "Bind: ";
			//			reference->print(std::cout, dtg_->getBindings());
			//			std::cout << "(" << getIndex(*reference) << ") with: ";
			//			bounded_atom->print(std::cout, dtg_->getBindings());
			//			std::cout << "(" << index << ")" << std::endl;

						assert (reference_term->unify(reference_bounded_atom->getId(), *domain_term, bounded_atom->getId(), dtg_->getBindings()));
					}
					assert (reference_term->isTheSameAs(reference_bounded_atom->getId(), *domain_term, bounded_atom->getId(), dtg_->getBindings()));
				}
			}
		}
	}

	atoms_.push_back(bounded_atom);
	indexes_[bounded_atom] = index;
}

bool DomainTransitionGraphNode::merge(const DomainTransitionGraphNode& other)
{
//	dtg_->mergePredicates(other.getDTG());
	
	// Copy all atoms from the given node to this one.
	bool merged = false;
	for (std::vector<BoundedAtom*>::const_iterator ci = other.getAtoms().begin(); ci != other.getAtoms().end(); ci++)
	{
		BoundedAtom* other_bounded_atom = *ci;
		InvariableIndex other_index = other.getIndex(*other_bounded_atom);

		// Make sure we don't add an entry twice.
		bool already_present = false;
		for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
		{
			BoundedAtom* bounded_atom = *ci;
			InvariableIndex index = getIndex(*bounded_atom);
			
			if (index == other_index && dtg_->getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), other_bounded_atom->getAtom(), other_bounded_atom->getId(), &other.getDTG().getBindings()))
			{
				std::cout << "The bounded atom to add: ";
				other_bounded_atom->print(std::cout, other.getDTG().getBindings());
				std::cout << " already exists: ";
				bounded_atom->print(std::cout, getDTG().getBindings());
				std::cout << std::endl;
///				already_present = true;

				break;
			}
		}
		
		if (already_present) continue;
		
		// We assert that no bindings have been made at this stage.
		StepID new_atom_id = dtg_->getBindings().createVariableDomains(other_bounded_atom->getAtom());
		BoundedAtom* bounded_atom = new BoundedAtom(new_atom_id, other_bounded_atom->getAtom(), other_bounded_atom->getProperty());
		
		// Make sure the new atom has the same values as the original.
		for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
		{
			const Term* bounded_term = bounded_atom->getAtom().getTerms()[i];
			const Term* other_bounded_term = other_bounded_atom->getAtom().getTerms()[i];
			bounded_term->makeDomainEqualTo(bounded_atom->getId(), *other_bounded_term, other_bounded_atom->getId(), dtg_->getBindings(), &other.getDTG().getBindings());
		}
		
		merged = true;
		atoms_.push_back(bounded_atom);
		indexes_[bounded_atom] = other_index;
	}
	
	/**
	 * If the given node has been merged with this one, we must also merge the possible transitions and unique ids.
	 */
	if (merged)
	{
		for (std::vector<unsigned int>::const_iterator ci = other.unique_ids_.begin(); ci != other.unique_ids_.end(); ci++)
		{
			bool is_new = true;
			unsigned int other_id = *ci;
			for (std::vector<unsigned int>::const_iterator ci = unique_ids_.begin(); ci != unique_ids_.end(); ci++)
			{
				if (other_id == *ci)
				{
					is_new = false;
					break;
				}
			}
			
			if (is_new)
			{
				unique_ids_.push_back(other_id);
			}
		}
		
		possible_actions_.insert(other.possible_actions_.begin(), other.possible_actions_.end());
	}
	
	// TEST
	// Make sure all the indexes are accounted for.
	for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
	{
		BoundedAtom* bounded_atom = *ci;
		getIndex(*bounded_atom);
	}
	
	return merged;
}

void DomainTransitionGraphNode::removeAtom(const BoundedAtom& bounded_atom)
{
	for (std::vector<BoundedAtom*>::iterator i = atoms_.begin(); i != atoms_.end(); i++)
	{
		const BoundedAtom* ba = *i;
		if (ba == &bounded_atom)
		{
			atoms_.erase(i);
			break;
		}
	}

	indexes_.erase(&bounded_atom);
}

InvariableIndex DomainTransitionGraphNode::getIndex(const BoundedAtom& atom) const
{
	std::map<const BoundedAtom*, InvariableIndex>::const_iterator ci = indexes_.find(&atom);
	if (ci == indexes_.end())
	{
		std::cout << "This bounded atom is not known!" << std::endl;
		assert(false);
	}

	return (*ci).second;
}

InvariableIndex DomainTransitionGraphNode::getIndex(StepID id, const Atom& atom) const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		const BoundedAtom* dtg_node_atom = *ci;
		for (std::vector<const Term*>::const_iterator ci = dtg_node_atom->getAtom().getTerms().begin(); ci != dtg_node_atom->getAtom().getTerms().end(); ci++)
		{
			const Term* dtg_atom_term = *ci;
			
			/**
			 * Check if this variable domain is connected to any of the given atom's terms.
			 */
			for (unsigned int i = 0; i < atom.getTerms().size(); i++)
			{
				const Term* term = atom.getTerms()[i];
				if (term->isTheSameAs(id, *dtg_atom_term, dtg_node_atom->getId(), dtg_->getBindings()))
				{
					return i;
				}
			}
		}
	}
	/*
	std::cout << "This bounded atom is not known!" << std::endl;
	atom.print(std::cout, dtg_->getBindings(), id);
	std::cout << std::endl;
	print(std::cout);
	std::cout << std::endl;
	*/
	//assert (false);
	return std::numeric_limits<unsigned int>::max();
}

bool DomainTransitionGraphNode::operator==(const DomainTransitionGraphNode& dtg_node) const
{
	if (dtg_node.getAtoms().size() != getAtoms().size())
	{
		return false;
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		const BoundedAtom* matching_atom = NULL;
		const BoundedAtom* atom = *ci;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.atoms_.begin(); ci != dtg_node.atoms_.end(); ci++)
		{
			const BoundedAtom* other_atom = *ci;
			
			// Check if they share the same predicate and if they link to the same invariable.
			if (atom->getAtom().getPredicate() == other_atom->getAtom().getPredicate() &&
			    getIndex(*atom) == dtg_node.getIndex(*other_atom))
			{
				matching_atom = other_atom;
				break;
			}
		}
		
		// If no matching atom was found the nodes are not the same.
		if (matching_atom == NULL)
		{
			return false;
		}
		
		// Next we check if the variable domains are equal.
		for (unsigned int i = 0; i < atom->getAtom().getArity(); i++)
		{
			const Term* term = atom->getAtom().getTerms()[i];
			const Term* matching_term = matching_atom->getAtom().getTerms()[i];
			
			// NOTE: Inefficient.
			std::vector<const Object*> term_domain = term->getDomain(atom->getId(), dtg_->getBindings());
			std::vector<const Object*> matching_domain = matching_term->getDomain(matching_atom->getId(), dtg_->getBindings());

			if (term_domain.size() != matching_domain.size())
			{
				return false;
			}
			
			std::sort(term_domain.begin(), term_domain.end());
			std::sort(matching_domain.begin(), matching_domain.end());
			std::vector<const Object*> intersection(term_domain.size());
			
			std::set_intersection(term_domain.begin(), term_domain.end(), matching_domain.begin(), matching_domain.end(), intersection.end());
			
			if (intersection.size() != term_domain.size())
			{
				return false;
			}
		}
	}
	
	// All tests were passed so the nodes must be the same.
	return true;
}

bool DomainTransitionGraphNode::groundTerm(std::vector<DomainTransitionGraphNode*>& grounded_nodes, const Term& term_to_ground, StepID term_id) const
{
	std::cout << "[DomainTransitionGraphNode::groundTerm] Ground the term: ";
	term_to_ground.print(std::cout, dtg_->getBindings(), term_id);
	std::cout << "(" << &term_to_ground.getDomain(term_id, dtg_->getBindings()) << ") in the node : " << *this << std::endl;
	
	const std::vector<const Object*>& domain = term_to_ground.getDomain(term_id, dtg_->getBindings());
	
	for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
	{
		const Object* object_to_ground_to = *ci;
		DomainTransitionGraphNode* new_node = new DomainTransitionGraphNode(*this, false);
		
		for (unsigned int i = 0; i < atoms_.size(); i++)
		{
			const BoundedAtom* bounded_atom = atoms_[i];
			
			// Check which of these variables need to be grounded.
			for (unsigned int j = 0; j < bounded_atom->getAtom().getTerms().size(); j++)
			{
				const Term* term = bounded_atom->getAtom().getTerms()[j];
				
				if (term->isTheSameAs(bounded_atom->getId(), term_to_ground, term_id, dtg_->getBindings()))
				{
					std::cout << "GROUND : ";
					term->print(std::cout, dtg_->getBindings(), bounded_atom->getId());
					std::cout << std::endl;
					const BoundedAtom* bounded_atom_to_ground = new_node->getAtoms()[i];
					bounded_atom_to_ground->getAtom().getTerms()[j]->unify(bounded_atom_to_ground->getId(), *object_to_ground_to, term_id, dtg_->getBindings());
				}
			}
		}
		
		grounded_nodes.push_back(new_node);
	}
	return grounded_nodes.size() > 0;
}

bool DomainTransitionGraphNode::addTransition(const std::vector<BoundedAtom>& enablers, const Action& action, DomainTransitionGraphNode& to_node)
{
	//std::cout << "[DomainTransitionGraphNode::addTransition] " << action << " from " << *this << " to " << to_node << std::endl;
	Transition* transition = Transition::createTransition(enablers, action, *this, to_node, dtg_->getDTGManager().getInitialFacts());
	if (transition == NULL || !addTransition(*transition, false))
	{
	//	std::cout << "[DomainTransitionGraphNode::addTransition] FAIL!" << std::endl;
		return false;
	}

	//std::cout << "[DomainTransitionGraphNode::addTransition] Result!" << *this << std::endl;
	return true;
}


bool DomainTransitionGraphNode::addTransition(const Transition& transition, bool update_possible_transitions)
{
//	std::cout << "[DomainTransitionGraphNode::addTransition] " << transition.getStep()->getAction() << std::endl;
	assert (&transition.getFromNode().getDTG() == &transition.getToNode().getDTG());

	// Make sure this transition is actually valid.

	// Make sure a transition with the same action doesn't already exist!
	StepID new_transition_step_id = transition.getStep()->getStepId();
	const Bindings& bindings = transition.getFromNode().getDTG().getBindings();
	for (std::vector<const Transition*>::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
	{
		const Transition* existing_transition = *ci;
		StepID existing_transition_step_id = existing_transition->getStep()->getStepId();

//		std::cout << "Compare ";
//		existing_transition->getStep()->getAction().print(std::cout, bindings, existing_transition->getStep()->getStepId());
//		std::cout << " v.s. ";
//		transition.getStep()->getAction().print(std::cout, bindings, transition.getStep()->getStepId());
//		std::cout << std::endl;

		if (&existing_transition->getStep()->getAction() == &transition.getStep()->getAction() &&
		    &existing_transition->getToNode() == &transition.getToNode())
		{
			// Check if these actions are identical.
			const std::vector<const Variable*>& existing_action_variables = existing_transition->getStep()->getAction().getVariables();
			const std::vector<const Variable*>& transition_action_variables = transition.getStep()->getAction().getVariables();

			bool are_identical = true;
			for (unsigned int i = 0; i < existing_action_variables.size(); i++)
			{
//				if (!bindings.canUnify(*existing_action_variables[i], existing_transition_step_id, *transition_action_variables[i], new_transition_step_id)
				if (existing_action_variables[i]->canUnify(existing_transition_step_id, *transition_action_variables[i], new_transition_step_id, bindings) ||
				    bindings.getVariableDomain(existing_transition_step_id, *existing_action_variables[i]).getDomain().size() != bindings.getVariableDomain(new_transition_step_id, *transition_action_variables[i]).getDomain().size())
				{
					are_identical = false;
					break;
				}
			}

			if (are_identical)
			{
//				std::cout << "[DomainTransitionGraphNode::addTransition] FAIL! Transition already exists..." << *this << std::endl;
				return false;
			}
		}
	}
	transitions_.push_back(&transition);
	
	if (update_possible_transitions)
	{
		// Only called when the first transitions are added. Are then only updated with the copy constructor.
		///assert (transition.getToNode().unique_ids_.size() == 1);
		possible_actions_.insert(std::make_pair(transition.getToNode().unique_ids_[0], &transition.getStep()->getAction()));
	}
	
	return true;
}

bool DomainTransitionGraphNode::removeTransition(const Transition& transition)
{
	for (std::vector<const Transition*>::iterator i = transitions_.begin(); i != transitions_.end(); i++)
	{
		if (*i == &transition)
		{
			transitions_.erase(i);
			return true;
		}
	}

	return false;
}

void DomainTransitionGraphNode::removeTransitions(bool reset_cached_actions)
{
	transitions_.clear();
	
	if (reset_cached_actions)
	{
		possible_actions_.clear();
	}
}

bool DomainTransitionGraphNode::containsEmptyVariableDomain() const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
		{
			const Term* term = *ci;
			if (term->getDomain(bounded_atom->getId(), dtg_->getBindings()).empty())
			{
				return true;
			}
		}
	}
	
	return false;
}

void DomainTransitionGraphNode::removeUnsupportedTransitions()
{
	for (std::vector<const Transition*>::reverse_iterator i = transitions_.rbegin(); i != transitions_.rend(); i++)
	{
		const Transition* transition = *i;
		
		std::vector<const Atom*> preconditions;
		Utility::convertFormula(preconditions, &transition->getStep()->getAction().getPrecondition());
		
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;
			if (precondition->getPredicate().isStatic())
			{
				continue;
			}
			
			// If the precondition is not static, search for a DTG node which supports it.
			if (!dtg_->getDTGManager().isSupported(transition->getStep()->getStepId(), *precondition, dtg_->getBindings()))
			{
//				std::cout << "!!! ";
//				transition->getStep()->getAction().print(std::cout, dtg_->getBindings(), transition->getStep()->getStepId());
//				std::cout << " is not supported!" << std::endl;
				
//				precondition->print(std::cout, dtg_->getBindings(), transition->getStep()->getStepId());
//				std::cout << std::endl;
				removeTransition(**i);
				break;
			}
		}
	}
}

void DomainTransitionGraphNode::getPossibleActions(std::vector<const Action*>& possible_actions, const DomainTransitionGraphNode& dtg_node) const
{
	for (std::vector<unsigned int>::const_iterator ci = dtg_node.unique_ids_.begin(); ci != dtg_node.unique_ids_.end(); ci++)
	{
		std::pair<std::multimap<unsigned int, const Action*>::const_iterator, std::multimap<unsigned int, const Action*>::const_iterator> possible_actions_iterators = possible_actions_.equal_range(*ci);
		for (std::multimap<unsigned int, const Action*>::const_iterator ci = possible_actions_iterators.first; ci != possible_actions_iterators.second; ci++)
		{
			const Action* possible_action = (*ci).second;
			bool exists = false;
			for (std::vector<const Action*>::const_iterator ci = possible_actions.begin(); ci != possible_actions.end(); ci++)
			{
				if (possible_action == *ci)
				{
					exists = true;
					break;
				}
			}
			
			if (!exists)
			{
				possible_actions.push_back(possible_action);
			}
		}
	}
}

bool DomainTransitionGraphNode::isSupported(unsigned int id, const Atom& atom, const Bindings& bindings) const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
	{
		if (dtg_->getBindings().canUnify((*ci)->getAtom(), (*ci)->getId(), atom, id, &bindings))
		{
			return true;
		}
	}
	
	return false;
}

void DomainTransitionGraphNode::print(std::ostream& os) const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
	{
		(*ci)->getAtom().print(os, getDTG().getBindings(), (*ci)->getId());
		os << "(" << getIndex(**ci) << ")";
	}
}

std::ostream& operator<<(std::ostream& os, const DomainTransitionGraphNode& node)
{
/*	os << "%";
	for (std::vector<unsigned int>::const_iterator ci = node.unique_ids_.begin(); ci != node.unique_ids_.end(); ci++)
	{
		os << *ci << "  ";
	}
	os << "%";*/
	
	for (std::vector<BoundedAtom*>::const_iterator ci = node.getAtoms().begin(); ci != node.getAtoms().end(); ci++)
	{
		(*ci)->getAtom().print(os, node.getDTG().getBindings(), (*ci)->getId());
		os << "(" << node.getIndex(**ci) << ")";
	}

	for (std::vector<const Transition*>::const_iterator ci = node.transitions_.begin(); ci != node.transitions_.end(); ci++)
	{
		os << std::endl;
		const Transition* transition = *ci;
		os << "\t -> ";

		for (std::vector<BoundedAtom*>::const_iterator ci = transition->getToNode().getAtoms().begin(); ci != transition->getToNode().getAtoms().end(); ci++)
		{
			(*ci)->getAtom().print(os, node.getDTG().getBindings(), (*ci)->getId());
			//(*ci)->getAtom().print(os);
			os << "(" << transition->getToNode().getIndex(**ci) << ")";
		}

		os << " [";
		transition->getStep()->getAction().print(os, node.getDTG().getBindings(), transition->getStep()->getStepId());
		//os << transition->getStep()->getAction();
		os << "]";

/*		const std::vector<BoundedAtom>& enablers = transition->getEnablers();
		os << "; Enablers: ";
		for (std::vector<BoundedAtom>::const_iterator enabler_ci = enablers.begin(); enabler_ci != enablers.end(); enabler_ci++)
		{
			(*enabler_ci).second->print(os);
			if (enabler_ci + 1 != enablers.end())
			{
				os << ", ";
			}
		}*/
	}
	
/*	os << " -=> ";
	for (std::multimap<unsigned int, const Action*>::const_iterator ci = node.possible_actions_.begin(); ci != node.possible_actions_.end(); ci++)
	{
		std::cout << "$ " << (*ci).first << " -> " << *(*ci).second << std::endl;
	}
	os << " <=-";*/
	return os;
}

};

};

