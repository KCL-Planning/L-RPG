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

///#define MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_DEBUG
//#define MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS

namespace MyPOP {

namespace SAS_Plus {

DomainTransitionGraphNode::DomainTransitionGraphNode(DomainTransitionGraph& dtg, unsigned int unique_id)
	: dtg_(&dtg)
{
	unique_ids_.push_back(unique_id);
}

DomainTransitionGraphNode::DomainTransitionGraphNode(const DomainTransitionGraphNode& dtg_node)
	: dtg_(dtg_node.dtg_)
{
	// We take the same atom and bindings as the template we copy all the information from.
	// NOTE: This needs to change, the clone might not be linked to the same DTG!
	unique_ids_.insert(unique_ids_.end(), dtg_node.unique_ids_.begin(), dtg_node.unique_ids_.end());
	
	copyAtoms(dtg_node);
}

DomainTransitionGraphNode::DomainTransitionGraphNode(const DomainTransitionGraphNode& dtg_node, DomainTransitionGraph& dtg)
	: dtg_(&dtg)
{
	unique_ids_.insert(unique_ids_.end(), dtg_node.unique_ids_.begin(), dtg_node.unique_ids_.end());
	copyAtoms(dtg_node);
}

void DomainTransitionGraphNode::copyAtoms(const DomainTransitionGraphNode& dtg_node)
{
	// Construct a new atoms equal to the atoms used by dtg node. We make a copy of the terms as
	// this makes it easier to clean up afterwards (delete all terms in the destructor).
	for (std::vector<BoundedAtom*>::const_iterator dtg_node_ci = dtg_node.atoms_.begin(); dtg_node_ci != dtg_node.atoms_.end(); dtg_node_ci++)
	{
		const BoundedAtom* bounded_atom = *dtg_node_ci;
		StepID org_step_id = bounded_atom->getId();
		const Atom& org_atom = bounded_atom->getAtom();

		std::vector<const Term*>* new_terms = new std::vector<const Term*>();
		for (std::vector<const Term*>::const_iterator ci = org_atom.getTerms().begin(); ci != org_atom.getTerms().end(); ci++)
		{
			// We know that all terms are variables, so this is just a sanity check.
			const Term* term = *ci;
			
			new_terms->push_back(new Variable(*term->getType(), term->getName()));
		}
		const Atom* new_atom = new Atom(org_atom.getPredicate(), *new_terms, org_atom.isNegative(), true);
		StepID new_step_id = dtg_->getBindings().createVariableDomains(*new_atom);

		BoundedAtom* new_fact = new BoundedAtom(new_step_id, *new_atom, bounded_atom->getProperties());
		addAtom(*new_fact, dtg_node.getIndex(*bounded_atom));

		// Update the variable domains.
		// NOTE: Due to the nature of this function we cannot update the equal to variables as we do not copy these
		// relations. While this means this copy will be completely unaffected by any changes to the original and visa
		// versa we do loose this amount of information.
		for (unsigned int i = 0; i < new_atom->getTerms().size(); i++)
		{
			const Term* term = new_atom->getTerms()[i];
			const Term* old_term = org_atom.getTerms()[i];
			
			if (dtg_node.grounded_terms_.find(old_term) != dtg_node.grounded_terms_.end())
			{
				grounded_terms_.insert(term);
			}
			
			// Make sure the new domain transition graph is not connected to the same variable domain, but 
			// have the same objects in their domain.
			term->makeDomainEqualTo(new_step_id, *old_term, org_step_id, dtg_->getBindings(), &dtg_node.getDTG().getBindings());

			// Check if this term was equal to another term in the original dtg node. If so we must 
			// preserve this link.
			for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.atoms_.begin(); ci != dtg_node_ci; ci++)
			{
				const BoundedAtom* org_bounded_atom = *ci;
				
				for (unsigned int j = 0; j < org_bounded_atom->getAtom().getArity(); j++)
				{
					if (org_bounded_atom == bounded_atom && i == j)
					{
						continue;
					}
					
					if (old_term->isTheSameAs(bounded_atom->getId(), *org_bounded_atom->getAtom().getTerms()[j], org_bounded_atom->getId(), dtg_node.getDTG().getBindings()))
					{
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
						std::cout << "Unify: ";
						old_term->print(std::cout, dtg_->getBindings(), bounded_atom->getId());
						std::cout << " with ";
						org_bounded_atom->getAtom().getTerms()[j]->print(std::cout, dtg_->getBindings(), org_bounded_atom->getId());
						std::cout << "." << std::endl;
#endif
						
						const BoundedAtom* atom_with_matching_term = atoms_[std::distance(dtg_node.atoms_.begin(), ci)];
						term->unify(new_step_id, *atom_with_matching_term->getAtom().getTerms()[j], atom_with_matching_term->getId(), dtg_->getBindings());
					}
				}
			}
		}
	}
}

DomainTransitionGraphNode::~DomainTransitionGraphNode()
{
	if (transitions_.size() > 0)
	{
		for (unsigned int i = 0; i < transitions_.size() - 1; i++)
		{
			for (unsigned int j = i + 1; j < transitions_.size(); j++)
			{
				assert (transitions_[i] != transitions_[j]);
			}
		}
	}
	
	// Delete the transitions.
	for (std::vector<const Transition*>::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
	{
		delete *ci;
	}

	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		dtg_->getBindings().removeBindings((*ci)->getId());
		delete *ci;
	}
}

bool DomainTransitionGraphNode::contains(StepID id, const Atom& atom, InvariableIndex index) const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		const BoundedAtom* existing_bounded_atom = *ci;
		if (getIndex(*existing_bounded_atom) == index)
		{
			if (dtg_->getBindings().canUnify(existing_bounded_atom->getAtom(), existing_bounded_atom->getId(), atom, id))
			{
				return true;
			}
		}
	}
	return false;
}

bool DomainTransitionGraphNode::containsExactCopyOf(const BoundedAtom& bounded_atom) const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		const BoundedAtom* existing_bounded_atom = *ci;
		
		if (dtg_->getBindings().areIdentical(existing_bounded_atom->getAtom(), existing_bounded_atom->getId(), bounded_atom.getAtom(), bounded_atom.getId()))
		{
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
			bounded_atom.getAtom().print(std::cout, dtg_->getBindings(), bounded_atom.getId());
#endif
			return true;
		}
	}
	return false;
}

bool DomainTransitionGraphNode::addAtom(BoundedAtom& bounded_atom, InvariableIndex index)
{
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
	std::cout << "Add the atom: ";
	bounded_atom.print(std::cout, dtg_->getBindings());
	std::cout << "(" << index << ") to : " << *this << std::endl;
#endif
	
	// Testing...
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		if (bounded_atom.isMutexWith(**ci, dtg_->getBindings()))
		{
			bounded_atom.print(std::cout, dtg_->getBindings());
			std::cout << " and ";
			(*ci)->print(std::cout, dtg_->getBindings());
			std::cout << " are mutex!" << std::endl;
//			bounded_atom->getAtom().print(std::cout);
//			std::cout << "(" << index << ") and ";
//			(*ci)->getAtom().print(std::cout);
//			std::cout << "(" << getIndex(**ci) << ") are mutex!" << std::endl;
			assert (false);
		}
	}
	
	if (contains(bounded_atom.getId(), bounded_atom.getAtom(), index))
	{
		return false;
	}

	if (index != NO_INVARIABLE_INDEX)
	{
		// Check if the variable domain  of the i'th variable is bounded to the others. Do this only if they form part of the same
		// property space.
		for (std::vector<const Property*>::const_iterator ci = bounded_atom.getProperties().begin(); ci != bounded_atom.getProperties().end(); ci++)
		{
			const Property* new_property = *ci;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
			{
				const BoundedAtom* reference_bounded_atom = *ci;
				
				for (std::vector<const Property*>::const_iterator ci = reference_bounded_atom->getProperties().begin(); ci != reference_bounded_atom->getProperties().end(); ci++)
				{
					const Property* reference_property = *ci;
					
					if (&new_property->getPropertyState().getPropertySpace() == &reference_property->getPropertyState().getPropertySpace())
					{
						if (getIndex(*reference_bounded_atom) >= reference_bounded_atom->getAtom().getTerms().size())
						{
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
							std::cout << "Tried to add an atom to : " << std::endl << *this << std::endl;
							
							std::cout << "Could not find the index of the bounded atom: ";
							reference_bounded_atom->print(std::cout, dtg_->getBindings());
							std::cout << "." << std::endl;
#endif
							continue;
						}
						const Term* reference_term = reference_bounded_atom->getAtom().getTerms()[getIndex(*reference_bounded_atom)];
						const Term* domain_term = bounded_atom.getAtom().getTerms()[index];
						
						if (!reference_term->isTheSameAs(reference_bounded_atom->getId(), *domain_term, bounded_atom.getId(), dtg_->getBindings()))
						{
				//			std::cout << "Bind: ";
				//			reference->print(std::cout, dtg_->getBindings());
				//			std::cout << "(" << getIndex(*reference) << ") with: ";
				//			bounded_atom->print(std::cout, dtg_->getBindings());
				//			std::cout << "(" << index << ")" << std::endl;

#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_DEBUG
							assert (reference_term->unify(reference_bounded_atom->getId(), *domain_term, bounded_atom->getId(), dtg_->getBindings()));
#else
							reference_term->unify(reference_bounded_atom->getId(), *domain_term, bounded_atom.getId(), dtg_->getBindings());
#endif
						}
						assert (reference_term->isTheSameAs(reference_bounded_atom->getId(), *domain_term, bounded_atom.getId(), dtg_->getBindings()));
					}
				}
			}
		}
	}

	atoms_.push_back(&bounded_atom);
	indexes_[&bounded_atom] = index;
	return true;
}

void DomainTransitionGraphNode::removeAtom(const BoundedAtom& bounded_atom)
{
	for (std::vector<BoundedAtom*>::iterator i = atoms_.begin(); i != atoms_.end(); i++)
	{
		const BoundedAtom* ba = *i;
		if (ba == &bounded_atom)
		{
			atoms_.erase(i);
			delete ba;
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
	return NO_INVARIABLE_INDEX;
}

bool DomainTransitionGraphNode::canMap(const std::vector<const BoundedAtom*>& mapping) const
{
	bool mask[atoms_.size()];
	memset(&mask[0], false, sizeof(bool) * atoms_.size());
	
	return findMapping(mapping, 0, mask);
}

bool DomainTransitionGraphNode::findMapping(const std::vector<const BoundedAtom*>& mapping, unsigned int index, bool mask[]) const
{
	const BoundedAtom* atom_to_search_for = mapping[index];
	
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		unsigned int atom_index = std::distance(atoms_.begin(), ci);
		if (mask[atom_index]) continue;
		
		const BoundedAtom* dtg_node_fact = *ci;
//		if (dtg_->getBindings().canUnifyBoundedAtoms(*atom_to_search_for, *dtg_node_fact))
		if (atom_to_search_for->canUnifyWith(*dtg_node_fact, dtg_->getBindings()))
		{
			// If we have found a mapping for the last node we are done!
			if (index + 1 == mapping.size()) return true;
			
			// Otherwise bind the found mapping and try to find a mapping for the other nodes.
			bool new_mask[atoms_.size()];
			memcpy(new_mask, mask, sizeof(bool) * atoms_.size());
			new_mask[atom_index] = true;
			return findMapping(mapping, index + 1, new_mask);
		}
	}
	
	return false;
}

bool DomainTransitionGraphNode::canUnifyWith(const DomainTransitionGraphNode& other) const
{
//	std::cout << "Can unify: " << *this << " and " << node2 << "?" << std::endl;
	for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
	{
		BoundedAtom* bounded_atom1 = *ci;
		
		bool canUnify = false;
		for (std::vector<BoundedAtom*>::const_iterator ci = other.getAtoms().begin(); ci != other.getAtoms().end(); ci++)
		{
			BoundedAtom* bounded_atom2 = *ci;
			if (getDTG().getBindings().canUnify(bounded_atom1->getAtom(), bounded_atom1->getId(), bounded_atom2->getAtom(), bounded_atom2->getId(), &other.getDTG().getBindings()) &&
			    getIndex(*bounded_atom1) == other.getIndex(*bounded_atom2) &&
			    bounded_atom1->getAtom().isNegative() == bounded_atom2->getAtom().isNegative())
			{
				canUnify = true;
				break;
			}
		}

		// If one of the atoms cannot be unified, return false;
		if (!canUnify)
		{
			return false;
		}
	}

	// Make sure none of the atoms are mutually exclusive.
	if (getDTG().areMutex(*this, other))
	{
		return false;
	}

	return true;
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
	const std::vector<const Object*>& domain = term_to_ground.getDomain(term_id, dtg_->getBindings());
	bool found_term_to_ground = false;
	
	for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
	{
		const Object* object_to_ground_to = *ci;
		DomainTransitionGraphNode* new_node = new DomainTransitionGraphNode(*this);
		
		for (unsigned int i = 0; i < atoms_.size(); i++)
		{
			const BoundedAtom* bounded_atom = atoms_[i];
			
			// Check which of these variables need to be grounded.
			for (unsigned int j = 0; j < bounded_atom->getAtom().getTerms().size(); j++)
			{
				const Term* term = bounded_atom->getAtom().getTerms()[j];
				
				if (term->isTheSameAs(bounded_atom->getId(), term_to_ground, term_id, dtg_->getBindings()))
				{
					const BoundedAtom* bounded_atom_to_ground = new_node->getAtoms()[i];
					const Term* term_to_ground = bounded_atom_to_ground->getAtom().getTerms()[j];
					new_node->grounded_terms_.insert(term_to_ground);
					term_to_ground->unify(bounded_atom_to_ground->getId(), *object_to_ground_to, term_id, dtg_->getBindings());
					found_term_to_ground = true;
				}
			}
		}
		
		grounded_nodes.push_back(new_node);
		
		if (!found_term_to_ground) break;
	}
	return found_term_to_ground;
}

bool DomainTransitionGraphNode::groundTerms(std::vector<DomainTransitionGraphNode*>& grounded_nodes, const std::vector<const std::vector<const Object*>* >& variable_domains_to_ground, const std::map<const std::vector<const Object*>*, const Object*>& bound_objects) const
{
	/**
	 * If more than a single term needs to be grounded the pointers to the original terms will not refer to the actual terms
	 * to be grounded any more. Therefore all terms to be grounded are indexed so we know which one to ground regardless of
	 * where they are stored in memory.
	 */
	std::vector<std::pair<unsigned int, unsigned int> > terms_to_ground_pos;
	
	// We create a dummy node where we ground all the variables which need to be grounded and create clones from this one.
	DomainTransitionGraphNode* pre_grounded_node = new DomainTransitionGraphNode(*this);
	
	for (std::vector<const std::vector<const Object*>* >::const_iterator ci = variable_domains_to_ground.begin(); ci != variable_domains_to_ground.end(); ci++)
	{
		const std::vector<const Object*>* variable_domain_to_ground = *ci;
		
		// Identify which terms to ground.
		for (std::vector<BoundedAtom*>::const_iterator dtg_atoms_ci = atoms_.begin(); dtg_atoms_ci != atoms_.end(); dtg_atoms_ci++)
		{
			const BoundedAtom* bounded_atom = *dtg_atoms_ci;
			unsigned int dtg_atom_index = std::distance((std::vector<BoundedAtom*>::const_iterator)(atoms_.begin()), dtg_atoms_ci);
			
			for (unsigned int i = 0;  i < bounded_atom->getAtom().getArity(); i++)
			{
				const std::vector<const Object*>& variable_domain = bounded_atom->getVariableDomain(i, dtg_->getBindings());
				std::map<const std::vector<const Object*>*, const Object*>::const_iterator found_fixed_variable_domain = bound_objects.find(&variable_domain);
				
				// Check if we are forced to ground a variable domain to a certain object.
				if (found_fixed_variable_domain != bound_objects.end())
				{
					std::vector<const Object*> possible_object_set;
					possible_object_set.push_back((*found_fixed_variable_domain).second);
					pre_grounded_node->getAtoms()[dtg_atom_index]->getAtom().getTerms()[i]->makeDomainEqualTo(pre_grounded_node->getAtoms()[dtg_atom_index]->getId(), possible_object_set, dtg_->getBindings());
				}
				else if (&bounded_atom->getVariableDomain(i, dtg_->getBindings()) == variable_domain_to_ground)
				{
					terms_to_ground_pos.push_back(std::make_pair(dtg_atom_index, i));
				}
			}
		}
	}

	// Move on to actual grounding.
	std::vector<DomainTransitionGraphNode*> open_list;
	open_list.push_back(pre_grounded_node);
	bool did_ground_a_term = false;
	
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
	std::cout << "Process " << open_list.size() << " DTG nodes." << std::endl;
#endif
	
	for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = terms_to_ground_pos.begin(); ci != terms_to_ground_pos.end(); ci++)
	{
		unsigned int atom_index = (*ci).first;
		unsigned int term_index = (*ci).second;
		
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
		std::cout << "Ground the " << term_index << "th term of the " << atom_index << " atom." << std::endl;
#endif
		
		std::vector<DomainTransitionGraphNode*> grounded_nodes_tmp;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
		{
			DomainTransitionGraphNode* node_to_ground = *ci;

#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
			std::cout << "Process: " << std::endl << *node_to_ground << std::endl;
#endif
			
			const BoundedAtom* atom_to_ground = node_to_ground->getAtoms()[atom_index];
			const Term* term_to_ground = atom_to_ground->getAtom().getTerms()[term_index];
			
			if (node_to_ground->groundTerm(grounded_nodes_tmp, *term_to_ground, atom_to_ground->getId()))
			{
				did_ground_a_term = true;
			}
			delete node_to_ground;
		}
		open_list.clear();
		open_list.insert(open_list.end(), grounded_nodes_tmp.begin(), grounded_nodes_tmp.end());
		
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
		std::cout << "Temp results: " << std::endl;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_nodes_tmp.begin(); ci != grounded_nodes_tmp.end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			std::cout << *dtg_node << std::endl;
		}
#endif
	}
	grounded_nodes.insert(grounded_nodes.end(), open_list.begin(), open_list.end());

	return did_ground_a_term;
}

bool DomainTransitionGraphNode::groundTerms(std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > >& grounded_nodes, const std::vector<const std::vector<const Object*>* >& variable_domains_to_ground) const
{
	/**
	 * If more than a single term needs to be grounded the pointers to the original terms will not refer to the actual terms
	 * to be grounded any more. Therefore all terms to be grounded are indexed so we know which one to ground regardless of
	 * where they are stored in memory.
	 */
	std::vector<std::pair<unsigned int, unsigned int> > terms_to_ground_pos;
	
	for (std::vector<const std::vector<const Object*>* >::const_iterator ci = variable_domains_to_ground.begin(); ci != variable_domains_to_ground.end(); ci++)
	{
		const std::vector<const Object*>* variable_domain_to_ground = *ci;
		
		// Identify which terms to ground.
		for (std::vector<BoundedAtom*>::const_iterator dtg_atoms_ci = atoms_.begin(); dtg_atoms_ci != atoms_.end(); dtg_atoms_ci++)
		{
			const BoundedAtom* bounded_atom = *dtg_atoms_ci;
			
			for (unsigned int i = 0;  i < bounded_atom->getAtom().getArity(); i++)
			{
				if (&bounded_atom->getVariableDomain(i, dtg_->getBindings()) == variable_domain_to_ground)
				{
					terms_to_ground_pos.push_back(std::make_pair(std::distance((std::vector<BoundedAtom*>::const_iterator)(atoms_.begin()), dtg_atoms_ci), i));
				}
			}
		}
	}
	
	// Move on to actual grounding.
	std::vector<DomainTransitionGraphNode*> open_list;
//	open_list.push_back(this);
	open_list.push_back(new DomainTransitionGraphNode(*this));
	bool did_ground_a_term = false;
	
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
	std::cout << "Process " << open_list.size() << " DTG nodes." << std::endl;
#endif 
	
	for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = terms_to_ground_pos.begin(); ci != terms_to_ground_pos.end(); ci++)
	{
		unsigned int atom_index = (*ci).first;
		unsigned int term_index = (*ci).second;
		
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
		std::cout << "Ground the " << term_index << "th term of the " << atom_index << " atom." << std::endl;
#endif
		
		std::vector<DomainTransitionGraphNode*> grounded_nodes_tmp;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
		{
			DomainTransitionGraphNode* node_to_ground = *ci;

#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
			std::cout << "Process: " << std::endl << *node_to_ground << std::endl;
#endif
			
			const BoundedAtom* atom_to_ground = node_to_ground->getAtoms()[atom_index];
			const Term* term_to_ground = atom_to_ground->getAtom().getTerms()[term_index];
			
			if (node_to_ground->groundTerm(grounded_nodes_tmp, *term_to_ground, atom_to_ground->getId()))
			{
				did_ground_a_term = true;
			}
			delete node_to_ground;
		}
		open_list.clear();
		open_list.insert(open_list.end(), grounded_nodes_tmp.begin(), grounded_nodes_tmp.end());
		
#ifdef MYPOP_SAS_PLUS_DOMAIN_TRANSITION_GRAPH_NODE_COMMENTS
		std::cout << "Temp results: " << std::endl;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_nodes_tmp.begin(); ci != grounded_nodes_tmp.end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			std::cout << *dtg_node << std::endl;
		}
#endif
	}
	
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
	{
		DomainTransitionGraphNode* grounded_node = *ci;
		std::map<const std::vector<const Object*>*, const Object*>* grounded_variables = new std::map<const std::vector<const Object*>*, const Object*>();
		
		for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = terms_to_ground_pos.begin(); ci != terms_to_ground_pos.end(); ci++)
		{
			unsigned int atom_index = (*ci).first;
			unsigned int term_index = (*ci).second;
			(*grounded_variables)[&getAtoms()[atom_index]->getVariableDomain(term_index, dtg_->getBindings())] = grounded_node->getAtoms()[atom_index]->getVariableDomain(term_index, dtg_->getBindings())[0];
		}
		
		grounded_nodes.push_back(std::make_pair(grounded_node, grounded_variables));
	}
	return did_ground_a_term;
}

bool DomainTransitionGraphNode::addTransition(const Action& action, DomainTransitionGraphNode& to_node)
{
	//std::cout << "[DomainTransitionGraphNode::addTransition] " << action << " from " << *this << " to " << to_node << std::endl;
	Transition* transition = Transition::createTransition(action, *this, to_node);
	if (transition == NULL || !addTransition(*transition))
	{
	//	std::cout << "[DomainTransitionGraphNode::addTransition] FAIL!" << std::endl;
		return false;
	}

	//std::cout << "[DomainTransitionGraphNode::addTransition] Result!" << *this << std::endl;
	return true;
}


bool DomainTransitionGraphNode::addTransition(const Transition& transition)
{
	assert (&transition != NULL);
//	std::cout << "[DomainTransitionGraphNode::addTransition] " << transition.getStep()->getAction() << std::endl;
	assert (&transition.getFromNode().getDTG() == &transition.getToNode().getDTG());

	// Make sure this transition is actually valid.

	// Make sure a transition with the same action doesn't already exist!
	StepID new_transition_step_id = transition.getStepId();
	const Bindings& bindings = transition.getFromNode().getDTG().getBindings();
	for (std::vector<const Transition*>::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
	{
		const Transition* existing_transition = *ci;
		StepID existing_transition_step_id = existing_transition->getStepId();

//		std::cout << "Compare ";
//		existing_transition->getStep()->getAction().print(std::cout, bindings, existing_transition->getStep()->getStepId());
//		std::cout << " v.s. ";
//		transition.getStep()->getAction().print(std::cout, bindings, transition.getStep()->getStepId());
//		std::cout << std::endl;

		if (&existing_transition->getAction() == &transition.getAction() &&
		    &existing_transition->getToNode() == &transition.getToNode())
		{
			// Check if these actions are identical.
			const std::vector<const Variable*>& existing_action_variables = existing_transition->getAction().getVariables();
			const std::vector<const Variable*>& transition_action_variables = transition.getAction().getVariables();

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
	// NOTE: SolveSubSets actually adds transitions without cahnging the from node...
	//assert (&transition.getFromNode() == this);
	transitions_.push_back(&transition);
	
	return true;
}

bool DomainTransitionGraphNode::removeTransition(const Transition& transition)
{
	for (std::vector<const Transition*>::iterator i = transitions_.begin(); i != transitions_.end(); i++)
	{
		if (*i == &transition)
		{
			transitions_.erase(i);
			delete *i;
/*			for (std::vector<const Variable*>::const_iterator ci = transition.getStep()->getAction().getVariables().begin(); ci != transition.getStep()->getAction().getVariables().end(); ci++)
			{
				const Variable* variable = *ci;
				dtg_->getBindings().removeBindings(transition.getStep()->getStepId(), *variable);
			}*/
			return true;
		}
	}

	return false;
}

void DomainTransitionGraphNode::removeTransitions()
{
	// Remove all bindings as well!
	// TODO: Memory leak if not uncommented!
	for (std::vector<const Transition*>::iterator ci = transitions_.begin(); ci != transitions_.end(); ci++)
	{
		const Transition* transition = *ci;
		delete transition;
/*		StepID transition_id = transition->getStep()->getStepId();
		
		for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
		{
			const Variable* variable = *ci;
			dtg_->getBindings().removeBindings(transition_id, *variable);
		}
*/
	}
	transitions_.clear();
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

// Recursive function.
bool DomainTransitionGraphNode::validateTermMappings(std::vector<BoundedAtom*>::const_iterator begin,
                                                     std::vector<BoundedAtom*>::const_iterator end,
                                                     const std::vector<const Atom*>& initial_facts,
                                                     const std::map<const std::vector<const Object*>*, std::vector<const Object*>* >& term_mappings) const
{
	if (begin == end)
		return true;
	
	const BoundedAtom* bounded_atom = *begin;
	const Atom& dtg_node_atom = bounded_atom->getAtom();
	StepID dtg_node_atom_id = bounded_atom->getId();
	
	for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		const Atom* initial_fact = *ci;
		if (dtg_->getBindings().canUnify(*initial_fact, Step::INITIAL_STEP, dtg_node_atom, dtg_node_atom_id))
		{
			// Add this object to the DTGs objects! :)
			std::map<const std::vector<const Object*>*, std::vector<const Object*>* > new_term_mappings(term_mappings);
			
			// Check if the terms can be unified with the giving mappings.
			
			std::vector<std::vector<const Object*>* > domains_to_clean_up;
			
			bool can_be_mapped = true;
			for (unsigned int i = 0; i < dtg_node_atom.getArity(); i++)
			{
				const Term* bounded_term = dtg_node_atom.getTerms()[i];
				const std::vector<const Object*>& term_domain = bounded_term->getDomain(dtg_node_atom_id, dtg_->getBindings());
				const std::vector<const Object*>& initial_fact_domain = initial_fact->getTerms()[i]->getDomain(Step::INITIAL_STEP, dtg_->getBindings());

				bool domain_empty = true;
				
				std::vector<const Object*>* org_current_domain = new_term_mappings[&term_domain];
				//std::vector<const Object*> new_current_domain(*org_current_domain);
				std::vector<const Object*>* new_current_domain = new std::vector<const Object*>(*org_current_domain);
				domains_to_clean_up.push_back(new_current_domain);
				
				new_term_mappings[&term_domain] = new_current_domain;
				
				// Limit the domain to those objects present in both.
				for (std::vector<const Object*>::reverse_iterator ri = new_current_domain->rbegin(); ri != new_current_domain->rend(); ri++)
				{
					const Object* object = *ri;
					bool present = false;
					for (std::vector<const Object*>::const_iterator ci = initial_fact_domain.begin(); ci != initial_fact_domain.end(); ci++)
					{
						const Object* initial_object = *ci;
						if (initial_object == object)
						{
							present = true;
							domain_empty = false;
							break;
						}
					}
					
					if (!present)
					{
						new_current_domain->erase(ri.base() - 1);
					}
				}
				
				// If the domain has become empty, it is a false unification and ew need to break.
				if (domain_empty)
				{
					can_be_mapped = false;
					break;
				}
			}
			
			if (!can_be_mapped)
			{
				for (std::vector<std::vector<const Object*>* >::const_iterator ci = domains_to_clean_up.begin(); ci != domains_to_clean_up.end(); ci++)
				{
					delete *ci;
				}
				continue;
			}
			
			// Call the function recursively and try to unify with the next bounded atom.
			if (validateTermMappings(begin + 1, end, initial_facts, new_term_mappings))
			{
				for (std::vector<std::vector<const Object*>* >::const_iterator ci = domains_to_clean_up.begin(); ci != domains_to_clean_up.end(); ci++)
				{
					delete *ci;
				}
				return true;
			}
			
			for (std::vector<std::vector<const Object*>* >::const_iterator ci = domains_to_clean_up.begin(); ci != domains_to_clean_up.end(); ci++)
			{
				delete *ci;
			}
		}
	}
	return false;
}

void DomainTransitionGraphNode::getSubsets(std::vector<DomainTransitionGraphNode*>& subsets, const std::vector<DomainTransitionGraphNode*>& all_dtg_nodes) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = all_dtg_nodes.begin(); ci != all_dtg_nodes.end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		if (isSuperSetOf(*dtg_node))
		{
			subsets.push_back(dtg_node);
		}
	}
}

bool DomainTransitionGraphNode::isSuperSetOf(const DomainTransitionGraphNode& other) const
{
//	std::cout << "Check if ";
//	print(std::cout);
//	std::cout << " is a super set of ";
//	other.print(std::cout);
//	std::cout << std::endl;
	
	for (std::vector<BoundedAtom*>::const_iterator ci = other.getAtoms().begin(); ci != other.getAtoms().end(); ci++)
	{
		const BoundedAtom* other_bounded_atom = *ci;
		
		bool contains_super_set = false;
		for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
		{
			const BoundedAtom* this_bounded_atom = *ci;
			
			if (!getDTG().getBindings().canUnify(this_bounded_atom->getAtom(), this_bounded_atom->getId(), other_bounded_atom->getAtom(), other_bounded_atom->getId(), &other.getDTG().getBindings()))
			{
				continue;
			}
			
			bool all_variable_domains_are_super_sets = true;
			for (unsigned int i = 0; i < other_bounded_atom->getAtom().getArity(); i++)
			{
				const std::vector<const Object*>& other_variable_domain = other_bounded_atom->getVariableDomain(i, other.getDTG().getBindings());
				const std::vector<const Object*>& this_variable_domain = this_bounded_atom->getVariableDomain(i, getDTG().getBindings());
				
				bool is_super_set = true;
				for (std::vector<const Object*>::const_iterator ci = other_variable_domain.begin(); ci != other_variable_domain.end(); ci++)
				{
					const Object* other_object = *ci;
					bool contains_object = false;
					
					for (std::vector<const Object*>::const_iterator ci = this_variable_domain.begin(); ci != this_variable_domain.end(); ci++)
					{
						const Object* this_object = *ci;
						if (other_object == this_object)
						{
							contains_object = true;
							break;
						}
					}
					
					if (!contains_object)
					{
						is_super_set = false;
						break;
					}
				}
				
				if (!is_super_set)
				{
					all_variable_domains_are_super_sets = false;
					break;
				}
			}
			
			if (!all_variable_domains_are_super_sets)
			{
				continue;
			}
			
			// If all tests have been succesfull, we know this is a superset!
			contains_super_set = true;
			break;
		}
		
		if (!contains_super_set)
		{
//			std::cout << "It is not a superset, because the fact: ";
//			other_bounded_atom->print(std::cout, other.getDTG().getBindings());
//			std::cout << " could not be mapped." << std::endl;
			return false;
		}
	}
	return true;
}

bool DomainTransitionGraphNode::isSubSetOf(const DomainTransitionGraphNode& dtg_node) const
{
	return dtg_node.isSuperSetOf(*this);
}

bool DomainTransitionGraphNode::isEquivalentTo(const DomainTransitionGraphNode& other) const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = atoms_.begin(); ci != atoms_.end(); ci++)
	{
		const BoundedAtom* this_fact = *ci;
		
		bool found_equivalent = false;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = other.getAtoms().begin(); ci != other.getAtoms().end(); ci++)
		{
			const BoundedAtom* other_fact = *ci;
			
			if (this_fact->isEquivalentTo(*other_fact, dtg_->getBindings()))
			{
				found_equivalent = true;
				break;
			}
		}
		
		if (!found_equivalent)
			return false;
	}
	
	return true;
}

bool DomainTransitionGraphNode::isTermGrounded(const Term& term) const
{
	return grounded_terms_.count(&term) != 0;
}

void DomainTransitionGraphNode::print(std::ostream& os) const
{
	for (std::vector<BoundedAtom*>::const_iterator ci = getAtoms().begin(); ci != getAtoms().end(); ci++)
	{
		os << "\t";
		(*ci)->print(os, getDTG().getBindings());
		os << std::endl;
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
		//os << "\t";
		(*ci)->print(os, node.getDTG().getBindings());
//		(*ci)->getAtom().print(os, node.getDTG().getBindings(), (*ci)->getId());
		os << "(" << node.getIndex(**ci) << ")" << std::endl;
		
/*		const BoundedAtom* bounded_atom = *ci;
		for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
		{
			const Term* term = *ci;
			if (node.isTermGrounded(*term))
			{
				os << "G";
			}
			else
			{
				os << "L";
			}
		}
		os << std::endl;
*/

/*		if ((*ci)->getProperty() != NULL)
		{
			os << "[ps=" << &(*ci)->getProperty()->getPropertyState().getPropertySpace() << "]";
		}
*/
	}

	for (std::vector<const Transition*>::const_iterator ci = node.transitions_.begin(); ci != node.transitions_.end(); ci++)
	{
		const Transition* transition = *ci;
		os << "\t -> ";

		for (std::vector<BoundedAtom*>::const_iterator ci2 = transition->getToNode().getAtoms().begin(); ci2 != transition->getToNode().getAtoms().end(); ci2++)
		{
			(*ci2)->getAtom().print(os, node.getDTG().getBindings(), (*ci2)->getId());
			//(*ci2)->getAtom().print(os);
			os << "(" << transition->getToNode().getIndex(**ci2) << ")";
		}

		os << " [";
		transition->getAction().print(os, node.getDTG().getBindings(), transition->getStepId());
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

//		if (ci + 1!= node.transitions_.end())
		{
			os << std::endl;
		}
	}
	return os;
}

};

};

