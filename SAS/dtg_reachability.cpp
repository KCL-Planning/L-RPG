#include <cstring>
#include <iterator>
#include <sys/time.h>

#include "dtg_reachability.h"
#include "equivalent_object_group.h"
#include "dtg_manager.h"
#include "dtg_graph.h"
#include "dtg_node.h"
#include "property_space.h"
#include "transition.h"
#include "type_manager.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

///define MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
#define DTG_REACHABILITY_KEEP_TIME
namespace MyPOP {
	
namespace SAS_Plus {

ReachableFact::ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
	: bounded_atom_(&bounded_atom), bindings_(&bindings)
{
	term_domain_mapping_ = new EquivalentObjectGroup*[bounded_atom.getAtom().getArity()];
	
	for (std::vector<const Term*>::const_iterator ci = bounded_atom.getAtom().getTerms().begin(); ci != bounded_atom.getAtom().getTerms().end(); ci++)
	{
		const Term* term = *ci;
		const std::vector<const Object*>& domain = term->getDomain(bounded_atom.getId(), bindings);
		
		assert (domain.size() == 1);
		
		EquivalentObjectGroup& corresponding_eog = eog_manager.getEquivalentObject(*domain[0]).getEquivalentObjectGroup();
		term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] = &corresponding_eog;
		assert (term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] != NULL);
	}
	
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
}

ReachableFact::ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, EquivalentObjectGroup** term_domain_mapping)
	: bounded_atom_(&bounded_atom), bindings_(&bindings), term_domain_mapping_(term_domain_mapping)
{
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
}

bool ReachableFact::conflictsWith(const std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>& mapping) const
{
	for (std::vector<const Term*>::const_iterator ci = bounded_atom_->getAtom().getTerms().begin(); ci != bounded_atom_->getAtom().getTerms().end(); ci++)
	{
		unsigned int index = std::distance(bounded_atom_->getAtom().getTerms().begin(), ci);
		const std::vector<const Object*>& variable_domain = (*ci)->getDomain(bounded_atom_->getId(), *bindings_);
		
		 std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>::const_iterator ci = mapping.find(&variable_domain);
		 if (ci == mapping.end()) continue;
		 
		 if ((*ci).second != term_domain_mapping_[index]) return false;
	}
	return true;
}
	
void ReachableFact::updateMappings(std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>& mapping) const
{
	for (std::vector<const Term*>::const_iterator ci = bounded_atom_->getAtom().getTerms().begin(); ci != bounded_atom_->getAtom().getTerms().end(); ci++)
	{
		unsigned int index = std::distance(bounded_atom_->getAtom().getTerms().begin(), ci);
		const std::vector<const Object*>& variable_domain = (*ci)->getDomain(bounded_atom_->getId(), *bindings_);
		
		 std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>::const_iterator ci = mapping.find(&variable_domain);
		 assert (ci != mapping.end());
		 
		 term_domain_mapping_[index] = (*ci).second;
		 assert (term_domain_mapping_[index] != NULL);
	}
	
	for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
}

bool ReachableFact::containsNonRootEOG() const
{
	for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
	{
		if (!term_domain_mapping_[i]->isRootNode()) return true;
	}
	
	return false;
}

bool ReachableFact::isEquivalentTo(const ReachableFact& other) const
{
//	std::cout << "Are " << *this << " and " << other << " equivalent?" << std::endl;
	
	if (bounded_atom_->getAtom().getArity() != other.bounded_atom_->getAtom().getArity())
	{
//		std::cout << "Arities don't match up!" << std::endl;
		return false;
	}
	
	// Ignore those terms which have been marked as invariable in both reached facts.
	char this_mask = 0;
	char other_mask = 0;
	
	for (std::vector<const Property*>::const_iterator ci = bounded_atom_->getProperties().begin(); ci != bounded_atom_->getProperties().end(); ci++)
	{
		const Property* property = *ci;
		if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
		
		// Except when it has been grounded!
		if (term_domain_mapping_[property->getIndex()]->isGrounded()) continue;
		
		this_mask |= 0x1 << property->getIndex();
	}
	
	for (std::vector<const Property*>::const_iterator ci = other.bounded_atom_->getProperties().begin(); ci != other.bounded_atom_->getProperties().end(); ci++)
	{
		const Property* property = *ci;
		if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
		
		// Except when it has been grounded!
		if (other.term_domain_mapping_[property->getIndex()]->isGrounded()) continue;
		
		other_mask |= 0x1 << property->getIndex();
	}
	
	char combined_mask = this_mask & other_mask;
	
	for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
	{
		if (((0x1 << i) & combined_mask) != 0) continue;

		if (!term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
		{
//			std::cout << "The " << i << "th term is at odds!" << std::endl;
			return false;
		}
	}
	return true;
}

bool ReachableFact::isIdenticalTo(const ReachableFact& other) const
{
//	std::cout << "Are " << *this << " and " << other << " equivalent?" << std::endl;
	
	if (bounded_atom_->getAtom().getArity() != other.bounded_atom_->getAtom().getArity())
	{
//		std::cout << "Arities don't match up!" << std::endl;
		return false;
	}
	for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
		assert (other.term_domain_mapping_[i] != NULL);
//		std::cout << "Check " << *term_domain_mapping_[i] << " v.s. " << *other.term_domain_mapping_[i] << std::endl;
		
		if (!term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
		{
			return false;
		}
	}
	return true;
}

void ReachableFact::printGrounded(std::ostream& os) const
{
	os << "Print grounded of: " << *this << std::endl;
	unsigned int counter[bounded_atom_->getAtom().getArity()];
	memset (&counter[0], 0, sizeof(unsigned int) * bounded_atom_->getAtom().getArity());
	
	bool done = false;
	while (!done)
	{
		os << bounded_atom_->getAtom().getPredicate().getName() << " ";
		for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
		{
			const std::vector<const EquivalentObject*>& objects = term_domain_mapping_[i]->getEquivalentObjects();
			
			os << *objects[counter[i]];
			
			if (i + 1 != bounded_atom_->getAtom().getArity())
			{
				os << " ";
			}
		}
		os << std::endl;
		
		// Update counters or stop if all objects have been printed.
		for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
		{
			if (counter[i] + 1 == term_domain_mapping_[i]->getEquivalentObjects().size())
			{
				if (i + 1 == bounded_atom_->getAtom().getArity())
				{
					done = true;
					break;
				}
				
				counter[i] = 0;
				continue;
			}
			
			++counter[i];
			break;
		}
	}
}

void ReachableFact::getAllReachableFacts(std::vector<const BoundedAtom*>& results) const
{
	unsigned int counter[bounded_atom_->getAtom().getArity()];
	memset (&counter[0], 0, sizeof(unsigned int) * bounded_atom_->getAtom().getArity());
	
	bool done = false;
	while (!done)
	{
		std::vector<const Term*>* terms = new std::vector<const Term*>();
		
		for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
		{
			const std::vector<const EquivalentObject*>& objects = term_domain_mapping_[i]->getEquivalentObjects();
			terms->push_back(&objects[counter[i]]->getObject());
		}
		
		// Update counters or stop if all objects have been printed.
		for (unsigned int i = 0; i < bounded_atom_->getAtom().getArity(); i++)
		{
			if (counter[i] + 1 == term_domain_mapping_[i]->getEquivalentObjects().size())
			{
				if (i + 1 == bounded_atom_->getAtom().getArity())
				{
					done = true;
					break;
				}
				
				counter[i] = 0;
				continue;
			}
			
			++counter[i];
			break;
		}
		
		Atom* new_atom = new Atom(bounded_atom_->getAtom().getPredicate(), *terms, false);
		results.push_back(new BoundedAtom(Step::INITIAL_STEP, *new_atom));
	}
}

std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact)
{
	os << "Reachable fact: (" << reachable_fact.bounded_atom_->getAtom().getPredicate().getName() << " ";
	for (unsigned int i = 0; i < reachable_fact.bounded_atom_->getAtom().getArity(); i++)
	{
		const std::vector<const EquivalentObject*>& objects = reachable_fact.term_domain_mapping_[i]->getEquivalentObjects();
		os << "{";
		for (std::vector<const EquivalentObject*>::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
		{
			os << (*ci)->getObject();
			if (ci + 1 != objects.end())
			{
				os << ", ";
			}
		}
		os << "}";
		if (i + 1 != reachable_fact.bounded_atom_->getAtom().getArity())
		{
			os << ", ";
		}
		//os << "- " << *reachable_fact.term_domain_mapping_[i]-> << "(" << reachable_fact.index_ << std::endl;
	}
	os << ")";
	
	os << "%";
	for (std::vector<const Property*>::const_iterator ci = reachable_fact.bounded_atom_->getProperties().begin(); ci != reachable_fact.bounded_atom_->getProperties().end(); ci++)
	{
		os << **ci << ", ";
	}
	
	os << "%" << std::endl;
	return os;
}

/**
 * ResolvedBoundedAtom.
 */
ResolvedBoundedAtom::ResolvedBoundedAtom(const BoundedAtom& bounded_atom, const Bindings& bindings)
	 : atom_(&bounded_atom.getAtom())
{
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		variable_domains_.push_back(&bounded_atom.getVariableDomain(i, bindings));
	}
}
	
const std::vector<const Object*>& ResolvedBoundedAtom::getVariableDomain(unsigned int index) const
{
	assert (index < variable_domains_.size());
	return *variable_domains_[index];
}

/**
 * ReachableSet.
 */
ReachableSet::ReachableSet(const MyPOP::SAS_Plus::EquivalentObjectGroupManager& eog_manager)
	: eog_manager_(&eog_manager)
{

}

void ReachableSet::initialiseInitialFacts(const std::vector< ReachableFact* >& initial_facts)
{
	/**
	 * Match all the initial facts with the facts in the set. We store the results only locally because we will use the
	 * processNewReachableFact to do the actual work for us.
	 */
	unsigned int index = 0;
	std::vector<std::vector<const ReachableFact*>*> local_reachable_set(reachable_set_);
	for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = facts_set_.begin(); ci != facts_set_.end(); ci++)
	{
		const ResolvedBoundedAtom* resolved_atom = *ci;
		
		// Check which initial facts can merge with the given atom.
		for (std::vector< ReachableFact* >::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
		{
			const ReachableFact* reachable_fact = *ci;
			
			// The predicate of the fact in this set should be more general than the one we try to 'merge' with.
			if (!resolved_atom->getAtom().getPredicate().canSubstitute(reachable_fact->getBoundedAtom().getAtom().getPredicate()))
			{
				continue;
			}
			
			local_reachable_set[index]->push_back(reachable_fact);
		}
		
		++index;
	}
	
	/**
	 * After all initial facts are mapped, we will try to combine them as good as possible. The way the DTG nodes are created mean
	 * that the facts at index `i` shares at least one variable domain with any of the facts at index {0, 1, ..., i - 1} - except for
	 * the fact at index 0. So this allows us to efficiently create all the sets.
	 */
	index = 0;
	for (std::vector<std::vector<const ReachableFact*>*>::const_iterator ci = local_reachable_set.begin(); ci != local_reachable_set.end(); ci++)
	{
		std::vector<const ReachableFact*>* reachable_set = *ci;
		for (std::vector<const ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end(); ci++)
		{
			processNewReachableFact(**ci, index);
		}
		
		++index;
	}
}

void ReachableSet::addBoundedAtom(const MyPOP::SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings)
{
	ResolvedBoundedAtom* new_resolved_bounded_atom = new ResolvedBoundedAtom(bounded_atom, bindings);
	facts_set_.push_back(new_resolved_bounded_atom);
	reachable_set_.push_back(new std::vector<const ReachableFact*>());
	
	// Generate the constraints sets.
	std::vector<std::pair<unsigned int, unsigned int> >** new_constraints_sets = new std::vector<std::pair<unsigned int, unsigned int> >*[bounded_atom.getAtom().getArity()];
	for (unsigned int i = 0; i  < bounded_atom.getAtom().getArity(); i++)
	{
		new_constraints_sets[i] = new std::vector<std::pair<unsigned int, unsigned int> >();
	}
	
	
	for (unsigned int i = 0; i < facts_set_.size() - 1; i++)
	{
		const ResolvedBoundedAtom* previous_resolved_bounded_atom = facts_set_[i];
		
		for (unsigned int j = 0; j < new_resolved_bounded_atom->getAtom().getArity(); j++)
		{
			for (unsigned int k = 0; k < previous_resolved_bounded_atom->getAtom().getArity(); k++)
			{
				if (&previous_resolved_bounded_atom->getVariableDomain(k) == &new_resolved_bounded_atom->getVariableDomain(j))
				{
					new_constraints_sets[j]->push_back(std::make_pair(i, k));
				}
			}
		}
	}
}

bool ReachableSet::canSatisfyConstraints(const ReachableFact& reachable_fact, std::vector<const ReachableFact*>& reachable_set) const
{
	unsigned int index = reachable_set.size();
	std::vector<std::pair<unsigned int, unsigned int> >** constraints = constraints_set_[index];
	for (unsigned int i = 0; i < reachable_fact.getBoundedAtom().getAtom().getArity(); i++)
	{
		std::vector<std::pair<unsigned int, unsigned int> >* variable_constraints = constraints[i];
		
		for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = variable_constraints->begin(); ci != variable_constraints->end(); ci++)
		{
			unsigned int fact_index = (*ci).first;
			unsigned int variable_index = (*ci).second;
			// Check if the relationship holds.
			if (reachable_fact.getTermDomain(i) != reachable_set[fact_index]->getTermDomain(variable_index))
			{
				return false;
			}
		}
	}
	
	return true;
}

void ReachableSet::processNewReachableFact(const ReachableFact& reachable_fact, unsigned int index)
{
	// Add the fact to the reachable set, but make sure it isn't already part of it!
	std::vector<const ReachableFact*>* reachable_set = reachable_set_[index];
	
	for (std::vector<const ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end(); ci++)
	{
		if (reachable_fact.isIdenticalTo(**ci)) return;
	}
	
	reachable_set_[index]->push_back(&reachable_fact);
	
	// If the index is 0, it means it is the start of a new 'root'.
	if (index == 0)
	{
		std::vector<const ReachableFact*>* new_reachable_set = new std::vector<const ReachableFact*>();
		new_reachable_set->push_back(&reachable_fact);
		fully_reachable_sets_.push_back(new_reachable_set);
		
		generateNewReachableSets(*new_reachable_set);
	}
	// Otherwise, we need to search for all sets the new node can be a part of and process these.
	else
	{
		for (std::vector<std::vector<const ReachableFact*>* >::const_iterator ci = fully_reachable_sets_.begin(); ci != fully_reachable_sets_.end(); ci++)
		{
			std::vector<const ReachableFact*>* reachable_set = *ci;
			if (reachable_set->size() != index) continue;
			
			// Check if the newly reachable fact satisfies all the constraints of the previous assignments.
			if (!canSatisfyConstraints(reachable_fact, *reachable_set)) continue;
			
			// If the constraints are satisfied, add the facts and search for new facts to add.
			std::vector<const ReachableFact*>* new_reachable_set = new std::vector<const ReachableFact*>();
			new_reachable_set->push_back(&reachable_fact);
			
			generateNewReachableSets(*new_reachable_set);
		}
	}
}

void ReachableSet::generateNewReachableSets(std::vector<const ReachableFact*>& reachable_sets_to_process)
{
	unsigned int index = reachable_sets_to_process.size();
	
	// Check if we are done.
	if (index == facts_set_.size()) return;
	
	// Try all possible facts which we have proven to be reachable for the 'index'th index.
	for (std::vector<const ReachableFact*>::const_iterator ci = reachable_set_[index]->begin(); ci != reachable_set_[index]->end(); ci++)
	{
		const ReachableFact* reachable_fact = *ci;
		
		if (!canSatisfyConstraints(*reachable_fact, *reachable_set_[index])) continue;
		
		// If the constraints are satisfied, add the facts and search for new facts to add.
		std::vector<const ReachableFact*>* new_reachable_set = new std::vector<const ReachableFact*>();
		new_reachable_set->push_back(reachable_fact);
		
		generateNewReachableSets(*new_reachable_set);
	}
}

/**
 * ReachableNode
 */
ReachableNode::ReachableNode(const DomainTransitionGraphNode& dtg_node, const EquivalentObjectGroupManager& eog_manager)
	: ReachableSet(eog_manager), dtg_node_(&dtg_node)
{

}

void ReachableNode::initialise(const std::vector<ReachableFact*>& initial_facts)
{
	initialiseInitialFacts(initial_facts);
	
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transitions_.begin(); ci != reachable_transitions_.end(); ci++)
	{
		ReachableTransition* reachable_transition = *ci;
		
		reachable_transition->initialise(initial_facts);
	}
}

void ReachableNode::addReachableTransition(ReachableTransition& reachable_transition)
{
	reachable_transitions_.push_back(&reachable_transition);
}

std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node)
{
	os << "ReachableNode: " << std::endl;
	return os;
}

/**
 * Reachable Transition.
 */
ReachableTransition::ReachableTransition(const MyPOP::SAS_Plus::Transition& transition, const ReachableNode& from_node, const ReachableNode& to_node, const EquivalentObjectGroupManager& eog_manager)
	: ReachableSet(eog_manager), from_node_(&from_node), to_node_(&to_node), transition_(&transition)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "New reachable transition: " << transition << "." << std::endl;
#endif

	// Determine the set of grounded variables.
	std::set<const std::vector<const Object*>*> grounded_variables;
	for (std::vector<const Variable*>::const_iterator ci = transition.getStep()->getAction().getVariables().begin(); ci != transition.getStep()->getAction().getVariables().end(); ci++)
	{
		const Variable* variable = *ci;
		const std::vector<const Object*>& variable_domain = variable->getDomain(transition.getStep()->getStepId(), transition.getFromNode().getDTG().getBindings());
		
		if (variable_domain.size() == 1)
		{
			const EquivalentObject& eo = eog_manager.getEquivalentObject(*variable_domain[0]);
			if (eo.getEquivalentObjectGroup().isGrounded())
			{
				grounded_variables.insert(&variable_domain);
			}
		}
	}

	// Find out which preconditions are not part of the from node.
	const std::vector<std::pair<const Atom*, InvariableIndex> >& all_preconditions = transition.getAllPreconditions();
	const Bindings& bindings = transition.getFromNode().getDTG().getBindings();
			
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions.begin(); ci != all_preconditions.end(); ci++)
	{
		const Atom* precondition = (*ci).first;
		bool precondition_part_of_from_node = false;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = transition.getFromNode().getAtoms().begin(); ci != transition.getFromNode().getAtoms().end(); ci++)
		{
			const BoundedAtom* from_fact = *ci;
			if (bindings.areIdentical(from_fact->getAtom(), from_fact->getId(), *precondition, transition.getStep()->getStepId()))
			{
				precondition_part_of_from_node = true;
				break;
			}
		}
		
		if (precondition_part_of_from_node) continue;
		
		// Convert the precondition into a bounded atom.
		std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
		transition.getFromNode().getDTG().getDTGManager().getDTGNodes(found_nodes, transition.getStep()->getStepId(), *precondition, transition.getFromNode().getDTG().getBindings());
		
		std::vector<const Property*>* precondition_properties = new std::vector<const Property*>();
		for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
		{
			const BoundedAtom* bounded_atom = (*ci).second;
			
			for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
			{
				const Property* property = *ci;
				if (std::find(precondition_properties->begin(), precondition_properties->end(), property) != precondition_properties->end()) continue;
				precondition_properties->push_back(property);
			}
		}
		
		assert (precondition_properties->size() != 0);
		
		BoundedAtom* bounded_precondition = new BoundedAtom(transition.getStep()->getStepId(), *precondition, *precondition_properties);
		
		// For all those not part of the from node, add them to a list.
		EquivalentObjectGroup* grounded_object_group = NULL;
		for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
		{
			const Term* precondition_term = *ci;
			const std::vector<const Object*>& precondition_domain = precondition_term->getDomain(transition.getStep()->getStepId(), bindings);
			if (grounded_variables.count(&precondition_domain) != 0)
			{
				grounded_object_group = &eog_manager.getEquivalentObject(*precondition_domain[0]).getEquivalentObjectGroup();
				assert (grounded_object_group->isGrounded());
				break;
			}
		}
		
		addBoundedAtom(*bounded_precondition, bindings);
	}
}

void ReachableTransition::initialise(const std::vector<ReachableFact*>& initial_facts)
{
	initialiseInitialFacts(initial_facts);
}

/*******************************
 * DTGReachability
*******************************/

DTGReachability::DTGReachability(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::SAS_Plus::DomainTransitionGraph& dtg_graph, const MyPOP::TermManager& term_manager)
	: term_manager_(&term_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "DTG Reachability on graph: " << dtg_graph << "." << std::endl;
#endif

	// Initialise the individual groups per object.
	equivalent_object_manager_ = new EquivalentObjectGroupManager(*this, dtg_manager, dtg_graph, term_manager);

	
	std::map<const DomainTransitionGraphNode*, ReachableNode*> node_mapping;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		
		ReachableNode* reachable_node = new ReachableNode(*dtg_node, *equivalent_object_manager_);
		reachable_nodes_.push_back(reachable_node);
		node_mapping[dtg_node] = reachable_node;
	}
	
	for (std::map<const DomainTransitionGraphNode*, ReachableNode*>::const_iterator ci = node_mapping.begin(); ci != node_mapping.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		ReachableNode* reachable_from_node = (*ci).second;
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			ReachableNode* reachable_to_node = node_mapping[&transition->getToNode()];
			ReachableTransition* reachable_transition = new ReachableTransition(**ci, *reachable_from_node, *reachable_to_node, *equivalent_object_manager_);
			reachable_transitions_[*ci] = reachable_transition;
			 
			reachable_from_node->addReachableTransition(*reachable_transition);
		}
	}
}

void DTGReachability::performReachabilityAnalsysis(std::vector<const ReachableFact*>& result, const std::vector<const BoundedAtom*>& initial_facts, const Bindings& bindings)
{
//	double time_propagating = 0;
//	double time_iterating = 0;
//	double time_establishing_equivalances = 0;
//	unsigned int amount_of_iterating = 0;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Start performing reachability analysis." << std::endl;
#endif

	// Transform the set of initial facts into reachable facts, which means we drop the variable domains
	// and work solely with equivalent object groups.
	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		ReachableFact* initial_reachable_fact = new ReachableFact(**ci, bindings, *equivalent_object_manager_);
		established_reachable_facts_.push_back(initial_reachable_fact);
	}


	equivalent_object_manager_->initialise(initial_facts);

	//DTGPropagator propagator(*this, *equivalent_object_manager_, *dtg_graph_);
	
	// Keep a list of all established facts so far.
	//std::vector<const BoundedAtom*> established_facts(initial_facts);
	
	// List of already achieved transitions.
	//std::set<const Transition*> achieved_transitions;
	
	//for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	//{
	//	const BoundedAtom* init_bounded_atom = *ci;
	//	if (init_bounded_atom->getAtom().getPredicate().isStatic())
	//	{
	//		ReachableFact* static_reachable_fact = new ReachableFact(*init_bounded_atom, dtg_graph_->getBindings(), *equivalent_object_manager_);
	//		static_facts_.push_back(static_reachable_fact);
	//	}
	//}
	
	//unsigned int pre_size = 0;
	
	struct timeval start_time_init;
	gettimeofday(&start_time_init, NULL);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Find initial supported DTG nodes." << std::endl;
#endif
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		ReachableNode* reachable_node = *ci;
		reachable_node->initialise(established_reachable_facts_);
	}

/*
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		// Initialise the reachability structure(s) with the values from the initial state.
		const DomainTransitionGraphNode* dtg_node = *ci;
		const std::vector<BoundedAtom*>& atoms_to_achieve = dtg_node->getAtoms();
		std::vector<std::vector<const BoundedAtom*>* > supporting_tupples;
		std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > variable_assignments;
		std::vector<const BoundedAtom*> initial_supporting_facts;
		getSupportingFacts(supporting_tupples, variable_assignments, atoms_to_achieve, initial_supporting_facts, established_reachable_facts);

		// Mark those transitions whose node have been 'filled' by the initial state.
		for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = supporting_tupples.begin(); ci != supporting_tupples.end(); ci++)
		{
			makeReachable(*dtg_node, **ci);
		}
	}
	
#ifdef DTG_REACHABILITY_KEEP_TIME
	struct timeval end_time_init;
	gettimeofday(&end_time_init, NULL);
	
	double time_spend = end_time_init.tv_sec - start_time_init.tv_sec + (end_time_init.tv_usec - start_time_init.tv_usec) / 1000000.0;
	std::cerr << "Time spend initiating initial structure: " << time_spend << std::endl;
#endif

	// Keep on iterator as long as we can establish new facts.
	bool new_transitions_achieved = false;
	do 
	{
		//pre_size = established_facts.size();
		
//		std::cout << "Iterator till fix point." << std::endl;
#ifdef DTG_REACHABILITY_KEEP_TIME
		struct timeval start_time;
		gettimeofday(&start_time, NULL);
#endif
		new_transitions_achieved = iterateTillFixPoint(propagator, established_facts, achieved_transitions);
#ifdef DTG_REACHABILITY_KEEP_TIME
		struct timeval end_time;
		gettimeofday(&end_time, NULL);
#endif
		
//		std::cout << "[DONE!] Iterator till fix point." << std::endl;
#ifdef DTG_REACHABILITY_KEEP_TIME
		time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
		std::cerr << "Time spend iterating: " << time_spend << std::endl;
#endif
		
		// After no other transitions can be reached we establish the object equivalence relations.
//		std::cout << "Update equivalences." << std::endl;
#ifdef DTG_REACHABILITY_KEEP_TIME
		gettimeofday(&start_time, NULL);
#endif
		equivalent_object_manager_->updateEquivalences(reachable_nodes_);
#ifdef DTG_REACHABILITY_KEEP_TIME
		gettimeofday(&end_time, NULL);
		time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
		std::cerr << "Time spend establishing equivalent relationships: " << time_spend << std::endl;
#endif
//		std::cout << "[DONE!] Update equivalences." << std::endl;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		equivalent_object_manager_->print(std::cout);
#endif

//		std::cout << "Handle external dependencies." << std::endl;
#ifdef DTG_REACHABILITY_KEEP_TIME
		gettimeofday(&start_time, NULL);
#endif
		//new_transitions_achieved = handleExternalDependencies(established_facts) || new_transitions_achieved;
#ifdef DTG_REACHABILITY_KEEP_TIME
		gettimeofday(&end_time, NULL);
		time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
		std::cerr << "Time spend resolving external dependencies: " << time_spend << std::endl;
#endif
//		std::cout << "[DONE!] Handle external dependencies." << std::endl;
	} while (new_transitions_achieved);
	//} while (pre_size != established_facts.size());
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << " -= All supported facts! :D =- " << std::endl;
	for (std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const BoundedAtom*>* >* >::const_iterator ci = supported_facts_.begin(); ci != supported_facts_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		const std::vector<std::vector<const BoundedAtom*>* >* supported_tupples = (*ci).second;
		
		std::cout << "The DTG node: ";
		dtg_node->print(std::cout);
		std::cout << " is supported by the following tupples:" << std::endl;
		
		for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = supported_tupples->begin(); ci != supported_tupples->end(); ci++)
		{
			std::vector<const BoundedAtom*>* tupple = *ci;
			std::cout << "{" << std::endl;
			for (std::vector<const BoundedAtom*>::const_iterator ci = tupple->begin(); ci != tupple->end(); ci++)
			{
				std::cout << "* ";
				(*ci)->print(std::cout, dtg_graph_->getBindings());
				std::cout << "." << std::endl;
			}
			std::cout << "}" << std::endl;
		}
	}
	
	std::cout << "All the facts from the EOGs: " << std::endl;
	equivalent_object_manager_->printAll(std::cout);
	std::cout << std::endl;

	std::cout << "Transitions which were not satisfied: " << std::endl;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			if (achieved_transitions.count(*ci) == 0)
			{
				std::cout << **ci << std::endl;
			}
		}
	}
#endif
*/
/*
	std::ofstream ofs;
	ofs.open("lollipop_rpg_results", std::ios::out);
	
	equivalent_object_manager_->printAll(ofs);
	ofs.close();
*/
//	equivalent_object_manager_->getAllReachableFacts(reachable_facts);
}

ReachableTransition& DTGReachability::getReachableTransition(const Transition& transition) const
{
	std::map<const Transition*, ReachableTransition*>::const_iterator ci = reachable_transitions_.find(&transition);
	assert (ci != reachable_transitions_.end());
	return *(*ci).second;
}


/*******************************
 * DTGPropagator
*******************************/

DTGPropagator::DTGPropagator(DTGReachability& dtg_reachability, EquivalentObjectGroupManager& equivalent_object_manager, const DomainTransitionGraph& dtg_graph)
	 : dtg_reachability_(&dtg_reachability),  equivalent_object_manager_(&equivalent_object_manager), dtg_graph_(&dtg_graph)
{
	
}

void DTGPropagator::propagateReachableNodes()
{
/*
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::propagateReachableNodes]" << std::endl;

	std::cout << "Current state: " << std::endl;
	equivalent_object_manager_->print(std::cout);
	std::cout << std::endl;
#endif

//	bool mask[dtg_graph_->getNodes().size()];
//	memset(&mask[0], false, dtg_graph_->getNodes().size() * sizeof(bool));
	
	bool finished = false;
	while (!finished)
	{
		finished = true;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
		{
//			unsigned int index = std::distance(dtg_graph_->getNodes().begin(), ci);
			
//			if (mask[index]) continue;
//			mask[index] = true;
			
			const DomainTransitionGraphNode* dtg_node = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Work on the DTG node: " << *dtg_node << std::endl;
#endif

			// If the DTG node is part of an attribute space we need to construct all possible values the nodes can take.
			// TODO: uncomment line below!
			//if (dtg_node->isAttributeSpace())
			{
///				unsigned int misses = 0;
///				unsigned int hits = 0;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Found a dtg node which is part of a attribute space: " << *dtg_node << "." << std::endl;
#endif
				const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*> mappings;
				const std::vector<const ReachableFact*> assignments;
				std::vector<const ReachableNode*> results;
				
				const std::vector<const ReachableFact*>* cached_reachable_facts[dtg_node->getAtoms().size()];
				bool reachable = true;
				for (unsigned int i = 0; i < dtg_node->getAtoms().size(); i++)
				{
					std::vector<const ReachableFact*>* reachable_facts = new std::vector<const ReachableFact*>();
					equivalent_object_manager_->getSupportingFacts(*reachable_facts, *dtg_node->getAtoms()[i], dtg_node->getDTG().getBindings());
					if (reachable_facts->empty())
					{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "Could not find supporting facts for the bounded atom: ";
						dtg_node->getAtoms()[i]->print(std::cout, dtg_node->getDTG().getBindings());
						std::cout << std::endl;
#endif
						reachable = false;
						break;
					}
					cached_reachable_facts[i] = reachable_facts;
				}
				
				if (reachable)
				{
					mapPossibleFacts(results, cached_reachable_facts, *dtg_node, mappings, assignments);
					
					for (std::vector<const ReachableNode*>::const_iterator ci = results.begin(); ci != results.end(); ci++)
					{
						const ReachableNode* reachable_node =  *ci;
						if (dtg_graph_closed_list_.count(std::make_pair(dtg_node, reachable_node)) != 0) continue;
						
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "* " << *reachable_node << "." << std::endl;
#endif
						dtg_graph_closed_list_.insert(std::make_pair(dtg_node, reachable_node));
						if (!equivalent_object_manager_->makeReachable(*dtg_node, *reachable_node))
						{
///							++misses;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//							std::cout << "Already reachable!" << std::endl;
#endif
						}
///						else
///						{
///							++hits;
///						}
					}
//					if (hits + misses != 0)
//					{
//						double accuracy = 0;
//						if (misses == 0) accuracy = 100;
//						else accuracy = ((double)hits / (hits + misses)) * 100;
//						std::cerr << "Map possible maps hits / misses: " << hits << "/" << misses << " " << accuracy << "%." << std::endl;
//					}
				}
			}
			
//			Bindings& bindings = dtg_node->getDTG().getBindings();
			
			std::vector<const ReachableNode*> reachable_node;
			equivalent_object_manager_->getSupportingFacts(reachable_node, *dtg_node);

			if (reachable_node.empty()) continue;
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Reachable nodes: " << std::endl;
			for (std::vector<const ReachableNode*>::const_iterator ci = reachable_node.begin(); ci != reachable_node.end(); ci++)
			{
				const ReachableNode* reachable_node = *ci;
				std::cout << "- " << *reachable_node << "." << std::endl;
			}
#endif
			
			for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;
				ReachableTransition& reachable_transition = dtg_reachability_->getReachableTransition(*transition);
				
				reachable_transition.updateVariables();
				
				/// Check if the transition is possible.
				const std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >& possible_mappings = reachable_transition.getPossibleMappings();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				if (possible_mappings.size() > 0)
				{
					std::cout << "Propagate the transition: " << *transition << "." << std::endl;
					for (std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >::const_iterator ci = possible_mappings.begin(); ci != possible_mappings.end(); ci++)
					{
						const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* possible_mapping = *ci;
						
						for (std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator ci = possible_mapping->begin(); ci != possible_mapping->end(); ci++)
						{
							std::cout << "Map: " << (*ci).first << " to ";
							(*ci).second->printObjects(std::cout);
							std::cout << "." << std::endl;
						}
						
						
						std::cout << " - (" << transition->getStep()->getAction().getPredicate() << " ";
						for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
						{
							const Variable* variable = *ci;
							const std::vector<const Object*>& variable_domain = variable->getDomain(transition->getStep()->getStepId(), dtg_node->getDTG().getBindings());
							
							std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator find_ci = possible_mapping->find(&variable_domain);
							
							if (find_ci == possible_mapping->end())
							{
								std::cout << "The variable domain: ";
								variable->print(std::cout, dtg_node->getDTG().getBindings(), transition->getStep()->getStepId());
								std::cout << "$" << &variable_domain << "$ was not mapped in the possible mappings!!!" << std::endl;
								continue;
							}
							
							std::cout << "|Map: ";
							for (std::vector<const Object*>::const_iterator ci2 = (*find_ci).first->begin(); ci2 != (*find_ci).first->end(); ci2++)
							{
								(*ci2)->print(std::cout, dtg_node->getDTG().getBindings(), transition->getStep()->getStepId());
								std::cout << ", ";
							}
							std::cout << "$" << (*find_ci).first << "$ =-> |";
							
							(*find_ci).second->printObjects(std::cout);
							
							if (ci + 1 != transition->getStep()->getAction().getVariables().end())
								std::cout << ", ";
						}
						std::cout << ")" << std::endl;
					}
				}
				else
				{
					std::cout << "Transition has not been reached yet! " << *transition << std::endl;
				}
#endif

				for (std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >::const_iterator ci = possible_mappings.begin(); ci != possible_mappings.end(); ci++)
				{
					const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* reachable_transition_mapping = *ci;
					// Update the mapping to include the assignments made to the reachable_node.
					for (std::vector<const ReachableNode*>::const_iterator ci = reachable_node.begin(); ci != reachable_node.end(); ci++)
					{
						const ReachableNode* reachable_node = *ci;
						bool reachable_node_possible = true;

						
						std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* possible_mapping = new std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>(*reachable_transition_mapping);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "Process reachable node: " << *reachable_node << "." << std::endl;
#endif
						for (std::vector<const ReachableFact*>::const_iterator ci = reachable_node->getSupportingFacts().begin(); ci != reachable_node->getSupportingFacts().end(); ci++)
						{
							unsigned index = std::distance(reachable_node->getSupportingFacts().begin(), ci);
							const ReachableFact* reachable_fact = *ci;
//							std::cout << "Get the bounded atom at index: " << reachable_fact->index_ << "." << std::endl;
							
							const BoundedAtom* bounded_atom = dtg_node->getAtoms()[index];
							assert (bounded_atom != NULL);
							
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "Update the fact: ";
							bounded_atom->print(std::cout, dtg_node->getDTG().getBindings());
							std::cout << " to " << *reachable_fact << "." << std::endl;
#endif
							for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
							{
								const Term* term = bounded_atom->getAtom().getTerms()[i];
								const std::vector<const Object*>& term_domain = term->getDomain(bounded_atom->getId(), dtg_node->getDTG().getBindings());
								
								EquivalentObjectGroup& reachable_fact_eog = reachable_fact->getTermDomain(i);
								
								// Make sure there is no conflict between the mappings of the reachable transition and those of the reachable node!
								if (possible_mapping->count(&term_domain) != 0)
								{
									if ((*possible_mapping)[&term_domain] != &reachable_fact_eog)
									{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
										std::cout << "The mapping of " << &term_domain << " has been set to ";
										(*possible_mapping)[&term_domain]->printObjects(std::cout);
										std::cout << " by the reachable transition." << std::endl;
										std::cout << "But the reachable node sets it to: ";
										reachable_fact_eog.printObjects(std::cout);
										std::cout << "." << std::endl;
#endif
										reachable_node_possible = false;
										break;
									}
								}
								
								(*possible_mapping)[&term_domain] = &reachable_fact_eog;
							}
							
							if (!reachable_node_possible) break;
						}
						
						if (!reachable_node_possible) continue;

						if (dtg_reachability_->makeToNodeReachable(*transition, *possible_mapping))
						{
							finished = false;
						}
						closed_list_.insert(std::make_pair(transition, reachable_node));
					}
				}
			}
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::propagateReachableNodes] DONE!" << std::endl;
#endif
*/
}


void DTGPropagator::mapPossibleFacts(std::vector<const ReachableNode*>& results, const std::vector<const ReachableFact*>* cached_reachable_facts[], const DomainTransitionGraphNode& dtg_node, const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& mappings, const std::vector<const ReachableFact*>& assignments)
{
/*	// If we have found a reachable fact for every fact in the dtg node, create a reachable node and add it to the list of reachable facts.
	if (assignments.size() == dtg_node.getAtoms().size())
	{
		std::vector<const ReachableFact*>* reachable_facts = new std::vector<const ReachableFact*>(assignments);
		ReachableNode* reachable_node = new ReachableNode(dtg_node, *reachable_facts);
		results.push_back(reachable_node);
		return;
	}
	
	// The fact to work on.
	const BoundedAtom* current_fact = dtg_node.getAtoms()[assignments.size()];
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	std::cout << "+ Work on: ";
//	current_fact->print(std::cout, dtg_node.getDTG().getBindings());
//	std::cout << "." << std::endl;
	
//	std::cout << "+ Assignments so far: " << std::endl;
//	for (std::vector<const ReachableFact*>::const_iterator ci = assignments.begin(); ci != assignments.end(); ci++)
//	{
//		std::cout << "++ " << **ci << "." << std::endl;
//	}
#endif
	
	// Get all possible facts.
	const std::vector<const ReachableFact*>* reachable_facts = cached_reachable_facts[assignments.size()];
//	equivalent_object_manager_->getSupportingFacts(reachable_facts, *current_fact, dtg_node.getDTG().getBindings());
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	assert (!reachable_facts->empty());
//	if (reachable_facts.size() == 0)
//	{
//		std::cout << " No reachable facts found :((." << std::endl;
//	}
#endif
	
	// Check if they are consistent with the current mappings.
	for (std::vector<const ReachableFact*>::const_iterator ci = reachable_facts->begin(); ci != reachable_facts->end(); ci++)
	{
		const ReachableFact* reachable_fact = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//		std::cout << "Possible reachable fact: " << *reachable_fact << "." << std::endl;
#endif
		
		std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*> new_mappings(mappings);
		
		bool consistent = true;
		for (unsigned int i = 0; i < current_fact->getAtom().getArity(); i++)
		{
			const std::vector<const Object*>& domain_variable = current_fact->getVariableDomain(i, dtg_node.getDTG().getBindings());
			const EquivalentObjectGroup& eog = reachable_fact->getTermDomain(i);
			
			std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator ci = new_mappings.find(&domain_variable);
			if (ci == new_mappings.end())
			{
				new_mappings[&domain_variable] = &eog;
			}
			else if ((*ci).second != &eog)
			{
				consistent = false;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//				std::cout << "Clash! Cannot be used!" << std::endl;
#endif
				break;
			}
		}
		
		if (!consistent) continue;
		
		std::vector<const ReachableFact*> new_assignments(assignments);
		//new_assignments.push_back(new ReachableFact(assignments.size(), *reachable_fact->bounded_atom_, *reachable_fact->bindings_, reachable_fact->term_domain_mapping_));
		new_assignments.push_back(reachable_fact);
		
		mapPossibleFacts(results, cached_reachable_facts, dtg_node, new_mappings, new_assignments);
	}
*/
}

};
	
};
