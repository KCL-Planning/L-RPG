#include <cstring>
#include <iterator>
#include <sys/time.h>

#include "dtg_reachability.h"
#include "dtg_manager.h"
#include "dtg_graph.h"
#include "dtg_node.h"
#include "property_space.h"
#include "transition.h"
#include "type_manager.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

#define MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
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

bool ReachableNode::isEquivalentTo(const ReachableNode& other) const
{
	if (dtg_node_ != other.dtg_node_) return false;
	
	for (unsigned int i = 0; i < supporting_facts_->size(); i++)
	{
		const ReachableFact* this_fact = (*supporting_facts_)[i];
		const ReachableFact* other_fact = (*other.supporting_facts_)[i];
		
		if (!this_fact->isEquivalentTo(*other_fact)) return false;
	}
	
	return true;
}

bool ReachableNode::isIdenticalTo(const ReachableNode& other) const
{
	if (dtg_node_ != other.dtg_node_) return false;
	
	for (unsigned int i = 0; i < supporting_facts_->size(); i++)
	{
		const ReachableFact* this_fact = (*supporting_facts_)[i];
		const ReachableFact* other_fact = (*other.supporting_facts_)[i];
		
		if (!this_fact->isIdenticalTo(*other_fact)) return false;
	}
	
	return true;
}

std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node)
{
	os << "ReachableNode: " << std::endl;
	for (std::vector<const ReachableFact*>::const_iterator ci = reachable_node.supporting_facts_->begin(); ci != reachable_node.supporting_facts_->end(); ci++)
	{
		os << "- " << **ci << std::endl;
	}
	return os;
}

ReachableTransition::ReachableTransition(const MyPOP::SAS_Plus::Transition& transition, const EquivalentObjectGroupManager& eog_manager)
	: transition_(&transition), equivalent_object_group_manager_(&eog_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "New reachable transition: " << transition << "." << std::endl;
#endif

	// TODO: This assertion fails!
//	assert (preconditions.size() == transition.getFromNode().getAtoms().size());
	
	for (std::vector<const Variable*>::const_iterator ci = transition.getStep()->getAction().getVariables().begin(); ci != transition.getStep()->getAction().getVariables().end(); ci++)
	{
		const Variable* variable = *ci;
		const std::vector<const Object*>& variable_domain = variable->getDomain(transition.getStep()->getStepId(), transition.getFromNode().getDTG().getBindings());
		bool covered = false;
		
		// If the domain is grounded we do not need to care! :D
		if (variable_domain.size() == 1)
		{
			const EquivalentObject& eo = eog_manager.getEquivalentObject(*variable_domain[0]);
			if (eo.getEquivalentObjectGroup().isGrounded()) continue;
		}
		
		
		// Check if this variable is covered by the preconditions.
		for (std::vector<BoundedAtom*>::const_iterator ci = transition.getFromNode().getAtoms().begin(); ci != transition.getFromNode().getAtoms().end(); ci++)
		{
			const BoundedAtom* from_fact = *ci;
			
			for (std::vector<const Term*>::const_iterator ci = from_fact->getAtom().getTerms().begin(); ci != from_fact->getAtom().getTerms().end(); ci++)
			{
				const Term* from_fact_term = *ci;
				if (&from_fact_term->getDomain(from_fact->getId(), transition.getFromNode().getDTG().getBindings()) == &variable_domain)
				{
					covered = true;
					break;
				}
			}
			
			if (covered) break;
		}
		
		if (!covered)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Transition: " << transition << std::endl;
			std::cout << "The variable ";
			variable->print(std::cout, transition.getFromNode().getDTG().getBindings(), transition.getStep()->getStepId());
			std::cout << "is not covered by the atoms in the from node!" << std::endl;
#endif

			// Determine the most efficient way of finding the possible facts for this transition. Which is any grounded nodes!
			const std::vector<std::pair<const Atom*, InvariableIndex> >& all_preconditions = transition.getAllPreconditions();
			
			for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions.begin(); ci != all_preconditions.end(); ci++)
			{
				const Atom* precondition = (*ci).first;
				bool contains_variable_domain = false;
				EquivalentObjectGroup* grounded_object_group = NULL;
				for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
				{
					const Term* precondition_term = *ci;
					const std::vector<const Object*>& precondition_variable = precondition_term->getDomain(transition.getStep()->getStepId(), transition.getFromNode().getDTG().getBindings());
					if (&precondition_variable == &variable_domain)
					{
						contains_variable_domain = true;
					}
					
					else if (precondition_variable.size() == 1)
					{
						EquivalentObjectGroup& eog = eog_manager.getEquivalentObject(*precondition_variable[0]).getEquivalentObjectGroup();
						if (eog.isGrounded())
						{
							grounded_object_group = &eog;
						}
					}
				}
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				if (contains_variable_domain)
				{
					std::cout << "Relevant precondition: ";
					precondition->print(std::cout, transition.getFromNode().getDTG().getBindings(), transition.getStep()->getStepId());
					std::cout << "." << std::endl;
					
					if (grounded_object_group != NULL)
					{
						std::cout << "Grounded object: " << *grounded_object_group << std::endl;
					}
				}
#endif
				
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
				relevant_preconditions_.push_back(std::make_pair(bounded_precondition, grounded_object_group));
			}
		}
	}
}

void ReachableTransition::updateVariables()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	std::cout << "[ReachableTransition::findMappings] ReachableTransition::updateVariables()" << std::endl;
//	std::cout << "[ReachableTransition::findMappings] Transition: " << *transition_ << std::endl;
#endif

	possible_mappings_.clear();
	std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >* mapping =  new std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >();
	findMappings(*mapping, 0);

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
/*	std::cout << "[ReachableTransition::findMappings] All possible mappings found:" << std::endl;
	
	for (std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >::const_iterator ci = possible_mappings_.begin(); ci != possible_mappings_.end(); ci++)
	{
		const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* mapping = *ci;
		
		for (std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator ci = mapping->begin(); ci != mapping->end(); ci++)
		{
			std::cout << "Map: " << (*ci).first << " to ";
			(*ci).second->printObjects(std::cout);
			std::cout << "." << std::endl;
		}
	}
*/
#endif
}

void ReachableTransition::findMappings(std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >& current_mapping, unsigned int index)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
/*	std::cout << "[ReachableTransition::findMappings] " << index << std::endl;
	std::cout << "[ReachableTransition::findMappings] Mappings so far:" << std::endl;
	for (std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >::const_iterator ci = current_mapping.begin(); ci != current_mapping.end(); ci++)
	{
		std::cout << "Map: " << (*ci).first << " to ";
		(*ci).second->printObjects(std::cout);
		std::cout << std::endl;
	}*/
#endif
	
	if (index == relevant_preconditions_.size())
	{
		addMapping(current_mapping);
		return;
	}
	
	const BoundedAtom* precondition = relevant_preconditions_[index].first;
	EquivalentObjectGroup* eog = relevant_preconditions_[index].second;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
/*	std::cout << "Process the precondition: ";
	precondition->print(std::cout, transition_->getFromNode().getDTG().getBindings());
	
	if (eog != NULL)
	{
		std::cout << " grounded EOG: " << *eog->getEquivalentObjects()[0] << "." << std::endl;
	}
	else
	{
		std::cout << " no grounded EOG." << std::endl;
	}*/
#endif

	std::vector<const EquivalentObjectGroup*> groups_to_check;
	
	if (eog != NULL)
	{
		groups_to_check.push_back(eog);
	}
	else
	{
		for (unsigned int i = 0; i < precondition->getAtom().getArity(); i++)
		{
			const std::vector<const Object*>& variable = precondition->getVariableDomain(i, transition_->getFromNode().getDTG().getBindings());
			
			for (std::vector<const Object*>::const_iterator ci = variable.begin(); ci != variable.end(); ci++)
			{
				const Object* object = *ci;
				EquivalentObject& eo = equivalent_object_group_manager_->getEquivalentObject(*object);
				
				EquivalentObjectGroup& root_eog = eo.getEquivalentObjectGroup().getRootNode();
				
				if (std::find(groups_to_check.begin(), groups_to_check.end(), &root_eog) == groups_to_check.end())
				{
					groups_to_check.push_back(&root_eog);
				}
			}
		}
	}

	std::vector<const ReachableFact*> results;
	
	for (std::vector<const EquivalentObjectGroup*>::const_iterator ci = groups_to_check.begin(); ci != groups_to_check.end(); ci++)
	{
		(*ci)->getSupportingFacts(results, *precondition, transition_->getFromNode().getDTG().getBindings());
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	std::cout << "Found reachable facts: " << results.size() << "." << std::endl;
#endif
	
	// Check which reachable facts do not violate the current bindings and add the as possible mappings.
	for (std::vector<const ReachableFact*>::const_iterator ci = results.begin(); ci != results.end(); ci++)
	{
		const ReachableFact* reachable_fact = *ci;
		bool matches = true;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//		std::cout << "Index: " << index << "; Reachable fact: " << *reachable_fact << "." << std::endl;
#endif
		
		std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >* new_current_mapping = new std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >(current_mapping);
		
		for (unsigned int i = 0; i < precondition->getAtom().getArity(); i++)
		{
			const std::vector<const Object*>& variable = precondition->getVariableDomain(i, transition_->getFromNode().getDTG().getBindings());
			
			std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >::const_iterator ci = current_mapping.find(&variable);
			
			if (ci != current_mapping.end())
			{
				if ((*ci).second != &reachable_fact->getTermDomain(i))
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//					std::cout << "Clash at the " << i << "th term!" << std::endl;
#endif
					matches = false;
					break;
				}
			}
			else
			{
				(*new_current_mapping)[&variable] = &reachable_fact->getTermDomain(i);
			}
		}
		
		if (!matches)
		{
			//delete new_current_mapping;
			continue;
		}
		
		findMappings(*new_current_mapping, index + 1);
	}
}

void ReachableTransition::addMapping(const std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >& new_mapping)
{

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
/*	std::cout << "[ReachableTransition::addMapping] " << *transition_ << "." << std::endl;
	for (std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >::const_iterator ci = new_mapping.begin(); ci != new_mapping.end(); ci++)
	{
		const std::vector< const MyPOP::Object* >* domain = (*ci).first;
		const MyPOP::SAS_Plus::EquivalentObjectGroup* eog = (*ci).second;
		std::cout << "Map: {";
		for (std::vector< const MyPOP::Object* >::const_iterator ci = domain->begin(); ci != domain->end(); ci++)
		{
			(*ci)->print(std::cout, transition_->getFromNode().getDTG().getBindings(), transition_->getStep()->getStepId());
			
			if (ci + 1 != domain->end())
			{
				std::cout << ", ";
			}
		}
		std::cout << "} $" << domain << "$ to ";
		eog->printObjects(std::cout);
		std::cout << "." << std::endl;
	}*/
#endif


	// Sanity check.
	/*for (std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >::const_iterator ci = new_mapping.begin(); ci != new_mapping.end(); ci++)
	{
		const std::vector<const Object*>* domain = (*ci).first;
		bool present = false;
		for (std::vector<const Variable*>::const_iterator ci = transition_->getStep()->getAction().getVariables().begin(); ci != transition_->getStep()->getAction().getVariables().end(); ci++)
		{
			if (domain == &(*ci)->getDomain(transition_->getStep()->getStepId(), transition_->getFromNode().getDTG().getBindings()))
			{
				present = true;
				break;
			}
		}
		
		if (!present)
		{
			std::cout << "The mapping: " << domain << " is not present in the variables of the transition!" << std::endl;
			assert (false);
		}
	}*/

	possible_mappings_.push_back(&new_mapping);
}
	
EquivalentObject::EquivalentObject(const Object& object, EquivalentObjectGroup& equivalent_object_group)
	: object_(&object), equivalent_group_(&equivalent_object_group)
{
	
}
	
void EquivalentObject::addInitialFact(const ReachableFact& reachable_fact)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Add " << reachable_fact << " to " << *this << std::endl;
#endif
	if (std::find(initial_facts_.begin(), initial_facts_.end(), &reachable_fact) == initial_facts_.end())
	{
		initial_facts_.push_back(&reachable_fact);
	}
}

bool EquivalentObject::areEquivalent(const EquivalentObject& other) const
{
//	std::cout << "Are " << other << " and " << *this << " equivalent?" << std::endl;

	if (initial_facts_.size() != other.initial_facts_.size() ||
	    initial_facts_.empty())
	{
//		std::cout << initial_facts_.size() << " v.s. " << other.initial_facts_.size() << std::endl;
		return false;
	}
	
	for (std::vector<const ReachableFact*>::const_iterator ci = initial_facts_.begin(); ci != initial_facts_.end(); ci++)
	{
		const ReachableFact* this_reachable_fact = *ci;
		
		bool is_fact_reachable = false;
		for (std::vector<const ReachableFact*>::const_iterator ci = other.initial_facts_.begin(); ci != other.initial_facts_.end(); ci++)
		{
			const ReachableFact* other_reachable_fact = *ci;
			
			if (this_reachable_fact->isEquivalentTo(*other_reachable_fact))
			{
				is_fact_reachable = true;
				break;
			}
		}
		
		if (!is_fact_reachable)
		{
//			std::cout << "The fact: " << *this_reachable_fact << " is not reachable!" << std::endl;
			return false;
		}
	}

//	std::cout << "Are equivalent!" << std::endl;
	return true;
}

std::ostream& operator<<(std::ostream& os, const EquivalentObject& equivalent_object)
{
	os << *equivalent_object.object_;
/*	os << " {" << std::endl;
	for (std::vector<const ReachableFact*>::const_iterator ci = equivalent_object.initial_facts_.begin(); ci != equivalent_object.initial_facts_.end(); ci++)
	{
		(*ci)->bounded_atom_->print(os, *(*ci)->bindings_);
		os << " (" << (*ci)->index_ << ")" << std::endl;
	}
	os << " }";*/
	return os;
}

EquivalentObjectGroup::EquivalentObjectGroup(const DomainTransitionGraph& dtg_graph, const Object* object, bool is_grounded)
	: dtg_graph_(&dtg_graph), is_grounded_(is_grounded), link_(NULL)
{
	if (object != NULL)
	{
		initialiseFingerPrint(*object);
	}
}

bool EquivalentObjectGroup::isRootNode() const
{
	return link_ == NULL;
}

bool EquivalentObjectGroup::contains(const Object& object) const
{
	for (std::vector<const EquivalentObject*>::const_iterator ci = equivalent_objects_.begin(); ci != equivalent_objects_.end(); ci++)
	{
		const EquivalentObject* eo = *ci;
		if (&eo->getObject() == &object) return true;
	}
	return false;
}

bool EquivalentObjectGroup::isIdenticalTo(EquivalentObjectGroup& other)
{
	return getRootNode() == other.getRootNode();
}
	
void EquivalentObjectGroup::initialiseFingerPrint(const Object& object)
{
	// Check the DTG graph and check which DTG nodes an object can be part of based on its type.
	unsigned int number_of_facts = 0;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			number_of_facts += (*ci)->getAtom().getArity();
		}
	}
	
	finger_print_size_ = number_of_facts;
	finger_print_ = new bool[number_of_facts];
	memset(&finger_print_[0], false, sizeof(bool) * number_of_facts);
	
	number_of_facts = 0;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
			{
				const Term* term = *ci;
				
				if (object.getType()->isSubtypeOf(*term->getType()) || object.getType()->isEqual(*term->getType()))
				{
					finger_print_[number_of_facts] = true;
				}
				++number_of_facts;
			}
		}
	}
}

bool EquivalentObjectGroup::makeReachable(const DomainTransitionGraphNode& dtg_node, const BoundedAtom& bounded_atom, ReachableFact& reachable_fact)
{
//	std::cout << "Try to make reachable: " << reachable_fact << " in this context: " << *this << std::endl;
	bool added_something = false;
	std::pair<std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator, std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator> ret;
	std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci;
	
	ret = reachable_facts_.equal_range(std::make_pair(&dtg_node, &bounded_atom));
	bool already_part = false;
	for (ci = ret.first; ci != ret.second; ci++)
	{
		if ((*ci).second->isIdenticalTo(reachable_fact))
		{
//			std::cout << "Found equivalent reachable fact: " << *(*ci).second << std::endl;
			already_part = true;
			break;
		}
	}
	
	if (!already_part)
	{
		reachable_facts_.insert(std::make_pair(std::make_pair(&dtg_node, &bounded_atom), &reachable_fact));
		added_something = true;
	}
	
	for (std::vector<const Property*>::const_iterator ci = bounded_atom.getProperties().begin(); ci != bounded_atom.getProperties().end(); ci++)
	{
		const Property* property = *ci;
		
		std::pair<std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator, std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator> ret;
		std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator ci;
		
		ret = reachable_properties_.equal_range(std::make_pair(property->getPredicate().getName(), property->getIndex()));
		bool already_part = false;
		for (ci = ret.first; ci != ret.second; ci++)
		{
			if ((*ci).second->isIdenticalTo(reachable_fact))
			{
//				std::cout << "Found equivalent property: " << *(*ci).second << std::endl;
				already_part = true;
				break;
			}
		}
		
		if (!already_part)
		{
			added_something = true;
			reachable_properties_.insert(std::make_pair(std::make_pair(property->getPredicate().getName(), property->getIndex()), &reachable_fact));
		}
	}
	return added_something;
}


bool EquivalentObjectGroup::makeReachable(ReachableFact& reachable_fact)
{
	bool added_something = false;
//	std::cout << "Try to make " << reachable_fact << " reachable in this context: " << *this << "." << std::endl;
	
	for (std::vector<const Property*>::const_iterator ci = reachable_fact.getBoundedAtom().getProperties().begin(); ci != reachable_fact.getBoundedAtom().getProperties().end(); ci++)
	{
		const Property* property = *ci;
		
		std::pair<std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator, std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator> ret;
		std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator ci;
		
		ret = reachable_properties_.equal_range(std::make_pair(property->getPredicate().getName(), property->getIndex()));
		bool already_part = false;
		for (ci = ret.first; ci != ret.second; ci++)
		{
			if ((*ci).second->isIdenticalTo(reachable_fact))
			{
//				std::cout << "Is identical to: " << *(*ci).second << std::endl;
				already_part = true;
				break;
			}
		}
		
		if (!already_part)
		{
			added_something = true;
			reachable_properties_.insert(std::make_pair(std::make_pair(property->getPredicate().getName(), property->getIndex()), &reachable_fact));
		}
	}
	return added_something;
}

void EquivalentObjectGroup::addEquivalentObject(const EquivalentObject& eo)
{
	equivalent_objects_.push_back(&eo);
}

void EquivalentObjectGroup::getSupportingFacts(std::vector<const ReachableFact*>& results, const DomainTransitionGraphNode& dtg_node, const BoundedAtom& bounded_atom) const
{
	std::pair<std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator, std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator> ret;
	std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci;
	
	ret = reachable_facts_.equal_range(std::make_pair(&dtg_node, &bounded_atom));
	for (ci = ret.first; ci != ret.second; ci++)
	{
		results.push_back((*ci).second);
	}
}

void EquivalentObjectGroup::getSupportingFacts(std::vector<const ReachableFact*>& results, const BoundedAtom& bounded_atom, const Bindings& bindings) const
{
	if (bounded_atom.getProperties().empty())
	{
		std::cout << "The bounded atom: ";
		bounded_atom.print(std::cout, bindings);
		std::cout << " contains no properties!" << std::endl;
		assert (false);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	std::cout << "Find supporting facts for: ";
//	bounded_atom.print(std::cout, bindings);
//	std::cout << std::endl;
#endif
	
	for (std::vector<const Property*>::const_iterator ci = bounded_atom.getProperties().begin(); ci != bounded_atom.getProperties().end(); ci++)
	{
		const Property* property = *ci;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//		std::cout << "Possible property: " << *property << "." << std::endl;
#endif
		
		std::pair<std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator, std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator> ret;
		std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator it;
		
		ret = reachable_properties_.equal_range(std::make_pair(property->getPredicate().getName(), property->getIndex()));
		
		for (it = ret.first; it != ret.second; it++)
		{
			ReachableFact* reachable_candidate = (*it).second;
			
			bool matches = true;
			for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
			{
				const std::vector<const Object*>& variable_domain = bounded_atom.getVariableDomain(i, bindings);
				const EquivalentObjectGroup& eog = reachable_candidate->getTermDomain(i);
				
				bool overlaps = false;
				
				for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ci++)
				{
					const Object* object = *ci;
					if (eog.contains(*object))
					{
						overlaps = true;
						break;
					}
				}
				
				if (!overlaps)
				{
					matches = false;
					break;
				}
			}
			
			if (matches)
			{
				// Make sure not to include the same result multiple times!
				bool already_part = false;
				for (std::vector<const ReachableFact*>::const_iterator ci = results.begin(); ci != results.end(); ci++)
				{
					if (reachable_candidate->isIdenticalTo(**ci))
					{
						already_part = true;
//						std::cout << *reachable_candidate << " was already added!" << std::endl;
//						assert (false);
						break;
					}
				}
				
				if (!already_part)
				{
//					std::cout << "Add: " << *reachable_candidate << "." << std::endl;
					results.push_back(reachable_candidate);
				}
			}
		}
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	if (results.empty())
//	{
//		std::cout << "No reacahble facts :((." << std::endl;
//	}
//	else
//	{
//		std::cout << "Reachable facts: " << std::endl;
//		for (std::vector<const ReachableFact*>::const_iterator ci = results.begin(); ci != results.end(); ci++)
//		{
//			std::cout << "* " << **ci << "." << std::endl;
//		}
//	}
#endif
}

bool EquivalentObjectGroup::tryToMergeWith(EquivalentObjectGroup& other_group, const std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* >& reachable_nodes)
{
	// If the object has been grounded it cannot be merged!
	if (is_grounded_ || other_group.is_grounded_)
	{
		return false;
	}
	
	// If two object groups are part of the same root node they are already merged!
	EquivalentObjectGroup& this_root_node = getRootNode();
	EquivalentObjectGroup& other_root_node = other_group.getRootNode();
	if (&this_root_node == &other_root_node)
	{
		return true;
	}
	
	// Make sure to only call this method with the root nodes.
	if (link_ != NULL)
	{
		return this_root_node.tryToMergeWith(other_root_node, reachable_nodes);
	}
	else if (other_group.link_ != NULL)
	{
		return tryToMergeWith(other_root_node, reachable_nodes);
	}

	// Only allow to merge two equivalent object groups if the fingerprints are equal!
	assert (finger_print_size_ == other_group.finger_print_size_);
	if (memcmp(finger_print_, other_group.finger_print_, finger_print_size_) != 0)
	{
		return false;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Try to merge: " << *this << " with " << other_group << "." << std::endl;
#endif

	for (std::vector<const EquivalentObject*>::const_iterator ci = other_group.equivalent_objects_.begin(); ci != other_group.equivalent_objects_.end(); ci++)
	{
		const EquivalentObject* other_equivalent_object = *ci;
		const std::vector<const ReachableFact*>& initial_facts = other_equivalent_object->getInitialFacts();
		
		bool all_initial_facts_reachable = initial_facts.size() > 0;
		for (std::vector<const ReachableFact*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
		{
			const ReachableFact* initial_fact = *ci;
			
			bool initial_fact_reached = false;
			for (std::vector<const Property*>::const_iterator ci = initial_fact->getBoundedAtom().getProperties().begin(); ci != initial_fact->getBoundedAtom().getProperties().end(); ci++)
			{
				const Property* property = *ci;
				std::pair<std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator, std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator> ret;
				std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator i;
				
				ret = reachable_properties_.equal_range(std::make_pair(property->getPredicate().getName(), property->getIndex()));
				
				for (i = ret.first; i != ret.second; i++)
				{
					ReachableFact* reachable_fact = (*i).second;
					if (initial_fact->isEquivalentTo(*reachable_fact))
					{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << *reachable_fact << "is equivalent to " << *initial_fact << "." << std::endl;
#endif
						initial_fact_reached = true;
						break;
					}
				}
				
				if (initial_fact_reached) break;
			}
			
			if (!initial_fact_reached)
			{
				all_initial_facts_reachable = false;
				break;
			}
		}
		
		if (!all_initial_facts_reachable) return false;
		else break;
	}
	
	for (std::vector<const EquivalentObject*>::const_iterator ci = equivalent_objects_.begin(); ci != equivalent_objects_.end(); ci++)
	{
		const EquivalentObject* other_equivalent_object = *ci;
		const std::vector<const ReachableFact*>& initial_facts = other_equivalent_object->getInitialFacts();
		
		bool all_initial_facts_reachable = initial_facts.size() > 0;
		for (std::vector<const ReachableFact*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
		{
			const ReachableFact* initial_fact = *ci;
			
			bool initial_fact_reached = false;
			for (std::vector<const Property*>::const_iterator ci = initial_fact->getBoundedAtom().getProperties().begin(); ci != initial_fact->getBoundedAtom().getProperties().end(); ci++)
			{
				const Property* property = *ci;
				std::pair<std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator, std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator> ret;
				std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator i;
				
				ret = other_group.reachable_properties_.equal_range(std::make_pair(property->getPredicate().getName(), property->getIndex()));
				
				for (i = ret.first; i != ret.second; i++)
				{
					ReachableFact* reachable_fact = (*i).second;
					if (initial_fact->isEquivalentTo(*reachable_fact))
					{
						initial_fact_reached = true;
						break;
					}
				}
				
				if (initial_fact_reached) break;
			}
			
			if (!initial_fact_reached)
			{
				all_initial_facts_reachable = false;
				break;
			}
		}
		
		if (!all_initial_facts_reachable) return false;
		else break;
	}
	
	merge(other_group);
	return true;
}

bool EquivalentObjectGroup::operator==(const EquivalentObjectGroup& other) const
{
	// Determine the root nodes.
	const EquivalentObjectGroup* this_root = this;
	const EquivalentObjectGroup* other_root = &other;
	while (other_root->link_ != NULL) other_root = other_root->link_;
	while (this_root->link_ != NULL) this_root = this_root->link_;
	
	return this_root == other_root;
}

bool EquivalentObjectGroup::operator!=(const EquivalentObjectGroup& other) const
{
	return !(*this == other);
}

void EquivalentObjectGroup::printObjects(std::ostream& os) const
{
	for (std::vector<const EquivalentObject*>::const_iterator ci = equivalent_objects_.begin(); ci != equivalent_objects_.end(); ci++)
	{
		os << (*ci)->getObject();
		if (ci + 1 != equivalent_objects_.end())
		{
			os << ", ";
		}
	}
}

void EquivalentObjectGroup::printGrounded(std::ostream& os) const
{
	for (std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		(*ci).second->printGrounded(os);
	}
}

void EquivalentObjectGroup::getAllReachableFacts(std::vector<const BoundedAtom*>& results, const std::set<const EquivalentObjectGroup*>& processed_eogs) const
{
	for (std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		const ReachableFact* reachable_fact = (*ci).second;
//		std::cerr << "Process: " << *reachable_fact << "." << std::endl;
		bool already_processed = false;
		for (unsigned int i = 0; i < reachable_fact->getBoundedAtom().getAtom().getArity(); i++)
		{
			if (!reachable_fact->getTermDomain(i).isRootNode() || processed_eogs.count(&reachable_fact->getTermDomain(i)) != 0)
			{
				already_processed = true;
//				std::cerr << "Skip!" << std::endl;
				break;
			}
		}
		
		if (already_processed) continue;
		
		(*ci).second->getAllReachableFacts(results);
	}
}


void EquivalentObjectGroup::merge(EquivalentObjectGroup& other_group)
{
	assert (other_group.link_ == NULL);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Merging " << *this << " with " << other_group << "." << std::endl;
#endif
	
	equivalent_objects_.insert(equivalent_objects_.begin(), other_group.equivalent_objects_.begin(), other_group.equivalent_objects_.end());
	reachable_facts_.insert(other_group.reachable_facts_.begin(), other_group.reachable_facts_.end());
	reachable_properties_.insert(other_group.reachable_properties_.begin(), other_group.reachable_properties_.end());
	other_group.link_ = this;
	
//	std::cout << "Result " << *this << "." << std::endl;
	
}

EquivalentObjectGroup& EquivalentObjectGroup::getRootNode()
{
	if (link_ == NULL)
		return *this;
	return link_->getRootNode();
}

std::ostream& operator<<(std::ostream& os, const EquivalentObjectGroup& group)
{
	if (group.link_ != NULL)
	{
		os << *group.link_;
		return os;
	}
	
//	os << " -= EquivalentObjectGroup =- " << std::endl;
	os << "{ ";
	for (std::vector<const EquivalentObject*>::const_iterator ci = group.equivalent_objects_.begin(); ci != group.equivalent_objects_.end(); ci++)
	{
		const EquivalentObject* eo = *ci;
		os << eo->getObject();
		if (ci + 1 != group.equivalent_objects_.end())
		{
			os << ", ";
		}
	}
	os << " }" << std::endl;

	std::cout << "Reachable properties: " << std::endl;
	for (std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator ci = group.reachable_properties_.begin(); ci != group.reachable_properties_.end(); ci++)
	{
		std::cout << "- " << *(*ci).second << std::endl;
	}
	
	std::cout << "Reachable facts: " << std::endl;
	for (std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci = group.reachable_facts_.begin(); ci != group.reachable_facts_.end(); ci++)
	{
		std::cout << "- " << *(*ci).second << std::endl;
	}

	return os;
}

EquivalentObjectGroupManager::EquivalentObjectGroupManager(const DTGReachability& dtg_reachability, const DomainTransitionGraphManager& dtg_manager, const DomainTransitionGraph& dtg_graph, const TermManager& term_manager, const std::vector<const BoundedAtom*>& initial_facts)
	: dtg_reachability_(&dtg_reachability)
{
	// Create initial data structures.
	for (std::vector<const Object*>::const_iterator ci = term_manager.getAllObjects().begin(); ci != term_manager.getAllObjects().end(); ci++)
	{
		const Object* object = *ci;
		EquivalentObjectGroup* equivalent_object_group = new EquivalentObjectGroup(dtg_graph, object, dtg_manager.isObjectGrounded(*object));
		EquivalentObject* equivalent_object = new EquivalentObject(*object, *equivalent_object_group);
		equivalent_object_group->addEquivalentObject(*equivalent_object);
		
		equivalent_groups_.push_back(equivalent_object_group);
		object_to_equivalent_object_mapping_[object] = equivalent_object;
	}

	EquivalentObjectGroup* zero_arity_equivalent_object_group = new EquivalentObjectGroup(dtg_graph, NULL, true);
	equivalent_groups_.push_back(zero_arity_equivalent_object_group);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Done initialising data structures." << std::endl;
#endif
	
	// Look for the DTG nodes which are supported in the initial state.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		const std::vector<BoundedAtom*>& atoms_to_achieve = dtg_node->getAtoms();
		std::vector<std::vector<const BoundedAtom*>* > supporting_tupples;
		std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > variable_assignments;
		std::vector<const BoundedAtom*> initial_supporting_facts;
		
		std::cout << "Process the DTG node: " << *dtg_node << std::endl;
		
		dtg_reachability.getSupportingFacts(supporting_tupples, variable_assignments, atoms_to_achieve, initial_supporting_facts, initial_facts);

		for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = supporting_tupples.begin(); ci != supporting_tupples.end(); ci++)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Found a set of supporting facts for the DTG node: " << std::endl;
			dtg_node->print(std::cout);
			std::cout << std::endl;
#endif
			const std::vector<const BoundedAtom*>* supporting_tupple = *ci;
			
			std::vector<const ReachableFact*>* reachable_facts = new std::vector<const ReachableFact*>();

			for (std::vector<const BoundedAtom*>::const_iterator ci = supporting_tupple->begin(); ci != supporting_tupple->end(); ci++)
			{
				const BoundedAtom* bounded_atom = *ci;
				
				unsigned int index = std::distance(supporting_tupple->begin(), ci);
				
				ReachableFact* reachable_fact = new ReachableFact(*bounded_atom, dtg_node->getDTG().getBindings(), *this);
				reachable_facts->push_back(reachable_fact);
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << " * ";
				bounded_atom->print(std::cout, dtg_graph.getBindings());
				std::cout << "." << std::endl;
#endif
				
				for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
				{
					const Property* property = *ci;
					//if (property->getIndex() == NO_INVARIABLE_INDEX)
					//	continue;
					
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "the index " << property->getIndex() << " of the atom ";
					bounded_atom->print(std::cout, dtg_graph.getBindings());
					std::cout << " is invariable!" << std::endl;
#endif
					
					if (property->getIndex() == NO_INVARIABLE_INDEX)
					{
						for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
						{
							const std::vector<const Object*>& domain = bounded_atom->getVariableDomain(i, dtg_graph.getBindings());
							for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
							{
								EquivalentObject* equivalent_object = object_to_equivalent_object_mapping_[*ci];
								assert (equivalent_object != NULL);
								
//								equivalent_object->addInitialFact(*reachable_fact);
								equivalent_object->getEquivalentObjectGroup().makeReachable(*dtg_node, *dtg_node->getAtoms()[index], *reachable_fact);
							}
						}
					}
					else
					{
						const std::vector<const Object*>& domain = bounded_atom->getVariableDomain(property->getIndex(), dtg_graph.getBindings());
						for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
						{
							EquivalentObject* equivalent_object = object_to_equivalent_object_mapping_[*ci];
							assert (equivalent_object != NULL);
							
//							equivalent_object->addInitialFact(*reachable_fact);
							equivalent_object->getEquivalentObjectGroup().makeReachable(*dtg_node, *dtg_node->getAtoms()[index], *reachable_fact);
						}
					}
				}
				
				if (bounded_atom->getAtom().getArity() == 0)
				{
					zero_arity_equivalent_object_group->makeReachable(*reachable_fact);
				}
			}
			
			ReachableNode* reachable_node = new ReachableNode(*dtg_node, *reachable_facts);
			supported_dtg_nodes_.insert(std::make_pair(dtg_node, reachable_node));
		}
	}
	
	// Make initial facts reachable and initialise the initial states.
	std::vector<BoundedAtom*> bounded_initial_facts;
	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		BoundedAtom* new_bounded_atom = new BoundedAtom(bounded_atom->getId(), bounded_atom->getAtom(), bounded_atom->getProperties());
		bounded_initial_facts.push_back(new_bounded_atom);
		
		// Fill in the missing gaps :).
		for (unsigned int i = 0; i < new_bounded_atom->getAtom().getArity(); i++)
		{
			bool supported = false;
			for (std::vector<const Property*>::const_iterator ci = new_bounded_atom->getProperties().begin(); ci != new_bounded_atom->getProperties().end(); ci++)
			{
				if ((*ci)->getIndex() == i)
				{
					supported = true;
					break;
				}
			}
			
			if (supported) continue;
			
			PropertySpace* ps = new PropertySpace();
			std::vector<std::pair<const Predicate*, InvariableIndex> >* predicates = new std::vector<std::pair<const Predicate*, InvariableIndex> >();
			predicates->push_back(std::make_pair(&new_bounded_atom->getAtom().getPredicate(), NO_INVARIABLE_INDEX));
			PropertyState* pst = new PropertyState(*ps, *predicates);
			new_bounded_atom->addProperty(*pst->getProperties()[0]);
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = bounded_initial_facts.begin(); ci != bounded_initial_facts.end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		EquivalentObjectGroup** initial_eog = new EquivalentObjectGroup*[bounded_atom->getAtom().getArity()];
		std::vector<EquivalentObjectGroup*> eog_cache;
		
		for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
		{
			EquivalentObjectGroup& eog = object_to_equivalent_object_mapping_[bounded_atom->getVariableDomain(i, dtg_graph.getBindings())[0]]->getEquivalentObjectGroup();
			eog_cache.push_back(&eog);
			initial_eog[i] = &eog;
		}
		
		ReachableFact* rf = new ReachableFact(*bounded_atom, dtg_graph.getBindings(), initial_eog);
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci = eog_cache.begin(); ci != eog_cache.end(); ci++)
		{
			EquivalentObjectGroup* eog = *ci;
			eog->makeReachable(*rf);
			
			for (std::vector<const EquivalentObject*>::const_iterator ci = eog->getEquivalentObjects().begin(); ci != eog->getEquivalentObjects().end(); ci++)
			{
				const_cast<EquivalentObject*>((*ci))->addInitialFact(*rf);
			}
		}
	}
	
	// try to merge EOGs.
	std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* > reachable_nodes;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		std::vector<const DomainTransitionGraphNode*>* self_reachable_node_list = new std::vector<const DomainTransitionGraphNode*>();
		self_reachable_node_list->push_back(dtg_node);
		reachable_nodes[dtg_node] = self_reachable_node_list;
	}
	
	bool merge_mask[equivalent_groups_.size()];
	memset(&merge_mask[0], false, sizeof(bool) * equivalent_groups_.size());
	unsigned int index1 = 0;
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end() - 1; ci++)
	{
		if (merge_mask[index1])
		{
			++index1;
			continue;
		}
		EquivalentObjectGroup* eog1 = *ci;
		
		unsigned int index2 = index1 + 1;
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci2 = ci + 1; ci2 != equivalent_groups_.end(); ci2++)
		{
			EquivalentObjectGroup* eog2 = *ci2;
			
			if (merge_mask[index2])
			{
				++index2;
				continue;
			}
			if (eog1->tryToMergeWith(*eog2, reachable_nodes))
			{
				merge_mask[index2] = true;
			}
			++index2;
		}
		++index1;
	}
	
	for (std::vector<EquivalentObjectGroup*>::reverse_iterator ri = equivalent_groups_.rbegin(); ri != equivalent_groups_.rend(); ri++)
	{
		unsigned int index = std::distance(equivalent_groups_.begin(), ri.base() - 1);
		if (merge_mask[index])
		{
			equivalent_groups_.erase(ri.base() - 1);
		}
	}
	
	deleteMergedEquivalenceGroups();
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Merge together equivalent groups if their initial states match - Done!" << std::endl;
	std::cout << "EOG manager Ready for use!" << std::endl;
	print(std::cout);
	printAll(std::cout);
#endif
}


void EquivalentObjectGroupManager::deleteMergedEquivalenceGroups()
{
	bool dirty = true;
	while (dirty)
	{
		dirty = false;
		for (std::multimap<const DomainTransitionGraphNode*, const ReachableNode*>::iterator i = supported_dtg_nodes_.begin(); i != supported_dtg_nodes_.end(); i++)
		{
			std::pair<const DomainTransitionGraphNode*, const ReachableNode*> item = *i;
			const ReachableNode* reachable_node = item.second;
			reachable_node->sanityCheck();
			bool remove = false;
			
			for (std::vector<const ReachableFact*>::const_iterator ci = reachable_node->getSupportingFacts().begin(); ci != reachable_node->getSupportingFacts().end(); ci++)
			{
				const ReachableFact* fact = *ci;
				
				if (fact->containsNonRootEOG())
				{
					remove = true;
					break;
				}
			}
			
			if (remove)
			{
				supported_dtg_nodes_.erase(i);
				dirty = true;
				break;
			}
			
			reachable_node->sanityCheck();
		}
	}
}

void EquivalentObjectGroupManager::getSupportingFacts(std::vector<const ReachableNode*>& results, const DomainTransitionGraphNode& dtg_node) const
{
	std::pair<std::multimap<const DomainTransitionGraphNode*, const ReachableNode* >::const_iterator, std::multimap<const DomainTransitionGraphNode*, const ReachableNode* >::const_iterator> ret;
	std::multimap<const DomainTransitionGraphNode*, const ReachableNode* >::const_iterator ci;
	
	ret = supported_dtg_nodes_.equal_range(&dtg_node);
	
	for (ci = ret.first; ci != ret.second; ci++)
	{
		const ReachableNode* reached_node = (*ci).second;
		reached_node->sanityCheck();
		results.push_back(reached_node);
	}
}

void EquivalentObjectGroupManager::getSupportingFacts(std::vector<const ReachableFact*>& results, const BoundedAtom& bounded_atom, const Bindings& bindings) const
{
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end(); ci++)
	{
		assert ((*ci)->isRootNode());
		(*ci)->getSupportingFacts(results, bounded_atom, bindings);
	}
}

void EquivalentObjectGroupManager::updateEquivalences(const std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* >& reachable_nodes_)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[EquivalentObjectGroupManager::updateEquivalences]" << std::endl;
#endif
	bool to_remove[equivalent_groups_.size()];
	memset(&to_remove[0], false, sizeof(bool) * equivalent_groups_.size());
	
	// Check if an initial mapping for an object can be reached from the initial mapping of another object.
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end() - 1; ci++)
	{
		EquivalentObjectGroup* equivalent_group1 = *ci;
		if (to_remove[std::distance((std::vector<EquivalentObjectGroup*>::const_iterator)equivalent_groups_.begin(), ci)])
		{
			continue;
		}
		
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci2 = ci + 1; ci2 != equivalent_groups_.end(); ci2++)
		{
			EquivalentObjectGroup* equivalent_group2 = *ci2;
			if (to_remove[std::distance((std::vector<EquivalentObjectGroup*>::const_iterator)equivalent_groups_.begin(), ci2)])
			{
				continue;
			}
			
			// Check if any of the initial DTG nodes of both groups can be reached from one another.
			if (equivalent_group1->tryToMergeWith(*equivalent_group2, reachable_nodes_))
			{
				// Remove group2 if it has merged with group 1.
				to_remove[std::distance((std::vector<EquivalentObjectGroup*>::const_iterator)equivalent_groups_.begin(), ci2)] = true;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << *equivalent_group2 << " has been merged with " << *equivalent_group1 << "." << std::endl;
#endif
			}
		}
	}
	
	// Remove the nodes which have been merged.
	for (int i = equivalent_groups_.size() - 1; i > -1; i--)
	{
		if (to_remove[i])
		{
			equivalent_groups_.erase(equivalent_groups_.begin() + i);
		}
	}
}


EquivalentObject& EquivalentObjectGroupManager::getEquivalentObject(const Object& object) const
{
	std::map<const Object*, EquivalentObject*>::const_iterator ci = object_to_equivalent_object_mapping_.find(&object);
	assert (ci != object_to_equivalent_object_mapping_.end());
	
	return *(*ci).second;
}

bool EquivalentObjectGroupManager::makeReachable(const DomainTransitionGraphNode& dtg_node, const ReachableNode& reachable_node)
{
	for (std::vector<const ReachableFact*>::const_iterator ci = reachable_node.getSupportingFacts().begin(); ci != reachable_node.getSupportingFacts().end(); ci++)
	{
		ReachableFact* reachable_fact = const_cast<ReachableFact*>(*ci);
		
		for (unsigned int i = 0; i < reachable_fact->getBoundedAtom().getAtom().getArity(); i++)
		{
			EquivalentObjectGroup& eog = reachable_fact->getTermDomain(i);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			if (eog.makeReachable(dtg_node, reachable_fact->getBoundedAtom(), *reachable_fact))
			{
				std::cout << "New reachable fact: " << *reachable_fact << "." << std::endl;
			}
#else
			eog.makeReachable(dtg_node, reachable_fact->getBoundedAtom(), *reachable_fact);
#endif
		}
	}
	
	std::pair<std::multimap<const DomainTransitionGraphNode*, const ReachableNode*>::const_iterator, std::multimap<const DomainTransitionGraphNode*, const ReachableNode*>::const_iterator> ret;
	std::multimap<const DomainTransitionGraphNode*, const ReachableNode*>::const_iterator ci;
	
	ret = supported_dtg_nodes_.equal_range(&dtg_node);
	
	for (ci = ret.first; ci != ret.second; ci++)
	{
		const ReachableNode* already_reachable_node = (*ci).second;
		if (already_reachable_node->isIdenticalTo(reachable_node)) return false;
	}
	
	supported_dtg_nodes_.insert(std::make_pair(&dtg_node, &reachable_node));
	return true;
}


void EquivalentObjectGroupManager::print(std::ostream& os) const
{
	os << "All equivalence groups:" << std::endl;
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end(); ci++)
	{
		os << **ci << std::endl;
	}
}
	

void EquivalentObjectGroupManager::printAll(std::ostream& os) const
{
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end(); ci++)
	{
		std::cout << "Print all grounded facts of the EOG: " << **ci << std::endl;
		
		(*ci)->printGrounded(os);
//		os << **ci << std::endl;
	}
}

void EquivalentObjectGroupManager::getAllReachableFacts(std::vector<const BoundedAtom*>& results) const
{
	std::set<const EquivalentObjectGroup*> processed_eogs;
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end(); ci++)
	{
		(*ci)->getAllReachableFacts(results, processed_eogs);
		processed_eogs.insert(&(*ci)->getRootNode());
	}
}

/*******************************
 * DTGReachability
*******************************/

DTGReachability::DTGReachability(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::SAS_Plus::DomainTransitionGraph& dtg_graph, const MyPOP::TermManager& term_manager, const std::vector< const MyPOP::SAS_Plus::BoundedAtom* >& initial_facts)
	: dtg_manager_(&dtg_manager), dtg_graph_(&dtg_graph), term_manager_(&term_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "DTG Reachability on graph: " << dtg_graph << "." << std::endl;
#endif

	// Initialise the individual groups per object.
	equivalent_object_manager_ = new EquivalentObjectGroupManager(*this, *dtg_manager_, *dtg_graph_, term_manager, initial_facts);

	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		supported_facts_[dtg_node] = new std::vector<std::vector<const BoundedAtom*> *>();
		std::vector<const DomainTransitionGraphNode*>* reachable_dtg_nodes = new std::vector<const DomainTransitionGraphNode*>();
		reachable_dtg_nodes->push_back(dtg_node);
		reachable_nodes_[dtg_node] = reachable_dtg_nodes;
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			reachable_transitions_[*ci] = new ReachableTransition(**ci, *equivalent_object_manager_);
		}
	}
}

bool DTGReachability::makeToNodeReachable(const Transition& transition, const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& possible_mapping) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::makeToNodeReachable]" << std::endl;
	
	const ReachableTransition& reachable_transition = getReachableTransition(transition);
	
	const std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >& reachable_transition_mappings = reachable_transition.getPossibleMappings();
	for (std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >::const_iterator ci = reachable_transition_mappings.begin(); ci != reachable_transition_mappings.end(); ci++)
	{
		std::cout << "Reachable transitions: " << std::endl;
		const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* reachable_mappings = *ci;
		
		for (std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator ci = reachable_mappings->begin(); ci != reachable_mappings->end(); ci++)
		{
			std::cout << "Map: ";
			
			const std::vector<const Object*>* domain = (*ci).first;
			const EquivalentObjectGroup* eog = (*ci).second;
			for (std::vector<const Object*>::const_iterator ci = domain->begin(); ci != domain->end(); ci++)
			{
				(*ci)->print(std::cout, transition.getToNode().getDTG().getBindings(), transition.getStep()->getStepId());
				if (ci + 1 != domain->end())
					std::cout << ", ";
			}
			std::cout << "$" << domain << "$" << std::endl;
			
			std::cout << " to: ";
			eog->printObjects(std::cout);
			std::cout << "." << std::endl;
		}
	}

	std::cout << "Other mappings: " << std::endl;

	for (std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator ci = possible_mapping.begin(); ci != possible_mapping.end(); ci++)
	{
		std::cout << "Map: ";
		
		const std::vector<const Object*>* domain = (*ci).first;
		const EquivalentObjectGroup* eog = (*ci).second;
		for (std::vector<const Object*>::const_iterator ci = domain->begin(); ci != domain->end(); ci++)
		{
			(*ci)->print(std::cout, transition.getToNode().getDTG().getBindings(), transition.getStep()->getStepId());
			if (ci + 1 != domain->end())
				std::cout << ", ";
		}
		std::cout << domain << std::endl;
		//std::cout << " to: " << *eog << "." << std::endl;
		std::cout << " to: ";
		eog->printObjects(std::cout);
		std::cout << "." << std::endl;
	}
#endif

	std::vector<const ReachableFact*>* reachable_facts[transition.getToNode().getAtoms().size()];
	const Bindings& bindings = transition.getToNode().getDTG().getBindings();
	
	for (unsigned int i = 0; i < transition.getToNode().getAtoms().size(); i++)
	{
		reachable_facts[i] = new std::vector<const ReachableFact*>();
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = transition.getToNode().getAtoms().begin(); ci != transition.getToNode().getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		unsigned int index = std::distance(transition.getToNode().getAtoms().begin(), ci);
		
		// Check to which effect this bounded_atom is linked to (if any).
		const Atom* linked_effect = NULL;
		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition.getEffects().begin(); ci != transition.getEffects().end(); ci++)
		{
			const Atom* effect = (*ci).first;
			if (bindings.areIdentical(*effect, transition.getStep()->getStepId(), bounded_atom->getAtom(), bounded_atom->getId()))
			{
				linked_effect = effect;
				break;
			}
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "(" << bounded_atom->getAtom().getPredicate().getName();
#endif

		// Iterate over all possible reachable facts.
		bool done = false;
		unsigned int counter[bounded_atom->getAtom().getArity()];
		memset(&counter[0], 0, sizeof(unsigned int) * bounded_atom->getAtom().getArity());
		
		bool unmapping[bounded_atom->getAtom().getArity()];
		memset(&unmapping[0], false, sizeof(bool) * bounded_atom->getAtom().getArity());

		while (!done)
		{
			done = true;
			EquivalentObjectGroup** term_domain_mapping = new EquivalentObjectGroup*[bounded_atom->getAtom().getArity()];
		
			std::set<EquivalentObjectGroup*> tmp;
			for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
			{
				
				// Check if this term is a free variable.
				bool free_variable = false;
				if (linked_effect != NULL)
				{
					const Term* term = linked_effect->getTerms()[i];
					if (transition.isVariableFree(*term))
					{
						free_variable = true;
					}
				}
				
				const std::vector<const Object*>& variable_domain = bounded_atom->getVariableDomain(i, bindings);
				std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator find_ci = possible_mapping.find(&variable_domain);
				
				/**
				 * In some cases the terms of some of the effects of an action are not present in the preconditions. In our 
				 * terms this must mean that the term is lifted and is not restricted by the action.
				 */
				if (free_variable || find_ci == possible_mapping.end())
				{
					unmapping[i] = true;
					const Object* object = variable_domain[counter[i]];

					EquivalentObjectGroup* tmp_eog = const_cast<EquivalentObjectGroup*>(&equivalent_object_manager_->getEquivalentObject(*object).getEquivalentObjectGroup());
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					if (free_variable)
					{
						std::cout << "*(free_variable)*";
					}
					else
					{
						std::cout << "*(no mapping found)*";
					}
					tmp_eog->printObjects(std::cout);
					std::cout << "*";
#endif
					tmp.insert(tmp_eog);
					term_domain_mapping[i] = tmp_eog;
				}
				else
				{
					EquivalentObjectGroup* eog = const_cast<EquivalentObjectGroup*>((*find_ci).second);
					tmp.insert(eog);
					term_domain_mapping[i] = eog;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "{ ";
					eog->printObjects(std::cout);
					std::cout << " }";
					
					if (i + 1 != bounded_atom->getAtom().getArity())
					{
						std::cout << ", ";
					}
#endif
				}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "$" << &variable_domain << "$";
#endif
			}
			
			ReachableFact* new_reachable_fact = new ReachableFact(*bounded_atom, bindings, term_domain_mapping);
			reachable_facts[index]->push_back(new_reachable_fact);
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//			std::cout << "Reachable for the " << index << "th atom: " << *new_reachable_fact << std::endl;
#endif
			
			for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
			{
				if (unmapping[i])
				{
					++counter[i];
					
					const std::vector<const Object*>& variable_domain = bounded_atom->getVariableDomain(i, bindings);
					
					if (counter[i] == variable_domain.size())
					{
						counter[i] = 0;
						continue;
					}
					else
					{
						done = false;
						break;
					}
				}
			}
		}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT		
		std::cout << "), " << std::endl;
#endif
	}
	
	// Construct the reachable node(s).
	unsigned int counter[transition.getToNode().getAtoms().size()];
	memset(&counter[0], 0, sizeof(unsigned int) * transition.getToNode().getAtoms().size());
	
	
	unsigned int expected_results = 1;
	for (unsigned int i = 0; i < transition.getToNode().getAtoms().size(); i++)
	{
		expected_results *= reachable_facts[i]->size();
	}
	
	bool new_facts_achieved = false;
	
	unsigned int reachable_nodes_found = 0;
	bool done = false;
	while (!done)
	{
		std::vector<const ReachableFact*>* resulting_reachable_facts = new std::vector<const ReachableFact*>();
		
		for (unsigned int i = 0; i < transition.getToNode().getAtoms().size(); i++)
		{
			resulting_reachable_facts->push_back((*reachable_facts[i])[counter[i]]);
		}
		
		for (unsigned int i = 0; i < transition.getToNode().getAtoms().size(); i++)
		{
			if (counter[i] + 1 == reachable_facts[i]->size())
			{
				if (i + 1 == transition.getToNode().getAtoms().size())
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

		ReachableNode* reachable_node = new ReachableNode(transition.getToNode(), *resulting_reachable_facts);
		if (equivalent_object_manager_->makeReachable(transition.getToNode(), *reachable_node))
		{
			new_facts_achieved = true;
		}
		++reachable_nodes_found;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Reachable: " << *reachable_node << "." << std::endl;
#endif
	}
	
	if (reachable_nodes_found != expected_results)
	{
		std::cout << "Found nodes: " << reachable_nodes_found << " expected: " << expected_results << "." << std::endl;
		assert (false);
	}
	
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "." << std::endl;
#endif

	return new_facts_achieved;
}

bool DTGReachability::makeReachable(const DomainTransitionGraphNode& dtg_node, std::vector<const BoundedAtom*>& new_reachable_facts)
{
	std::vector<std::vector<const BoundedAtom*> *>* already_reachable_facts = supported_facts_[&dtg_node];
	
	// Make sure the set of new reachable facts is not already part of the supported set.
	for (std::vector<std::vector<const BoundedAtom*> *>::const_iterator ci = already_reachable_facts->begin(); ci != already_reachable_facts->end(); ci++)
	{
		const std::vector<const BoundedAtom*>* reachable_facts = *ci;
		
		if (reachable_facts->size() != new_reachable_facts.size()) continue;
		
		bool all_facts_are_equal = true;
		for (unsigned int i = 0; i < reachable_facts->size(); i++)
		{
			if (!dtg_graph_->getBindings().areEquivalent((*reachable_facts)[i]->getAtom(), (*reachable_facts)[i]->getId(), new_reachable_facts[i]->getAtom(), new_reachable_facts[i]->getId()))
			{
				all_facts_are_equal = false;
				break;
			}
		}
		
		if (all_facts_are_equal)
		{
			return false;
		}
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "New Reachable Fact: " << std::endl;
#endif
	std::vector<const ReachableFact*>* reachable_facts = new std::vector<const ReachableFact*>();
	for (std::vector<const BoundedAtom*>::const_iterator ci = new_reachable_facts.begin(); ci != new_reachable_facts.end(); ci++)
	{
		reachable_facts->push_back(new ReachableFact(**ci, dtg_node.getDTG().getBindings(), *equivalent_object_manager_));
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "- ";
		(*ci)->print(std::cout, dtg_graph_->getBindings());
		std::cout << "." << std::endl;
#endif
	}
	ReachableNode* reachable_node = new ReachableNode(dtg_node, *reachable_facts);
	equivalent_object_manager_->makeReachable(dtg_node, *reachable_node);
	
	already_reachable_facts->push_back(&new_reachable_facts);
	return true;
}

void DTGReachability::performReachabilityAnalsysis(std::vector<const BoundedAtom*>& reachable_facts, const std::vector<const BoundedAtom*>& initial_facts)
{
//	double time_propagating = 0;
//	double time_iterating = 0;
//	double time_establishing_equivalances = 0;
//	unsigned int amount_of_iterating = 0;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Start performing reachability analysis." << std::endl;
#endif
	
	DTGPropagator propagator(*this, *equivalent_object_manager_, *dtg_graph_);
	
	// Keep a list of all established facts so far.
	std::vector<const BoundedAtom*> established_facts(initial_facts);
	
	// List of already achieved transitions.
	std::set<const Transition*> achieved_transitions;
	
	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		const BoundedAtom* init_bounded_atom = *ci;
		if (init_bounded_atom->getAtom().getPredicate().isStatic())
		{
			ReachableFact* static_reachable_fact = new ReachableFact(*init_bounded_atom, dtg_graph_->getBindings(), *equivalent_object_manager_);
			static_facts_.push_back(static_reachable_fact);
		}
	}
	
	//unsigned int pre_size = 0;
	
	struct timeval start_time_init;
	gettimeofday(&start_time_init, NULL);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Find initial supported DTG nodes." << std::endl;
#endif
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		// Initialise the reachability structure(s) with the values from the initial state.
		const DomainTransitionGraphNode* dtg_node = *ci;
		const std::vector<BoundedAtom*>& atoms_to_achieve = dtg_node->getAtoms();
		std::vector<std::vector<const BoundedAtom*>* > supporting_tupples;
		std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > variable_assignments;
		std::vector<const BoundedAtom*> initial_supporting_facts;
		getSupportingFacts(supporting_tupples, variable_assignments, atoms_to_achieve, initial_supporting_facts, established_facts);

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

	std::ofstream ofs;
	ofs.open("lollipop_rpg_results", std::ios::out);
	
	equivalent_object_manager_->printAll(ofs);
	ofs.close();
	
	equivalent_object_manager_->getAllReachableFacts(reachable_facts);
}

bool DTGReachability::handleExternalDependencies(std::vector<const BoundedAtom*>& established_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::handleExternalDependencies]" << std::endl;
#endif

	bool new_facts_reached = false;

	// Check for DTG nodes which have a transition in which a grounded node links two facts which are part of different
	// balanced sets.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		
		std::map<const Transition*, std::vector<const std::vector<const Object*>* >* > transitions;
		dtg_node->getExternalDependendTransitions(transitions);
		
		/**
		 * For each transition which contains terms with an external dependency we evaluate all the values these
		 * external dependend terms can have and see if any other nodes are reachable from the from node of the
		 * transition.
		 *
		 * Examples where this situation can occur is in driverlog in the unload transitions between { (in package truck)
		 * AND (at truck loc) } -> (at package loc). The final location of the package is dependend on the location of the
		 * truck. However, the location of the truck is not handled by the object package and the driver action is not
		 * part of the package's property space.
		 *
		 * Therefore we check which trucks can have a package on board and what locations these trucks can occupy. This will
		 * determine where packages can be unloaded.
		 */
		for (std::map<const Transition*, std::vector<const std::vector<const Object*>* >* >::const_iterator ci = transitions.begin(); ci != transitions.end(); ci++)
		{
			const Transition* transition = (*ci).first;
			
			const std::vector<const std::vector<const Object*>* >* dependend_term_domains = (*ci).second;
			
			// Check if atom which is part of the external dependency can take on different values for the grounded term.
			const DomainTransitionGraphNode& from_node = transition->getFromNode();
			assert (&from_node == dtg_node);
			std::vector<const ReachableNode*> supporting_nodes;
			equivalent_object_manager_->getSupportingFacts(supporting_nodes, from_node);
			
			if (supporting_nodes.size() == 0)
			{
				continue;
			}

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "The transition: " << *transition << " has external dependencies!" << std::endl;
#endif
			// Prepate a mask so we can identify which terms have external dependencies and which do not.
			unsigned int largest_arity = 0;
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				if ((*ci)->getAtom().getArity() > largest_arity)
				{
					largest_arity = (*ci)->getAtom().getArity();
				}
			}
			bool dependend_term_mapping[from_node.getAtoms().size()][largest_arity];
			memset(&dependend_term_mapping[0][0], false, sizeof(bool) * largest_arity * dependend_term_domains->size());

			std::vector<const BoundedAtom*> equivalent_nodes_to_find;
			bool facts_with_external_dependencies[from_node.getAtoms().size()];
			memset(&facts_with_external_dependencies[0], false, sizeof(bool) * from_node.getAtoms().size());
			
			/**
			 * Determine which facts and terms contain external dependencies. We create a list of bounded atoms which
			 * is used to search for DTG nodes which contain the same facts as the from node of the transition except 
			 * for those terms which is external dependend. So in the example above of driverlog the location is the
			 * external dependend term and may vary in the DTG nodes we are looking for - the rest needs to the exactly
			 * the same!
			 */
			for (std::vector<BoundedAtom*>::const_iterator ci = from_node.getAtoms().begin(); ci != from_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* from_node_bounded_atom = *ci;
				BoundedAtom& new_bounded_atom = BoundedAtom::createBoundedAtom(from_node_bounded_atom->getAtom(), from_node_bounded_atom->getProperties(), dtg_graph_->getBindings());
				
				// Make the term's domain equal to the original - except if has an external dependency.
				for (unsigned int i = 0; i < new_bounded_atom.getAtom().getArity(); i++)
				{
					const std::vector<const Object*>& org_domain = from_node_bounded_atom->getAtom().getTerms()[i]->getDomain(from_node_bounded_atom->getId(), dtg_graph_->getBindings());
					const Term* new_term = new_bounded_atom.getAtom().getTerms()[i];
					
					// It is not a dependend term - copy.
					if (std::find(dependend_term_domains->begin(), dependend_term_domains->end(), &org_domain) == dependend_term_domains->end())
					{
						new_term->makeDomainEqualTo(new_bounded_atom.getId(), org_domain, dtg_graph_->getBindings());
						dependend_term_mapping[std::distance(from_node.getAtoms().begin(), ci)][i] = false;
					}
					// Else it is a dependend term - leave it.
					else
					{
						facts_with_external_dependencies[std::distance(from_node.getAtoms().begin(), ci)] = true;
						dependend_term_mapping[std::distance(from_node.getAtoms().begin(), ci)][i] = true;
					}
				}
				equivalent_nodes_to_find.push_back(&new_bounded_atom);
			}
			
			// Now find all the DTG nodes which match this criterium.
			std::vector<const DomainTransitionGraphNode*> matching_dtgs;
			dtg_graph_->getNodes(matching_dtgs, equivalent_nodes_to_find);

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Found matching DTG nodes: " << std::endl;
			for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = matching_dtgs.begin(); ci != matching_dtgs.end(); ci++)
			{
				const DomainTransitionGraphNode* dtg_node = *ci;
				std::cout << *dtg_node << std::endl;
			}
#endif

			/**
			 * For every DTG node which conforms to the above requirements, we check if the external dependencies
			 * can be satisfied to make these nodes reachable from the from node.
			 */
			for (std::vector<const ReachableNode*>::const_iterator ci = supporting_nodes.begin(); ci != supporting_nodes.end(); ci++)
			{
				const ReachableNode* reachable_node = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Start with reachable node: " << *reachable_node << "." << std::endl;
#endif
				
				for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = matching_dtgs.begin(); ci != matching_dtgs.end(); ci++)
				{
					const DomainTransitionGraphNode* equivalent_dtg_node = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "Process: " << *equivalent_dtg_node << "." << std::endl;
#endif

					if (equivalent_dtg_node == &from_node) continue;
					if (equivalent_dtg_node->getAtoms().size() != from_node.getAtoms().size())
					{
						continue;
//						std::cout << "[handleExternalDependencies] The two dtg nodes cannot be handled: " << std::endl;
//						std::cout << "1: " << from_node << std::endl;
//						std::cout << "2: " << *equivalent_dtg_node << std::endl;
//						assert (false);
					}
					
					std::vector<std::vector<const ReachableFact*>* > reachable_facts;
					for (unsigned int i = 0; i < equivalent_dtg_node->getAtoms().size(); i++)
					{
						reachable_facts.push_back(new std::vector<const ReachableFact*>());
					}
					
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "Process the facts of: " << std::endl;
					std::cout << *dtg_node << std::endl;
					std::cout << " AND " << std::endl;
					std::cout << *equivalent_dtg_node << std::endl;
#endif
					
					/**
					 * Check which node(s) differs and see if the already established reachable EOGs has reached the required facts.
					 */
					for (unsigned int i = 0; i < equivalent_dtg_node->getAtoms().size(); i++)
					{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "Process the " << i << "th fact..." << std::endl;
#endif

						std::cout << " Reachable node: " << *reachable_node << std::endl;

						const BoundedAtom* equivalent_fact = equivalent_dtg_node->getAtoms()[i];
						const BoundedAtom* this_fact = dtg_node->getAtoms()[i];
						reachable_node->sanityCheck();
						
						const ReachableFact& reachable_this_fact = reachable_node->getSupportingFact(i);
						reachable_this_fact.sanityCheck();
						
						std::vector<const ReachableFact*>* this_reachable_facts = reachable_facts[i];
						
						// TODO: Get all possible values! Not the ones reachable for this specific DTG node!
						if (dtg_node->getDTG().getBindings().areEquivalent(equivalent_fact->getAtom(), equivalent_fact->getId(), this_fact->getAtom(), this_fact->getId(), &equivalent_dtg_node->getDTG().getBindings()))
						{
							ReachableFact* reachable_equivalent_fact = new ReachableFact(*equivalent_fact, equivalent_dtg_node->getDTG().getBindings(), reachable_this_fact.getTermDomains());
							this_reachable_facts->push_back(reachable_equivalent_fact);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "* Found: " << *reachable_equivalent_fact << "." << std::endl;
#endif
							continue;
						}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "The following facts differ: ";
						this_fact->print(std::cout, dtg_node->getDTG().getBindings());
						std::cout << " -> ";
						equivalent_fact->print(std::cout, equivalent_dtg_node->getDTG().getBindings());
						std::cout << "." << std::endl;
#endif
						// If they differ, determine the invariable and see if that invariable can take on the required value.
						PropertySpace tmp_ps;
						std::vector<std::pair<const Predicate*, InvariableIndex> > tmp_p;
						PropertyState tmp_pst(tmp_ps, tmp_p);
						
						std::vector<const Property*> properties;
						for (unsigned int j = 0; j < this_fact->getAtom().getArity(); j++)
						{
							const Property* property = new Property(tmp_pst, this_fact->getAtom().getPredicate(), j);
							properties.push_back(property);
						}
						
						bool can_be_achieved = false;
						for (unsigned int j = 0; j < this_fact->getAtom().getArity(); j++)
						{
							BoundedAtom tmp_bounded_atom(equivalent_fact->getId(), equivalent_fact->getAtom(), properties);
							
							reachable_this_fact.sanityCheck();
							const EquivalentObjectGroup& eog = reachable_this_fact.getTermDomain(j);
							
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "Reachable from: " << eog << "?" << std::endl;
#endif
							
							std::vector<const ReachableFact*> results;
							eog.getSupportingFacts(results, tmp_bounded_atom, equivalent_dtg_node->getDTG().getBindings());
							
							for (std::vector<const ReachableFact*>::const_iterator ci = results.begin(); ci != results.end(); ci++)
							{
								ReachableFact* reachable_fact = new ReachableFact((*ci)->getBoundedAtom(), (*ci)->getBindings(), (*ci)->getTermDomains());
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
								std::cout << "* Found: " << *reachable_fact << "." << std::endl;
#endif
								this_reachable_facts->push_back(reachable_fact);
								can_be_achieved = true;
							}
						}
						if (!can_be_achieved) break;
					}

					bool is_reachable = true;
					for (std::vector<std::vector<const ReachableFact*>* >::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
					{
						if ((*ci)->empty())
						{
							is_reachable = false;
							break;
						}
					}
					
					if (!is_reachable) continue;
					
					unsigned int counter[equivalent_dtg_node->getAtoms().size()];
					memset(&counter[0], 0, sizeof(unsigned int) * equivalent_dtg_node->getAtoms().size());
					
					bool done = false;
					while (!done)
					{
						std::vector<const ReachableFact*>* cur_reachable_facts = new std::vector<const ReachableFact*>();
						
						for (unsigned int i = 0; i < equivalent_dtg_node->getAtoms().size(); i++)
						{
							cur_reachable_facts->push_back((*reachable_facts[i])[counter[i]]);
						}
						
						/// Make achievable.
						ReachableNode* reachable_node = new ReachableNode(*equivalent_dtg_node, *cur_reachable_facts);
						if (!equivalent_object_manager_->makeReachable(*equivalent_dtg_node, *reachable_node))
						{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "The reachable node: " << *reachable_node << " was already achieved!!!" << std::endl;
#endif
						}
						else
						{
							new_facts_reached = true;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "Achieved by: " << *reachable_node << "." << std::endl;
#endif
						}
						
						for (unsigned int j = 0; j < equivalent_dtg_node->getAtoms().size(); j++)
						{
							if (counter[j] + 1 == reachable_facts[j]->size())
							{
								if (j + 1 == equivalent_dtg_node->getAtoms().size())
								{
									done = true;
									break;
								}
								
								counter[j] = 0;
								continue;
							}
							
							++counter[j];
							break;
						}
					}
				}
			}
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::handleExternalDependencies] - Done!" << std::endl;
#endif
	return new_facts_reached;
}

bool DTGReachability::iterateTillFixPoint(DTGPropagator& propagator, std::vector<const BoundedAtom*>& established_facts, std::set<const Transition*>& achieved_transitions)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::iterateTillFixPoint]" << std::endl;
#endif
	
	std::vector<const DomainTransitionGraphNode*> initial_satisfied_nodes;
	
	// While there are transitions achieved:
	unsigned int amount_of_achieved_transitions = achieved_transitions.size();
	bool new_transition_achieved = true;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	unsigned int iteration_nr = 0;
#endif
	while (new_transition_achieved)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Iteration " << iteration_nr++ << "." << std::endl;
#endif
		new_transition_achieved = false;

		// For each transition of a marked node:
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_graph = *ci;
			for (std::vector<const Transition*>::const_iterator ci = dtg_graph->getTransitions().begin(); ci != dtg_graph->getTransitions().end(); ci++)
			{
				/// Check if the preconditions of the transition have been satisfied.
				const Transition* transition = *ci;
				
				if (achieved_transitions.count(transition) != 0)
				{
///					assert (reachable_transitions_[transition]->getPossibleMappings().size() > 0);
					continue;
				}
				
				const DomainTransitionGraphNode& from_dtg_node = transition->getFromNode();
				
				std::vector<const ReachableNode*> supporting_facts;
				equivalent_object_manager_->getSupportingFacts(supporting_facts, from_dtg_node);

				if (supporting_facts.empty())
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//					std::cout << " * No supporting facts for the transition: " << *transition << "." << std::endl;
#endif
					continue;
				}
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << " * Work on the transition: " << *transition << "." << std::endl;
#endif

				std::set<const std::vector<const Object*>* > invariable_terms;
				for (std::vector<const ReachableNode*>::const_iterator ci = supporting_facts.begin(); ci != supporting_facts.end(); ci++)
				{
					const ReachableNode* reached_node = *ci;
					
					for (std::vector<const ReachableFact*>::const_iterator ci = reached_node->getSupportingFacts().begin(); ci != reached_node->getSupportingFacts().end(); ci++)
					{
						const ReachableFact* reached_fact = *ci;
						
						for (std::vector<const Property*>::const_iterator ci = reached_fact->getBoundedAtom().getProperties().begin(); ci != reached_fact->getBoundedAtom().getProperties().end(); ci++)
						{
							const Property* property = *ci;
							if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
							
							invariable_terms.insert(&reached_fact->getBoundedAtom().getAtom().getTerms()[property->getIndex()]->getDomain(reached_fact->getBoundedAtom().getId(), dtg_graph_->getBindings()));
						}
					}
				}
				
				/**
				 * Determine if the other preconditions are satisfied as well! :)
				 */
				for (std::vector<const ReachableNode*>::const_iterator ci = supporting_facts.begin(); ci != supporting_facts.end(); ci++)
				{
					const ReachableNode* reached_node = *ci;
					if (canSatisfyPreconditions(*transition, *reached_node, invariable_terms))
					{
						reachable_nodes_[&transition->getFromNode()]->push_back(&transition->getToNode());
						achieved_transitions.insert(transition);
						new_transition_achieved = true;
						break;
					}
				}
			}
		}
		
		// Propagate the reachable nodes.
		propagator.propagateReachableNodes();
	}
	
	return achieved_transitions.size() != amount_of_achieved_transitions;
}

bool DTGReachability::canSatisfyPreconditions(const Transition& transition, const ReachableNode& supporting_node, std::set<const std::vector<const Object*>* >& invariables) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::canSatisfyPreconditions] Check if the preconditions of the transition: " << transition << " are satisfiable!" << std::endl;
#endif

	const DomainTransitionGraphNode& from_dtg_node = transition.getFromNode();
	const Bindings& bindings = from_dtg_node.getDTG().getBindings();
	
	// Create a mapping from variable domains to the equivalent object group which supports them.
	std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* variable_domain_mapping = new std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>();
	
	// Populate the mapping.
	for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node.getAtoms().begin(); ci != from_dtg_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		unsigned int atom_index = std::distance(from_dtg_node.getAtoms().begin(), ci);
		for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
		{
			const Term* term = *ci;
			const std::vector<const Object*>& domain = term->getDomain(bounded_atom->getId(), bindings);
			
			unsigned int term_index = std::distance(bounded_atom->getAtom().getTerms().begin(), ci);
			variable_domain_mapping->insert(std::make_pair(&domain, &supporting_node.getSupportingFact(atom_index).getTermDomain(term_index)));
		}
	}
	
	std::vector<std::pair<const Atom*, InvariableIndex> > all_preconditions = transition.getAllPreconditions();
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::reverse_iterator ri = all_preconditions.rbegin(); ri != all_preconditions.rend(); ri++)
	{
		const Atom* precondition = (*ri).first;
//		bool satisfied = false;
		
		// Make sure we only consider preconditions which have not previously been achieved.
		for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node.getAtoms().begin(); ci != from_dtg_node.getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			
			if (dtg_graph_->getBindings().areIdentical(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition.getStep()->getStepId()))
			{
				all_preconditions.erase(ri.base() - 1);
//				satisfied = true;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "The precondition: ";
				precondition->print(std::cout, bindings, transition.getStep()->getStepId());
				std::cout << " is supported by ";
				bounded_atom->print(std::cout, bindings);
				std::cout << "." << std::endl;
#endif
				break;
			}
		}
		
//		if (satisfied) continue;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Unsatisfied precondition: ";
		precondition->print(std::cout, bindings, transition.getStep()->getStepId());
		std::cout << "." << std::endl;
#endif
	}
	
	const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* possible_mapping = canSatisfyPrecondition(all_preconditions, 0, transition, invariables, *variable_domain_mapping);
		
	if (possible_mapping == NULL || possible_mapping->size() == 0)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Could not find a possible mapping :((" << std::endl;
#endif
		return false;
	}
	
	getReachableTransition(transition).addMapping(*possible_mapping);
	
	makeToNodeReachable(transition, *possible_mapping);
	return true;
}

const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* DTGReachability::canSatisfyPrecondition(std::vector<std::pair<const Atom*, InvariableIndex> >& all_preconditions, unsigned int index, const Transition& transition, std::set<const std::vector<const Object*>* >& invariables, std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& domain_variable_mapping) const
{
	// We're done!
	if (index == all_preconditions.size())
	{
		return &domain_variable_mapping;
	}
	
	const Bindings& bindings = transition.getFromNode().getDTG().getBindings();
	const Atom* precondition = all_preconditions[index].first;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the precondition: ";
		precondition->print(std::cout, bindings, transition.getStep()->getStepId());
		std::cout << "." << std::endl;
#endif
	
	// TODO: We skip static preconditions - for now.
	if (precondition->getPredicate().isStatic())
	{
		for (std::vector<const ReachableFact*>::const_iterator ci = static_facts_.begin(); ci != static_facts_.end(); ci++)
		{
			const ReachableFact* static_reachable_fact = *ci;
			
			if (bindings.areEquivalent(static_reachable_fact->getBoundedAtom().getAtom(), static_reachable_fact->getBoundedAtom().getId(), *precondition, transition.getStep()->getStepId()))
			{
				for (unsigned int i = 0; i < precondition->getArity(); i++)
				{
					const std::vector<const Object*>& precondition_variable_domain = precondition->getTerms()[i]->getDomain(transition.getStep()->getStepId(), bindings);
					domain_variable_mapping[&precondition_variable_domain] = &static_reachable_fact->getTermDomain(i);
				}
				break;
			}
		}
		return canSatisfyPrecondition(all_preconditions, index + 1, transition, invariables, domain_variable_mapping);
	}
	
	// TODO: Implement method to translate predicate -> set of properties.
	// Translate precondition to a bounded atom.
	std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
	dtg_graph_->getDTGManager().getDTGNodes(found_nodes, transition.getStep()->getStepId(), *precondition, bindings);
	
	std::vector<const Property*> precondition_properties;
	for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
	{
		const BoundedAtom* bounded_atom = (*ci).second;
		
		for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
		{
			const Property* property = *ci;
			if (std::find(precondition_properties.begin(), precondition_properties.end(), property) != precondition_properties.end()) continue;
			precondition_properties.push_back(property);
		}
	}
	
	const BoundedAtom bounded_precondition(transition.getStep()->getStepId(), *precondition, precondition_properties);
	
	if (bounded_precondition.getAtom().getArity() == 0)
	{
		std::vector<const ReachableFact*> results;
		equivalent_object_manager_->getSupportingFacts(results, bounded_precondition, bindings);
		
		if (!results.empty())
		{
			return canSatisfyPrecondition(all_preconditions, index + 1, transition, invariables, domain_variable_mapping);
		}
		else
		{
			return NULL;
		}
	}
	
	// Check which term is linked to an invariable, in the case of attribute spaces there might not be an invariable,
	// in that case we will need to process all the terms and treat them all as invariables.
	bool process[bounded_precondition.getAtom().getArity()];
	memset(&process[0], false, sizeof(bool) * bounded_precondition.getAtom().getArity());
	
	bool found_property = false;
	for (std::vector<const Property*>::const_iterator ci = bounded_precondition.getProperties().begin(); ci != bounded_precondition.getProperties().end(); ci++)
	{
		const Property* property = *ci;
		if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
		
		found_property = true;
		process[property->getIndex()] = true;
		//const Term* invariable_term = bounded_precondition.getAtom().getTerms()[property->getIndex()];
	}
	
	if (!found_property)
	{
		memset(&process[0], true, sizeof(bool) * bounded_precondition.getAtom().getArity());
	}

	for (unsigned int i = 0; i < bounded_precondition.getAtom().getArity(); i++)
	{
		if (!process[i]) continue;
		
		const Term* invariable_term = bounded_precondition.getAtom().getTerms()[i];
		const std::vector<const Object*>& term_domain = invariable_term->getDomain(transition.getStep()->getStepId(), dtg_graph_->getBindings());
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//		std::cout << "Invariable term: ";
//		invariable_term->print(std::cout, dtg_graph_->getBindings(), transition.getStep()->getStepId());
//		std::cout << "." << std::endl;
#endif
		
		// Get the corresponding EOG(s).
		std::vector<const EquivalentObjectGroup*> eogs;
		for (std::vector<const Object*>::const_iterator ci = term_domain.begin(); ci != term_domain.end(); ci++)
		{
			const EquivalentObject& eo = equivalent_object_manager_->getEquivalentObject(**ci);
			const EquivalentObjectGroup& eog = eo.getEquivalentObjectGroup();
			if (std::find(eogs.begin(), eogs.end(), &eog) != eogs.end())
			{
				continue;
			}
			
			eogs.push_back(&eog);
//			std::cout << "Check eog: " << eog << "." << std::endl;
			
			std::vector<const ReachableFact*> supporting_facts;
			eog.getSupportingFacts(supporting_facts, bounded_precondition, bindings);
			
			// Make sure it is consistent with the other assignments made to the variable domains.
			for (vector<const ReachableFact*>::const_iterator ci = supporting_facts.begin(); ci != supporting_facts.end(); ci++)
			{
				const ReachableFact* reachable_fact = *ci;
				
//				std::cout << "Process: " << *reachable_fact << std::endl;
				
				bool matches = true;
				for (unsigned int i = 0; i < precondition->getArity(); i++)
				{
					const std::vector<const Object*>& precondition_variable_domain = precondition->getTerms()[i]->getDomain(transition.getStep()->getStepId(), bindings);
					
					std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator ci = domain_variable_mapping.find(&precondition_variable_domain);
					if (ci != domain_variable_mapping.end())
					{
						const EquivalentObjectGroup* corresponding_eog = (*ci).second;
						
						if (&reachable_fact->getTermDomain(i) != corresponding_eog)
						{
							
//							std::cout << "! The mapping of the " << i << "th term of " << *reachable_fact << " did not match with the already established mapping " << *corresponding_eog << "." << std::endl;
							
							matches = false;
							break;
						}
					}
				}
				
				if (matches)
				{
//					std::cout << "Supporing fact: " << *reachable_fact << "." << std::endl;
					std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* new_domain_variable_mapping = new std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>(domain_variable_mapping);
					
					for (unsigned int i = 0; i < precondition->getArity(); i++)
					{
						const std::vector<const Object*>& precondition_variable_domain = precondition->getTerms()[i]->getDomain(transition.getStep()->getStepId(), bindings);
						(*new_domain_variable_mapping)[&precondition_variable_domain] = &reachable_fact->getTermDomain(i);
					}
					
					return canSatisfyPrecondition(all_preconditions, index + 1, transition, invariables, *new_domain_variable_mapping);
				}
			}
		}
		
		// After all the preconditions have been satisfied, store the reached effects! :)
		
	}
	return NULL;
}

void DTGReachability::getSupportingFacts(std::vector<std::vector<const BoundedAtom*>* >& supporting_tupples, const std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >& variable_assignments, const std::vector<BoundedAtom*>& atoms_to_achieve, const std::vector<const BoundedAtom*>& initial_supporting_facts, const std::vector<const BoundedAtom*>& initial_facts) const
{
	if (atoms_to_achieve.empty())
	{
		// Check if there is such a fact among the initial states!
		return;
		assert (false);
	}
	
	assert (atoms_to_achieve.size() > initial_supporting_facts.size());
	const BoundedAtom* atom_to_process = atoms_to_achieve[initial_supporting_facts.size()];
	
//	std::cout << "[" << initial_supporting_facts.size() << "] The atom to achieve: ";
//	atom_to_process->print(std::cout, dtg_graph_->getBindings());
//	std::cout << std::endl;

	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		StepID initial_fact_id = (*ci)->getId();
		const Atom& initial_fact = (*ci)->getAtom();
		
		if (dtg_graph_->getBindings().canUnify(initial_fact, initial_fact_id, atom_to_process->getAtom(), atom_to_process->getId()))
		{
//			std::cout << "Initial fact which can unify: ";
//			initial_fact.print(std::cout, dtg_graph_->getBindings(), initial_fact_id);
//			std::cout << std::endl;

			// Check if all terms can be supported.
			bool terms_supported = true;
			std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >* variable_assignments_clone = new std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >(variable_assignments);
			
			for (std::vector<const Term*>::const_iterator ci = atom_to_process->getAtom().getTerms().begin(); ci != atom_to_process->getAtom().getTerms().end(); ci++)
			{
				const Term* atom_term = *ci;
				unsigned int term_index = std::distance(atom_to_process->getAtom().getTerms().begin(), ci);
				
				const std::vector<const Object*>& term_domain_atom_to_process = atom_term->getDomain(atom_to_process->getId(), dtg_graph_->getBindings());
				const std::vector<const Object*>& initial_fact_domain = initial_fact.getTerms()[term_index]->getDomain(initial_fact_id, dtg_graph_->getBindings());

				// Find the assignments made to the term's domain.
				std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >::const_iterator found_domain = variable_assignments_clone->find(&term_domain_atom_to_process);
				
				// If no assignments have been made yet we make them equal to the initial fact's domain.
				if (found_domain == variable_assignments_clone->end())
				{
					(*variable_assignments_clone)[&term_domain_atom_to_process] = &initial_fact_domain;
//					std::cout << "Bind the " << term_index << "th term to: ";
//					for (std::vector<const Object*>::const_iterator ci = initial_fact_domain.begin(); ci != initial_fact_domain.end(); ci++)
//					{
//						(*ci)->print(std::cout, dtg_graph_->getBindings(), initial_fact_id);
//						if (ci + 1 != initial_fact_domain.end())
//						{
//							std::cout << ", ";
//						}
//					}
//					std::cout << "." << std::endl;
				}
				// If previous assignments have been made, we take the intersection between the previous assignments and the fact we found
				// to be unifiable with this fact.
				else
				{
					std::vector<const Object*> existing_domain = *(*variable_assignments_clone)[&term_domain_atom_to_process];
					
					// Get the intersection of the variable assignments made and the new assignment just made.
					std::vector<const Object*> initial_fact_domain_sorted_copy(initial_fact_domain);
					std::sort(initial_fact_domain_sorted_copy.begin(), initial_fact_domain_sorted_copy.end());
					std::sort(existing_domain.begin(), existing_domain.end());
					std::vector<const Object*>* intersection = new std::vector<const Object*>(std::max(initial_fact_domain_sorted_copy.size(), existing_domain.size()));
					std::vector<const Object*>::iterator intersection_end = std::set_intersection(initial_fact_domain_sorted_copy.begin(), initial_fact_domain_sorted_copy.end(), existing_domain.begin(), existing_domain.end(), intersection->begin());
					
					// If the intersection is empty we know that the term cannot be supported.
					if (intersection_end == intersection->begin())
					{
						terms_supported = false;
						break;
					}
					
					// Otherwise, we need to update the variable domain which has been modified.
					intersection->resize(std::distance(intersection->begin(), intersection_end));
					(*variable_assignments_clone)[&term_domain_atom_to_process] = intersection;
				}
			}
			
			if (!terms_supported)
			{
//				std::cout << "Terms not supported." << std::endl;
				continue;
			}
			
			// Construct the facts which support the preconditions.
			std::vector<const BoundedAtom*>* initial_supporting_facts_clone = new std::vector<const BoundedAtom*>(initial_supporting_facts);
			initial_supporting_facts_clone->push_back(new BoundedAtom(initial_fact_id, initial_fact));
			
//			std::cout << "Initial su->size() == atoms_to_achieve.size?" << std::endl;
//			std::cout << initial_supporting_facts_clone->size()  << " ==  " << atoms_to_achieve.size() << std::endl;
			if (initial_supporting_facts_clone->size() == atoms_to_achieve.size())
			{
				std::vector<const BoundedAtom*>* finalized_supporting_facts = new std::vector<const BoundedAtom*>();
				
//				std::cout << "The following nodes support the DTG node!" << std::endl;
				for (std::vector<BoundedAtom*>::const_iterator ci = atoms_to_achieve.begin(); ci != atoms_to_achieve.end(); ci++)
				{
					const BoundedAtom* atom_to_achieve = *ci;
					const BoundedAtom& new_bounded_atom = BoundedAtom::createBoundedAtom(atom_to_achieve->getAtom(), atom_to_achieve->getProperties(), dtg_graph_->getBindings());
					
					finalized_supporting_facts->push_back(&new_bounded_atom);
					
//					std::cout << " * (" << atom_to_achieve->getAtom().getPredicate().getName();
					for (std::vector<const Term*>::const_iterator ci = atom_to_achieve->getAtom().getTerms().begin(); ci != atom_to_achieve->getAtom().getTerms().end(); ci++)
					{
						const Term* term_of_atom_to_achieve = *ci;
						unsigned int term_index = std::distance(atom_to_achieve->getAtom().getTerms().begin(), ci);
						const Term* new_bounded_atom_term = new_bounded_atom.getAtom().getTerms()[term_index];
						
						const std::vector<const Object*>& variable_domain_of_atom_to_achieve = term_of_atom_to_achieve->getDomain(atom_to_achieve->getId(), dtg_graph_->getBindings());
						const std::vector<const Object*>* possible_assignments = (*variable_assignments_clone)[&variable_domain_of_atom_to_achieve];

						new_bounded_atom_term->makeDomainEqualTo(new_bounded_atom.getId(), *possible_assignments, dtg_graph_->getBindings());
					}
				}
				

				supporting_tupples.push_back(finalized_supporting_facts);
			}
			else
			{
				getSupportingFacts(supporting_tupples, *variable_assignments_clone, atoms_to_achieve, *initial_supporting_facts_clone, initial_facts);
			}
		}
	}
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
/*					if (hits + misses != 0)
					{
						double accuracy = 0;
						if (misses == 0) accuracy = 100;
						else accuracy = ((double)hits / (hits + misses)) * 100;
						std::cerr << "Map possible maps hits / misses: " << hits << "/" << misses << " " << accuracy << "%." << std::endl;
					}*/
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
						// TODO: This pruning fails, but we need something to speed things up!
/*						if (closed_list_.count(std::make_pair(transition, reachable_node)) != 0)
						{
							std::cout << *reachable_node << " was already processed, continue!" << std::endl;
							continue;
						}*/
						
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
}


void DTGPropagator::mapPossibleFacts(std::vector<const ReachableNode*>& results, const std::vector<const ReachableFact*>* cached_reachable_facts[], const DomainTransitionGraphNode& dtg_node, const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& mappings, const std::vector<const ReachableFact*>& assignments)
{
	// If we have found a reachable fact for every fact in the dtg node, create a reachable node and add it to the list of reachable facts.
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
}

};
	
};
