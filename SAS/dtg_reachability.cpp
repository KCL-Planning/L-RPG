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

ReachableFact::ReachableFact(unsigned int index, const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
	: index_(index), bounded_atom_(&bounded_atom), bindings_(&bindings)
{
	term_domain_mapping_ = new EquivalentObjectGroup*[bounded_atom.getAtom().getArity()];
	
	for (std::vector<const Term*>::const_iterator ci = bounded_atom.getAtom().getTerms().begin(); ci != bounded_atom.getAtom().getTerms().end(); ci++)
	{
		const Term* term = *ci;
		const std::vector<const Object*>& domain = term->getDomain(bounded_atom.getId(), bindings);
		
		assert (domain.size() == 1);
		
		EquivalentObjectGroup& corresponding_eog = eog_manager.getEquivalentObject(*domain[0]).getEquivalentObjectGroup();
		term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] = &corresponding_eog;
	}
}

ReachableFact::ReachableFact(unsigned int index, const BoundedAtom& bounded_atom, const Bindings& bindings, EquivalentObjectGroup** term_domain_mapping_)
	: index_(index), bounded_atom_(&bounded_atom), bindings_(&bindings), term_domain_mapping_(term_domain_mapping_)
{
	
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
	
	// TODO: depricated.
	if (index_ != other.index_)
	{
//		std::cout << "Indexes don't match up!" << std::endl;
		return false;
	}
	
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
		
		this_mask |= 0x1 << property->getIndex();
	}
	
	for (std::vector<const Property*>::const_iterator ci = other.bounded_atom_->getProperties().begin(); ci != other.bounded_atom_->getProperties().end(); ci++)
	{
		const Property* property = *ci;
		if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
		
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
	
	// TODO: depricated.
	if (index_ != other.index_)
	{
//		std::cout << "Indexes don't match up!" << std::endl;
		return false;
	}
	
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
	os << "){" << reachable_fact.index_ << "}";
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

void ReachableTransition::addMapping(const std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::SAS_Plus::EquivalentObjectGroup* >& new_mapping)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Transition: " << *transition_ << " is reachable!" << std::endl;
#endif

/*	// Make sure all variables are mapped!
	for (std::vector<BoundedAtom*>::const_iterator ci = transition_->getFromNode().getAtoms().begin(); ci != transition_->getFromNode().getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
		{
			const Term* term = *ci;
			const std::vector<const Object*>& domain = term->getDomain(bounded_atom->getId(), transition_->getFromNode().getDTG().getBindings());
			assert (new_mapping.find(&domain) != new_mapping.end());
		}
	}
	
	for (std::vector<BoundedAtom*>::const_iterator ci = transition_->getToNode().getAtoms().begin(); ci != transition_->getToNode().getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
		{
			const Term* term = *ci;
			const std::vector<const Object*>& domain = term->getDomain(bounded_atom->getId(), transition_->getFromNode().getDTG().getBindings());
			if (new_mapping.find(&domain) == new_mapping.end())
			{
				std::cout << "The term: ";
				term->print(std::cout, transition_->getFromNode().getDTG().getBindings(), bounded_atom->getId());
				std::cout << " in the fact: ";
				bounded_atom->print(std::cout, transition_->getFromNode().getDTG().getBindings());
				std::cout << " was not mapped!!!" << std::endl;
				assert (false);
			}
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
//	std::cout << "Add " << reachable_fact << " to " << *this << std::endl;
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

EquivalentObjectGroup::EquivalentObjectGroup(const DomainTransitionGraph& dtg_graph, const Object& object)
	: dtg_graph_(&dtg_graph), link_(NULL)
{
	initialiseFingerPrint(object);
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


void EquivalentObjectGroup::updateReachableFacts(const Object& object, const DomainTransitionGraphNode& dtg_node)
{
	for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		bool is_part = false;
		for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
		{
			const std::vector<const Object*>& domain = bounded_atom->getVariableDomain(i, dtg_node.getDTG().getBindings());
			if (std::find(domain.begin(), domain.end(), &object) != domain.end())
			{
				is_part = true;
				break;
			}
		}
		
		if (is_part)
		{
//			std::vector<const EquivalentObjectGroup*>* terms = new std::vector<const EquivalentObjectGroup*>();
			
//			EOGFact* eog_fact = new EOGFact(bounded_atom->getAtom().getPredicate(), const std::vector<const EquivalentObjectGroup*>& terms);
			
		}
	}
}

bool EquivalentObjectGroup::makeReachable(const DomainTransitionGraphNode& dtg_node, const BoundedAtom& bounded_atom, ReachableFact& reachable_fact)
{
	bool added_something = false;
	std::pair<std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator, std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator> ret;
	std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci;
	
	ret = reachable_facts_.equal_range(std::make_pair(&dtg_node, &bounded_atom));
	bool already_part = false;
	for (ci = ret.first; ci != ret.second; ci++)
	{
		if ((*ci).second->isIdenticalTo(reachable_fact))
		{
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
	for (std::vector<const Property*>::const_iterator ci = bounded_atom.getProperties().begin(); ci != bounded_atom.getProperties().end(); ci++)
	{
		const Property* property = *ci;
		
		std::pair<std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator, std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator> ret;
		std::multimap<std::pair<std::string, unsigned int>, ReachableFact*>::const_iterator it;
		
		ret = reachable_properties_.equal_range(std::make_pair(property->getPredicate().getName(), property->getIndex()));
		
		for (it = ret.first; it != ret.second; it++)
		{
			ReachableFact* reachable_candidate = (*it).second;
			
//			std::cout << "found a candidate: " << *reachable_candidate << "." << std::endl;
			
			bool matches = true;
			for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
			{
				const std::vector<const Object*>& variable_domain = bounded_atom.getVariableDomain(i, bindings);
				const EquivalentObjectGroup* eog = reachable_candidate->term_domain_mapping_[i];
				
				bool overlaps = false;
				
				for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ci++)
				{
					const Object* object = *ci;
					if (eog->contains(*object))
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
				results.push_back(reachable_candidate);
			}
		}
	}
}

bool EquivalentObjectGroup::tryToMergeWith(EquivalentObjectGroup& other_group, const std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* >& reachable_nodes)
{
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
//	std::cout << "Try to merge: " << *this << " with " << other_group << "." << std::endl;
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
			for (std::vector<const Property*>::const_iterator ci = initial_fact->bounded_atom_->getProperties().begin(); ci != initial_fact->bounded_atom_->getProperties().end(); ci++)
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
			for (std::vector<const Property*>::const_iterator ci = initial_fact->bounded_atom_->getProperties().begin(); ci != initial_fact->bounded_atom_->getProperties().end(); ci++)
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

void EquivalentObjectGroup::getAllReachableFacts(std::vector<const BoundedAtom*>& results) const
{
	for (std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		(*ci).second->getAllReachableFacts(results);
	}
}


void EquivalentObjectGroup::merge(EquivalentObjectGroup& other_group)
{
	assert (other_group.link_ == NULL);
	
//	std::cout << "Merging " << *this << " with " << other_group << "." << std::endl;
	
	equivalent_objects_.insert(equivalent_objects_.begin(), other_group.equivalent_objects_.begin(), other_group.equivalent_objects_.end());
	reachable_facts_.insert(other_group.reachable_facts_.begin(), other_group.reachable_facts_.end());
	reachable_properties_.insert(other_group.reachable_properties_.begin(), other_group.reachable_properties_.end());
	other_group.link_ = this;
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

	return os;
}

EquivalentObjectGroupManager::EquivalentObjectGroupManager(const DTGReachability& dtg_reachability, const DomainTransitionGraph& dtg_graph, const TermManager& term_manager, const std::vector<const BoundedAtom*>& initial_facts)
	: dtg_reachability_(&dtg_reachability)
{
	// Create initial data structures.
	for (std::vector<const Object*>::const_iterator ci = term_manager.getAllObjects().begin(); ci != term_manager.getAllObjects().end(); ci++)
	{
		const Object* object = *ci;
		EquivalentObjectGroup* equivalent_object_group = new EquivalentObjectGroup(dtg_graph, *object);
		EquivalentObject* equivalent_object = new EquivalentObject(*object, *equivalent_object_group);
		equivalent_object_group->addEquivalentObject(*equivalent_object);
		
		equivalent_groups_.push_back(equivalent_object_group);
		object_to_equivalent_object_mapping_[object] = equivalent_object;
	}
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
				
				ReachableFact* reachable_fact = new ReachableFact(index, *bounded_atom, dtg_node->getDTG().getBindings(), *this);
				reachable_facts->push_back(reachable_fact);
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << " * ";
				bounded_atom->print(std::cout, dtg_graph.getBindings());
				std::cout << "." << std::endl;
#endif
				
				for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
				{
					const Property* property = *ci;
					if (property->getIndex() == NO_INVARIABLE_INDEX)
						continue;
					
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "the index " << property->getIndex() << " of the atom ";
					bounded_atom->print(std::cout, dtg_graph.getBindings());
					std::cout << " is invariable!" << std::endl;
#endif
					
					const std::vector<const Object*>& domain = bounded_atom->getVariableDomain(property->getIndex(), dtg_graph.getBindings());
					for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
					{
						EquivalentObject* equivalent_object = object_to_equivalent_object_mapping_[*ci];
						assert (equivalent_object != NULL);
						
						equivalent_object->addInitialFact(*reachable_fact);
						equivalent_object->getEquivalentObjectGroup().makeReachable(*dtg_node, *dtg_node->getAtoms()[index], *reachable_fact);
					}
				}
			}
			
			ReachableNode* reachable_node = new ReachableNode(*dtg_node, *reachable_facts);
			supported_dtg_nodes_.insert(std::make_pair(dtg_node, reachable_node));
		}
	}
	
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
#endif
/*
	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		const BoundedAtom* bounded_atom = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
		{
			const Property* property = *ci;
			if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
			
			
		}
	}
*/
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
			bool remove = false;
			
			for (std::vector<const ReachableFact*>::const_iterator ci = reachable_node->supporting_facts_->begin(); ci != reachable_node->supporting_facts_->end(); ci++)
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
		results.push_back(reached_node);
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
	for (std::vector<const ReachableFact*>::const_iterator ci = reachable_node.supporting_facts_->begin(); ci != reachable_node.supporting_facts_->end(); ci++)
	{
		ReachableFact* reachable_fact = const_cast<ReachableFact*>(*ci);
		
		for (unsigned int i = 0; i < reachable_fact->bounded_atom_->getAtom().getArity(); i++)
		{
			EquivalentObjectGroup* eog = reachable_fact->term_domain_mapping_[i];
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			if (eog->makeReachable(dtg_node, *reachable_fact->bounded_atom_, *reachable_fact))
			{
				std::cout << "New reachable fact: " << *reachable_fact << "." << std::endl;
			}
#else
			eog->makeReachable(dtg_node, *reachable_fact->bounded_atom_, *reachable_fact);
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
		(*ci)->printGrounded(os);
//		os << **ci << std::endl;
	}
}

void EquivalentObjectGroupManager::getAllReachableFacts(std::vector<const BoundedAtom*>& results) const
{
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end(); ci++)
	{
		(*ci)->getAllReachableFacts(results);
	}
}

DTGReachability::DTGReachability(const DomainTransitionGraph& dtg_graph)
	: dtg_graph_(&dtg_graph)
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		supported_facts_[dtg_node] = new std::vector<std::vector<const BoundedAtom*> *>();
		std::vector<const DomainTransitionGraphNode*>* reachable_dtg_nodes = new std::vector<const DomainTransitionGraphNode*>();
		reachable_dtg_nodes->push_back(dtg_node);
		reachable_nodes_[dtg_node] = reachable_dtg_nodes;
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			reachable_transitions_[*ci] = new ReachableTransition(**ci);
		}
	}
}

void DTGReachability::propagateReachableNodes()
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
			
//			Bindings& bindings = dtg_node->getDTG().getBindings();
			
			std::vector<const ReachableNode*> reachable_node;
			equivalent_object_manager_->getSupportingFacts(reachable_node, *dtg_node);

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
				const ReachableTransition& reachable_transition = getReachableTransition(*transition);
				
				/// Check if the transition is possible.
				const std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >& possible_mappings = reachable_transition.getPossibleMappings();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				if (possible_mappings.size() > 0)
				{
					std::cout << "Propagate the transition: " << *transition << "." << std::endl;
					for (std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >::const_iterator ci = possible_mappings.begin(); ci != possible_mappings.end(); ci++)
					{
						const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* possible_mapping = *ci;
						
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
								std::cout << " was not mapped in the possible mappings!!!" << std::endl;
								continue;
							}
							
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

				// Some transitions have effects which are linked to terms in the preconditions which are not a part of the from node. Updating
				// the facts in the from node will not yield the required results. For example consider the following transition:
				//
				// (holding ball gripper) -> (in ball room)
				//
				// The value of room is not dictated by any of the terms in the from node, but rather by the precondition: (at hilbert room). Note
				// that hilbert nor room is part of the terms in the from node so it completely stands alone, we will call these /free variables/.
				//
				// To take this into account we need to identify these preconditions and assert what values they can take.
				// NOTE: Will need to change this into a function later on (e.g. room := all rooms which can contain a robot.
				std::set<const std::vector<const Object*>* > mapped_terms;
				
				for (std::vector<BoundedAtom*>::const_iterator ci = transition->getFromNode().getAtoms().begin(); ci != transition->getFromNode().getAtoms().end(); ci++)
				{
					const BoundedAtom* bounded_atom = *ci;
					for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
					{
						mapped_terms.insert(&bounded_atom->getVariableDomain(i, transition->getFromNode().getDTG().getBindings()));
					}
				}
				
				const std::vector<std::pair<const Atom*, InvariableIndex> >& all_preconditions = transition->getAllPreconditions();
				
				unsigned int size = 0;
				while (size != mapped_terms.size())
				{
					size = mapped_terms.size();
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions.begin(); ci != all_preconditions.end(); ci++)
					{
						const Atom* precondition = (*ci).first;
						
						bool contains_mapped_term = false;
						for (unsigned int i = 0; i < precondition->getArity(); i++)
						{
							const std::vector<const Object*>& domain = precondition->getTerms()[i]->getDomain(transition->getStep()->getStepId(), transition->getFromNode().getDTG().getBindings());
							if (mapped_terms.find(&domain) != mapped_terms.end())
							{
								contains_mapped_term = true;
								break;
							}
						}
						
						if (!contains_mapped_term) continue;
						
						for (unsigned int i = 0; i < precondition->getArity(); i++)
						{
							const std::vector<const Object*>& domain = precondition->getTerms()[i]->getDomain(transition->getStep()->getStepId(), transition->getFromNode().getDTG().getBindings());
							mapped_terms.insert(&domain);
						}
					}
				}
				
				/*
				// If two variables refer to eachother they are free variables too - only if the action variables involved are different too!
				for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
				{
					unsigned int index = std::distance(transition->getStep()->getAction().getVariables().begin(), ci);
					const std::vector<const Object*>& domain = (*ci)->getDomain(transition->getStep()->getStepId(), transition->getFromNode().getDTG().getBindings());
					for (std::vector<const Variable*>::const_iterator ci2 = transition->getStep()->getAction().getVariables().begin(); ci2 != transition->getStep()->getAction().getVariables().end(); ci2++)
					{
						unsigned int index2 = std::distance(transition->getStep()->getAction().getVariables().begin(), ci2);
						if (index == index2) continue;
						const std::vector<const Object*>& other_domain = (*ci2)->getDomain(transition->getStep()->getStepId(), transition->getFromNode().getDTG().getBindings());
						if (&domain == &other_domain)
						{
							mapped_terms.erase(&domain);
							break;
						}
					}
				}
				*/
				
				std::map<const std::vector<const Object*>*, EquivalentObjectGroup*> free_variable_mappings;
				for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
				{
					const std::vector<const Object*>& domain = (*ci)->getDomain(transition->getStep()->getStepId(), transition->getFromNode().getDTG().getBindings());
					if (mapped_terms.count(&domain) == 0)
					{
						std::cout << "The variable: ";
						(*ci)->print(std::cout, transition->getFromNode().getDTG().getBindings(), transition->getStep()->getStepId());
						std::cout << " is not bounded by the terms in from node!" << std::endl;

						EquivalentObjectGroup* eog = NULL;
						std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>::iterator it = free_variable_mappings.find(&domain);
						if (it != free_variable_mappings.end())
						{
							eog = (*it).second;
						}
						else
						{
							eog = new EquivalentObjectGroup(transition->getFromNode().getDTG(), *domain[0]);
							free_variable_mappings[&domain] = eog;
						}
						
						for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
						{
							EquivalentObject* eo = new EquivalentObject(**ci, *eog);
							eog->addEquivalentObject(*eo);
						}
						
						free_variable_mappings[&domain] = eog;
					}
				}
				
				for (std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>::const_iterator ci = free_variable_mappings.begin(); ci != free_variable_mappings.end(); ci++)
				{
					std::cout << "Bind " << (*ci).first << " to " << *(*ci).second << "." << std::endl;
				}

				for (std::vector<const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* >::const_iterator ci = possible_mappings.begin(); ci != possible_mappings.end(); ci++)
				{
					const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* reachable_transition_mapping = *ci;
					// Update the mapping to include the assignments made to the reachable_node.
					for (std::vector<const ReachableNode*>::const_iterator ci = reachable_node.begin(); ci != reachable_node.end(); ci++)
					{
						std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* possible_mapping = new std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>(*reachable_transition_mapping);
						const ReachableNode* reachable_node = *ci;
//						std::cout << "Process reachable node: " << *reachable_node << "." << std::endl;
						for (std::vector<const ReachableFact*>::const_iterator ci = reachable_node->supporting_facts_->begin(); ci != reachable_node->supporting_facts_->end(); ci++)
						{
							const ReachableFact* reachable_fact = *ci;
//							std::cout << "Get the bounded atom at index: " << reachable_fact->index_ << "." << std::endl;
							
							const BoundedAtom* bounded_atom = dtg_node->getAtoms()[reachable_fact->index_];
							assert (bounded_atom != NULL);
							
							for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
							{
								const Term* term = bounded_atom->getAtom().getTerms()[i];
								const std::vector<const Object*>& term_domain = term->getDomain(bounded_atom->getId(), dtg_node->getDTG().getBindings());
								
								EquivalentObjectGroup* reachable_fact_eog = reachable_fact->term_domain_mapping_[i];
								(*possible_mapping)[&term_domain] = reachable_fact_eog;
							}
						}
						
						// Free variables overwrite everything else.
						for (std::map<const std::vector<const Object*>*, EquivalentObjectGroup*>::const_iterator ci = free_variable_mappings.begin(); ci != free_variable_mappings.end(); ci++)
						{
							possible_mapping->erase((*ci).first);
						}
						possible_mapping->insert(free_variable_mappings.begin(), free_variable_mappings.end());
						
						makeToNodeReachable(*transition, *possible_mapping);
					}
				}
			}
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::propagateReachableNodes] DONE!" << std::endl;
#endif
}

void DTGReachability::makeToNodeReachable(const Transition& transition, const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& possible_mapping) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::makeToNodeReachable]" << std::endl;

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
		
		std::cout << " to: " << *eog << "." << std::endl;
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
				const std::vector<const Object*>& variable_domain = bounded_atom->getVariableDomain(i, bindings);
				std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>::const_iterator find_ci = possible_mapping.find(&variable_domain);
				
				/**
				 * In some cases the terms of some of the effects of an action are not present in the preconditions. In our 
				 * terms this must mean that the term is lifted and is not restricted by the action.
				 */
				if (find_ci == possible_mapping.end())
				{
					unmapping[i] = true;
					const Object* object = variable_domain[counter[i]];

					EquivalentObjectGroup* tmp_eog = const_cast<EquivalentObjectGroup*>(&equivalent_object_manager_->getEquivalentObject(*object).getEquivalentObjectGroup());
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					tmp_eog->printObjects(std::cout);
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
			}
			
			ReachableFact* new_reachable_fact = new ReachableFact(index, *bounded_atom, bindings, term_domain_mapping);
			//reachable_facts->push_back(new_reachable_fact);
			reachable_facts[index]->push_back(new_reachable_fact);
			
//			std::cout << "Reachable for the " << index << "th atom: " << *new_reachable_fact << std::endl;
			
			for (std::set<EquivalentObjectGroup*>::const_iterator ci = tmp.begin(); ci != tmp.end(); ci++)
			{
				(*ci)->makeReachable(transition.getToNode(), *bounded_atom, *new_reachable_fact);
			}
			
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
		}

		ReachableNode* reachable_node = new ReachableNode(transition.getToNode(), *resulting_reachable_facts);
		equivalent_object_manager_->makeReachable(transition.getToNode(), *reachable_node);
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "." << std::endl;
#endif
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
	unsigned int index = 0;
	for (std::vector<const BoundedAtom*>::const_iterator ci = new_reachable_facts.begin(); ci != new_reachable_facts.end(); ci++)
	{
		reachable_facts->push_back(new ReachableFact(index, **ci, dtg_node.getDTG().getBindings(), *equivalent_object_manager_));
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "- ";
		(*ci)->print(std::cout, dtg_graph_->getBindings());
		std::cout << "." << std::endl;
#endif
		++index;
	}
	ReachableNode* reachable_node = new ReachableNode(dtg_node, *reachable_facts);
	equivalent_object_manager_->makeReachable(dtg_node, *reachable_node);
	
	already_reachable_facts->push_back(&new_reachable_facts);
	return true;
}

void DTGReachability::performReachabilityAnalsysis(std::vector<const BoundedAtom*>& reachable_facts, const std::vector<const BoundedAtom*>& initial_facts, const TermManager& term_manager)
{
//	double time_propagating = 0;
//	double time_iterating = 0;
//	double time_establishing_equivalances = 0;
//	unsigned int amount_of_iterating = 0;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Start performing reachability analysis." << std::endl;
#endif
	// Initialise the individual groups per object.
	equivalent_object_manager_ = new EquivalentObjectGroupManager(*this, *dtg_graph_, term_manager, initial_facts);
	
	// Keep a list of all established facts so far.
	std::vector<const BoundedAtom*> established_facts(initial_facts);
	
	// List of already achieved transitions.
	std::set<const Transition*> achieved_transitions;
	
	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		const BoundedAtom* init_bounded_atom = *ci;
		if (init_bounded_atom->getAtom().getPredicate().isStatic())
		{
			ReachableFact* static_reachable_fact = new ReachableFact(std::numeric_limits<unsigned int>::max(), *init_bounded_atom, dtg_graph_->getBindings(), *equivalent_object_manager_);
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
		new_transitions_achieved = iterateTillFixPoint(established_facts, achieved_transitions);
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
		new_transitions_achieved = handleExternalDependencies(established_facts) || new_transitions_achieved;
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
				
				for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = matching_dtgs.begin(); ci != matching_dtgs.end() - 1; ci++)
				{
					const DomainTransitionGraphNode* equivalent_dtg_node = *ci;

					if (equivalent_dtg_node == &from_node) continue;
					assert (equivalent_dtg_node->getAtoms().size() == from_node.getAtoms().size());
					
					std::vector<const ReachableFact*>* reachable_facts = new std::vector<const ReachableFact*>();
					
					/**
					* Check which node(s) differs and see if the already established reachable EOGs has reached the required facts.
					*/
					for (unsigned int i = 0; i < equivalent_dtg_node->getAtoms().size(); i++)
					{
						const BoundedAtom* equivalent_fact = equivalent_dtg_node->getAtoms()[i];
						const BoundedAtom* this_fact = dtg_node->getAtoms()[i];
						
						const ReachableFact* reachable_this_fact = (*reachable_node->supporting_facts_)[i];
						
						if (dtg_node->getDTG().getBindings().areEquivalent(equivalent_fact->getAtom(), equivalent_fact->getId(), this_fact->getAtom(), this_fact->getId(), &equivalent_dtg_node->getDTG().getBindings()))
						{
							ReachableFact* reachable_equivalent_fact = new ReachableFact(reachable_this_fact->index_, *equivalent_fact, equivalent_dtg_node->getDTG().getBindings(), reachable_this_fact->term_domain_mapping_);
							reachable_facts->push_back(reachable_equivalent_fact);
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
							
							const EquivalentObjectGroup* eog = reachable_this_fact->term_domain_mapping_[j];
							
							//std::cout << "Reachable from: " << *eog << "?" << std::endl;
							
							std::vector<const ReachableFact*> results;
							eog->getSupportingFacts(results, tmp_bounded_atom, equivalent_dtg_node->getDTG().getBindings());
							
							if (results.size() > 0)
							{
								reachable_facts->push_back(results[0]);
								can_be_achieved = true;
								break;
							}
						}
						
						if (!can_be_achieved) break;
					}
					
					if (reachable_facts->size() != equivalent_dtg_node->getAtoms().size()) continue;
					
					/// Make achievable.
					ReachableNode* reachable_node = new ReachableNode(*equivalent_dtg_node, *reachable_facts);
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
				}
			}
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[DTGReachability::handleExternalDependencies] - Done!" << std::endl;
#endif
	return new_facts_reached;
}

bool DTGReachability::iterateTillFixPoint(std::vector<const BoundedAtom*>& established_facts, std::set<const Transition*>& achieved_transitions)
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
					assert (reachable_transitions_[transition]->getPossibleMappings().size() > 0);
					continue;
				}
				
				const DomainTransitionGraphNode& from_dtg_node = transition->getFromNode();
				
				std::vector<const ReachableNode*> supporting_facts;
				equivalent_object_manager_->getSupportingFacts(supporting_facts, from_dtg_node);

				if (supporting_facts.empty())
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << " * No supporting facts for the transition: " << *transition << "." << std::endl;
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
					
					for (std::vector<const ReachableFact*>::const_iterator ci = reached_node->supporting_facts_->begin(); ci != reached_node->supporting_facts_->end(); ci++)
					{
						const ReachableFact* reached_fact = *ci;
						
						for (std::vector<const Property*>::const_iterator ci = reached_fact->bounded_atom_->getProperties().begin(); ci != reached_fact->bounded_atom_->getProperties().end(); ci++)
						{
							const Property* property = *ci;
							if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
							
							invariable_terms.insert(&reached_fact->bounded_atom_->getAtom().getTerms()[property->getIndex()]->getDomain(reached_fact->bounded_atom_->getId(), dtg_graph_->getBindings()));
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
		propagateReachableNodes();
	}
	
	return achieved_transitions.size() != amount_of_achieved_transitions;
}

bool DTGReachability::canSatisfyPreconditions(const Transition& transition, const ReachableNode& supporting_node, std::set<const std::vector<const Object*>* >& invariables) const
{
//	std::cout << "[DTGReachability::canSatisfyPreconditions] Check if the preconditions of the transition: " << transition << " are satisfiable!" << std::endl;
	
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
			
			variable_domain_mapping->insert(std::make_pair(&domain, (*supporting_node.supporting_facts_)[atom_index]->term_domain_mapping_[term_index]));
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
//				std::cout << "The precondition: ";
//				precondition->print(std::cout, bindings, transition.getStep()->getStepId());
//				std::cout << " is supported by ";
//				bounded_atom->print(std::cout, bindings);
//				std::cout << "." << std::endl;
				break;
			}
		}
		
//		if (satisfied) continue;
		
//		std::cout << "Unsatisfied precondition: ";
//		precondition->print(std::cout, bindings, transition.getStep()->getStepId());
//		std::cout << "." << std::endl;
		
	}
	
	const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* possible_mapping = canSatisfyPrecondition(all_preconditions, 0, transition, invariables, *variable_domain_mapping);
	
	if (possible_mapping == NULL || possible_mapping->size() == 0) return false;
	
	// Check if all the 
	
	// Transition is possible! :D
//	std::cout << "Transition is possible! These are the effects: ";
	getReachableTransition(transition).addMapping(*possible_mapping);
	//std::vector<const ReachableFact*>* reachable_facts = new std::vector<const ReachableFact*>();
	
	makeToNodeReachable(transition, *possible_mapping);
	return true;
}

const std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>* DTGReachability::canSatisfyPrecondition(std::vector<std::pair<const Atom*, InvariableIndex> >& all_preconditions, unsigned int index, const Transition& transition, std::set<const std::vector<const Object*>* >& invariables, std::map<const std::vector<const Object*>*, const EquivalentObjectGroup*>& domain_variable_mapping) const
{
	if (all_preconditions.size() == 0)
	{
//		std::cout << "[DTGReachability::canSatisfyPrecondition] All preconditions are empty!" << std::endl;
		return &domain_variable_mapping;
	}
	
	const Bindings& bindings = transition.getFromNode().getDTG().getBindings();
	const Atom* precondition = all_preconditions[index].first;
	
	// TODO: We skip static preconditions - for now.
	if (precondition->getPredicate().isStatic())
	{
		for (std::vector<const ReachableFact*>::const_iterator ci = static_facts_.begin(); ci != static_facts_.end(); ci++)
		{
			const ReachableFact* static_reachable_fact = *ci;
			
			if (bindings.areEquivalent(static_reachable_fact->bounded_atom_->getAtom(), static_reachable_fact->bounded_atom_->getId(), *precondition, transition.getStep()->getStepId()))
			{
				for (unsigned int i = 0; i < precondition->getArity(); i++)
				{
					const std::vector<const Object*>& precondition_variable_domain = precondition->getTerms()[i]->getDomain(transition.getStep()->getStepId(), bindings);
					domain_variable_mapping[&precondition_variable_domain] = static_reachable_fact->term_domain_mapping_[i];
				}
				break;
			}
		}
		if (index == all_preconditions.size() - 1)
		{
			return &domain_variable_mapping;
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
	
//	std::cout << "Work on the precondition: ";
//	bounded_precondition.print(std::cout, bindings);
//	std::cout << "." << std::endl;
	
	// Check which term is linked to an invariable (it should!).
	// TODO: Handle facts which are not part of any DTG (i.e. do not have a property connected to them).
	for (std::vector<const Property*>::const_iterator ci = bounded_precondition.getProperties().begin(); ci != bounded_precondition.getProperties().end(); ci++)
	{
		const Property* property = *ci;
		if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
		
		const Term* invariable_term = bounded_precondition.getAtom().getTerms()[property->getIndex()];
		const std::vector<const Object*>& term_domain = invariable_term->getDomain(transition.getStep()->getStepId(), dtg_graph_->getBindings());
		
//		std::cout << "Invariable term: ";
//		invariable_term->print(std::cout, dtg_graph_->getBindings(), transition.getStep()->getStepId());
//		std::cout << "." << std::endl;
		
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
						
						if (reachable_fact->term_domain_mapping_[i] != corresponding_eog)
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
						(*new_domain_variable_mapping)[&precondition_variable_domain] = reachable_fact->term_domain_mapping_[i];
					}
					
					// We're done!
					if (index == all_preconditions.size() - 1)
					{
						return new_domain_variable_mapping;
					}
					else
					{
						return canSatisfyPrecondition(all_preconditions, index + 1, transition, invariables, *new_domain_variable_mapping);
					}
				}
//				else
//				{
//					std::cout << "No cookie :((" << std::endl;
//				}
			}
		}
		
		// After all the preconditions have been satisfied, store the reached effects! :)
		
	}
	return NULL;
}

void DTGReachability::getSupportingFacts(std::vector<std::vector<const BoundedAtom*>* >& supporting_tupples, const std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >& variable_assignments, const std::vector<BoundedAtom*>& atoms_to_achieve, const std::vector<const BoundedAtom*>& initial_supporting_facts, const std::vector<const BoundedAtom*>& initial_facts) const
{
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
/*					std::cout << "Bind the " << term_index << "th term to: ";
					for (std::vector<const Object*>::const_iterator ci = initial_fact_domain.begin(); ci != initial_fact_domain.end(); ci++)
					{
						(*ci)->print(std::cout, dtg_graph_->getBindings(), initial_fact_id);
						if (ci + 1 != initial_fact_domain.end())
						{
							std::cout << ", ";
						}
					}
					std::cout << "." << std::endl;*/
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
				continue;
			}
			
			// Construct the facts which support the preconditions.
			std::vector<const BoundedAtom*>* initial_supporting_facts_clone = new std::vector<const BoundedAtom*>(initial_supporting_facts);
			initial_supporting_facts_clone->push_back(new BoundedAtom(initial_fact_id, initial_fact));
			
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

};
	
};
