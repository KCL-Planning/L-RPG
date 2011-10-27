#include <cstring>
#include <iterator>
#include <sys/time.h>

#include "equivalent_object_group.h"
#include "dtg_reachability.h"
#include "dtg_manager.h"
#include "dtg_graph.h"
#include "dtg_node.h"
#include "property_space.h"
#include "transition.h"
#include "type_manager.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

namespace MyPOP {
	
namespace SAS_Plus {

/**
 * Equivalent Object.
 */
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

/**
 * Equivalent Object Group.
 */
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

/**
 * Equivalent Object Group Manager.
 */
EquivalentObjectGroupManager::EquivalentObjectGroupManager(const DTGReachability& dtg_reachability, const DomainTransitionGraphManager& dtg_manager, const DomainTransitionGraph& dtg_graph, const TermManager& term_manager)
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

	zero_arity_equivalent_object_group_ = new EquivalentObjectGroup(dtg_graph, NULL, true);
	equivalent_groups_.push_back(zero_arity_equivalent_object_group_);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Done initialising data structures." << std::endl;
#endif
}

void EquivalentObjectGroupManager::initialise(const std::vector<const BoundedAtom*>& initial_facts)
{
	// Look for the DTG nodes which are supported in the initial state.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		const std::vector<BoundedAtom*>& atoms_to_achieve = dtg_node->getAtoms();
		std::vector<std::vector<const ReachableFact*>* > supporting_tupples;
		std::map<const std::vector<const Object*>*, const ReachableFact* > variable_assignments;
		std::vector<const ReachableFact*> initial_supporting_facts;

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the DTG node: " << *dtg_node << std::endl;
#endif

		getSupportingFacts(supporting_tupples, variable_assignments, atoms_to_achieve, initial_supporting_facts, initial_facts);

		for (std::vector<std::vector<const ReachableFact*>* >::const_iterator ci = supporting_tupples.begin(); ci != supporting_tupples.end(); ci++)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Found a set of supporting facts for the DTG node: " << std::endl;
			dtg_node->print(std::cout);
			std::cout << std::endl;
#endif
			const std::vector<const ReachableFact*>* supporting_tupple = *ci;
			for (std::vector<const ReachableFact*>::const_iterator ci = supporting_tupple->begin(); ci != supporting_tupple->end(); ci++)
			{
				//unsigned int index = std::distance(supporting_tupple->begin(), ci);
				
				//const ReachableFact* reachable_fact = *ci;
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << " * ";
				bounded_atom->print(std::cout, dtg_graph.getBindings());
				std::cout << "." << std::endl;
#endif
			}
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

void EquivalentObjectGroupManager::getSupportingFacts(std::vector<const ReachableFact*>& results, const Predicate& predicate, const EquivalentObjectGroup* assigned_terms) const
{
	
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

};

};
