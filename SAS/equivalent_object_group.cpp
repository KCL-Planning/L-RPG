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

//#define MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//#define MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_DEBUG

namespace MyPOP {
	
namespace SAS_Plus {

/**
 * Equivalent Object.
 */
EquivalentObject::EquivalentObject(const Object& object, EquivalentObjectGroup& equivalent_object_group)
	: object_(&object), equivalent_group_(&equivalent_object_group)
{
	
}
	
void EquivalentObject::addInitialFact(ReachableFact& reachable_fact)
{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
	std::cout << "Add " << reachable_fact << " to the initial state of " << *this << std::endl;
#endif
	if (std::find(initial_facts_.begin(), initial_facts_.end(), &reachable_fact) == initial_facts_.end())
	{
		initial_facts_.push_back(&reachable_fact);
		equivalent_group_->addReachableFact(reachable_fact);
	}
}

bool EquivalentObject::areEquivalent(const EquivalentObject& other) const
{
//	std::cout << "Are " << other << " and " << *this << " equivalent?" << std::endl;

//	if (initial_facts_.size() != other.initial_facts_.size() ||
//	    initial_facts_.empty())
	if (initial_facts_.empty() || other.initial_facts_.empty())
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

bool EquivalentObject::isInitialStateReachable(const std::vector<ReachableFact*>& reachable_facts) const
{
	// Check if these initial facts are reachable by the facts reachable by this group of objects.
	for (std::vector<const ReachableFact*>::const_iterator ci = initial_facts_.begin(); ci != initial_facts_.end(); ci++)
	{
		const ReachableFact* initial_fact = *ci;

#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//		std::cout << "Compare: " << *initial_fact << "." << std::endl;
#endif
		
		bool is_initial_fact_reachable = false;
		for (std::vector<ReachableFact*>::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
		{
			const ReachableFact* reachable_fact = *ci;
			
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//		std::cout << " with: " << *reachable_fact<< "." << std::endl;
#endif
			
			if (initial_fact->isEquivalentTo(*reachable_fact))
			{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//				std::cout << *initial_fact << " is equivalent to " << *reachable_fact << std::endl;
#endif
				is_initial_fact_reachable = true;
				break;
			}
		}
		
		if (!is_initial_fact_reachable)
		{
			return false;
		}
	}
	// Got there!
	return true;
}

std::ostream& operator<<(std::ostream& os, const EquivalentObject& equivalent_object)
{
	os << *equivalent_object.object_;
	os << " Initial facts: {" << std::endl;
	for (std::vector<const ReachableFact*>::const_iterator ci = equivalent_object.initial_facts_.begin(); ci != equivalent_object.initial_facts_.end(); ci++)
	{
		os << **ci << std::endl;
	}
	os << " }";
	return os;
}

/**
 * Equivalent Object Group.
 */
EquivalentObjectGroup::EquivalentObjectGroup(const DomainTransitionGraph& dtg_graph, const Object* object, bool is_grounded)
	: is_grounded_(is_grounded), link_(NULL)
{
	if (object != NULL)
	{
		initialiseFingerPrint(dtg_graph, *object);
	}
}

bool EquivalentObjectGroup::contains(const Object& object) const
{
	for (std::vector<EquivalentObject*>::const_iterator ci = equivalent_objects_.begin(); ci != equivalent_objects_.end(); ci++)
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

bool EquivalentObjectGroup::hasSameFingerPrint(const EquivalentObjectGroup& other) const
{
	return memcmp(finger_print_, other.finger_print_, finger_print_size_ * sizeof(bool)) == 0;
//	for (unsigned int i = 0; i < finger_print_size_; i++)
//	{
//		if (finger_print_[i] != other.finger_print_[i]) return false;
//	}
//	return true;
}
	
void EquivalentObjectGroup::initialiseFingerPrint(const DomainTransitionGraph& dtg_graph, const Object& object)
{
	// Check the DTG graph and check which DTG nodes an object can be part of based on its type.
	unsigned int number_of_facts = 0;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
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
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
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

void EquivalentObjectGroup::addEquivalentObject(EquivalentObject& eo)
{
	equivalent_objects_.push_back(&eo);
}

void EquivalentObjectGroup::addReachableFact(ReachableFact& reachable_fact)
{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_DEBUG
	// Make sure we do not add any double instances!
	for (std::vector<ReachableFact*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		const ReachableFact* existing_reachable_fact = *ci;
		if (existing_reachable_fact->isIdenticalTo(reachable_fact))
		{
			std::cout << "Trying to add: " << reachable_fact << " to the following set: " << std::endl;
			
			for (std::vector<ReachableFact*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
			{
				const ReachableFact* existing_reachable_factz = *ci;
				std::cout << "* " << *existing_reachable_factz << std::endl;
			}
			
			std::cout << "However it is identical to: " << *existing_reachable_fact << std::endl;

			assert (false);
		}
	}
#endif
	reachable_facts_.push_back(&reachable_fact);
}

bool EquivalentObjectGroup::tryToMergeWith(EquivalentObjectGroup& other_group, std::vector<EquivalentObjectGroup*>& affected_groups)
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
		return this_root_node.tryToMergeWith(other_root_node, affected_groups);
	}
	else if (other_group.link_ != NULL)
	{
		return tryToMergeWith(other_root_node, affected_groups);
	}

	// Only allow to merge two equivalent object groups if the fingerprints are equal!
	assert (finger_print_size_ == other_group.finger_print_size_);
	if (memcmp(finger_print_, other_group.finger_print_, finger_print_size_) != 0)
	{
		return false;
	}
	
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//	std::cout << "Try to merge: " << *this << " with " << other_group << "." << std::endl;
#endif

	// TODO: This implementation isn't fast at all...
	bool can_merge = false;
	for (std::vector<EquivalentObject*>::const_iterator ci = other_group.equivalent_objects_.begin(); ci != other_group.equivalent_objects_.end(); ci++)
	{
		const EquivalentObject* other_equivalent_object = *ci;
		if (other_equivalent_object->isInitialStateReachable(reachable_facts_))
		{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//			std::cout << other_group << " can reach initial state of " << *this << std::endl;
#endif
			can_merge = true;
			break;
		}
	}
	if (!can_merge) return false;
	can_merge = false;
	
	for (std::vector<EquivalentObject*>::const_iterator ci = equivalent_objects_.begin(); ci != equivalent_objects_.end(); ci++)
	{
		const EquivalentObject* equivalent_object = *ci;
		if (equivalent_object->isInitialStateReachable(other_group.reachable_facts_))
		{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//			std::cout << *this << " can reach initial state of " << other_group << std::endl;
#endif
			can_merge = true;
			break;
		}
	}
	if (!can_merge) return false;
	
	merge(other_group, affected_groups);
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
	for (std::vector<EquivalentObject*>::const_iterator ci = equivalent_objects_.begin(); ci != equivalent_objects_.end(); ci++)
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
//	for (std::multimap<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*>, ReachableFact*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
//	{
//		(*ci).second->printGrounded(os);
//	}
}

void EquivalentObjectGroup::merge(EquivalentObjectGroup& other_group, std::vector<EquivalentObjectGroup*>& affected_groups)
{
	assert (other_group.link_ == NULL);
	
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
	std::cout << "Merging " << *this << " with " << other_group << "." << std::endl;
#endif
	
	equivalent_objects_.insert(equivalent_objects_.begin(), other_group.equivalent_objects_.begin(), other_group.equivalent_objects_.end());
	other_group.link_ = this;
	
	// TODO: Need to make sure we do not end up with multiple reachable facts which are identical!
	//std::vector<EquivalentObjectGroup*> affected_groups;
	
	// Facts which are already part of this EOG should already contain the updated reachable fact, so any facts which need to 
	// be updated can safely be removed.
	for (std::vector<ReachableFact*>::reverse_iterator ri = reachable_facts_.rbegin(); ri != reachable_facts_.rend(); ri++)
	{
		ReachableFact* reachable_fact = *ri;
		
		for (unsigned int i = 0; i < reachable_fact->getAtom().getArity(); i++)
		{
			EquivalentObjectGroup& eog = reachable_fact->getTermDomain(i);
			if (!eog.isRootNode())
			{
				reachable_facts_.erase(ri.base() - 1);
				for (unsigned int i = 0; i < reachable_fact->getAtom().getArity(); i++)
				{
					EquivalentObjectGroup& eog = reachable_fact->getTermDomain(i);
					
					if (&eog != this && std::find(affected_groups.begin(), affected_groups.end(), &eog) == affected_groups.end())
					{
						affected_groups.push_back(&eog);
					}
				}
				break;
			}
		}
	}
	std::vector<ReachableFact*> updated_facts(reachable_facts_);
	for (std::vector<ReachableFact*>::const_iterator ri = other_group.reachable_facts_.begin(); ri != other_group.reachable_facts_.end(); ri++)
	{
		ReachableFact* reachable_fact = *ri;
		// The set of reachable facts in this EOG and the other EOG should be disjunct so there is no way any of the facts 
		// are yet marked for removal.
		// However, if a fact contains a reference to the same EOG which is then merged with another EOG we cannot select the EOG with the same 
		// references as the "head" node.

		// If multiple EOGs have been updated it can be that one of the facts in this EOG is also affected. We should ignore the 
		// nodes marked for removal.
		if (reachable_fact->isMarkedForRemoval()) continue;
		
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//		std::cout << "Check if " << *reachable_fact << " needs to be updated!" << std::endl;
#endif
		// If the reachable fact contains a EOG which is not a root node, it means that a merge has taken place and we need to delete this node and
		// replace it with a reachable fact containing only root nodes.
		bool already_present = false;
		if (reachable_fact->updateTermsToRoot())
		{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//			std::cout << "Updated the reachable fact: " << *reachable_fact << std::endl;
#endif

			ReachableFact* identical_fact = NULL;
			for (std::vector<ReachableFact*>::const_iterator ci = updated_facts.begin(); ci != updated_facts.end(); ci++)
			{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//				std::cout << "Check if " << **ci << " and " << *reachable_fact << " are identical!" << std::endl;
#endif
				if ((*ci)->isIdenticalTo(*reachable_fact))
				{
					assert (*ci != reachable_fact);
					identical_fact = *ci;
					already_present = true;
					break;
				}
			}
			
			if (already_present)
			{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
				std::cout << "Remove: " << *reachable_fact << "[r=" << &reachable_fact->getReplacement() << "] because it is identical to the fact: " << *identical_fact << "[r=" << &identical_fact->getReplacement() << "]." << std::endl;
#endif
				reachable_fact->replaceBy(*identical_fact);
				
				for (unsigned int i = 0; i < reachable_fact->getAtom().getArity(); i++)
				{
					EquivalentObjectGroup& eog = reachable_fact->getTermDomain(i);
					
					if (/*&eog != this && */std::find(affected_groups.begin(), affected_groups.end(), &eog) == affected_groups.end())
					{
						affected_groups.push_back(&eog);
					}
				}
			}
			else
			{
				updated_facts.push_back(reachable_fact);
			}
		}
		
		if (!already_present)
		{
//#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_DEBUG
			addReachableFact(*reachable_fact);
//#endif
//			reachable_facts_.push_back(reachable_fact);
		}
	}

	// Clean up all the groups which have been affected by removing all the reachable facts which have been marked for removal.
	// NOTE: This can be done later after the whole merging is done! But this is just an optimisation we can perform
	// later too.
//	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = affected_groups.begin(); ci != affected_groups.end(); ci++)
//	{
//		EquivalentObjectGroup* eog = *ci;
//		eog->deleteRemovedFacts();
//	}
	
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
	std::cout << "Result of merging: " << *this << "." << std::endl;
#endif
}

void EquivalentObjectGroup::deleteRemovedFacts()
{
	for (std::vector<ReachableFact*>::reverse_iterator ri = reachable_facts_.rbegin(); ri != reachable_facts_.rend(); ri++)
	{
		if ((*ri)->isMarkedForRemoval())
		{
			reachable_facts_.erase(ri.base() - 1);
		}
	}
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
	for (std::vector<EquivalentObject*>::const_iterator ci = group.equivalent_objects_.begin(); ci != group.equivalent_objects_.end(); ci++)
	{
		const EquivalentObject* eo = *ci;
		os << eo->getObject() << std::endl;
		
//		os << eo->getObject();
//		if (ci + 1 != group.equivalent_objects_.end())
//		{
//			os << ", ";
//		}
	}
	os << " }" << std::endl;

	std::cout << "Reachable facts: " << std::endl;
	for (std::vector<ReachableFact*>::const_iterator ci = group.reachable_facts_.begin(); ci != group.reachable_facts_.end(); ci++)
	{
		std::cout << "- " << **ci << std::endl;
	}
	return os;
}

/**
 * Equivalent Object Group Manager.
 */
EquivalentObjectGroupManager::EquivalentObjectGroupManager(const DomainTransitionGraphManager& dtg_manager, const DomainTransitionGraph& dtg_graph, const TermManager& term_manager)
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
	
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
	std::cout << "Done initialising data structures." << std::endl;
#endif
}

void EquivalentObjectGroupManager::initialise(const std::vector<ReachableFact*>& initial_facts)
{
	// Record the set of initial facts every object is part of.
	for (std::vector<ReachableFact*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		ReachableFact* initial_reachable_fact = *ci;
		
		if (initial_reachable_fact->getAtom().getArity() > 0)
		{
			for (unsigned int i = 0; i < initial_reachable_fact->getAtom().getArity(); i++)
			{
				EquivalentObjectGroup& eog = initial_reachable_fact->getTermDomain(i);
				for (std::vector<EquivalentObject*>::const_iterator ci = eog.getEquivalentObjects().begin(); ci != eog.getEquivalentObjects().end(); ci++)
				{
					(*ci)->addInitialFact(*initial_reachable_fact);
				}
			}
		}
		else
		{
			zero_arity_equivalent_object_group_->addReachableFact(*initial_reachable_fact);
		}
	}
	
	// Try to merge those eogs which are equivalent.
	//updateEquivalences();
	
//#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
//	std::cout << "Merge together equivalent groups if their initial states match - Done!" << std::endl;
//	std::cout << "EOG manager Ready for use!" << std::endl;
//	print(std::cout);
//	printAll(std::cout);
//#endif
}

void EquivalentObjectGroupManager::updateEquivalences()
{
	// Try to merge those eogs which are equivalent.
	bool merge_mask[equivalent_groups_.size()];
	memset(&merge_mask[0], false, sizeof(bool) * equivalent_groups_.size());
	unsigned int index1 = 0;
	
	std::vector<EquivalentObjectGroup*> affected_groups;
	
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
			if (eog1->tryToMergeWith(*eog2, affected_groups))
			{
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
				std::cout << "Merged: " << *eog1 << "." << std::endl;
#endif
				merge_mask[index2] = true;
			}
			++index2;
		}
		++index1;
	}
	
	unsigned int removed_instances = 0;
	for (std::vector<EquivalentObjectGroup*>::reverse_iterator ri = equivalent_groups_.rbegin(); ri != equivalent_groups_.rend(); ri++)
	{
		unsigned int index = std::distance(equivalent_groups_.begin(), ri.base() - 1);
		if (merge_mask[index])
		{
			++removed_instances;
			equivalent_groups_.erase(ri.base() - 1);
		}
	}
	
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = affected_groups.begin(); ci != affected_groups.end(); ci++)
	{
		EquivalentObjectGroup* eog = *ci;
		if (eog->isRootNode())
		{
			eog->deleteRemovedFacts();
		}
	}
	
#ifdef MYPOP_SAS_PLUS_EQUIAVLENT_OBJECT_COMMENT
	std::cerr << "[EquivalentObjectGroupManager::updateEquivalences] Merged: " << removed_instances << " EOGs!" << std::endl;
#endif
}


EquivalentObject& EquivalentObjectGroupManager::getEquivalentObject(const Object& object) const
{
	std::map<const Object*, EquivalentObject*>::const_iterator ci = object_to_equivalent_object_mapping_.find(&object);
	if (ci == object_to_equivalent_object_mapping_.end())
	{
		std::cout << "Could not find the Equivalent Object for the object: " << object << std::endl;
		assert (false);
	}
	
	return *(*ci).second;
}

void EquivalentObjectGroupManager::getAllReachableFacts(std::vector<const ReachableFact*>& result) const
{
	std::set<const EquivalentObjectGroup*> closed_list;
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end(); ci++)
	{
		EquivalentObjectGroup* eog = *ci;
		const std::vector<ReachableFact*>& reachable_fact = eog->getReachableFacts();
		
		for (std::vector<ReachableFact*>::const_iterator ci = reachable_fact.begin(); ci != reachable_fact.end(); ci++)
		{
			// Make sure it hasn't been processed yet.
			ReachableFact* reachable_fact = *ci;
			bool has_been_processed = false;
			
			for (unsigned int i = 0; i < reachable_fact->getAtom().getArity(); i++)
			{
				if (closed_list.count(&reachable_fact->getTermDomain(i)) != 0)
				{
					has_been_processed = true;
					break;
				}
			}
			
			if (has_been_processed) continue;

			result.push_back(reachable_fact);
		}
		
		closed_list.insert(eog);
	}
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

};

};
