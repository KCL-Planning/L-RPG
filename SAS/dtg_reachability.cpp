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

namespace MyPOP {
	
namespace SAS_Plus {

EquivalentObjectGroup::EquivalentObjectGroup(const Object& object, const DomainTransitionGraph& dtg_graph)
	: dtg_graph_(&dtg_graph), link_(NULL)
{
	initial_mapping_[&object] = new std::vector<const DomainTransitionGraphNode*>();
	initialiseFingerPrint(object, dtg_graph);
}
	
EquivalentObjectGroup::EquivalentObjectGroup(const Object& object, const DomainTransitionGraph& dtg_graph, std::vector<const DomainTransitionGraphNode*>& initial_dtgs)
	: dtg_graph_(&dtg_graph), link_(NULL)
{
	initial_mapping_[&object] = &initial_dtgs;
	initialiseFingerPrint(object, dtg_graph);
}

void EquivalentObjectGroup::initialiseFingerPrint(const Object& object, const DomainTransitionGraph& dtg_graph)
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

bool EquivalentObjectGroup::addInitialDTGNodeMapping(const Object& object, const DomainTransitionGraphNode& dtg_node)
{
	if (link_ != NULL)
	{
		return link_->addInitialDTGNodeMapping(object, dtg_node);
	}
	std::map<const Object*, std::vector<const DomainTransitionGraphNode*> *>::iterator i = initial_mapping_.find(&object);
	std::vector<const DomainTransitionGraphNode*>* mapping;
	if (i == initial_mapping_.end())
	{
		mapping = new std::vector<const DomainTransitionGraphNode*>();
	}
	else
	{
		mapping = (*i).second;
	}
	mapping->push_back(&dtg_node);
	
	updateReachableFacts(object, dtg_node);
	
	return true;
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
	std::cout << "Try to merge: " << *this << " with " << other_group << "." << std::endl;
#endif

	// Check if this is reachable from other and visa versa.
	for (std::map<const Object*, std::vector<const DomainTransitionGraphNode*> *>::const_iterator ci = initial_mapping_.begin(); ci != initial_mapping_.end(); ci++)
	{
		const std::vector<const DomainTransitionGraphNode*>* this_initial_dtgs = (*ci).second;
		
		if (this_initial_dtgs->size() == 0)
		{
			continue;
		}
		
		for (std::map<const Object*, std::vector<const DomainTransitionGraphNode*> *>::const_iterator ci = other_group.initial_mapping_.begin(); ci != other_group.initial_mapping_.end(); ci++)
		{
			const std::vector<const DomainTransitionGraphNode*>* other_initial_dtgs = (*ci).second;
			
			if (other_initial_dtgs->size() == 0)
			{
				continue;
			}
			
			// Keep a boolean array to record which facts can be reached from each other's states.
			bool this_initial_reachable[this_initial_dtgs->size()];
			memset(&this_initial_reachable[0], false, sizeof(bool) * this_initial_dtgs->size());
			
			bool other_initial_reachable[other_initial_dtgs->size()];
			memset(&other_initial_reachable[0], false, sizeof(bool) * other_initial_dtgs->size());
			
			for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = this_initial_dtgs->begin(); ci != this_initial_dtgs->end(); ci++)
			{
				const DomainTransitionGraphNode* this_initial_dtg = *ci;
				unsigned int this_initial_dtg_index = std::distance(this_initial_dtgs->begin(), ci);
				std::vector<const DomainTransitionGraphNode*>* reachable_nodes_from_this = (*reachable_nodes.find(this_initial_dtg)).second;

				for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = other_initial_dtgs->begin(); ci != other_initial_dtgs->end(); ci++)
				{
					const DomainTransitionGraphNode* other_initial_dtg = *ci;
					unsigned int other_initial_dtg_index = std::distance(other_initial_dtgs->begin(), ci);
					std::vector<const DomainTransitionGraphNode*>* reachable_nodes_from_other = (*reachable_nodes.find(other_initial_dtg)).second;
					
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "New set of initial DTG nodes to test! " << std::endl;
					this_initial_dtg->print(std::cout);
					std::cout << std::endl << "is reachable from" << std::endl;
					other_initial_dtg->print(std::cout);
					std::cout << std::endl << " and visa versa!" << std::endl;
#endif

					if (!other_initial_reachable[other_initial_dtg_index])
					{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "Check if" << std::endl;
						other_initial_dtg->print(std::cout);
						std::cout << std::endl << "is reachable from" << std::endl;
						this_initial_dtg->print(std::cout);
						std::cout << std::endl;
#endif

						for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = reachable_nodes_from_this->begin(); ci != reachable_nodes_from_this->end(); ci++)
						{
							const DomainTransitionGraphNode* reachable_dtg_node = *ci;
							if (reachable_dtg_node == other_initial_dtg || other_initial_dtg->isSubSetOf(*reachable_dtg_node))
							{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
								if (reachable_dtg_node == other_initial_dtg)
									std::cout << "They are the same!" << std::endl;
								else
									std::cout << "One is a subset of the other!" << std::endl;
#endif
								other_initial_reachable[other_initial_dtg_index] = true;
								break;
							}
						}
					}
					
					if (!this_initial_reachable[this_initial_dtg_index])
					{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "Check if" << std::endl;
						this_initial_dtg->print(std::cout);
						std::cout << std::endl << "is reachable from" << std::endl;
						other_initial_dtg->print(std::cout);
						std::cout << std::endl;
#endif
						for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = reachable_nodes_from_other->begin(); ci != reachable_nodes_from_other->end(); ci++)
						{
							const DomainTransitionGraphNode* reachable_dtg_node = *ci;
							if (reachable_dtg_node == this_initial_dtg || this_initial_dtg->isSubSetOf(*reachable_dtg_node))
							{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
								if (reachable_dtg_node == this_initial_dtg)
									std::cout << "They are the same!" << std::endl;
								else
									std::cout << "One is a subset of the other!" << std::endl;
#endif
								this_initial_reachable[this_initial_dtg_index] = true;
								break;
							}
						}
					}
				}
			}
			
			bool is_reachable = true;
			
			for (unsigned int i = 0; i < this_initial_dtgs->size(); i++)
			{
				if (!this_initial_reachable[this_initial_dtgs->size()])
				{
					is_reachable = false;
					break;
				}
			}
			
			if (is_reachable)
			{
				for (unsigned int i = 0; i < other_initial_dtgs->size(); i++)
				{
					if (!other_initial_reachable[other_initial_dtgs->size()])
					{
						is_reachable = false;
						break;
					}
				}
			}
			
			if (is_reachable)
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << *this << " is reachable from " << other_group << "." << std::endl;
#endif
				merge(other_group);
				return true;
			}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			else
			{
				for (unsigned int i = 0; i < this_initial_dtgs->size(); i++)
				{
					if (!this_initial_reachable[this_initial_dtgs->size()])
					{
						std::cout << "- ";
						(*this_initial_dtgs)[i]->print(std::cout);
						std::cout << " is NOT reachable!" << std::endl;
					}
				}
				
				for (unsigned int i = 0; i < other_initial_dtgs->size(); i++)
				{
					if (!other_initial_reachable[other_initial_dtgs->size()])
					{
						std::cout << "- ";
						(*other_initial_dtgs)[i]->print(std::cout);
						std::cout << " is NOT reachable!" << std::endl;
					}
				}
			}
#endif
		}
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << *this << " is NOT reachable from " << other_group << "." << std::endl;
#endif
	return false;
}

void EquivalentObjectGroup::merge(EquivalentObjectGroup& other_group)
{
	assert (other_group.link_ == NULL);
	initial_mapping_.insert(other_group.initial_mapping_.begin(), other_group.initial_mapping_.end());
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
	os << " -= EquivalentObjectGroup =- " << std::endl;
	
	for (std::map<const Object*, std::vector<const DomainTransitionGraphNode*> *>::const_iterator ci = group.initial_mapping_.begin(); ci != group.initial_mapping_.end(); ci++)
	{
		os << *(*ci).first << " -> " << std::endl;
		
		std::vector<const DomainTransitionGraphNode*>* initial_nodes = (*ci).second;
		
		for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = initial_nodes->begin(); ci != initial_nodes->end(); ci++)
		{
			os << "* ";
			(*ci)->print(os);
			os << std::endl;
		}
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
		EquivalentObjectGroup* equivalent_group = new EquivalentObjectGroup(*object, dtg_graph);
		equivalent_groups_.push_back(equivalent_group);
		object_to_equivalent_group_mapping_[object] = equivalent_group;
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Done initialising data strucutres." << std::endl;
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
			std::cout << "Found a set of supporting facts for the DTG node: " << *dtg_node << std::endl;
#endif
			const std::vector<const BoundedAtom*>* supporting_tupple = *ci;

			for (std::vector<const BoundedAtom*>::const_iterator ci = supporting_tupple->begin(); ci != supporting_tupple->end(); ci++)
			{
				const BoundedAtom* bounded_atom = *ci;
				
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
						assert (object_to_equivalent_group_mapping_.find(*ci) != object_to_equivalent_group_mapping_.end());
						EquivalentObjectGroup* matching_equivalent_group = object_to_equivalent_group_mapping_[*ci];
						matching_equivalent_group->addInitialDTGNodeMapping(**ci, *dtg_node);
					}
				}
			}
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
	
	// Compare the equivalent objects and check if they share the same initial state. If this is the case, combine them.
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Merge together equivalent groups if their initial states match." << std::endl;
#endif
	for (std::map<const Object*, EquivalentObjectGroup*>::const_iterator ci = object_to_equivalent_group_mapping_.begin(); ci != object_to_equivalent_group_mapping_.end(); ci++)
	{
		if (++ci == object_to_equivalent_group_mapping_.end()) break;
		--ci;
		
//		const Object* object = (*ci).first;
		EquivalentObjectGroup* equivalent_object_group = (*ci).second;

		for (std::map<const Object*, EquivalentObjectGroup*>::const_iterator ci2 = ci; ci2 != object_to_equivalent_group_mapping_.end(); ci2++)
		{
			if (ci == ci2) continue;
			
//			const Object* other_object = (*ci2).first;
			EquivalentObjectGroup* other_equivalent_object_group = (*ci2).second;
			
			if (equivalent_object_group->tryToMergeWith(*other_equivalent_object_group, reachable_nodes))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Merged: " << *equivalent_object_group << " and " << other_equivalent_object_group << "." << std::endl;
#endif
				object_to_equivalent_group_mapping_[(*ci2).first] = equivalent_object_group;
			}
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Merge together equivalent groups if their initial states match - Done!" << std::endl;
#endif
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

void EquivalentObjectGroupManager::print(std::ostream& os) const
{
	std::cout << "All equivalence groups:" << std::endl;
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = equivalent_groups_.begin(); ci != equivalent_groups_.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
}
	
	
DTGReachability::DTGReachability(const DomainTransitionGraph& dtg_graph)
	: dtg_graph_(&dtg_graph)
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		supported_facts_[*ci] = new std::vector<std::vector<const BoundedAtom*> *>();
		std::vector<const DomainTransitionGraphNode*>* reachable_dtg_nodes = new std::vector<const DomainTransitionGraphNode*>();
		reachable_dtg_nodes->push_back(*ci);
		reachable_nodes_[*ci] = reachable_dtg_nodes;
	}
}

void DTGReachability::propagateReachableNodes()
{
	bool finished = false;
	while (!finished)
	{
		finished = true;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			
			std::vector<const DomainTransitionGraphNode*>* reachable_nodes = reachable_nodes_[dtg_node];
			assert (reachable_nodes != NULL);
			
			std::vector<const DomainTransitionGraphNode*> new_reachable_nodes;
			
			// For each of the reachable nodes, add the nodes which are reachable from this node to those reachable from this node.
			for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = reachable_nodes->begin(); ci != reachable_nodes->end(); ci++)
			{
				const DomainTransitionGraphNode* reachable_dtg_node = *ci;
				if (dtg_node == reachable_dtg_node) continue;
				
				assert (reachable_dtg_node != NULL);
				
				std::vector<const DomainTransitionGraphNode*>* reachable_from_reachable_nodes = reachable_nodes_[reachable_dtg_node];
				assert (reachable_from_reachable_nodes != NULL);
				
				new_reachable_nodes.insert(new_reachable_nodes.end(), reachable_from_reachable_nodes->begin(), reachable_from_reachable_nodes->end());
			}
			
			for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = new_reachable_nodes.begin(); ci != new_reachable_nodes.end(); ci++)
			{
				const DomainTransitionGraphNode* new_dtg_node = *ci;
				if (std::find(reachable_nodes->begin(), reachable_nodes->end(), new_dtg_node) == reachable_nodes->end())
				{
					reachable_nodes->push_back(new_dtg_node);
					finished = false;
				}
			}
		}
	}
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
	for (std::vector<const BoundedAtom*>::const_iterator ci = new_reachable_facts.begin(); ci != new_reachable_facts.end(); ci++)
	{
		std::cout << "- ";
		(*ci)->print(std::cout, dtg_graph_->getBindings());
		std::cout << "." << std::endl;
	}
#endif
	
	already_reachable_facts->push_back(&new_reachable_facts);
	return true;
}

void DTGReachability::performReachabilityAnalsysis(const std::vector<const BoundedAtom*>& initial_facts, const TermManager& term_manager)
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
	
	unsigned int pre_size = 0;
	
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
	struct timeval end_time_init;
	gettimeofday(&end_time_init, NULL);
	
	double time_spend = end_time_init.tv_sec - start_time_init.tv_sec + (end_time_init.tv_usec - start_time_init.tv_usec) / 1000000.0;
	std::cerr << "Time spend initiating initial structure: " << time_spend << std::endl;

	// Keep on iterator as long as we can establish new facts.
	do 
	{
		pre_size = established_facts.size();
		
		struct timeval start_time;
		gettimeofday(&start_time, NULL);
		iterateThroughFixedPoint(established_facts, achieved_transitions);
		struct timeval end_time;
		gettimeofday(&end_time, NULL);
		
		time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
		std::cerr << "Time spend iterating: " << time_spend << std::endl;
		
		// After no other transitions can be reached we establish the object equivalence relations.
		gettimeofday(&start_time, NULL);
		equivalent_object_manager_->updateEquivalences(reachable_nodes_);
		gettimeofday(&end_time, NULL);
		time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
		std::cerr << "Time spend establishing equivalent relationships: " << time_spend << std::endl;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		equivalent_object_manager_->print(std::cout);
#endif

		gettimeofday(&start_time, NULL);
		handleExternalDependencies(established_facts);
		gettimeofday(&end_time, NULL);
		time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
		std::cerr << "Time spend resolving external dependencies: " << time_spend << std::endl;
		
	} while (pre_size != established_facts.size());
	
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
#endif

	for (std::vector<const BoundedAtom*>::const_iterator ci = established_facts.begin(); ci != established_facts.end(); ci++)
	{
		std::cout << "- ";
		(*ci)->print(std::cout, dtg_graph_->getBindings());
		std::cout << std::endl;
	}
}

void DTGReachability::handleExternalDependencies(std::vector<const BoundedAtom*>& established_facts)
{
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
			const std::vector<std::vector<const BoundedAtom*>* >* supporing_facts_from_node = supported_facts_[&from_node];

			if (supporing_facts_from_node->size() == 0)
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
			for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = matching_dtgs.begin(); ci != matching_dtgs.end() - 1; ci++)
			{
				const DomainTransitionGraphNode* equivalent_dtg_node = *ci;

				if (equivalent_dtg_node == &from_node) continue;
				assert (equivalent_dtg_node->getAtoms().size() == from_node.getAtoms().size());
				
				/**
				 * We construct the bounded atoms corresponding to the facts which need to be reached to satisfy the
				 * externally dependend facts.
				 */
				for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = supporing_facts_from_node->begin(); ci != supporing_facts_from_node->end(); ci++)
				{
					const std::vector<const BoundedAtom*>* supporting_facts = *ci;
				
					/**
					 * Check all the facts of the potential to nodes and check if we can reach them - we only need to
					 * check the facts which contain an external dependency.
					 */
					bool all_externally_dependend_facts_can_be_reached = true;
					std::vector<const BoundedAtom*>* reachable_facts = new std::vector<const BoundedAtom*>();
					for (unsigned int i = 0; i < from_node.getAtoms().size(); i++)
					{
						if (!facts_with_external_dependencies[i])
						{
							reachable_facts->push_back((*supporting_facts)[i]);
							continue;
						}
						
						const BoundedAtom* from_supporting_fact = (*supporting_facts)[i];
						const BoundedAtom* equivalent_fact_to_reach = equivalent_dtg_node->getAtoms()[i];
						
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						// Check if the fact from from_node can reach the fact in the equivalent dtg node.
						std::cout << "Can we reach: ";
						equivalent_fact_to_reach->print(std::cout, dtg_graph_->getBindings());
						std::cout << " from {";
						
						for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = supporing_facts_from_node->begin(); ci != supporing_facts_from_node->end(); ci++)
						{
							std::vector<const BoundedAtom*>* supporting_facts = *ci;
							if (supporting_facts->size() != from_node.getAtoms().size())
							{
								std::cout << "The supporting facts for the DTG node:" << std::endl;
								std::cout << from_node << ": " << std::endl;
								for (std::vector<const BoundedAtom*>::const_iterator ci = supporting_facts->begin(); ci != supporting_facts->end(); ci++)
								{
									(*ci)->print(std::cout, dtg_graph_->getBindings());
									std::cout << std::endl;
								}
								assert (false);
							}
							(**ci)[i]->print(std::cout, dtg_graph_->getBindings());
						}
						std::cout << "}?" << std::endl;
#endif
					
						const BoundedAtom& atom_to_reach = BoundedAtom::createBoundedAtom(equivalent_fact_to_reach->getAtom(), equivalent_fact_to_reach->getProperties(), dtg_graph_->getBindings());
						for (unsigned int j = 0; j < atom_to_reach.getAtom().getArity(); j++)
						{
							const Term* atom_to_reach_term = atom_to_reach.getAtom().getTerms()[j];
							const Term* to_node_term = equivalent_fact_to_reach->getAtom().getTerms()[j];
							const Term* from_node_term = from_supporting_fact->getAtom().getTerms()[j];
							
							assert (i < from_node.getAtoms().size());
							assert (j < largest_arity);
							
							// Check if this term is externally dependend, if it is we make it equal to the to node.
							if (dependend_term_mapping[i][j])
							{
								atom_to_reach_term->makeDomainEqualTo(atom_to_reach.getId(), to_node_term->getDomain(equivalent_fact_to_reach->getId(), dtg_graph_->getBindings()), dtg_graph_->getBindings());
							}
							// Else we make it equal to the from node.
							else
							{
								atom_to_reach_term->makeDomainEqualTo(atom_to_reach.getId(), from_node_term->getDomain(from_supporting_fact->getId(), dtg_graph_->getBindings()), dtg_graph_->getBindings());
							}
						}
						reachable_facts->push_back(&atom_to_reach);
						
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "Atom to search for: ";
						atom_to_reach.print(std::cout, dtg_graph_->getBindings());
						std::cout << std::endl;
#endif
						
						// TODO: Very inefficient, in the future we will use object equivalence groups to handle this.
						bool has_been_achieved = false;
						for (std::vector<const BoundedAtom*>::const_iterator ci = established_facts.begin(); ci != established_facts.end(); ci++)
						{
							const BoundedAtom* reached_atom = *ci;
//							if (dtg_graph_->getBindings().canUnifyBoundedAtoms(*reached_atom, atom_to_reach))
							if (reached_atom->canUnifyWith(atom_to_reach, dtg_graph_->getBindings()))
							{
								has_been_achieved = true;
								break;
							}
						}
						
						if (!has_been_achieved)
						{
							all_externally_dependend_facts_can_be_reached = false;
							break;
						}
					}
					
					if (all_externally_dependend_facts_can_be_reached)
					{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << *equivalent_dtg_node << " can be reached from: " << std::endl;
						
						for (std::vector<const BoundedAtom*>::const_iterator ci = supporting_facts->begin(); ci != supporting_facts->end(); ci++)
						{
							const BoundedAtom* bounded_atom = *ci;
							std::cout << " * ";
							bounded_atom->print(std::cout, dtg_graph_->getBindings());
							std::cout << "." << std::endl;
						}
						
						// Add the new facts to the list! :)
						std::cout << "New bounded atoms to add:" << std::endl;
						for (std::vector<const BoundedAtom*>::const_iterator ci = reachable_facts->begin(); ci != reachable_facts->end(); ci++)
						{
							std::cout << "* ";
							(*ci)->print(std::cout, dtg_graph_->getBindings());
							std::cout << std::endl;
						}
#endif
						assert (equivalent_dtg_node != NULL);

						reachable_nodes_[&from_node]->push_back(equivalent_dtg_node);
						makeReachable(*equivalent_dtg_node, *reachable_facts);
					}
				}
			}
		}
	}
}

void DTGReachability::iterateThroughFixedPoint(std::vector<const BoundedAtom*>& established_facts, std::set<const Transition*>& achieved_transitions)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Start new iteration." << std::endl;
#endif
	
	std::vector<const DomainTransitionGraphNode*> initial_satisfied_nodes;
	
	// While there are transitions achieved:
	bool new_transition_achieved = true;
	while (new_transition_achieved)
	{
		new_transition_achieved = false;
		
		// Propagate the reachable nodes.
		propagateReachableNodes();

		// For each transition of a marked node:
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_graph = *ci;
			for (std::vector<const Transition*>::const_iterator ci = dtg_graph->getTransitions().begin(); ci != dtg_graph->getTransitions().end(); ci++)
			{
				/// Check if the preconditions of the transition have been satisfied.
				const Transition* transition = *ci;
				
				if (achieved_transitions.count(transition) != 0) continue;
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << " * Work on the transition: " << *transition << "." << std::endl;
#endif
				const DomainTransitionGraphNode& from_dtg_node = transition->getFromNode();
				
				// Instantiate the DTG node by assigning the terms to domains we have already determined to be reachable.
				const std::vector<std::vector<const BoundedAtom*>* >* assignable_atoms = supported_facts_[&from_dtg_node];
				
				for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = assignable_atoms->begin(); ci != assignable_atoms->end(); ci++)
				{
					std::vector<const BoundedAtom*>* possible_assignment = *ci;

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "Possible assignments: ";
					for (std::vector<const BoundedAtom*>::const_iterator ci = possible_assignment->begin(); ci != possible_assignment->end(); ci++)
					{
						const BoundedAtom* assignment = *ci;
						assignment->print(std::cout, dtg_graph_->getBindings());
						if (ci != possible_assignment->end() - 1)
						{
							std::cout << ", ";
						}
					}
					std::cout << "." << std::endl;
#endif
					
					// Map the action variable's domain to a set of objects which supports the transition. The variable domains of the
					// action variables will match the fact in the DTG nodes which allows us to find a set of facts which satisfy the
					// action's precondition and take the effects as newly established facts.
					std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > term_assignments;
					
					// Assign the predetermined assignments.
					for (std::vector<const BoundedAtom*>::iterator possible_assignment_ci = possible_assignment->begin(); possible_assignment_ci != possible_assignment->end(); possible_assignment_ci++)
					{
						const BoundedAtom* possible_atom_assignment = *possible_assignment_ci;
						const BoundedAtom* dtg_node_atom = from_dtg_node.getAtoms()[std::distance(possible_assignment->begin(), possible_assignment_ci)];
						
						for (std::vector<const Term*>::const_iterator ci = dtg_node_atom->getAtom().getTerms().begin(); ci != dtg_node_atom->getAtom().getTerms().end(); ci++)
						{
							const Term* dtg_node_atom_term = *ci;
							const Term* possible_atom_assignment_term = possible_atom_assignment->getAtom().getTerms()[std::distance(dtg_node_atom->getAtom().getTerms().begin(), ci)];
							
							const std::vector<const Object*>& dtg_node_atom_term_domain = dtg_node_atom_term->getDomain(dtg_node_atom->getId(), dtg_graph_->getBindings());
							const std::vector<const Object*>& possible_atom_assignment_term_domain = possible_atom_assignment_term->getDomain(possible_atom_assignment->getId(), dtg_graph_->getBindings());
							
							term_assignments[&dtg_node_atom_term_domain] = &possible_atom_assignment_term_domain;
						}
					}

					const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
					
					// Convert into bounded atoms for algorithm.
					std::vector<BoundedAtom*> bounded_preconditions;
					
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
					{
						const Atom* precondition = (*ci).first;
						bounded_preconditions.push_back(new BoundedAtom(transition->getStep()->getStepId(), *precondition));
					}
					
					std::vector<const BoundedAtom*> initial_supporting_facts;
					std::vector<std::vector<const BoundedAtom*>* >* supporting_tupples = new std::vector<std::vector<const BoundedAtom*>* >();
					getSupportingFacts(*supporting_tupples, term_assignments, bounded_preconditions, initial_supporting_facts, established_facts);
					
					// If tupple(s) of possible assignments have been found we assign these to the action variables and extract the facts which have been achieved.
					if (!supporting_tupples->empty())
					{
						achieved_transitions.insert(transition);
						std::vector<const DomainTransitionGraphNode*>* reachable_nodes = reachable_nodes_[&from_dtg_node];
						if (std::find(reachable_nodes->begin(), reachable_nodes->end(), &transition->getToNode()) == reachable_nodes->end())
						{
							assert (&transition->getToNode() != NULL);
							reachable_nodes_[&from_dtg_node]->push_back(&transition->getToNode());
						}
						
						assert (&transition->getToNode().getDTG() == dtg_graph_);
						
	//					std::cout << "Add the node: " << transition->getToNode() << std::endl;
						
						new_transition_achieved = true;

	//					std::cout << " ** Found supporting tupple(s)!" << std::endl;
						// For each tupple of supporting facts determine the domains of each of the action parameters and use these to determine the achieved facts.
						//for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = supporting_tupples->begin(); ci != supporting_tupples->end(); ci++)
						{
							// Bind each term of the action to the supporting atom's term domains.
							const std::vector<const Object*>* action_parameter_domains[transition->getStep()->getAction().getVariables().size()];
							for (unsigned int i = 0; i < transition->getStep()->getAction().getVariables().size(); i++)
							{
								action_parameter_domains[i] = NULL;
							}
							
							//const std::vector<const BoundedAtom*>* supporting_atoms = *ci;
							const std::vector<const BoundedAtom*>* supporting_atoms = *supporting_tupples->begin();
							
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "Supporting tupple:" << std::endl;
							for (std::vector<const BoundedAtom*>::const_iterator ci = supporting_atoms->begin(); ci != supporting_atoms->end(); ci++)
							{
								const BoundedAtom* supporting_atom = *ci;
								std::cout << "- ";
								supporting_atom->print(std::cout, dtg_graph_->getBindings());
								std::cout << "." << std::endl;
							}
#endif
							
							/**
							 * Map the facts of the supporting tupple to the variables of the action.
							 */
							for (std::vector<const BoundedAtom*>::const_iterator ci = supporting_atoms->begin(); ci != supporting_atoms->end(); ci++)
							{
								const BoundedAtom* supporting_bounded_atom = *ci;

								unsigned int precondition_index = std::distance(supporting_atoms->begin(), ci);
								const std::pair<const Atom*, InvariableIndex>& matching_precondition = preconditions[precondition_index];
								
								for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
								{
									const Variable* action_variable = *ci;
									const std::vector<const Object*>& action_variable_domain = action_variable->getDomain(transition->getStep()->getStepId(), dtg_graph_->getBindings());
									
									unsigned int action_variable_index = std::distance(transition->getStep()->getAction().getVariables().begin(), ci);
									
									// Map the supporting domains to the variables of the action.
									for (std::vector<const Term*>::const_iterator ci = matching_precondition.first->getTerms().begin(); ci != matching_precondition.first->getTerms().end(); ci++)
									{
										const Term* precondition_term = *ci;
										const std::vector<const Object*>& term_variable_domain = precondition_term->getDomain(transition->getStep()->getStepId(), dtg_graph_->getBindings());
										unsigned int term_index = std::distance(matching_precondition.first->getTerms().begin(), ci);

										if (&action_variable_domain == &term_variable_domain)
										{
											const std::vector<const Object*>& supporting_atom_variable_domain = supporting_bounded_atom->getAtom().getTerms()[term_index]->getDomain(supporting_bounded_atom->getId(), dtg_graph_->getBindings());
											
											// Debug, if we have already assigned a value to the action variable, make sure that the new one
											// is the same, otherwise something is wrong.
											if (action_parameter_domains[action_variable_index] != NULL)
											{
												bool domains_are_equal = true;
												if (action_parameter_domains[action_variable_index]->size() != supporting_atom_variable_domain.size())
													domains_are_equal = false;
												else
												{
													for (unsigned int i = 0; i < supporting_atom_variable_domain.size(); i++)
													{
														if ((*action_parameter_domains[action_variable_index])[i] != supporting_atom_variable_domain[i])
														{
															domains_are_equal = false;
															break;
														}
													}
												}
												
												if (!domains_are_equal)
												{
													std::cout << "Replace: { ";
													for (std::vector<const Object*>::const_iterator ci = action_parameter_domains[action_variable_index]->begin(); ci != action_parameter_domains[action_variable_index]->end(); ci++)
													{
														assert (*ci != NULL);
														(*ci)->print(std::cout, dtg_graph_->getBindings(), transition->getStep()->getStepId());
														if (ci + 1 != action_parameter_domains[action_variable_index]->end())
														{
															std::cout << ", ";
														}
													}
													std::cout << " with ";
													for (std::vector<const Object*>::const_iterator ci = supporting_atom_variable_domain.begin(); ci != supporting_atom_variable_domain.end(); ci++)
													{
														(*ci)->print(std::cout, dtg_graph_->getBindings(), supporting_bounded_atom->getId());
														if (ci + 1 != supporting_atom_variable_domain.end())
														{
															std::cout << ", ";
														}
													}
													std::cout << std::endl;
													assert (false);
												}
											}
											else
											{
												action_parameter_domains[action_variable_index] = &supporting_atom_variable_domain;
											}
										}
									}
								}
							}
							
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "Created the following action: (" << transition->getStep()->getAction().getPredicate();
							for (unsigned int i = 0; i < transition->getStep()->getAction().getVariables().size(); i++)
							{
								const std::vector<const Object*>* variable_domain = action_parameter_domains[i];
								std::cout << "{";
								for (std::vector<const Object*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ci++)
								{
									(*ci)->print(std::cout, dtg_graph_->getBindings(), 0);
									if (ci + 1 != variable_domain->end())
										std::cout << ", ";
								}
								std::cout << "} ";
								if (i != transition->getStep()->getAction().getVariables().size() - 1)
									std::cout << ", ";
							}
							std::cout << ")" << std::endl;
#endif
							
							/**
							 * Check the to node to find out which facts have been reached.
							 */
							const DomainTransitionGraphNode& to_node = transition->getToNode();
							std::vector<const BoundedAtom*>* to_node_achievers = new std::vector<const BoundedAtom*>();
							for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
							{
								BoundedAtom* to_node_bounded_atom = *ci;
								std::vector<const Term*>* new_atom_terms = new std::vector<const Term*>();
								std::vector<const std::vector<const Object*>* > new_atom_domains;

								// Bind the terms of the to node to the action variables to get the achieved facts.
								for (std::vector<const Term*>::const_iterator ci = to_node_bounded_atom->getAtom().getTerms().begin(); ci != to_node_bounded_atom->getAtom().getTerms().end(); ci++)
								{
									const Term* to_node_term = *ci;
									new_atom_terms->push_back(to_node_term);
									const std::vector<const Object*>& to_node_term_domain = to_node_term->getDomain(to_node_bounded_atom->getId(), dtg_graph_->getBindings());
										
									bool is_bounded = false;
									
									for (unsigned int i = 0; i < transition->getStep()->getAction().getVariables().size(); i++)
									{
										const std::vector<const Object*>& action_variable_domain = transition->getStep()->getAction().getVariables()[i]->getDomain(transition->getStep()->getStepId(), dtg_graph_->getBindings());
										if (&to_node_term_domain == &action_variable_domain)
										{
											const std::vector<const Object*>* matching_variable_domain = action_parameter_domains[i];

											// If no matching variable domain has been found, all values are possible.
											if (matching_variable_domain == NULL)
											{
												matching_variable_domain  = &to_node_term->getDomain(to_node_bounded_atom->getId(), dtg_graph_->getBindings());
											}
											
											assert (matching_variable_domain != NULL);
											new_atom_domains.push_back(matching_variable_domain);
											assert (matching_variable_domain->size() > 0);
											is_bounded = true;
											break;
										}
									}
									
									/**
									 * If a term in the to node is not bounded it must have been grounded, so we simply copy the
									 * original variable domain.
									 */
									if (!is_bounded)
									{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
										std::cout << "Could not find the assignment for the term: ";
										to_node_term->print(std::cout, dtg_graph_->getBindings(), to_node_bounded_atom->getId());
										std::cout << " in ";
										to_node_bounded_atom->print(std::cout, dtg_graph_->getBindings());
										std::cout << "." << std::endl;
#endif
										new_atom_domains.push_back(&to_node_term->getDomain(to_node_bounded_atom->getId(), dtg_graph_->getBindings()));
									}
								}
								
								Atom* achieved_fact = new Atom(to_node_bounded_atom->getAtom().getPredicate(), *new_atom_terms, to_node_bounded_atom->getAtom().isNegative());
								BoundedAtom& achieved_bounded_atom = BoundedAtom::createBoundedAtom(*achieved_fact, dtg_graph_->getBindings());
								
								assert (achieved_fact->getArity() == achieved_fact->getPredicate().getArity());
								assert (new_atom_domains.size() == achieved_fact->getPredicate().getArity());
								assert (new_atom_terms->size() == achieved_fact->getPredicate().getArity());
								assert (achieved_fact->getTerms().size() == achieved_fact->getPredicate().getArity());
								
								// Bound the achieved fact to the supporting domains.
								for (unsigned int i = 0; i < achieved_fact->getArity(); i++)
								{
									achieved_fact->getTerms()[i]->makeDomainEqualTo(achieved_bounded_atom.getId(), *new_atom_domains[i], dtg_graph_->getBindings());
									assert (achieved_fact->getTerms()[i]->getDomain(achieved_bounded_atom.getId(), dtg_graph_->getBindings()).size() > 0);
								}
								
								bool present = false;
								for (std::vector<const BoundedAtom*>::const_iterator ci = established_facts.begin(); ci != established_facts.end(); ci++)
								{
									const BoundedAtom* bounded_atom = *ci;
									if (dtg_graph_->getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), achieved_bounded_atom.getAtom(), achieved_bounded_atom.getId()))
									{
										bool terms_match = true;
										for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
										{
											const Term* established_fact_term = *ci;
											const Term* newly_achieved_fact_term = achieved_fact->getTerms()[std::distance(bounded_atom->getAtom().getTerms().begin(), ci)];
											
											if (!established_fact_term->isEquivalentTo(bounded_atom->getId(), *newly_achieved_fact_term, achieved_bounded_atom.getId(), dtg_graph_->getBindings()))
											{
												terms_match = false;
												break;
											}
										}
										
										if (!terms_match)
											continue;
										
										present = true;
										
	//									std::cout << "ALREADY ACHIEVED -=(";
	//									achieved_bounded_atom.print(std::cout, dtg_graph_->getBindings());
	//									std::cout << ")=-" << std::endl;
										break;
									}
								}

								if (!present)
								{
									established_facts.push_back(&achieved_bounded_atom);
	//								std::cout << "-=(";
	//								achieved_bounded_atom.print(std::cout, dtg_graph_->getBindings());
	//								std::cout << ")=-" << std::endl;
								}
								to_node_achievers->push_back(&achieved_bounded_atom);
							}
							
							if (to_node.getAtoms().size() != to_node_achievers->size())
							{
								continue;
	/*							std::cout << "Found the following achievers for: " << to_node << ":" << std::endl;
								
								for (std::vector<const BoundedAtom*>::const_iterator ci = to_node_achievers->begin(); ci != to_node_achievers->end(); ci++)
								{
									std::cout << " * ";
									(*ci)->print(std::cout, dtg_graph_->getBindings());
									std::cout << "." << std::endl;
								}
								assert (false);*/
							}
							makeReachable(to_node, *to_node_achievers);
	//						std::cout << "." << std::endl;
						}
					}
				}
				
				
				
				/// If so mark the transition as "achieved".
				
				/// Add to the from node of that transition the to node - as it is achievable from there.
				
				/// Mark the node of the end point of the transition - but only if it contains unachieved transitions.
			}
		}
		
		// Propagate the achievable nodes per DTG node.
	}

	// List for each DTG node which other nodes are reachable.
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "List reachable facts per DTGs: " << std::endl;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		std::cout << "Reachable nodes from: " << std::endl;
		dtg_node->print(std::cout);
		std::cout << std::endl << ":" << std::endl;
		
		std::vector<const DomainTransitionGraphNode*>* reachable_dtg_node = reachable_nodes_[dtg_node];
		for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = reachable_dtg_node->begin(); ci != reachable_dtg_node->end(); ci++)
		{
			std::cout << "* ";
			(*ci)->print(std::cout);
			std::cout << "." << std::endl;
		}
	}

	// List all nodes which are reachable.
	std::cout << "List of all achievable facts: " << std::endl;
	for (std::vector<const BoundedAtom*>::const_iterator ci  = established_facts.begin(); ci != established_facts.end(); ci++)
	{
		std::cout << "- ";
		(*ci)->print(std::cout, dtg_graph_->getBindings());
		std::cout << std::endl;
	}
#endif
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

};
	
};
