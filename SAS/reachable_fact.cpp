#include "reachable_fact.h"
#include "dtg_manager.h"
#include "equivalent_object_group.h"
#include "../term_manager.h"
#include "../predicate_manager.h"
#include <stdlib.h>

namespace MyPOP {

namespace SAS_Plus {

ReachableFact::ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
	: atom_(&bounded_atom.getAtom()), replaced_by_(NULL)
{
	term_domain_mapping_ = new EquivalentObjectGroup*[bounded_atom.getAtom().getArity()];
	
	for (std::vector<const Term*>::const_iterator ci = bounded_atom.getAtom().getTerms().begin(); ci != bounded_atom.getAtom().getTerms().end(); ci++)
	{
		const Term* term = *ci;
		const std::vector<const Object*>& domain = term->getDomain(bounded_atom.getId(), bindings);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (domain.size() == 1);
#endif
		
		EquivalentObjectGroup& corresponding_eog = eog_manager.getEquivalentObject(*domain[0]).getEquivalentObjectGroup();
		term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] = &corresponding_eog;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] != NULL);
#endif
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
#endif
}

ReachableFact::ReachableFact(const Atom& atom, EquivalentObjectGroup** term_domain_mapping)
	: atom_(&atom), term_domain_mapping_(term_domain_mapping), replaced_by_(NULL)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < atom.getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
#endif
}

ReachableFact::~ReachableFact()
{
	delete[] term_domain_mapping_;
}

void* ReachableFact::operator new (size_t size)
{
	return g_reachable_fact_memory_pool->allocate(size);
}
	
void ReachableFact::operator delete (void* p)
{
	g_reachable_fact_memory_pool->free(p);
}

bool ReachableFact::updateTermsToRoot()
{
	bool updated_domain = false;
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		EquivalentObjectGroup& root_node = term_domain_mapping_[i]->getRootNode();
		if (&root_node != term_domain_mapping_[i])
		{
			term_domain_mapping_[i] = &root_node;
			updated_domain = true;
		}
	}
	
	// assert(updated_domain);
	
	return updated_domain;
}

bool ReachableFact::isEquivalentTo(const ReachableFact& other) const
{
//	std::cout << "Are " << *this << " and " << other << " equivalent?" << std::endl;
	
	if (atom_->getArity() != other.atom_->getArity())
	{
//		std::cout << "Arities don't match up!" << std::endl;
		return false;
	}
	
//	char combined_mask = mask_ & other.mask_;
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
//		if (((0x1 << i) & combined_mask) != 0)
		if (!term_domain_mapping_[i]->isGrounded())
		{
			// Make sure the types match up.
			if (!term_domain_mapping_[i]->hasSameFingerPrint(*other.term_domain_mapping_[i]))
			{
//				std::cout << "The " << i << "th term does not have the same fingerprint!" << std::endl;
				return false;
			}
		}

		else if (!term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
		{
//			std::cout << "The " << i << "th term is at odds!" << std::endl;
			return false;
		}
	}
	return true;
}

bool ReachableFact::isIdenticalTo(const ReachableFact& other) const
{
	if (atom_->getArity() != other.atom_->getArity())
	{
		return false;
	}
	
	if (atom_->getPredicate().getName() != other.atom_->getPredicate().getName())
	{
		return false;
	}
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (term_domain_mapping_[i] != NULL);
		assert (other.term_domain_mapping_[i] != NULL);
#endif
//		if (&term_domain_mapping_[i]->getRootNode() != &other.term_domain_mapping_[i]->getRootNode())
		if (term_domain_mapping_[i] != other.term_domain_mapping_[i])
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			if (term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
			{
				std::cerr << "Could not check if " << *this << " is equivalent to " << other << std::endl;
				std::cerr << "WRONG!" << std::endl;
				assert (false);
			}
#endif
			return false;
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		if (!term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
		{
			std::cerr << "WRONG!" << std::endl;
			exit(1);
		}
#endif
	}
	return true;
}

EquivalentObjectGroup& ReachableFact::getTermDomain(unsigned int index) const
{
	assert (index < atom_->getArity());
	EquivalentObjectGroup* eog = term_domain_mapping_[index];
	assert (eog != NULL);
	return *eog;
}

void ReachableFact::replaceBy(ReachableFact& replacement)
{
//	assert (replaced_by_ == NULL);
	replaced_by_ = &replacement;
	
	assert (replaced_by_->replaced_by_ != this);
}

//bool isMarkedForRemoval() const { return removed_flag_; }
//inline bool ReachableFact::isMarkedForRemoval() const { return replaced_by_ != NULL; }

const ReachableFact& ReachableFact::getReplacement() const
{
	if (replaced_by_ == NULL) return *this;
	
	assert (replaced_by_->replaced_by_ != this);
	
	return replaced_by_->getReplacement();
}

std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact)
{
	os << "Reachable fact: (" << reachable_fact.atom_->getPredicate().getName() << " ";
	for (unsigned int i = 0; i < reachable_fact.atom_->getArity(); i++)
	{
		const std::vector<EquivalentObject*>& objects = reachable_fact.term_domain_mapping_[i]->getEquivalentObjects();
		os << "{";
		for (std::vector<EquivalentObject*>::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
		{
			os << (*ci)->getObject();
			if (ci + 1 != objects.end())
			{
				os << ", ";
			}
		}
		os << "}";
		if (i + 1 != reachable_fact.atom_->getArity())
		{
			os << ", ";
		}
	}
//	os << ")" << "%" << &reachable_fact << "%" << reachable_fact.getAtom().getPredicate();
//	os << "[r=" << &reachable_fact.getReplacement() << "]";
	return os;
}

MemoryChunk::MemoryChunk(size_t unit_size, MyPOP::SAS_Plus::MemoryChunk* previous_chunk, unsigned int nr_units)
	: unit_size_(unit_size), previous_chunk_(previous_chunk), nr_units_(nr_units)
{
	// Allocate all the memory we need.
	allocated_memory_ = malloc(nr_units_ * (unit_size + sizeof(struct MemoryElement)));
	assert (allocated_memory_ != NULL);
	
	// Structure the memory, such that each memory element points to the next available memory location.
	struct MemoryElement* next_unit = NULL;
	for (unsigned int i = 0; i < nr_units; i++)
	{
		unsigned int index = nr_units - 1 - i;
		MemoryElement* cur_unit = (struct MemoryElement*)((char*)allocated_memory_ + index * (unit_size + sizeof(struct MemoryElement)));
		cur_unit->next_free_memory_slot_ = next_unit;
		next_unit = cur_unit;
	}
}

MemoryChunk::~MemoryChunk()
{
	free(allocated_memory_);
	delete previous_chunk_;
}

MemoryPool::MemoryPool(size_t unit_size)
	: unit_size_(unit_size)
{
//	std::cerr << "Initialise the memory pool with the size of: " << unit_size << std::endl;
	latest_created_chunk_ = NULL;
	createNewMemoryChunk();
}

MemoryPool::~MemoryPool()
{
	delete latest_created_chunk_;
}

void* MemoryPool::allocate(size_t size)
{
	MemoryElement* next_free_slot = current_free_slot_->next_free_memory_slot_;
	MemoryElement* to_return = current_free_slot_;
	current_free_slot_ = next_free_slot;
	
	// Check if we need to allocate more memory!
	if (current_free_slot_ == NULL) createNewMemoryChunk();
	
	return to_return;
}

void MemoryPool::free(void* p)
{
	MemoryElement* to_free = static_cast<struct MemoryElement*>(p);
	to_free->next_free_memory_slot_ = current_free_slot_;
	current_free_slot_ = to_free;
}

void MemoryPool::createNewMemoryChunk()
{
	latest_created_chunk_ = new MemoryChunk(unit_size_, latest_created_chunk_);
	current_free_slot_ = latest_created_chunk_->begin();
}

};

};