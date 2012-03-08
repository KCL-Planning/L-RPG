#include "reachable_fact.h"
#include "dtg_manager.h"
#include "equivalent_object_group.h"
#include "../term_manager.h"
#include "../predicate_manager.h"

namespace MyPOP {

namespace SAS_Plus {

unsigned int ReachableFactMemoryPool::MEMORY_CHUNK_SIZE_ = 1000;
	
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

ReachableFactMemoryChunk::ReachableFactMemoryChunk(unsigned int chunk_size, ReachableFactMemoryChunk* previous_chunk)
	: chunk_size_(chunk_size), previous_chunk_(previous_chunk)
{
	allocated_memory_ = new MemoryElement*[chunk_size];
	//for (unsigned int i = chunk_size - 1; i >= 0; i--)
	for (unsigned int i = 0; i < chunk_size; i++)
	{
		unsigned int index = chunk_size - 1 - i;
		if (index == chunk_size - 1) 
		{
			allocated_memory_[index] = new MemoryElement(NULL, NULL);
		}
		else
		{
			allocated_memory_[index] = new MemoryElement(allocated_memory_[index + 1], NULL);
		}
	}
}

ReachableFactMemoryChunk::~ReachableFactMemoryChunk()
{
	for (unsigned int i = 0; i < chunk_size_; i++)
	{
		delete allocated_memory_[i];
	}
	delete[] allocated_memory_;
	
	delete previous_chunk_;
}

ReachableFactMemoryPool::ReachableFactMemoryPool(unsigned int max_arity)
	: max_arity_(max_arity)
{
	std::cerr << "Initialise the memory pool with a max arity of: " << max_arity << std::endl;
	current_free_slots_ = new MemoryElement*[max_arity + 1];
	latest_created_chunks_ = new ReachableFactMemoryChunk*[max_arity + 1];
	
	for (unsigned int i = 0; i <= max_arity; i++)
	{
		latest_created_chunks_[i] = NULL;
		createNewMemoryChunk(i);
	}
}

ReachableFactMemoryPool::~ReachableFactMemoryPool()
{
	delete[] current_free_slots_;
	for (unsigned int i = 0; i <= max_arity_; i++)
	{
		delete latest_created_chunks_[i];
	}
	delete[] latest_created_chunks_;
}
	
ReachableFact& ReachableFactMemoryPool::createReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
{
	if (current_free_slots_[bounded_atom.getAtom().getArity()] == NULL) createNewMemoryChunk(bounded_atom.getAtom().getArity());
	MemoryElement* next_free_slot = current_free_slots_[bounded_atom.getAtom().getArity()]->next_free_memory_slot_;
	
	ReachableFact* rf = new ReachableFact(bounded_atom, bindings, eog_manager);
	
	current_free_slots_[bounded_atom.getAtom().getArity()]->element_ = rf;
	current_free_slots_[bounded_atom.getAtom().getArity()] = next_free_slot;
	
	return *rf;
}
		
ReachableFact& ReachableFactMemoryPool::createReachableFact(const Atom& atom, EquivalentObjectGroup** term_domain_mapping)
{
	if (current_free_slots_[atom.getArity()] == NULL) createNewMemoryChunk(atom.getArity());
	MemoryElement* next_free_slot = current_free_slots_[atom.getArity()]->next_free_memory_slot_;
	
	// If the current free slot contains a copy of a reachable fact, exploit it!
	ReachableFact* rf;
	if (current_free_slots_[atom.getArity()]->element_ != NULL)
	{
		current_free_slots_[atom.getArity()]->element_->atom_ = &atom;
		current_free_slots_[atom.getArity()]->element_->term_domain_mapping_ = term_domain_mapping;
		current_free_slots_[atom.getArity()]->element_->replaced_by_ = NULL;
		
		rf = current_free_slots_[atom.getArity()]->element_;
	}
	else
	{
		rf = new ReachableFact(atom, term_domain_mapping);
		current_free_slots_[atom.getArity()]->element_ = rf;
	}
	current_free_slots_[atom.getArity()] = next_free_slot;
	return *rf;
}

void ReachableFactMemoryPool::deleteReachableFact(ReachableFact& reachable_fact)
{
	// The memory it occupies is restructured as a MemoryElement.
	MemoryElement* to_free = reinterpret_cast<MemoryElement*>(&reachable_fact - sizeof(MemoryElement*));
	to_free->next_free_memory_slot_ = current_free_slots_[reachable_fact.getAtom().getArity()];
	current_free_slots_[reachable_fact.getAtom().getArity()] = to_free;
}

void ReachableFactMemoryPool::createNewMemoryChunk(unsigned int arity)
{
	assert (arity <= max_arity_);
	latest_created_chunks_[arity] = new ReachableFactMemoryChunk(MEMORY_CHUNK_SIZE_, latest_created_chunks_[arity]);
	current_free_slots_[arity] = latest_created_chunks_[arity]->begin();
}

};

};