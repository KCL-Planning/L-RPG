#include "memory_pool.h"
#include <stdlib.h>
#include <assert.h>

namespace MyPOP {

namespace UTILITY {

MemoryChunk::MemoryChunk(size_t unit_size, MemoryChunk* previous_chunk, unsigned int nr_units)
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