#ifndef MYPOP_UTILITY_MEMORY_POOL_H
#define MYPOP_UTILITY_MEMORY_POOL_H

#include <cstring>

namespace MyPOP {

namespace UTILITY {

struct MemoryElement
{
	MemoryElement* next_free_memory_slot_;
};

class MemoryChunk
{
public:
	MemoryChunk(size_t unit_size, MemoryChunk* previous_chunk, unsigned int nr_units = 100000);
	~MemoryChunk();

	MemoryElement* begin() const { return (struct MemoryElement*)allocated_memory_; }
	
private:
	
	void* allocated_memory_;
	
	size_t unit_size_;
	MemoryChunk* previous_chunk_;
	unsigned int nr_units_;
};

/**
 * This is a memory pool which is used to make the usage of reachable facts more efficient in both time and memory.
 */
class MemoryPool
{
public:
	/**
	 * Create a memory pool for the given set of arities.
	 */
	MemoryPool(size_t unit_size);
	
	~MemoryPool();
	
	void* allocate(size_t size);
	
	void free(void* p);
	
private:
	
	size_t unit_size_;
	
	void createNewMemoryChunk();
	
	MemoryElement* current_free_slot_;
	
	MemoryChunk* latest_created_chunk_;
};

};

};

#endif // MYPOP_UTILITY_MEMORY_POOL_H
