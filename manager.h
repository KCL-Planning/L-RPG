#ifndef MYPOP_MANAGER_H
#define MYPOP_MANAGER_H

#include <vector>

///#define MYPOP_MANAGER_COMMENTS

namespace MyPOP {

typedef unsigned int IndexID;
const unsigned int INVALID_INDEX_ID = -1;

/**
 * Internally every managable object is stored in an array defined in the
 * manager. The index is equal to the id assigned to the object.
 */
//template <class U>
class ManageableObject {

public:
	// Constructor. The ID is assigned to the object once it is added to the manager.
	ManageableObject()
		: id_(INVALID_INDEX_ID) {}

	// Get the unique ID of this object.
	IndexID getId() const { return id_; }

	// Set the unique ID of this object.
	void setId(IndexID id) { id_ = id; }

protected:
	// The unique ID of this object.
	IndexID id_;
};


/**
 * Template for classes which manage a single set of objects. Each object
 * has a unique ID which is assigned to them upon adding it to this manager.
 * All the objects are stored in a vector and their index is equal to their ID.
 *
 * T is the subclass of manager.
 * U is the object to be indexed.
 */
template <class U>
class Manager {
public:

	// Destroy all the stored objects.
	virtual ~Manager()
	{
#ifdef MYPOP_MANAGER_COMMENTS
		std::cout << "[Destructor] Manager" << std::endl;
#endif

		for (unsigned int i = 0; i < objects_.size(); i++)
			delete objects_[i];
	}

	// Return the type with the given ID.
	const U& getManagableObject(IndexID id) const
	{
		return *objects_[id];
	}
	
	// Get all the objects.
	const std::vector<U*>& getManagableObjects() const
	{
		return objects_;
	}

	// Add a new object to the manager, the ID will be equal to highest_id_ and
	// the highest_id_ will be incremented by 1.
	void addManagableObject(U* obj)
	{
		obj->setId(objects_.size());
		objects_.push_back(obj);
		++highest_id_;
	}

protected:

	// The constructor.
	Manager()
		: highest_id_(0) {}

	// All objects are stored into this array. The ID of every type corresponds to the
	// index of the array where that object is stored.
	std::vector<U*> objects_;

	// The number of items added to this manager.
	IndexID highest_id_;
};

};

#endif
