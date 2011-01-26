#ifndef MYPOP_TYPE_MANAGER
#define MYPOP_TYPE_MANAGER

#include <vector>
#include <boost/dynamic_bitset.hpp>
#include "VALfiles/ptree.h"
#include "manager.h"

namespace MyPOP {

class Object;
class TermManager;

/**
 * PDDL Type.
 * Internally every type is assigned a bit in a bit array equal in length to the number
 * of the total number of types. Checks for super- / subtypes are done by bitcomparison,
 * check the relevant methods for a detailed explanation.
 */
class Type : public ManageableObject {//<Type> {

public:
	// Construct a type with the given name and supertype.
	Type(const string& name, const Type* type);

	// Destructor.
	~Type();

	// Determine the supertypes of this type and store them in a bitset
	// of length total_types.
	void processSupertypes(int total_types);

	// Check if the given type is equal to this type.
	bool isEqual(const Type& type) const;

	// Check if this type is competible with the given type, i.e. can we use
	// this type for a substitute of the given type.
	bool isCompatible(const Type& type) const;

	// Check if this type is a subtype of the given type.
	bool isSubtypeOf(const Type& type) const;

	// Check if this type is a supertype of the given type.
	bool isSupertypeOf(const Type& type) const;

	// Get the name of this type.
	const std::string& getName() const { return name_; }

	// Get the supertype of this type.
	const Type* getSupertype() const { return supertype_; }
	
	// Get all the subtypes of this type.
	const std::vector<const Type*> getSubtypes() const { return subtypes_; }
	
	// Add a term as a direct subtype of this type.
	void addSubtype(const Type& subtype);

private:
	// The name of this type as defined in the domain file.
	const string name_;

	// The supertype of this type.
	const Type* supertype_;

	// All the subtypes of this type.
	std::vector<const Type*> subtypes_;

	// A bitset which determines which types this type is a subtype of
	// (including itself). The bitset is aligned with the type ids. I.e.
	// if bit N is true then this type is a subtype of type with type ID N.
	boost::dynamic_bitset<>* is_subtype_of_;

	// Print the type in a human readable form.
	friend std::ostream& operator<<(std::ostream& os, const Type& type);
};

std::ostream& operator<<(std::ostream& os, const Type& type);

/**
 * All types in the current domain are stored by this manager.
 */
class TypeManager : public Manager<Type> {

public:
	// Constructor.
	TypeManager();
	virtual ~TypeManager();

	// After parsing the domain and problem files we pass all the types to the TypeManager
	// to store them into our own structure.
	void processTypes(const VAL::pddl_type_list& types);

	// Process all the objects from the problem file by storing them internally.
	void processObjects(TermManager& term_manager, const VAL::const_symbol_list& objects);

	// Return all objects of a certain type.
	void getObjectsOfType(std::vector<const Object*>& objects_of_type, const Type& type) const;

	// Get the type object with the given name.
	const Type* getType(const std::string& type_name) const;

protected:

	// Process a single type, before create a type we want to have processed all its
	// supertypes. This function is called recursively until it finds a type without
	// any supertypes and then builds the tree up from there. In addition to the super-
	// types also the direct subtypes are processed and stored with every type.
	Type* processType(const VAL::pddl_type& type);

	// Map the given object to the given type and all supertypes. This allows the planner to get quick
	// access of all objects related to a certain type.
	void mapObjectToType(const Object& object, const Type& type);

private:
	// During construction of the types keep track of the indexing from the
	// pddl type to TypeID. This allows us to instantiate all the types in a
	// single iteration.
	//std::map<const VAL::pddl_type*, const Type*>* types_indexing_;

	std::map<std::string, Type*> types_mapping_;

	// Keep track of all the objects which are mapped to a similar type for
	// easy access.
	std::map<const Type*, std::vector<const Object*>*> objects_per_type_;
};

};

#endif
