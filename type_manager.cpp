
#include <map>
#include <assert.h>

#include "VALfiles/ptree.h"

#include "type_manager.h"
#include "logging.h"
#include "term_manager.h"


namespace MyPOP {

/*************************
 * The Type class
 *************************/
Type::Type(const string& name, const Type* supertype)
	: name_(name), supertype_(supertype), is_subtype_of_(NULL)
{

}

Type::~Type()
{
	delete is_subtype_of_;
}

void Type::processSupertypes(int total_types)
{
	// Create a bitset with a number of bits equal to the number of types.
	is_subtype_of_ = new boost::dynamic_bitset<>(total_types);

	// For every type ID this type is a subtype of, make the bit of the location equal to the
	// type ID true.
	const Type* parent = supertype_;
	while(parent != NULL) {
		is_subtype_of_->set(parent->id_, true);
		parent = parent->supertype_;
	}

	// Don't forget to add ourselves! :)
	is_subtype_of_->set(id_, true);
}

bool Type::isCompatible(const Type& type) const
{
	return isSubtypeOf(type) || isEqual(type);
}

bool Type::isEqual(const Type& type) const
{
	return (*is_subtype_of_ == *type.is_subtype_of_);
}

bool Type::isSubtypeOf(const Type& type) const
{
	// This type is a subtype if it shares all the subtypes of the given type.
	return (*is_subtype_of_ & *type.is_subtype_of_) == *type.is_subtype_of_ &&
	       !isEqual(type);
}

bool Type::isSupertypeOf(const Type& type) const
{
	// This type is a supertype if the given type shares all the subtype of this type.
	return (*is_subtype_of_ & *type.is_subtype_of_) == *is_subtype_of_ &&
	       !isEqual(type);
}

void Type::addSubtype(const Type& subtype)
{
	for (std::vector<const Type*>::const_iterator ci = subtypes_.begin(); ci != subtypes_.end(); ci++)
	{
		assert (*ci != &subtype);
	}	
	
	subtypes_.push_back(&subtype);
}

std::ostream& operator<<(std::ostream& os, const Type& type) {
	os << "[TYPE] " << type.name_ << "[" << type.id_ << "]";
	const Type* parent = type.supertype_;

	while (parent != NULL) {
		os << " -> " << parent->name_ << "[" << parent->id_ << "]";
		parent = parent->supertype_;
	}
	
	os << " direct subtypes: ";
	
	for (std::vector<const Type*>::const_iterator ci = type.subtypes_.begin(); ci != type.subtypes_.end(); ci++)
	{
		os << (*ci)->name_ << ", ";
	}	
	
	os << " {" << *type.is_subtype_of_ << "}";
	return os;
}


/*************************
 * The TypeManager class
 *************************/

TypeManager::TypeManager() 
{
	// During processing map the pddl types to our internal types for 
	// easy access during the parsing phase. This indexing is removed
	// once we don't need it anymore, i.e. after the parsing phase.
	//types_indexing_ = new std::map<const VAL::pddl_type*, const Type*>();
}

TypeManager::~TypeManager()
{
	//delete types_indexing_;
	//for (std::map<std::string, const Type*>::const_iterator ci = types_mapping_.begin(); ci != types_mapping_.end(); ci++)
	//{
	//	delete (*ci).second;
	//}
	for (std::map<const Type*, std::vector<const Object*>*>::const_iterator ci = objects_per_type_.begin(); ci != objects_per_type_.end(); ci++)
	{
		delete (*ci).second;
	}
}

void TypeManager::processTypes(const VAL::pddl_type_list& types)
{
	// Rank the types according to their type.
	for (VAL::pddl_type_list::const_iterator ci = types.begin(); ci != types.end(); ci++)
	{
		const VAL::pddl_type* type = *ci;
		processType(*type);
	}

	// For each type, determine its supertypes and store them for future use.
	for (unsigned int i = 0; i < highest_id_; i++)
	{
		// For every type set the same bitset length to store the supertype information.
		// This could be done in the constructor if we knew the number of types from the
		// start (see above), but this will do for now.
		objects_[i]->processSupertypes(highest_id_);
	}

	// Show the results.
	if (Logging::verbosity <= Logging::DEBUG)
	{
		for (unsigned int i = 0; i < highest_id_; i++)
		{
			std::cout << *objects_[i] << std::endl;
	
			for (unsigned int j = 0; j < highest_id_; j++) {
				if (objects_[i]->isSubtypeOf(*objects_[j]))
					std::cout << "SUBTYPE OF: " << *objects_[j] << std::endl;
				if (objects_[i]->isSupertypeOf(*objects_[j]))
					std::cout << "SUPERTYPE OF: " << *objects_[j] << std::endl;
				if (objects_[i]->isCompatible(*objects_[j]))
					std::cout << "COMPATIBLE WITH: " << *objects_[j] << std::endl;
			}
		}
	}
}

Type* TypeManager::processType(const VAL::pddl_type& type)
{
	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << type.getName() << "..." << std::endl;
	}
	const VAL::pddl_type* parent = type.type;
	Type* parent_type = NULL;

	// If the type has a supertype, process this one first.
	if (parent != NULL)
	{
		if (Logging::verbosity <= Logging::DEBUG)
		{
			std::cout << type.getName() << " has " << parent->getName() << " as a parent!" << std::endl;
		}

		// Check if the parent has already been constructed.
		std::map<std::string, Type*>::const_iterator parent_ci = types_mapping_.find(parent->getName());
		if (parent_ci == types_mapping_.end())
		{
			// If not, recursively search for a supertype who has either no supertype
			// or has a supertype which has already been processed.
			parent_type = processType(*parent);
		}
		else
		{
			// If it already has been defined, uncover it.
			parent_type = (*parent_ci).second;
		}

		assert (parent_type != NULL);
	}
	else if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << type.getName() << " has no parents." << std::endl;
	}


	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "Process " << type.getName() << std::endl;
	}

	// Create a new type with the given name if it hasn't already been created.
	std::map<std::string, Type*>::const_iterator type_ci = types_mapping_.find(type.getName());
	Type* new_type = NULL;

	if (type_ci == types_mapping_.end())
	{
		// If not, define it now and add it to the end of the types array.
		Type* type_to_add = new Type(type.getName(), parent_type);
		addManagableObject(type_to_add);
		new_type = type_to_add;
		//(*types_indexing_)[&type] = new_type;
		types_mapping_[type.getName()] = new_type;
		
		// If the type is new add it to the parent type as subtype.
		if (parent_type != NULL)
		{
			parent_type->addSubtype(*new_type);
		}
	}
	else
	{
		// Otherwise, uncover it.
		new_type = (*type_ci).second;
	}

	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "Done! Return type: " << type.getName() << std::endl;
	}
	return new_type;
}

void TypeManager::processObjects(TermManager& term_manager, const VAL::const_symbol_list& objects)
{
	for (VAL::const_symbol_list::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
	{
		const VAL::const_symbol* pddl_object = *ci;
		const Type* object_type = getType(pddl_object->type->getName());
		Object* object = new Object(object_type, pddl_object->getName());

		// Process the objects type and store it.
		while (object_type != NULL)
		{
			mapObjectToType(*object, *object_type);
			object_type = object_type->getSupertype();
		}

		// Add the object as a term.
		term_manager.addTerm(*pddl_object, *object);

		if (Logging::verbosity <= Logging::DEBUG)
		{
			std::cout << *object << std::endl;
		}
	}
}

void TypeManager::getObjectsOfType(std::vector<const Object*>& objects_of_type, const Type& type) const
{
	std::map<const Type*, std::vector<const Object*>*>::const_iterator ci = objects_per_type_.find(&type);
	if (ci != objects_per_type_.end())
	{
		std::vector<const Object*>* oot = (*ci).second;
		objects_of_type.insert(objects_of_type.begin(), (*oot).begin(), (*oot).end());
	}
}

void TypeManager::mapObjectToType(const Object& object, const Type& type)
{
	std::map<const Type*, std::vector<const Object*>*>::const_iterator ci = objects_per_type_.find(&type);
	std::vector<const Object*>* objects = NULL;
	if (ci == objects_per_type_.end())
	{
		objects = new std::vector<const Object*>();
		objects_per_type_[&type] = objects;
	}
	else
	{
		objects = (*ci).second;
	}

	// Map the object to the other objects of the same type, if it isn't already there.
	bool already_stored = false;
	for (std::vector<const Object*>::const_iterator ci = objects->begin(); ci != objects->end(); ci++)
	{
		if (&object == *ci)
		{
			already_stored = true;
			break;
		}
	}
	if (!already_stored)
	{
		objects->push_back(&object);
	}
}

const Type* TypeManager::getType(const std::string& type_name) const
{
	std::map<std::string, Type*>::const_iterator type = types_mapping_.find(type_name);
	if (type == types_mapping_.end())
	{
		std::cout << "Could not find the type with name " << type_name << std::endl;
		std::cout << "Known types:" << std::endl;
		for (std::map<std::string, Type*>::const_iterator ci = types_mapping_.begin(); ci != types_mapping_.end(); ci++)
		{
			std::cout << "- " << *(*ci).second << std::endl;
		}
		assert (false);
	}

	return (*type).second;
}

};
