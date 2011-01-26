#ifndef MYPOPPREDICATE_MANAGER_H
#define MYPOPPREDICATE_MANAGER_H

#include <iostream>
#include <vector>
#include <map>
#include "VALfiles/ptree.h"
#include "VALfiles/TIM.h"
#include "manager.h"

/**
 * We assume predicates are unique in a domain. If the name of a predicate is equal than Atoms will
 * share the same predicate object. During analysis properties of predicates (e.g. if they are static)
 * will be assigned to an object of this class.
 */
namespace MyPOP {

class Type;
class TypeManager;
class ActionManager;

class Predicate : public ManageableObject
{
public:
	Predicate(const std::string& name, const std::vector<const Type*>& types, bool is_static);

	~Predicate();

	/**
	 * Get the name of the predicate.
	 */
	const std::string& getName() const { return name_; }

	/**
	 * Get the types of the predicate.
	 */
	const std::vector<const Type*>& getTypes() const { return *types_; }

	/**
	 * Get the arity of this predicate.
	 */
	unsigned int getArity() const { return types_->size(); }

	/**
	 * Check if this predicate is static.
	 */
	bool isStatic() const { return is_static_; }

	/**
	 * Make or unmake this predicate static.
	 */
	void makeStatic(bool make_static);
	
	/**
	 * Check if this predicate can substitute for the given predicate.
	 * Requirements for meeting this:
	 * - The names must be the same.
	 * - The arity must be the same.
	 * - For each type: the type of this predicate must be equal or more general than each type of the given predicate.
	 * This ensures that all possible assignments of the values of the given predicate can also be made to this predicate.
	 * 
	 * For example the predicate (at ?object ?location) can substitute for (at ?truck ?location) if truck is a subset of object.
	 */
	bool canSubstitute(const Predicate& predicate) const;

	/**
	 * Check if two predicates are exactly the same.
	 * Requirements for meeting this:
	 * - The names must be the same.
	 * - The arity must be the same.
	 * - The types must be exactly the same.
	 */
	bool operator==(const Predicate& predicate) const;
	
	/**
	 * Check if two predicates are different.
	 * Requirements for meeting this are to violate any of the following:
	 * - The names must be the same.
	 * - The arity must be the same.
	 * - The types must be exactly the same.
	 */
	bool operator!=(const Predicate& predicate) const;

	friend std::ostream& operator<<(std::ostream&, const Predicate& predicate);
private:
	// The name of the predicate.
	const std::string name_;

	// The terms of this predicate.
	const std::vector<const Type*>* types_;

	// Is this predicate static?
	bool is_static_;
};

std::ostream& operator<<(std::ostream&, const Predicate& predicate);

class PredicateManager : public Manager<Predicate>
{
public:
    //PredicateManager(const TermManager& term_manager);
	PredicateManager(const TypeManager& type_manager);

	~PredicateManager();

	// Process all predicate names.
	void processPredicates(const VAL::pred_decl_list& predicates);

	// Post process all the predicates after we know all the operators of the domain. Determine which
	// predicates are static.
	void checkStaticPredicates(const ActionManager& action_manager);

	// Get the predicate of the given name and types.
	const Predicate* getPredicate(const std::string& name, const std::vector<const Type*>& types) const;

	// Get the predicate from the domain with its most general types.
	// TODO: remove
	const Predicate* getGeneralPredicate(const std::string& name) const;

private:
	// The term manager.
	const TypeManager* type_manager_;

	// We store all found predicates in a table, indexed by the predicate's name and types.
	std::map<std::pair<std::string, std::vector<const Type*> >, Predicate*> predicate_map_;

	// Store the most general predicate per name.
	// TODO: remove
	std::map<std::string, std::vector<const Type*>* > general_predicates_;

};

}

#endif
