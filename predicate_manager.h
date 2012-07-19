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

class Predicate
{
public:
	/**
	 * Extract the predicate information from the TIM analysis and construct all the predicate objects 
	 * we use in this planner.
	 */
	static void processPredicates(const VAL::pred_decl_list& predicates, const TypeManager& type_manager);
	
	/**
	 * Find a predicate which corresponds to the predicate used by TIM.
	 */
	static const Predicate& getPredicate(const TIM::Property& property, const TypeManager& type_manager);

	/**
	 * Post process all the predicates after we know all the operators of the domain. Determine which
	 * predicates are static.
	 */
	static void checkStaticPredicates(const ActionManager& action_manager);

	/**
	 * Get the predicate of the given name and types.
	 */
	static const Predicate& getPredicate(const std::string& name, const std::vector<const Type*>& types);
	
	/**
	 * Get all the predicates.
	 */
	static const std::vector<const Predicate*>& getPredicates() { return all_predicates_; }
	
	virtual ~Predicate();
	
	/**
	 * Get ID.
	 */
	unsigned int getId() const { return id_; }

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
	 * Check if this predicate can substitute for the given predicate.
	 * Requirements for meeting this:
	 * - The names must be the same.
	 * - The arity must be the same.
	 * - The types of this predicate must be equal or a super type of the types of the given predicate.
	 * This ensures that all possible assignments of the values of the given predicate can also be made to this predicate.
	 * 
	 * For example the predicate (at ?object ?location) is a superset of (at ?truck ?location) if truck is a subset of object.
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
	/**
	 * Create a new predicate. Because we generate all the possible predicates a priori there is no need to create new predicates
	 * afterwards.
	 */
	Predicate(unsigned int id, const std::string& name, const std::vector<const Type*>& types, bool is_static);
	
	Predicate(const Predicate& predicate);
	
	Predicate& operator=(const Predicate& predicate);
	
	// The id of the predicate.
	const unsigned int id_;
	
	// The name of the predicate.
	const std::string name_;

	// The terms of this predicate.
	const std::vector<const Type*>* types_;

	// Is this predicate static?
	bool is_static_;
	
	// To boost performance we cache which predicates this predicate can substitute.
	bool* can_substitute_;
	
	// After creating all the predicates the cache is initiated and we store which other predicates this predicate can substitute.
	void initCache();
	
	// All the predicates which have been created.
	static std::vector<const Predicate*> all_predicates_;
	static std::map<std::pair<std::string, std::vector<const Type*> >, Predicate*> predicate_map_;
};

std::ostream& operator<<(std::ostream&, const Predicate& predicate);
}

#endif
