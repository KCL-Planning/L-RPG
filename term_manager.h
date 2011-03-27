#ifndef MYPOP_TERM_MANAGER_H
#define MYPOP_TERM_MANAGER_H

#include <string>
#include <ostream>
#include <assert.h>
#include "VALfiles/ptree.h"
#include "manager.h"
#include "plan_types.h"

namespace MyPOP {

class Bindings;


class Type;
class TypeManager;
class Object;
class Variable;

/**
 * A term is an abstract class which can either be an object or a variable, all
 * the behavioural code is in these classes. Other classes only need to consider 
 * terms without worrying if the actual object is a variable or an object.
 */
class Term : public ManageableObject {
public:
	Term() {}

	virtual ~Term() {};

	/**
	 * Get the type of this term.
	 */
	const Type* getType() const { return type_; }

	/**
	 * Get the name of this term.
	 */
	const std::string& getName() const { return name_; }
	
	/**
	 * Check if this term is unifiable with the given term. This means that if we take the intersection
	 * of both term's domains it yields a non-empty set.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param lhs_bindings The class which contains the bindings for the lhs term.
	 * @param rhs_bindings The class which contains the bindings for the rhs term. If this value is assigned NULL it will
	 * be treated as equal to @param lhs_bindings
	 * @return True if the terms can be unified, false otherwise.
	 */
	bool canUnify(StepID lhs_id, const Term& rhs, StepID rhs_id, const Bindings& lhs_bindings, const Bindings* rhs_bindings = NULL) const;
	
	/**
	 * Unify the two terms, there are three different possible scenarios.
	 * - Both terms are variable: in this case we merge both variables, a change to one of the variables will
	 * affect the other variables. The are the same after unifying.
	 * - One is an object and the other a variable: in this case the variable's domain will be reduced to the 
	 * given object. There is no other relationt between both terms.
	 * - Both are objects: Nothing will happen, the result will be identical to a call to canUnify.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 */
	virtual bool unify(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const = 0;
	
	/**
	 * Make two term disjunct, the following cases can occur:
	 * - Both terms are variable: in this case we add each variable to each other's unequal table.
	 * - The LHS is a variable and the RHS is an object: in this case the object will be removed from the variable's domain.
	 * - The LHS is an object: Nothing will happen, but the program will fail if asked to make the domain of the object empty.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain of the lhs has been changed.
	 */
	virtual bool makeDisjunct(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const = 0;
	
	/**
	 * Modify the domain of this term such that it contains the same objects of the given term. Note that if
	 * the other term contains objects not contained in this term, these will not be added. So we take the
	 * conjunction of both domains and assign it to this domain.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	virtual bool makeDomainEqualTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings = NULL) const = 0;
	
	/**
	 * Modify the domain of this term such that it only contains the objects present in @param objects. We
	 * take the conjunction of this domain and the list of objects.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param objects The list of objects which this domain can take.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	virtual bool makeDomainEqualTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const = 0;

	/**
	 * Modify the domain of this term such that all objects present in the rhs term are removed from this term.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	virtual bool makeDomainUnequalTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings, Bindings* rhs_bindings = NULL) const = 0;

	/**
	 * Modify the domain of this term such that all the objects present in @param objects are removed from it.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param objects The list of objects which this domain can take.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	virtual bool makeDomainUnequalTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const = 0;
	
	/**
	 * Get the domain of this term, in the case of an object this will be a single object and in the
	 * case of the variable it will be a list of objects (possibly empty).
	 * @param id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings In the case of variables we need the bindings to discover its domain since it
	 * is stored in the Bindings class.
	 * @return The domain of this term.
	 */
	virtual const std::vector<const Object*>& getDomain(StepID id, const Bindings& bindings) const = 0;
	
	/**
	 * Check if two terms are the same, note that this is not an equivalent check, what is checked here is if
	 * both term's domains point to the same memory space.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if both term's domains point to the same memory space, false otherwise.
	 */
	bool isTheSameAs(StepID lhs_id, const Term& rhs, StepID rhs_id, const Bindings& bindings) const;
	
	/**
	 * Check if the given object is a member of this term's domain.
	 * @param object The object we are looking for.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if object is part of this term's domain.
	 */
	bool contains(const Object& object, StepID lhs_id, const Bindings& bindings) const;
	
	/**
	 * Check if at least one of the given objects is a member of this term's domain.
	 * @param objects The objects we are looking for.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if one of the objects is part of this term's domain.
	 */
	bool containsAtLeastOneOf(const std::vector<const Object*>& objects, StepID lhs_id, const Bindings& bindings) const;
	
	/**
	 * Method that should be called by @param bindings to bind this term to the given bindings object.
	 * @param Bindings the bindings object to bind this term to.
	 * @param new_step_id the id which should be given to the binding.
	 */
	virtual void bind(Bindings& bindings, StepID new_step_id) const = 0;
	
	/**
	 * Print the term in a userfriendly way.
	 */
	virtual void print(std::ostream& os, const Bindings& bindings, StepID id) const = 0;
	
	/**
	 * Unify this term with an object.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param object The object the compare the domain against.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	virtual bool unifyWith(StepID lhs_id, const Object& object, Bindings& bindings) const = 0;
	
	/**
	 * Unify this term with a variable.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param variable The variable to compare the domain against.
	 * @param rhs_id The step id for the variable, used to find its variable domain in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	virtual bool unifyWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const = 0;

	/**
	 * Make the given variable disjunct from this term.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param variable The variable to compare the domain against.
	 * @param rhs_id The step id for the variable, used to find its variable domain in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain of this term has been modified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	virtual bool makeDisjunctWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const = 0;

protected:
	Term(const Type& type, const std::string& name);
private:

	const Type* type_;
	const std::string name_;
};

std::ostream& operator<<(std::ostream& os, const Term& term);

/**
 * Object...
 */
class Object : public Term {
public:
	Object (const Type& type, const std::string& name);
	virtual ~Object();

	/**
	 * Unify the two terms, there are three different possible scenarios.
	 * - Both terms are variable: in this case we merge both variables, a change to one of the variables will
	 * affect the other variables. The are the same after unifying.
	 * - One is an object and the other a variable: in this case the variable's domain will be reduced to the 
	 * given object. There is no other relationt between both terms.
	 * - Both are objects: Nothing will happen, the result will be identical to a call to canUnify.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 */
	bool unify(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const;

	/**
	 * Make two term disjunct, the following cases can occur:
	 * - Both terms are variable: in this case we add each variable to each other's unequal table.
	 * - The LHS is a variable and the RHS is an object: in this case the object will be removed from the variable's domain.
	 * - The LHS is an object: Nothing will happen, but the program will fail if asked to make the domain of the object empty.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain of the lhs has been changed.
	 */
	bool makeDisjunct(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const;
	
	/**
	 * Modify the domain of this term such that it contains the same objects of the given term. Note that if
	 * the other term contains objects not contained in this term, these will not be added. So we take the
	 * conjunction of both domains and assign it to this domain.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainEqualTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings = NULL) const;

	/**
	 * Modify the domain of this term such that it only contains the objects present in @param objects. We
	 * take the conjunction of this domain and the list of objects.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param objects The list of objects which this domain can take.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainEqualTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const;

	/**
	 * Modify the domain of this term such that all objects present in the rhs term are removed from this term.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainUnequalTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings = NULL) const;

	/**
	 * Modify the domain of this term such that all the objects present in @param objects are removed from it.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param objects The list of objects which this domain can take.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainUnequalTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const;
	
	/**
	 * Get the domain of this term, in the case of an object this will be a single object and in the
	 * case of the variable it will be a list of objects (possibly empty).
	 * @param id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings In the case of variables we need the bindings to discover its domain since it
	 * is stored in the Bindings class.
	 * @return The domain of this term.
	 */
	const std::vector<const Object*>& getDomain(StepID id, const Bindings& bindings) const;
	
	/**
	 * Check if the given object is a member of this term's domain.
	 * @param object The object we are looking for.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if object is part of this term's domain.
	 */
	//bool contains(const Object& object, StepID lhs_id, const Bindings& bindings) const;

	/**
	 * In the case of objects nothing needs to be done, it cannot be bound.
	 * @param Bindings the bindings object to bind this term to.
	 * @param new_step_id the id which should be given to the binding.
	 * @note Bad design to have a NOP method...
	 */
	void bind(Bindings& bindings, StepID new_step_id) const;
	
	/**
	 * Print the term in a userfriendly way.
	 */
	void print(std::ostream& os, const Bindings& bindings, StepID id) const;
	
protected:
	
	/**
	 * Unify this term with an object.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param object The object the compare the domain against.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	bool unifyWith(StepID lhs_id, const Object& object, Bindings& bindings) const;
	
	/**
	 * Unify this term with a variable.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param variable The variable to compare the domain against.
	 * @param rhs_id The step id for the variable, used to find its variable domain in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	bool unifyWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const;

	/**
	 * Make the given variable disjunct from this term.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param variable The variable to compare the domain against.
	 * @param rhs_id The step id for the variable, used to find its variable domain in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain of this term has been modified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	bool makeDisjunctWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const;

private:
	// For efficiency reasons and making the implemenation easier, we force every object to
	// have a domain with only itself as member.
	std::vector<const Object*> domain_;
};

class Variable : public Term {
public:
	Variable (const Type& type, const std::string& name);
	
	virtual ~Variable();

	/**
	 * Unify the two terms, there are three different possible scenarios.
	 * - Both terms are variable: in this case we merge both variables, a change to one of the variables will
	 * affect the other variables. The are the same after unifying.
	 * - One is an object and the other a variable: in this case the variable's domain will be reduced to the 
	 * given object. There is no other relationt between both terms.
	 * - Both are objects: Nothing will happen, the result will be identical to a call to canUnify.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 */
	bool unify(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const;

	/**
	 * Make two term disjunct, the following cases can occur:
	 * - Both terms are variable: in this case we add each variable to each other's unequal table.
	 * - The LHS is a variable and the RHS is an object: in this case the object will be removed from the variable's domain.
	 * - The LHS is an object: Nothing will happen, but the program will fail if asked to make the domain of the object empty.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain of the lhs has been changed.
	 */
	bool makeDisjunct(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const;
	
	/**
	 * Modify the domain of this term such that it contains the same objects of the given term. Note that if
	 * the other term contains objects not contained in this term, these will not be added. So we take the
	 * conjunction of both domains and assign it to this domain.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainEqualTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings = NULL) const;
	
	/**
	 * Modify the domain of this term such that it only contains the objects present in @param objects. We
	 * take the conjunction of this domain and the list of objects.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param objects The list of objects which this domain can take.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainEqualTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const;

	/**
	 * Modify the domain of this term such that all objects present in the rhs term are removed from this term.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param rhs The term the compare the domain against.
	 * @param rhs_id The step id for the rhs term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainUnequalTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings = NULL) const;

	/**
	 * Modify the domain of this term such that all the objects present in @param objects are removed from it.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param objects The list of objects which this domain can take.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain has been modified, false otherwise.
	 */
	bool makeDomainUnequalTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const;
	
	/**
	 * Get the domain of this term, in the case of an object this will be a single object and in the
	 * case of the variable it will be a list of objects (possibly empty).
	 * @param id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings In the case of variables we need the bindings to discover its domain since it
	 * is stored in the Bindings class.
	 * @return The domain of this term.
	 */
	const std::vector<const Object*>& getDomain(StepID id, const Bindings& bindings) const;
	
	/**
	 * Check if the given object is a member of this term's domain.
	 * @param object The object we are looking for.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if object is part of this term's domain.
	 */
	//bool contains(const Object& object, StepID lhs_id, const Bindings& bindings) const;

	/**
	 * We make a callback to the bindings method and tell it to bind the variable to the given ID.
	 * It's inconvenient to do it this way, but this is the only way to shield the actual implemenation
	 * of all derived classes of Term.
	 * @param Bindings the bindings object to bind this term to.
	 * @param new_step_id the id which should be given to the binding.
	 */
	void bind(Bindings& bindings, StepID new_step_id) const;
	
	/**
	 * Print the term in a userfriendly way.
	 */
	void print(std::ostream& os, const Bindings& bindings, StepID id) const;
	
//protected:
	/**
	 * Unify this term with an object.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param object The object the compare the domain against.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	bool unifyWith(StepID lhs_id, const Object& object, Bindings& bindings) const;
	
	/**
	 * Unify this term with a variable.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param variable The variable to compare the domain against.
	 * @param rhs_id The step id for the variable, used to find its variable domain in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the terms can be unified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	bool unifyWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const;
	
	/**
	 * Make the given variable disjunct from this term.
	 * @param lhs_id The step id for this term, used to find its variable domain (if applicable) in @param bindings.
	 * @param variable The variable to compare the domain against.
	 * @param rhs_id The step id for the variable, used to find its variable domain in @param bindings.
	 * @param bindings The class which contains the bindings for both terms.
	 * @return True if the domain of this term has been modified, false otherwise.
	 * NOTE: this isn't very nice since it violates the OO paradigm (base class shouldn't be dependend on its
	 * derived classes).
	 */
	bool makeDisjunctWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const;
};

/**
 * All terms, that is objects and variables are stored by this manager.
 */
class TermManager : public Manager<Term> {

public:
	TermManager(const TypeManager& type_manager);
	virtual ~TermManager();

	// Process the variables linked to the actions.
	void processActionVariables(const VAL::operator_list& operators);

	// Add a variable (of an action) to the list of types.
	void addTerm(const VAL::symbol& symbol, Term& term);
	void addTerm(const VAL::symbol& symbol, Object& term);

	// Get the term object linked to the VAL::symbol as processed by the parser. Note 
	// that this function can only be called during the parsing phase, afterwards all references
	// to VAL::symbol are deleted.
	const Term* getTerm(const VAL::symbol&) const;
	const Term* getTerm(const std::string& name) const;
	
	// Get all the objects in the domain.
	const std::vector<const Object*>& getAllObjects() const { return domain_objects_; }
	
	// Return the type manager.
	const TypeManager& getTypeManager() const { return *type_manager_; }

private:
	const TypeManager* type_manager_;

	// During construction of the types keep track of the indexing from the
	// symbol type to TermID.
	std::map<const VAL::symbol*, const Term*>* term_indexing_;
	std::map<std::string, const Term*>* term_string_indexing_;
	
	// Store the objects from the domain separately.
	std::vector<const Object*> domain_objects_;
};

std::ostream& operator<<(std::ostream& os, const TermManager& term_manager);

};

#endif
