#ifndef MYPOP_BINDINGS_H
#define MYPOP_BINDINGS_H

#include <vector>
#include <map>
#include <ostream>
#include <set>

#include "plan.h"
#include "plan_types.h"

namespace MyPOP {

class Action;
class Step;
class Variable;
class TermManager;
class Object;
class Term;
class Atom;
class Type;
class Bindings;
class BindingsPropagator;

/**
 * The domain of a variable consists of: 
 * 1) The explicit set of objects which are the values the variable can be assigned to.
 * 2) The set of variable domains which share this domain.
 * 3) The set of domains which cannot be equal to this domain.
 * Note that because of (2) the variable domains share this domain if they have been made
 * equal.
 */
class VariableDomain
{
public:
	/**
	 * Create a domain which contains all the objects a variable can take.
	 */
	VariableDomain(const Bindings& bindings, StepID step, const Variable& variable);
	
	/**
	 * Create a shallow copy, but do not update the unequal bindings!
	 */
	VariableDomain(const VariableDomain& other, const Bindings& bindings);
	
	/**
	 * Update the bindings to unequal_variables.
	 */
	void updateBindings(const std::map<const VariableDomain*, VariableDomain*>& old_to_new_domain_mapping);

	/**
	 * Given this domain, alter it so that all values it can take are equal to
	 * the objects in the domain intersected with the objects in the domain of
	 * the given variable. Also the domains will be merged, so a change in one
	 * will change both.
	 * Return true if the domain of the variable has changed, false otherwise.
	 */
	bool makeEqualTo(const VariableDomain& variable_domain);
	
	/**
	 * Make the variable domain equal to a set of objects. We will only add the
	 * objects to the set if they are already part of the domain. Thus we take the
	 * intersection between the two.
	 * Return true if the domain of the variable has changed, false otherwise.
	 */
	bool makeEqualTo(const std::vector<const Object*>& objects);

	/**
	 * Make the value taken by the variables equal to the given object, if that
	 * object is part of the value domain, otherwise make it empty.
	 * Return true if the domain of the variable has changed, false otherwise.
	 */
	bool makeEqualTo(const Object& object);

	/**
	 * Alter the domain so that the value of the associated variables cannot be
	 * equal to the value of the variables linked to the given domain.
	 * Return true if the domain of the variable has changed, false otherwise.
	 */
	bool makeUnequalTo(VariableDomain& other_domain);

	/**
	 * Remove the given list of objects from the domain.
	 * Return true if the domain of the variable has changed, false otherwise.
	 */
	bool makeUnequalTo(const std::vector<const Object*>& objects);

	/**
	 * Remove the given object from the domain.
	 * Return true if the domain of the variable has changed, false otherwise.
	 */
	bool makeUnequalTo(const Object& object);

	/**
	 * Return all the objects the variable can be assigned to.
	 */
	const std::vector<const Object*>& getDomain() const { return domain_; }

	/**
	 * Get the intersection of this domain and the given domain.
	 */
	void getIntersection(std::vector<const Object*>& intersection, const std::vector<const Object*>& other_domain) const;

	/**
	 * Get the complement of this domain in the other domain. I.e. all the values which
	 * are in the other domain but not in this domain (other \ this).
	 */
	void getComplement(std::vector<const Object*>& complement, const std::vector<const Object*>& other_domain) const;
	
	/**
	 * Return if the intersection between the two variable domains is empty.
	 */
	bool isEmptyIntersection(const VariableDomain& other) const;

	/**
	 * Check if this domain contains the given object.
	 */
	bool contains(const Object& object) const;
	
	/**
	 * Remove all variables which are linked to the given step.
	 */
	void removeVariable(StepID step);

	/**
	 * Get the list of equal variables.
	 */
	const std::vector<std::pair<StepID, const Variable*> >& getEqualVariables() const { return equal_variables_; }

	/**
	 * Set the list of objects this variable domain can take. This overwrites the existing list.
	 */
	void setObjects(std::vector<const Object*>& objects);

	/**
	 * Get the list of variable domains which cannot have the same value as this one.
	 */
	const std::vector<VariableDomain*>& getUnequalVariables() const { return unequal_variables_; }
	std::vector<VariableDomain*>& getNonConstUnequalVariables() { return unequal_variables_; }
	
	/**
	 * Called every time a variable domain is removed.
	 */
	void variableDomainRemoved(const VariableDomain& variable_domain);

	friend std::ostream& operator<<(std::ostream& os, const VariableDomain& vd);

private:
	
	// Populate the variable domains with all objects of the given type.
	void populate(const Type& type);

	// The bindings of all variable domains.
	const Bindings* bindings_;

	// All possible values the variable can take.
	std::vector<const Object*> domain_;

	// All the variable domains which share this domain.
	std::vector<std::pair<StepID, const Variable*> > equal_variables_;

	// All domains which are not equal to this domain.
	std::vector<VariableDomain*> unequal_variables_;
};

std::ostream& operator<<(std::ostream& os, const VariableDomain& vd);

/**
 * Bindings represent the constraints on the domain of variables. In this context we
 * deal with atoms which have a set of variables of a certain type. During the planning
 * process we want to add constraints on the set of values these variables can take until
 * either the set becomes empty (dead end) or all the values in the set are applicable, 
 * i.e. they do not violate any other constraints.
 *
 * The objective is to make the bindings as powerful as possible, hopefully we will be
 * able to use CSP techniques to help with the pruning. One of the techniques we want
 * to use will split the planning problem into a set of sub problems. The bindings
 * should be able to capture the constraints such that we have to commit ourselves
 * as little as possible thus giving more flexability to the planner.
 */
class Bindings
{
public:
	Bindings(const TermManager& term_manager, const BindingsPropagator& propagator);

	Bindings(const Bindings& other);

	virtual ~Bindings();

	/**
	 * Get the variable domain. The planner will crash if the variable domain does not exists.
	 */
	const VariableDomain& getVariableDomain(StepID step_id, const Variable&) const;
	VariableDomain& getNonConstVariableDomain(StepID step_id, const Variable&);

	/**
	 * Create variable domains for each action variable.
	 */
	StepID createVariableDomains(const Action& action, StepID step_id = Step::INVALID_STEP);
	
	/**
	 * Create variable domain for each atom variable, all terms which are objects will be skipped.
	 */
	StepID createVariableDomains(const Atom& atom, StepID step_id = Step::INVALID_STEP);
	
	/**
	 * Remove bindings after the are no longer used.
	 */
	//void deleteVariableDomains(StepID step_id, const Variable& variable);

	/**
	 * Remove all binding constraints from a step id.
	 * Warning: Very expensive operation and should not be necessary during planning!
	 */
	void removeBindings(StepID step);
	void removeBindings(StepID step, const Variable& variable);
	void removeAllBut(const std::set<std::pair<StepID, const Term*> >& relevant_variable_domains);
	void removeRedundantVariables();

	/**
	 * Check if two atoms can be unified. This function will call the function canUnify for every
	 * pair of terms. If all terms can be unified this function will return true.
	 * @param atom1 The first atom to be unified.
	 * @param step1 The step ID of the first atom.
	 * @param atom2 The second atom to be unified, if the variables of this atom are not bound to this 
	 * binding object, other_bindings will be not zero and point to the binding object which does contain 
	 * the bindings for this atom.
	 * @param step2 The step ID of the second atom.
	 * @param other_bindings Default other_bindings in the Bindings object that is called. If other_bindings
	 * points to another Bindings object the variables will not be made the same, but the values from the domains
	 * are made equal.
	 */
	bool canUnify(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2, const Bindings* other_bindings = NULL) const;
	bool unify(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2);

	/**
	 * Check if two actions can be unified. This function will call the function canUnify for every
	 * pair of terms. If all terms can be unified this function will return true.
	 * @param action1 The first action to be unified.
	 * @param step1 The step ID of the first action.
	 * @param atom2 The second actions  to be unified, if the variables of this action are not bound to this 
	 * binding object, other_bindings will be not zero and point to the binding object which does contain 
	 * the bindings for this action.
	 * @param step2 The step ID of the second action.
	 * @param other_bindings Default other_bindings in the Bindings object that is called. If other_bindings
	 * points to another Bindings object the variables will not be made the same, but the values from the domains
	 * are made equal.
	 */
	bool canUnify(const Action& action1, StepID step1, const Action& action2, StepID step2, const Bindings* other_bindings = NULL) const;
	
	/**
	 * Make the variable domains equal. The atoms needs to be able to be unified, but instead of
	 * linking the variable domains as done by the unify action, this action will only change the
	 * domains of the variables by taking their intersections.
	 * @param atom1 The first atom to be made equal.
	 * @param step1 The step ID of the first atom.
	 * @param atom2 The second atom to be made equal, if the variables of this atom are not bound to this 
	 * binding object, other_bindings will be not zero and point to the binding object which does contain 
	 * the bindings for this atom.
	 * @param step2 The step ID of the second atom.
	 * @return true if the domains could be made equal, false otherwise.
	 */
	bool makeEqual(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2);

	/**
	 * Check if the variable domains are identical, this means all the terms are the same.
	 * @param atom1 The first atom to check.
	 * @param step1 The step ID of the first atom.
	 * @param atom2 The second atom to check.
	 * @param step2 The step ID of the second atom.
	 * @return true if the domains are equal, false otherwise.
	 */
	bool areIdentical(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2) const;

	/**
	 * Check if the variable domains are equivalent, this means all term's domains contain the same values.
	 * @param atom1 The first atom to check.
	 * @param step1 The step ID of the first atom.
	 * @param atom2 The second atom to check.
	 * @param step2 The step ID of the second atom.
	 * @return true if the domains are equal, false otherwise.
	 */
	bool areEquivalent(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2, const Bindings* other_bindings = NULL) const;

	/**
	 * Check if two atoms could effect one another based on the current bindings.
	 */
	bool affects(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2) const;

	/**
	 * Get the term manager.
	 */
	const TermManager& getTermManager() const { return *term_manager_; }
	
	/**
	 * Get the propagator.
	 */
	const BindingsPropagator& getPropagator() const { return *propagator_; }

	/**
	 * Add a new variable domain to the set.
	 */
	VariableDomain& createVariableDomain(StepID step_id, const Variable&);
	
	/**
	 * Only used when two variables have been merged, is only called by VariableDomain. This method
	 * updates the mapping table so all references to @param rhs are updated correctly.
	 * @param lhs The variable domain @param rhs has been merged with.
	 * @param rhs The variable domain which has been merged with @param lhs.
	 */
	void postProcessMerge(VariableDomain& lhs, const VariableDomain& rhs);

	unsigned int getNr() const { return binding_mapping_.size(); }
protected:
	/**
	 * The term manager.
	 */
	const TermManager* term_manager_;

	/**
	 * We can uniquely identify a variable's domain in a plan by looking at the step
	 * id and the variable of the action linked to that step.
	 */
	std::map<std::pair<StepID, const Variable*>, VariableDomain*> binding_mapping_;

	/**
	 * To aid deleting pointers after we destroy a bindings class, we keep track of a list
	 * containing all pointers.
	 */
	std::vector<VariableDomain*> variable_domains_;
	
	/**
	 * As the domains gets updated, the propagator is called to infer more restrictions
	 * on the variable domains. Every time makeEqualTo and makeUnequalTo is called the
	 * respective calls to the propagator is made.
	 */
	const BindingsPropagator* propagator_;

	/**
	 * We keep track of the next free StepID internally, everytime a new binding is made to 
	 * a new step id, either the step id is specifically given or it is left to this function
	 * to do so.
	 * @param step_id The prefered step_id, if this equals Step::INVALID_STEP than a new step
	 * id will be generated and returned. Otherwise step_id will be returned, but the next
	 * generated step id will be equal to step_id + 1.
	 */
	StepID getNextStep(StepID step_id);

private:

	/**
	 * We keep track of the next free StepID internally, every time a StepID is assigned
	 * this number is incremented.
	 */
	StepID next_free_step_id_;

	friend std::ostream& operator<<(std::ostream& os, const Bindings& bindings);
};

std::ostream& operator<<(std::ostream& os, const Bindings& bindings);

};

#endif
