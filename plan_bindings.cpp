#include <assert.h>
#include <set>

#include "plan_bindings.h"
#include "term_manager.h"
#include "predicate_manager.h"
#include "plan.h"
#include "formula.h"
#include "exceptions.h"
#include "bindings_propagator.h"
#include "type_manager.h"
#include "action_manager.h"

///#define MYPOP_VARIABLE_DOMAIN_DEBUG

namespace MyPOP {

/*************************
 * The VariableDomain class
 *************************/

VariableDomain::VariableDomain(const Bindings& bindings, StepID step_id, const Variable& variable)
	: bindings_(&bindings)
{
	equal_variables_.push_back(std::make_pair(step_id, &variable));

	// Initialize the domain so it can be of any object of the correct type.
	if (variable.getType() != NULL)
	{
		populate(*variable.getType());
	}
}

VariableDomain::VariableDomain(const VariableDomain& other, const Bindings& bindings)
{
	bindings_ = &bindings;

	// Shallow the domain and equal variable domains.
	domain_ = other.domain_;
	equal_variables_ = other.equal_variables_;

/*	Sanity check.
	for (unsigned int i = 0; i < unequal_variables_.size(); i++)
	{
		assert (unequal_variables_[i] == other.unequal_variables_[i]);
	}
*/

	// We do not update the unequal variables, as we need to wait for the bindings to create the new layer
	// of variable domains. When this is done the pointers will be updated in the function 'updateBindings'.
	unequal_variables_ = other.unequal_variables_;

/*	Sanity check.
	for (unsigned int i = 0; i < unequal_variables_.size(); i++)
	{
		assert (unequal_variables_[i] == other.unequal_variables_[i]);
	}
*/
}

void VariableDomain::populate(const Type& type)
{
	std::vector<const Object*> values;
	bindings_->getTermManager().getTypeManager().getObjectsOfType(values, type);
	domain_.insert(domain_.begin(), values.begin(), values.end());
}

void VariableDomain::updateBindings(const std::map<const VariableDomain*, VariableDomain*>& old_to_new_domain_mapping)
{
	for (unsigned int i = 0; i < unequal_variables_.size(); i++)
	{
		if (old_to_new_domain_mapping.find(unequal_variables_[i]) == old_to_new_domain_mapping.end())
		{
			assert(false);
		}

		unequal_variables_[i] = (*old_to_new_domain_mapping.find(unequal_variables_[i])).second;
	}
}

bool VariableDomain::makeEqualTo(const VariableDomain& variable_domain)
{
	if (this == &variable_domain)
	{
		return false;
	}
#ifdef MYPOP_VARIABLE_DOMAIN_DEBUG
	std::cout << "Restrict " << *this << " to " << variable_domain << std::endl;	
#endif
	
	// Make sure we do not do the restriction if it is already in place. To do this, we will compare 
	// a step, variable pair from the given variable domain against all those of this variable domain.
	StepID step = variable_domain.equal_variables_[0].first;
	const Variable& variable = *variable_domain.equal_variables_[0].second;

	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = equal_variables_.begin(); ci != equal_variables_.end(); ci++)
	{
		StepID equal_variable_step = (*ci).first;
		const Variable* equal_variable = (*ci).second;
#ifdef MYPOP_VARIABLE_DOMAIN_DEBUG
		std::cout << "Compare: " << (*ci).first << " == " << step << " && " << *(*ci).second << " == " << variable << std::endl;
#endif
		
		if (equal_variable_step == step && equal_variable == &variable)
		{
#ifdef MYPOP_VARIABLE_DOMAIN_DEBUG
			std::cout << "EQUAL!" << std::endl;
#endif
			return false;
		}
	}
	
	// Limit the domain to contain only the objects in both variables.
	std::vector<const Object*> new_domain;
	getIntersection(new_domain, variable_domain.domain_);

	domain_.clear();
	domain_.insert(domain_.begin(), new_domain.begin(), new_domain.end());

	// Next merge the equal to and unequal to relationships, but make sure we don't end up with duplicates.
	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = variable_domain.equal_variables_.begin(); ci != variable_domain.equal_variables_.end(); ci++)
	{
		bool contains_relationship = false;
		StepID equal_variable_step = (*ci).first;
		const Variable* equal_variable = (*ci).second;
		
		for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci2 = equal_variables_.begin(); ci2 != equal_variables_.end(); ci2++)
		{
			StepID equal_variable_step2 = (*ci2).first;
			const Variable* equal_variable2 = (*ci2).second;
			if (equal_variable_step == equal_variable_step2 && equal_variable == equal_variable2)
			{
				contains_relationship = true;
				break;
			}
		}

		// If the relationship is not part of this set yet, add it.
		if (!contains_relationship)
		{
			equal_variables_.push_back(*ci);
		}
	}

	for (std::vector<VariableDomain*>::const_iterator ci = variable_domain.unequal_variables_.begin(); ci != variable_domain.unequal_variables_.end(); ci++)
	{
		makeUnequalTo(**ci);
	}

#ifdef MYPOP_VARIABLE_DOMAIN_DEBUG
	std::cout << "Result of merge: " << *this << std::endl;
#endif
	
	return true;
}

bool VariableDomain::makeEqualTo(const Object& object)
{
	// Check if the object is part of this set.
	if (contains(object))
	{
		// If so, make sure this domain only contains the given object.
		if (domain_.size() > 1)
		{
			domain_.clear();
			domain_.push_back(&object);
			
			return true;
		}
		return false;
	}
	// Otherwise, make the domain empty.
	domain_.clear();
	return true;
}

bool VariableDomain::makeEqualTo(const std::vector<const Object*>& objects)
{
	std::vector<const Object*> intersection;
	getIntersection(intersection, objects);
	
	// Check if the domain changed.
	if (intersection.size() != domain_.size())
	{
		domain_.clear();
		domain_.insert(domain_.begin(), intersection.begin(), intersection.end());
		return true;
	}
	
	return false;
}

bool VariableDomain::makeUnequalTo(const std::vector<const Object*>& objects)
{
	// Check if the object is part of this set.
	bool domain_changed = false;
	for (std::vector<const Object*>::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
	{
		if (makeUnequalTo(**ci)) domain_changed = true;
	}
	return domain_changed;
}

bool VariableDomain::makeUnequalTo(const Object& object)
{
	// Check if the object is part of this set.
	for (std::vector<const Object*>::iterator ci = domain_.begin(); ci != domain_.end(); ci++)
	{
		if (*ci == &object)
		{
			domain_.erase(ci);
			return true;
		}
	}
	return false;
}

bool VariableDomain::makeUnequalTo(VariableDomain& other_domain)
{
	// Make sure the same unequal relationship is added twice.
	for (std::vector<VariableDomain*>::const_iterator ci = unequal_variables_.begin(); ci != unequal_variables_.end(); ci++)
	{
		if (*ci == &other_domain)
		{
			return false;
		}
	}

	// If the relationship is not part of this set yet, add the given domain to the unequal list.
	unequal_variables_.push_back(&other_domain);
	return true;
}

void VariableDomain::getIntersection(std::vector<const Object*>& intersection, const std::vector<const Object*>& other_domain) const
{
	for (std::vector<const Object*>::const_iterator ci = other_domain.begin(); ci != other_domain.end(); ci++)
	{
		for (std::vector<const Object*>::const_iterator ci2 = domain_.begin(); ci2 != domain_.end(); ci2++)
		{
			if (*ci == *ci2)
			{
				intersection.push_back(*ci);
				break;
			}
		}
	}
}

void VariableDomain::getComplement(std::vector<const Object*>& complement, const std::vector<const Object*>& other_domain) const
{
	for (std::vector<const Object*>::const_iterator ci = other_domain.begin(); ci != other_domain.end(); ci++)
	{
		bool object_found = false;
		for (std::vector<const Object*>::const_iterator ci2 = domain_.begin(); ci2 != domain_.end(); ci2++)
		{
			if (*ci == *ci2)
			{
				object_found = true;
				break;
			}
		}

		if (!object_found)
		{
			complement.push_back(*ci);
		}
	}
}

bool VariableDomain::isEmptyIntersection(const VariableDomain& other) const
{
	for (std::vector<const Object*>::const_iterator ci = other.domain_.begin(); ci != other.domain_.end(); ci++)
	{
		for (std::vector<const Object*>::const_iterator ci2 = domain_.begin(); ci2 != domain_.end(); ci2++)
		{
			if (*ci == *ci2)
			{
				return false;
			}
		}
	}

	return true;
}


bool VariableDomain::contains(const Object& object) const
{
	for (std::vector<const Object*>::const_iterator ci = domain_.begin(); ci != domain_.end(); ci++)
	{
		if (*ci == &object)
		{
			return true;
		}
	}
	return false;
}

void VariableDomain::removeVariable(MyPOP::StepID step)
{
	for (std::vector<std::pair<StepID, const Variable*> >::iterator i = equal_variables_.begin(); i != equal_variables_.end(); i++)
	{
		if ((*i).first == step)
		{
			equal_variables_.erase(i);
			break;
		}
	}
}

void Bindings::removeBindings(StepID step, const Variable& variable)
{
	assert (binding_mapping_.erase(std::make_pair(step, &variable)) != 0);
}

void Bindings::removeAllBut(const std::set<std::pair<StepID, const Term*> >& relevant_variable_domains)
{
	unsigned int variable_domains_removed = 0;
	unsigned int bindings_removed = 0;
	std::map<const VariableDomain*, unsigned int> pointer_counter;
	
	for (std::vector<VariableDomain*>::const_iterator ci = variable_domains_.begin(); ci != variable_domains_.end(); ++ci)
	{
		pointer_counter[*ci] = 0;
	}
	
	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.begin(); ci != binding_mapping_.end(); ++ci)
	{
		pointer_counter[(*ci).second] = pointer_counter[(*ci).second] + 1;
	}
	
	std::vector<std::pair<StepID, const Variable*> > to_delete;
	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.begin(); ci != binding_mapping_.end(); ++ci)
	{
		if (relevant_variable_domains.count((*ci).first) == 0)
		{
			to_delete.push_back((*ci).first);
		}
	}
	
	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = to_delete.begin(); ci != to_delete.end(); ++ci)
	{
		const VariableDomain* variable_domain = binding_mapping_[*ci];
		binding_mapping_.erase(*ci);
		unsigned int pointer_count = pointer_counter[variable_domain];
		pointer_counter[variable_domain] = pointer_count - 1;
		
		++bindings_removed;
		if (pointer_count - 1 == 0)
		{
			delete variable_domain;
			++variable_domains_removed;
		}
	}
	
	std::cerr << "Removed " << bindings_removed << " bindings and " << variable_domains_removed << " variable domains!" << std::endl;
}

void VariableDomain::setObjects(std::vector<const Object*>& objects)
{
	domain_.clear();

	std::set<const Object*> new_objects;
	new_objects.insert(objects.begin(), objects.end());


	domain_.insert(domain_.begin(), new_objects.begin(), new_objects.end());
}

void VariableDomain::variableDomainRemoved(const VariableDomain& variable_domain)
{
	for (std::vector<VariableDomain*>::reverse_iterator ri = unequal_variables_.rbegin(); ri != unequal_variables_.rend(); ri++)
	{
		if (*ri == &variable_domain)
		{
			unequal_variables_.erase(ri.base() - 1);
		}
	}
}

std::ostream& operator<<(std::ostream& os, const VariableDomain& vd)
{
	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = vd.equal_variables_.begin(); ci != vd.equal_variables_.end(); ci++)
	{
		os << "(" << (*ci).first << " " << (*ci).second->getName() << ")";
		if (ci + 1 != vd.equal_variables_.end())
			os << ", ";
	}

	os << " = { ";

	for (std::vector<const Object*>::const_iterator ci = vd.domain_.begin(); ci != vd.domain_.end(); ci++)
	{
		os << **ci;
		if (ci + 1 != vd.domain_.end())
			os << ", ";
	}

	os << " }";
	if (vd.unequal_variables_.size() > 0)
	{
		 os << " != {";
	
		for (std::vector<VariableDomain*>::const_iterator ci = vd.unequal_variables_.begin(); ci != vd.unequal_variables_.end(); ci++)
		{
			const VariableDomain& v = **ci;
			for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci2 = v.equal_variables_.begin(); ci2 != v.equal_variables_.end(); ci2++)
			{
				assert (ci2 != v.equal_variables_.end());
				os << "(" << (*ci2).first << " " << (*ci2).second->getName() << ")";
				if (ci2 + 1 != v.equal_variables_.end())
					os << ", ";
			}
			os << &v;
		}
	
		os << "}";
	}
	os << &vd;
	return os;
}

/*************************
 * The Bindings class
 *************************/

Bindings::Bindings(const TermManager& term_manager, const BindingsPropagator& propagator)
	: term_manager_(&term_manager), propagator_(&propagator), next_free_step_id_(0)
{

}

Bindings::Bindings(const Bindings& other)
{
//	std::cout << "Bindings::Bindings - copy " << other.binding_mapping_.size() << " bindings!" << std::endl;
	term_manager_ = other.term_manager_;
	propagator_ = other.propagator_;
	next_free_step_id_ = other.next_free_step_id_;

	// First we're going to make shallow copies of all variable domains, once these are in place we want to update the
	// references the domains holds towards other domains it is not equal to.
	std::map<const VariableDomain*, VariableDomain*> old_to_new_domain_mapping;
	std::vector<VariableDomain*> new_variable_domains;

	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator i = other.binding_mapping_.begin(); i != other.binding_mapping_.end(); i++)
	{
		const VariableDomain* old_domain = (*i).second;

		// Check if the domain has already been mapped.
		std::map<const VariableDomain*, VariableDomain*>::const_iterator ci = old_to_new_domain_mapping.find(old_domain);
		
		VariableDomain* new_domain_ptr = NULL;
		
		// If the mapping hasn't been made, do it now.
		if (ci == old_to_new_domain_mapping.end())
		{
			// Make a shallow copy.
			new_domain_ptr = new VariableDomain(*old_domain, *this);
			variable_domains_.push_back(new_domain_ptr);
			old_to_new_domain_mapping[old_domain] = new_domain_ptr;
			new_variable_domains.push_back(new_domain_ptr);
		}
		else
		{
			// Otherwise recover the domain ptr from the mapping.
			new_domain_ptr = (*ci).second;
		}
		
		binding_mapping_[(*i).first] = new_domain_ptr;
	}
	
	// Once all shallow copies have been made, we will now update the bindings with the new set of
	// variable domains.

	// The binding_mapping contains a list of all variable mappings, but also contains duplicates as at the
	// moment we do not remove these once variables are merged. So to avoid mapping a variable domain twice
	// (with undefined effects...) we keep track of a closed list.
	for (std::vector<VariableDomain*>::const_iterator i = new_variable_domains.begin(); i != new_variable_domains.end(); i++)
	{
		VariableDomain& new_domain = *(*i);
		new_domain.updateBindings(old_to_new_domain_mapping);
	}
}

Bindings::~Bindings()
{
	for (std::vector<VariableDomain*>::const_iterator ci = variable_domains_.begin(); ci != variable_domains_.end(); ci++)
	{
		delete *ci;
	}
}

const VariableDomain& Bindings::getVariableDomain(StepID step_id, const Variable& variable) const
{
	std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.find(std::make_pair(step_id, &variable));
	if (ci == binding_mapping_.end())
	{
//		for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator i = binding_mapping_.begin(); i != binding_mapping_.end(); i++)
//		{
//			std::pair<StepID, const Variable*> binding = (*i).first;
//			std::cout << binding.first << " and " << *binding.second << std::endl;
//		}
		
		std::cout << "Could not find the variable domain for: Step id: " << step_id << " " << variable << std::endl;
		throw RequestNonExistingVariableBindingException();
	}
	return *(*ci).second;
}

VariableDomain& Bindings::getNonConstVariableDomain(StepID step_id, const Variable& variable)
{
	return *const_cast<VariableDomain*>(&getVariableDomain(step_id, variable));
}

VariableDomain& Bindings::createVariableDomain(StepID step_id, const Variable& variable)
{
	assert (step_id != Step::INVALID_STEP);

	assert (binding_mapping_.find(std::make_pair(step_id, &variable)) == binding_mapping_.end());

	VariableDomain* new_variable_domain = new VariableDomain(*this, step_id, variable);
	variable_domains_.push_back(new_variable_domain);
	binding_mapping_[std::make_pair(step_id, &variable)] = new_variable_domain;
	return *new_variable_domain;
}

StepID Bindings::createVariableDomains(const Action& action, StepID step_id)
{
	step_id = getNextStep(step_id);

	const std::vector<const Variable*>& variables = action.getVariables();
	for (std::vector<const Variable*>::const_iterator ci = variables.begin(); ci != variables.end(); ci++)
	{
		createVariableDomain(step_id, **ci);
	}
	return step_id;
}

StepID Bindings::createVariableDomains(const Atom& atom, StepID step_id)
{
	step_id = getNextStep(step_id);
	const std::vector<const Term*>& terms = atom.getTerms();
	for (std::vector<const Term*>::const_iterator ci = terms.begin(); ci != terms.end(); ci++)
	{
		const Term* term = *ci;
		term->bind(*this, step_id);
	}

	return step_id;
}

void Bindings::removeBindings(StepID step)
{
	return;
	std::set<VariableDomain*> variable_domains_to_delete;
	std::vector<std::pair<StepID, const Variable*> > mappings_to_delete;
//	std::set<VariableDomain*> shared_variable_domains;
	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.begin(); ci != binding_mapping_.end(); ++ci)
	{
		if ((*ci).first.first == step)
		{
			variable_domains_to_delete.insert((*ci).second);
		}
//		else
//		{
//			variable_domains_to_delete.insert((*ci).second);
//		}
	}
	
	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = mappings_to_delete.begin(); ci != mappings_to_delete.end(); ++ci)
	{
		binding_mapping_.erase(*ci);
	}
	
	for (std::vector<VariableDomain*>::reverse_iterator ri = variable_domains_.rbegin(); ri != variable_domains_.rend(); ++ri)
	{
		VariableDomain* variable_domain = *ri;
		if (variable_domains_to_delete.find(*ri) == variable_domains_to_delete.end())
		{
			for (std::vector<VariableDomain*>::const_iterator ci = variable_domain->getUnequalVariables().begin(); ci != variable_domain->getUnequalVariables().end(); ci++)
			{
				(*ci)->variableDomainRemoved(*variable_domain);
			}
			
			delete variable_domain;
			variable_domains_.erase(ri.base() - 1);
		}
	}
}

void Bindings::removeRedundantVariables()
{
	// Remove all the bindings which are linked to the given step.
	//std::vector<VariableDomain*> variable_domains_to_remove;
	std::set<VariableDomain*> mapped_variable_domains;
	std::vector<std::pair<StepID, const Variable*> > mappings_to_remove;
	
	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.begin(); ci != binding_mapping_.end(); ++ci)
	{
		mapped_variable_domains.insert((*ci).second);
	}
	
	for (std::vector<VariableDomain*>::reverse_iterator ri = variable_domains_.rbegin(); ri != variable_domains_.rend(); ++ri)
	{
		VariableDomain* variable_domain = *ri;
		if (mapped_variable_domains.find(*ri) == mapped_variable_domains.end())
		{
			for (std::vector<VariableDomain*>::const_iterator ci = variable_domain->getUnequalVariables().begin(); ci != variable_domain->getUnequalVariables().end(); ci++)
			{
				(*ci)->variableDomainRemoved(*variable_domain);
			}
			
			delete variable_domain;
			variable_domains_.erase(ri.base() - 1);
		}
	}
}

bool Bindings::canUnify(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2, const Bindings* other_bindings) const
{
	// Make sure the predicates are the same.
	if (atom1.getPredicate().getName() != atom2.getPredicate().getName())
	{
		return false;
	}
	
	// Make sure the atoms have the same arity.
	if (atom1.getArity() != atom2.getArity())
	{
		return false;
	}
	
	// Only return true if all the pairs of terms of the atoms can be unified.
	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		if (!atom1.getTerms()[i]->canUnify(step1, *atom2.getTerms()[i], step2, *this, other_bindings))
		//if (!canUnify(*atom1.getTerms()[i], step1, *atom2.getTerms()[i], step2, other_bindings))
		{
			return false;
		}
	}
	
	return true;
}

bool Bindings::unify(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2)
{
/*	std::cout << "[Bindings::unify] ";
	atom1.print(std::cout, *this, step1);
	std::cout << " with ";
	atom2.print(std::cout, *this, step2);
	std::cout << std::endl;
*/
	if (!canUnify(atom1, step1, atom2, step2))
	{
///		std::cout << "canUnify failed!" << std::endl;
		return false;
	}

	// Only return true if all the pairs of terms of the atoms can be unified.
	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		if (!atom1.getTerms()[i]->unify(step1, *atom2.getTerms()[i], step2, *this))
		{
			return false;
		}
	}
	
	return true;
}

bool Bindings::canUnify(const Action& action1, StepID step1, const Action& action2, StepID step2, const Bindings* other_bindings) const
{
	// Make sure the predicates are the same.
	if (action1.getPredicate() != action2.getPredicate())
	{
		return false;
	}
	
	// Only return true if all the pairs of terms of the atoms can be unified.
	for (unsigned int i = 0; i < action1.getVariables().size(); i++)
	{
		//if (!canUnify(*action1.getVariables()[i], step1, *action2.getVariables()[i], step2, other_bindings))
		if (!action1.getVariables()[i]->canUnify(step1, *action2.getVariables()[i], step2, *this, other_bindings))
		{
			return false;
		}
	}
	
	return true;
}

bool Bindings::makeEqual(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2)
{
	if (!canUnify(atom1, step1, atom2, step2))
	{
		return false;
	}

/*
	std::cout << "Make equal: ";
	atom1.print(std::cout, *this, step1);
	std::cout << " and ";
	atom2.print(std::cout, (other_bindings == NULL ? *this : *other_bindings), step2);
	std::cout << std::endl;
*/

	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		atom1.getTerms()[i]->makeDomainEqualTo(step1, *atom2.getTerms()[i], step2, *this);
	}
	return true;
}

bool Bindings::areIdentical(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2) const 
{
	if (!canUnify(atom1, step1, atom2, step2))
	{
		return false;
	}
	
	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		if (!atom1.getTerms()[i]->isTheSameAs(step1, *atom2.getTerms()[i], step2, *this))
		{
			return false;
		}
	}
	
	return true;
}

bool Bindings::areEquivalent(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2, const Bindings* other_bindings) const
{
	if (!canUnify(atom1, step1, atom2, step2, other_bindings))
	{
		return false;
	}
	
	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		if (!atom1.getTerms()[i]->isEquivalentTo(step1, *atom2.getTerms()[i], step2, *this, other_bindings))
		{
			return false;
		}
	}
	
	return true;
}


bool Bindings::affects(const Atom& atom1, StepID step1, const Atom& atom2, const StepID step2) const
{
	// First make sure the predicates are the same.
	if (atom1.getPredicate().getName() != atom2.getPredicate().getName())
	//if (&atom1.getPredicate() != &atom2.getPredicate())
		return false;

	// If the sign isn't contradictory we can move on.
	if (atom1.isNegative() == atom2.isNegative())
		return false;

	// Check if the terms have the same number of parameters.
	if (atom1.getArity() != atom2.getArity())
		return false;

	// Make sure the types are the same and the intersections of the domains are not
	// empty.
	bool terms_differ = false;
	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		const Term* term1 = atom1.getTerms()[i];
		const Term* term2 = atom2.getTerms()[i];

		if (!term1->canUnify(step1, *term2, step2, *this))
		{
			terms_differ = true;
			break;
		}
	}
	if (terms_differ)
	{
		return false;
	}

#ifdef MYPOP_VARIABLE_DOMAIN_DEBUG
	atom1.print(std::cout);
	std::cout << "[" << step1 << "] affects ";
	atom2.print(std::cout);
	std::cout << "[" << step2 << "]" << std::endl;
#endif

	return true;
}

void Bindings::postProcessMerge(VariableDomain& lhs_vd, const VariableDomain& rhs_vd)
{
	// Make sure the bindings to the rhs (which has been merged with the lhs) are updated to point to the lhs variable domain.
	const std::vector<std::pair<StepID, const Variable*> >& equal_rhs_variables = rhs_vd.getEqualVariables();
	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = equal_rhs_variables.begin(); ci != equal_rhs_variables.end(); ci++)
	{
		binding_mapping_[std::make_pair((*ci).first, (*ci).second)] = &lhs_vd;
	}
/*
	// Next we need to make sure that all references to unequal variables are restored as the original pointer
	// might have changed due to the above merge.
	for (std::vector<VariableDomain*>::iterator ci = variable_domains_.begin(); ci != variable_domains_.end(); ci++)
	{
		std::vector<VariableDomain*>& unequals = (*ci)->getNonConstUnequalVariables();
		for (std::vector<VariableDomain*>::iterator ci2 = unequals.begin(); ci2 != unequals.end(); ci2++)
		{
			if (*ci2 == &rhs_vd)
			{
				unequals.erase(ci2);
				unequals.push_back(&lhs_vd);
				break;
			}
		}
	}
*/
}

StepID Bindings::getNextStep(StepID step_id)
{
	// Return the next available number.
	if (step_id == Step::INVALID_STEP)
	{
		step_id = next_free_step_id_++;
	}

	// Update the next number so it it always higher than the highest ever return.
	else
	{
		// Make sure that the number requested has not already been assigned!
		assert (next_free_step_id_ <= step_id);
		next_free_step_id_ = ++step_id;
	}

	// Sanity check, make sure we do not create a overflow.
	if (next_free_step_id_ == Step::INVALID_STEP)
	{
		std::cout << "We ran out of numbers to assign to steps!" << std::endl;
		assert(false);
	}

	return step_id;
}

std::ostream& operator<<(std::ostream& os, const Bindings& bindings)
{
	std::set<std::pair<StepID, const Variable*> > closed_list;

/*	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = bindings.binding_mapping_.begin(); ci != bindings.binding_mapping_.end(); ci++)
	{
		if (closed_list.find((*ci).first) != closed_list.end())
		{
			continue;
		}
		
		VariableDomain* variable_domain = (*ci).second;
		os << *variable_domain << std::endl;
		
		// Add all variables linked to this variable domain to the closed list, so we do not print
		// the same domain multiple times.
		for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci2 = variable_domain->getEqualVariables().begin(); ci2 != variable_domain->getEqualVariables().end(); ci2++)
		{
			closed_list.insert(std::make_pair((*ci2).first, (*ci2).second));
		}
	}*/
	os << "Bindings: " << bindings.binding_mapping_.size() << ", " << bindings.variable_domains_.size();
	return os;
}

};
