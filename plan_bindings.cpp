#include <assert.h>
#include <set>

#include "plan_bindings.h"
#include "term_manager.h"
#include "predicate_manager.h"
#include "plan.h"
#include "logging.h"
#include "formula.h"
#include "exceptions.h"
#include "bindings_propagator.h"
#include "type_manager.h"
#include "action_manager.h"

namespace MyPOP {

/*************************
 * The VariableBinding class
 *************************/

bool VariableBinding::applyTo(Bindings& bindings) const
{
	if (make_equal_)
	{
		return bindings.merge(variable_step_id_, *variable_, to_variable_step_id_,*to_variable_);
	}
	else
	{
		return bindings.makeDistinct(variable_step_id_, *variable_, to_variable_step_id_,*to_variable_);
	}
	return true;
}

/*************************
 * The ObjectBinding class
 *************************/

bool ObjectBinding::applyTo(Bindings& bindings) const
{
	if (make_equal_)
	{
		return bindings.assign(variable_step_id_, *variable_, *object_);
	}
	else
	{
		return bindings.unassign(variable_step_id_, *variable_, *object_);
	}
	return true;
}

/*************************
 * The ObjectsBinding class
 *************************/

bool ObjectsBinding::applyTo(Bindings& bindings) const
{
	if (make_equal_)
	{
		return bindings.assign(variable_step_id_, *variable_, *objects_);
	}
	else
	{
		return bindings.unassign(variable_step_id_, *variable_, *objects_);
	}
}

/*************************
 * The VariableDomain class
 *************************/

VariableDomain::VariableDomain(const BindingsFacade& bindings, StepID step_id, const Variable& variable)
	: bindings_(&bindings)
{
	equal_variables_.push_back(std::make_pair(step_id, &variable));

	// Initialize the domain so it can be of any object of the correct type.
	if (variable.getType() != NULL)
	{
		populate(*variable.getType());
	}
}

VariableDomain::VariableDomain(const VariableDomain& other, const BindingsFacade& bindings)
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
	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "Restrict " << *this << " to " << variable_domain << std::endl;	
	}
	
	// Make sure we do not do the restriction if it is already in place. To do this, we will compare 
	// a step, variable pair from the given variable domain agains all those of this variable domain.
	StepID step = variable_domain.equal_variables_[0].first;
	const Variable& variable = *variable_domain.equal_variables_[0].second;

	bool already_included = false;
	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = equal_variables_.begin(); ci != equal_variables_.end(); ci++)
	{
		if (Logging::verbosity <= Logging::DEBUG)
		{
			std::cout << "Compare: " << (*ci).first << " == " << step << " && " << *(*ci).second << " == " << variable << std::endl;
		}
		
		if ((*ci).first == step && (*ci).second == &variable)
		{
			if (Logging::verbosity <= Logging::DEBUG)
			{
				std::cout << "EQUAL!" << std::endl;
			}
			already_included = true;
			break;
		}
	}
	if (already_included)
	{
		return false;
	}
	
	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "NOT EQUAL!" << std::endl;
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
		for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci2 = equal_variables_.begin(); ci2 != equal_variables_.end(); ci2++)
		{
			if ((*ci).first == (*ci2).first && (*ci).second == (*ci2).second)
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

	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "Result of merge: " << *this << std::endl;
	}
	
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
	//for (std::vector<const Object*>::const_iterator ci = other.domain_.begin(); ci != other.domain_.end(); ci++)
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

void VariableDomain::setObjects(std::vector<const Object*>& objects)
{
	domain_.clear();

	std::set<const Object*> new_objects;
	new_objects.insert(objects.begin(), objects.end());


	domain_.insert(domain_.begin(), new_objects.begin(), new_objects.end());
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
 * The BindingsFacade class
 *************************/

BindingsFacade::BindingsFacade(const TermManager& term_manager, const BindingsPropagator& propagator)
	: term_manager_(&term_manager), propagator_(&propagator), next_free_step_id_(0)
{

}

BindingsFacade::BindingsFacade(const BindingsFacade& other)
{
	std::cout << "BindingsFacade::BindingsFacade - copy " << other.binding_mapping_.size() << " bindings!" << std::endl;
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

BindingsFacade::~BindingsFacade()
{
	for (std::vector<VariableDomain*>::const_iterator ci = variable_domains_.begin(); ci != variable_domains_.end(); ci++)
	{
		delete *ci;
	}
}

const VariableDomain& BindingsFacade::getVariableDomain(StepID step_id, const Variable& variable) const
{
	std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.find(std::make_pair(step_id, &variable));
	if (ci == binding_mapping_.end())
	{
		
		for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator i = binding_mapping_.begin(); i != binding_mapping_.end(); i++)
		{
			std::pair<StepID, const Variable*> binding = (*i).first;
			std::cout << binding.first << " and " << *binding.second << std::endl;
		}
		
		if (Logging::verbosity <= Logging::ERROR)
		{
			std::cout << "Could not find the variable domain for: Step id: " << step_id << " " << variable << std::endl;
		}
		throw RequestNonExistingVariableBindingException();
	}
	return *(*ci).second;
}

VariableDomain& BindingsFacade::getNonConstVariableDomain(StepID step_id, const Variable& variable)
{
	return *const_cast<VariableDomain*>(&getVariableDomain(step_id, variable));
}

void BindingsFacade::getVariableDomains(std::vector<const VariableDomain*>& variable_domains, StepID step_id, const Atom& atom) const
{
	for (std::vector<const Term*>::const_iterator ci = atom.getTerms().begin(); ci != atom.getTerms().end(); ci++)
	{
		// Only retrieve the domains of actual variables. N.B. objects don't have variable domains.
		if ((*ci)->isVariable())
		{
			variable_domains.push_back(&getVariableDomain(step_id, *(*ci)->asVariable()));
		}
	}
}

void BindingsFacade::getVariableDomains(std::vector<VariableDomain*>& variable_domains, StepID step_id, const Atom& atom)
{
	for (std::vector<const Term*>::const_iterator ci = atom.getTerms().begin(); ci != atom.getTerms().end(); ci++)
	{
		// Only retrieve the domains of actual variables. N.B. objects don't have variable domains.
		if ((*ci)->isVariable())
		{
			variable_domains.push_back(&getNonConstVariableDomain(step_id, *(*ci)->asVariable()));
		}
	}
}

VariableDomain& BindingsFacade::createVariableDomain(StepID step_id, const Variable& variable)
{
	assert (step_id != Step::INVALID_STEP);

	assert (binding_mapping_.find(std::make_pair(step_id, &variable)) == binding_mapping_.end());

	VariableDomain* new_variable_domain = new VariableDomain(*this, step_id, variable);
	variable_domains_.push_back(new_variable_domain);
	binding_mapping_[std::make_pair(step_id, &variable)] = new_variable_domain;
	return *new_variable_domain;
}

StepID BindingsFacade::createVariableDomains(const Action& action, StepID step_id)
{
	step_id = getNextStep(step_id);

	const std::vector<const Variable*>& variables = action.getVariables();
	for (std::vector<const Variable*>::const_iterator ci = variables.begin(); ci != variables.end(); ci++)
	{
		createVariableDomain(step_id, **ci);
	}
	return step_id;
}

StepID BindingsFacade::createVariableDomains(const Atom& atom, StepID step_id)
{
	step_id = getNextStep(step_id);
	const std::vector<const Term*>& terms = atom.getTerms();
	for (std::vector<const Term*>::const_iterator ci = terms.begin(); ci != terms.end(); ci++)
	{
		const Term* term = *ci;
		// Only initialise the terms which are actually variables.
		if (term->isVariable())
		{
			createVariableDomain(step_id, *term->asVariable());
		}
	}

	return step_id;
}

void BindingsFacade::removeBindings(StepID step)
{
	bool changed = true;
	
	// N^2 algorithm, but I'm not caring. reverse iterator doesn't play nice :(.
	while (changed)
	{
		changed = false;
		for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::iterator i = binding_mapping_.begin(); i != binding_mapping_.end(); i++)
		{
			std::pair<StepID, const Variable*> key = (*i).first;
			if (key.first == step)
			{
				// Remove this entry from the variable domain.
				(*i).second->removeVariable(step);
				binding_mapping_.erase(i);
				changed = true;
				break;
			}
		}
	}
}

bool BindingsFacade::canUnify(const Term& term1, StepID step1, const Term& term2, StepID step2, const BindingsFacade* other_bindings) const
{
	// Check if the second term is bound to this BindingsFacade or another one.
	if (other_bindings == NULL)
	{
		other_bindings = this;
	}
	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << term1.isVariable() << " and " << term2.isVariable() << std::endl;
	}

	// Two objects can only unify if they are exactly the same!
	if (term1.isObject() && term2.isObject())
	{
		if (Logging::verbosity <= Logging::DEBUG)
		{
			if (&term1 != &term2)
			{
				std::cout << term1 << " and " << term2 << " are different objects!" << std::endl;
			}
			else
			{
				std::cout << term1 << " and " << term2 << " are the same objects!" << std::endl;
			}
		}
		return (&term1 == &term2);
	}

	// If one of the two is a variable, check if the object is in the variable's domain.
	const Variable* variable = NULL;
	const Object* object = NULL;
	StepID step = Step::INVALID_STEP;
	const BindingsFacade* bindings = NULL;
	if (term1.isObject() && term2.isVariable())
	{
		object = term1.asObject();
		variable = term2.asVariable();
		step = step2;
		bindings = other_bindings;
	}
	else if (term1.isVariable() && term2.isObject())
	{
		object = term2.asObject();
		variable = term1.asVariable();
		step = step1;
		bindings = this;
	}

	// Otherwise, both terms are variables, check if the intersections of their domains is not empty.
	else
	{
		const VariableDomain& domain1 = getVariableDomain(step1, *term1.asVariable());
		const VariableDomain& domain2 = other_bindings->getVariableDomain(step2, *term2.asVariable());
		
		bool empty_intersection = domain1.isEmptyIntersection(domain2);

		if (Logging::verbosity <= Logging::INFO)
		{
			if (empty_intersection)
			{
				std::cout << "Domain is empty, could not unify " << domain1 << " and " << domain2 <<std::endl;
			}
		}

		return !empty_intersection;
	}

	// Check if the variable contains the given object in its set.
	const VariableDomain& domain = bindings->getVariableDomain(step, *variable);
	
	bool contains_object = domain.contains(*object);
	if (Logging::verbosity <= Logging::INFO)
	{
		if (!contains_object)
		{
			std::cout << "Domain is empty, " << *object << " was no part of the domain of " << domain <<std::endl;
		}
	}
	return contains_object;
}

bool BindingsFacade::unify(const Term& term1, StepID step1, const Term& term2, StepID step2, const BindingsFacade* other_bindings)
{
	if (other_bindings == NULL)
	{
		other_bindings = this;
	}

	// Check if we can unify the terms.
	if (!canUnify(term1, step1, term2, step2, other_bindings))
	{
		return false;
	}

	// If both terms are objects we know they are the same so we're done.
	if (term1.isObject() && term2.isObject())
	{
		return true;
	}

	// If one of the two is a variable, check if the object is in the variable's domain.
	const Variable* variable = NULL;
	const Object* object = NULL;
	StepID step = Step::INVALID_STEP;
	if (term1.isObject() && term2.isVariable())
	{
		object = term1.asObject();
		variable = term2.asVariable();
		step = step2;
	}
	else if (term1.isVariable() && term2.isObject())
	{
		object = term2.asObject();
		variable = term1.asVariable();
		step = step1;
	}

	// Both terms are variables so restrict their respective domains to they become the same.
	else
	{
		if (other_bindings == this)
		{
			VariableBinding vb(step1, *term1.asVariable(), step2, *term2.asVariable(), true);
			return addBinding(vb);
		}
		else
		{
			const VariableDomain& other_variable_domain = other_bindings->getVariableDomain(step2, *term2.asVariable());
			const std::vector<const Object*>& objects = other_variable_domain.getDomain();
			ObjectsBinding ob(step1, *term1.asVariable(), objects, true);
			return addBinding(ob);
		}
	}

	ObjectBinding ob(step, *variable, *object, true);
	return addBinding(ob);
}

bool BindingsFacade::canUnify(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2, const BindingsFacade* other_bindings) const
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
		if (!canUnify(*atom1.getTerms()[i], step1, *atom2.getTerms()[i], step2, other_bindings))
		{
			return false;
		}
	}
	
	return true;
}

bool BindingsFacade::unify(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2, const BindingsFacade* other_bindings)
{
	if (!canUnify(atom1, step1, atom2, step2, other_bindings))
		return false;

	// Only return true if all the pairs of terms of the atoms can be unified.
	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		if (!unify(*atom1.getTerms()[i], step1, *atom2.getTerms()[i], step2, other_bindings))
		{
			return false;
		}
	}
	
	return true;
}

bool BindingsFacade::canUnify(const Action& action1, StepID step1, const Action& action2, StepID step2, const BindingsFacade* other_bindings) const
{
	// Make sure the predicates are the same.
	if (action1.getPredicate() != action2.getPredicate())
	{
		return false;
	}
	
	// Only return true if all the pairs of terms of the atoms can be unified.
	for (unsigned int i = 0; i < action1.getVariables().size(); i++)
	{
		if (!canUnify(*action1.getVariables()[i], step1, *action2.getVariables()[i], step2, other_bindings))
		{
			return false;
		}
	}
	
	return true;
}

bool BindingsFacade::makeEqual(const Atom& atom1, StepID step1, const Atom& atom2, StepID step2, const BindingsFacade* other_bindings)
{
	if (!canUnify(atom1, step1, atom2, step2, other_bindings))
	{
		return false;
	}
	
	std::cout << "Make equal: ";
	atom1.print(std::cout, *this, step1);
	std::cout << " and ";
	atom2.print(std::cout, (other_bindings == NULL ? *this : *other_bindings), step2);
	std::cout << std::endl;
	
	// Only return true if all the pairs of terms of the atoms can be unified.
	for (unsigned int i = 0; i < atom1.getArity(); i++)
	{
		assert (makeEqual(*atom1.getTerms()[i], step1, *atom2.getTerms()[i], step2, other_bindings));
	}
	return true;
}

bool BindingsFacade::makeEqual(const Term& term1, StepID step1, const Term& term2, StepID step2, const BindingsFacade* other_bindings)
{
	if (!canUnify(term1, step1, term2, step2, other_bindings))
	{
		return false;
	}
	
	if (other_bindings == NULL)
	{
		other_bindings = this;
	}
	
	if (term1.isObject() && term2.isObject())
	{
		return true;
	}

	// If one of the two is a variable, check if the object is in the variable's domain.
	const Variable* variable = NULL;
	const Object* object = NULL;
	StepID step = Step::INVALID_STEP;
	if (term1.isObject() && term2.isVariable())
	{
		object = term1.asObject();
		variable = term2.asVariable();
		step = step2;
	}
	else if (term1.isVariable() && term2.isObject())
	{
		object = term2.asObject();
		variable = term1.asVariable();
		step = step1;
	}

	// Both terms are variables so restrict their respective domains to they become the same.
	else
	{
		const VariableDomain& variable_domain = getVariableDomain(step1, *term1.asVariable());
		const VariableDomain& other_variable_domain = other_bindings->getVariableDomain(step2, *term2.asVariable());
		
		std::cout << variable_domain << " v.s. " << other_variable_domain << std::endl;
		
		ObjectsBinding ob1(step1, *term1.asVariable(), other_variable_domain.getDomain(), true);
		ObjectsBinding ob2(step2, *term2.asVariable(), variable_domain.getDomain(), true);
		
		bool domain_changed = addBinding(ob1);
		domain_changed = addBinding(ob2) || domain_changed;
		
		return domain_changed;
	}

	ObjectBinding ob(step, *variable, *object, true);
	return addBinding(ob);
}

bool BindingsFacade::affects(const Atom& atom1, StepID step1, const Atom& atom2, const StepID step2) const
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

		// We do not need to check the type as this is implicitly done by the canUnify
		// function. This checks if the intersection of the variable domains for the
		// terms is empty. If not than we know that they share a common sub type.
/*		if (term1->getType() != term2->getType())
		{
			terms_differ = true;
			break;
		}
*/
		if (!canUnify(*term1, step1, *term2, step2))
		{
			terms_differ = true;
			break;
		}
	}
	if (terms_differ)
	{
		return false;
	}

	if (Logging::verbosity <= Logging::DEBUG)
	{
		atom1.print(std::cout);
		std::cout << "[" << step1 << "] affects ";
		atom2.print(std::cout);
		std::cout << "[" << step2 << "]" << std::endl;
	}

	return true;
}

StepID BindingsFacade::getNextStep(StepID step_id)
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

std::ostream& operator<<(std::ostream& os, const BindingsFacade& bindings)
{
	/*
	for (std::vector<VariableDomain*>::const_iterator ci = bindings.variable_domains_.begin(); ci != bindings.variable_domains_.end(); ci++)
	{
		os << **ci << std::endl;
	}
	*/

//	os << " v.s. " << std::endl;

	std::set<std::pair<StepID, const Variable*> > closed_list;

	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = bindings.binding_mapping_.begin(); ci != bindings.binding_mapping_.end(); ci++)
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
	}
	return os;
}

/*************************
 * The Bindings class
 *************************/

Bindings::Bindings(const TermManager& term_manager, const BindingsPropagator& propagator)
	: BindingsFacade(term_manager, propagator)
{

}

Bindings::Bindings(const BindingsFacade& other)
	: BindingsFacade(other)
{

}

Bindings::Bindings(const Bindings& other)
	: BindingsFacade(other)
{

}

Bindings::~Bindings()
{

}

bool Bindings::addBinding(const Binding& binding)
{
	//return binding.applyTo(*this);

	assert (binding.applyTo(*this));
/*	const Bindings* new_binding = new Bindings(*this);

	if (!binding.applyTo(*this))
	{
		delete new_binding;
		return false;
	}
*/
	
	// Applying the binding should invoke the propagator which must take take of the bindings constrains and return false
	// if a domain becomes empty.
/*	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.begin(); ci != binding_mapping_.end(); ci++)
	{
		if ((*ci).second->getDomain().size() == 0)
		{
			std::cout << "[Before] Bindings: " << *new_binding << std::endl;
			std::cout << "[After] Bindings: " << *this << std::endl;
			assert (false);
		}
	}*/
	
//	delete new_binding;
	return true;
}

bool Bindings::merge(StepID root_step, const Variable& root_variable, StepID leaf_step, const Variable& leaf_variable)
{
	// Make sure the domains are merged.
	VariableDomain& root_variable_domain = getNonConstVariableDomain(root_step, root_variable);
	const VariableDomain& leaf_variable_domain = getVariableDomain(leaf_step, leaf_variable);

	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "Merge " << root_variable_domain << " and " << leaf_variable_domain << std::endl;
	}
	if (&root_variable_domain == &leaf_variable_domain)
	{
		return true;
	}

	// Make sure the variable domain we want to merge with is not in the unequal list.
	const std::vector<VariableDomain*> unequals = root_variable_domain.getUnequalVariables();
	for (std::vector<VariableDomain*>::const_iterator ci = unequals.begin(); ci != unequals.end(); ci++)
	{
		if (*ci == &leaf_variable_domain)
		{
			return false;
		}
	}

	bool domain_has_changed = root_variable_domain.makeEqualTo(leaf_variable_domain);

	// Update the pointers in the mapping so the 'leaf' is merged into the 'root'.
	const std::vector<std::pair<StepID, const Variable*> >& equal_leaf_variables = leaf_variable_domain.getEqualVariables();
	for (std::vector<std::pair<StepID, const Variable*> >::const_iterator ci = equal_leaf_variables.begin(); ci != equal_leaf_variables.end(); ci++)
	{
		binding_mapping_[std::make_pair((*ci).first, (*ci).second)] = &root_variable_domain;
	}
	assert (&getVariableDomain(leaf_step, leaf_variable) == &root_variable_domain);

	// Next we need to make sure that all references to unequal variables are restored as the original pointer
	// might have changed due to the above merge.
	for (std::vector<VariableDomain*>::iterator ci = variable_domains_.begin(); ci != variable_domains_.end(); ci++)
	{
		std::vector<VariableDomain*>& unequals = (*ci)->getNonConstUnequalVariables();
		for (std::vector<VariableDomain*>::iterator ci2 = unequals.begin(); ci2 != unequals.end(); ci2++)
		{
			if (*ci2 == &leaf_variable_domain)
			{
				unequals.erase(ci2);
				unequals.push_back(&root_variable_domain);
				break;
			}
		}
	}

	// Make sure all bindings have been updated.
/*	for (std::map<std::pair<StepID, const Variable*>, VariableDomain*>::const_iterator ci = binding_mapping_.begin(); ci != binding_mapping_.end(); ci++)
	{
		if ((*ci).second == &leaf_variable_domain)
		{
			assert(false);
		}
	}*/
	
	if (domain_has_changed)
	{
		return propagator_->propagateAfterMakeEqual(*this, root_variable_domain, leaf_variable_domain);
	}

	return true;
}

bool Bindings::makeDistinct(StepID root_step, const Variable& root_variable, StepID leaf_step, const Variable& leaf_variable)
{
	VariableDomain& root_variable_domain = getNonConstVariableDomain(root_step, root_variable);
	VariableDomain& leaf_variable_domain = getNonConstVariableDomain(leaf_step, leaf_variable);

	// Make sure the domains are not the same, otherwise we will end up with empty domains.
	if (&root_variable_domain == &leaf_variable_domain)
	{
		return false;
	}

	if (root_variable_domain.makeUnequalTo(leaf_variable_domain))
	{
		return propagator_->propagateAfterMakeUnequal(*this, root_variable_domain, leaf_variable_domain);
	}
	return true;
}

bool Bindings::assign(StepID step, const Variable& variable, const Object& object)
{
	VariableDomain& variable_domain = getNonConstVariableDomain(step, variable);
	if (variable_domain.makeEqualTo(object))
	{
		return propagator_->propagateAfterMakeEqual(*this, variable_domain, object);
	}

	return true;
}

bool Bindings::assign(StepID step, const Variable& variable, const std::vector<const Object*>& objects)
{
	VariableDomain& variable_domain = getNonConstVariableDomain(step, variable);
	if (variable_domain.makeEqualTo(objects))
	{
		return propagator_->propagateAfterMakeEqual(*this, variable_domain, objects);
	}

	return true;
}

bool Bindings::unassign(StepID step, const Variable& variable, const Object& object)
{
	VariableDomain& variable_domain = getNonConstVariableDomain(step, variable);
	if (variable_domain.makeUnequalTo(object))
	{
		return propagator_->propagateAfterMakeUnequal(*this, variable_domain, object);
	}

	return true;
}

bool Bindings::unassign(StepID step, const Variable& variable, const std::vector<const Object*>& objects)
{
	VariableDomain& variable_domain = getNonConstVariableDomain(step, variable);
	if (variable_domain.makeUnequalTo(objects))
	{
		return propagator_->propagateAfterMakeUnequal(*this, variable_domain, objects);
	}

	return true;
}

};
