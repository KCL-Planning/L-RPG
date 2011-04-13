#include "term_manager.h"
#include "type_manager.h"
#include "plan_bindings.h"

///#define MYPOP_TERM_MANAGER_COMMENTS

namespace MyPOP {

/*************************
 * The Term class
 *************************/

Term::Term(const Type& type, const std::string& name)
	: type_(&type), name_(name)
{

}

bool Term::isTheSameAs(StepID lhs_id, const Term& rhs, StepID rhs_id, const Bindings& bindings) const
{
	const std::vector<const Object*>& lhs_domain = getDomain(lhs_id, bindings);
	const std::vector<const Object*>& rhs_domain = rhs.getDomain(rhs_id, bindings);
	return &lhs_domain ==  &rhs_domain;
}

bool Term::isEquivalentTo(StepID lhs_id, const Term& rhs, StepID rhs_id, const Bindings& bindings) const
{
	const std::vector<const Object*>& lhs_domain = getDomain(lhs_id, bindings);
	const std::vector<const Object*>& rhs_domain = rhs.getDomain(rhs_id, bindings);
	
	if (lhs_domain.size() != rhs_domain.size())
	{
		return false;
	}
	
	for (std::vector<const Object*>::const_iterator ci = lhs_domain.begin(); ci != lhs_domain.end(); ci++)
	{
		const Object* lhs_object = *ci;
		bool found = false;
		for (std::vector<const Object*>::const_iterator ci = rhs_domain.begin(); ci != rhs_domain.end(); ci++)
		{
			const Object* rhs_object = *ci;
			
			if (lhs_object == rhs_object)
			{
				found = true;
				break;
			}
		}
		
		if (!found)
		{
			return false;
		}
	}
	
	return true;
}

bool Term::canUnify(StepID lhs_id, const Term& rhs, StepID rhs_id, const Bindings& lhs_bindings, const Bindings* rhs_bindings) const
{
	if (rhs_bindings == NULL)
	{
		rhs_bindings = &lhs_bindings;
	}
	
	const std::vector<const Object*>& lhs_domain = getDomain(lhs_id, lhs_bindings);
	const std::vector<const Object*>& rhs_domain = rhs.getDomain(rhs_id, *rhs_bindings);
	
	for (std::vector<const Object*>::const_iterator ci = lhs_domain.begin(); ci != lhs_domain.end(); ci++)
	{
		const Object* lhs_object = *ci;
		for (std::vector<const Object*>::const_iterator ci = rhs_domain.begin(); ci != rhs_domain.end(); ci++)
		{
			const Object* rhs_object = *ci;
			
			if (lhs_object == rhs_object)
			{
				return true;
			}
		}
	}
	
	return false;
}

bool Term::contains(const Object& object, StepID lhs_id, const Bindings& bindings) const
{
	const std::vector<const Object*>& domain = getDomain(lhs_id, bindings);
	for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
	{
		if (*ci == &object)
			return true;
	}
	
	return false;
}

bool Term::containsAtLeastOneOf(const std::vector<const Object*>& objects, StepID lhs_id, const Bindings& bindings) const
{
	for (std::vector<const Object*>::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
	{
		if (contains(**ci, lhs_id, bindings))
		{
			return true;
		}
	}
	return false;
}


std::ostream& operator<<(std::ostream& os, const Term& term)
{
	os << term.getName();
	return os;
}

/*************************
 * The Object class
 *************************/
Object::Object(const Type& type, const std::string& name)
	: Term(type, name)
{
	domain_.push_back(this);
}

Object::~Object()
{
	
}

bool Object::unify(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const
{
	return rhs.unifyWith(rhs_id, *this, bindings);
}

bool Object::makeDisjunct(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const
{
	// We cannot make an object disjunct from anything.
	if (rhs.contains(*this, rhs_id, bindings))
	{
		std::cout << "Cannot make an object disjunct from itself!" << std::endl;
		assert (false);
	}
	return false;
}

bool Object::makeDomainEqualTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings) const
{
	if (rhs_bindings == NULL)
	{
		rhs_bindings = &lhs_bindings;
	}

	// Not sure what to do if asked to make equal to a term which does not contain the object in its domain.
	if (!rhs.contains(*this, rhs_id, *rhs_bindings))
	{
		std::cout << "Cannot make an object equal to something that does not contain the object..." << std::endl;
		assert (false);
	}
	
	// We cannot manipulate the object.
	return false;
}

bool Object::makeDomainEqualTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const
{
	// Not sure what to do if we are asked to make an object equal to an empty set.
	for (std::vector<const Object*>::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
	{
		if (*ci == this)
		{
			return false;
		}
	}
	
	std::cout << "Tried to make the domain of an object empty." << std::endl;
	
	assert (false);
	return true;
}

bool Object::makeDomainUnequalTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings) const
{
	if (rhs_bindings == NULL)
	{
		rhs_bindings = &lhs_bindings;
	}

	if (rhs.contains(*this, rhs_id, *rhs_bindings))
	{
		std::cout << "Tried to make an object unequal to itself..." << std::endl;
		assert (false);
	}
	
	return false;
}

bool Object::makeDomainUnequalTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const
{
	for (std::vector<const Object*>::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
	{
		if (*ci == this)
		{
			std::cout << "Tried to make an object unequal to itself..." << std::endl;
			assert (false);
		}
	}
	
	return false;
}

const std::vector<const Object*>& Object::getDomain(StepID id, const Bindings& bindings) const
{
	return domain_;
}

bool Object::unifyWith(StepID lhs_id, const Object& object, Bindings& bindings) const
{
	return this == &object;
}

bool Object::unifyWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const
{
	return variable.unifyWith(rhs_id, *this, bindings);
}

bool Object::makeDisjunctWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const
{
	VariableDomain& vd = bindings.getNonConstVariableDomain(rhs_id, variable);
	return vd.makeUnequalTo(*this);
}

void Object::bind(Bindings& bindings, StepID new_step_id) const
{
	
}

void Object::print(std::ostream& os, const Bindings& bindings, StepID id) const
{
	os << getName();
}

/*************************
 * The Variable class
 *************************/
Variable::Variable(const Type& type, const std::string& name)
	: Term(type, name)
{
	
}

Variable::~Variable()
{
	
}

bool Variable::unify(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const
{
	return rhs.unifyWith(rhs_id, *this, lhs_id, bindings);
}

bool Variable::makeDisjunct(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& bindings) const
{
	return rhs.makeDisjunctWith(rhs_id, *this, lhs_id, bindings);
}

bool Variable::makeDomainEqualTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings) const
{
	if (rhs_bindings == NULL)
	{
		rhs_bindings = &lhs_bindings;
	}
	VariableDomain& vd = lhs_bindings.getNonConstVariableDomain(lhs_id, *this);
	return vd.makeEqualTo(rhs.getDomain(rhs_id, *rhs_bindings));
}

bool Variable::makeDomainEqualTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const
{
	VariableDomain& vd = bindings.getNonConstVariableDomain(lhs_id, *this);
	return vd.makeEqualTo(objects);
}

bool Variable::makeDomainUnequalTo(StepID lhs_id, const Term& rhs, StepID rhs_id, Bindings& lhs_bindings, Bindings* rhs_bindings) const
{
	if (rhs_bindings == NULL)
	{
		rhs_bindings = &lhs_bindings;
	}
	
	VariableDomain& vd = lhs_bindings.getNonConstVariableDomain(lhs_id, *this);
	return vd.makeUnequalTo(rhs.getDomain(rhs_id, *rhs_bindings));
}

bool Variable::makeDomainUnequalTo(StepID lhs_id, const std::vector<const Object*>& objects, Bindings& bindings) const
{
	VariableDomain& vd = bindings.getNonConstVariableDomain(lhs_id, *this);
	return vd.makeUnequalTo(objects);
}

const std::vector<const Object*>& Variable::getDomain(StepID id, const Bindings& bindings) const
{
	const VariableDomain& vd = bindings.getVariableDomain(id, *this);
	return vd.getDomain();
}

bool Variable::unifyWith(StepID lhs_id, const Object& object, Bindings& bindings) const
{
	VariableDomain& vd = bindings.getNonConstVariableDomain(lhs_id, *this);
	return vd.makeEqualTo(object);
}

bool Variable::unifyWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const
{
	if (isTheSameAs(lhs_id, variable, rhs_id, bindings))
	{
		return true;
	}

	if (!canUnify(lhs_id, variable, rhs_id, bindings))
//	if (!bindings.canUnify(*this, lhs_id, variable, rhs_id))
	{
		return false;
	}
	
/*	std::cout << "Unify two variables: ";
	print(std::cout, bindings, lhs_id);
	std::cout << "(" << this << ") with ";
	variable.print(std::cout, bindings, rhs_id);
	std::cout << "(" << &variable << ")" << std::endl;
*/
	VariableDomain& lhs_vd = bindings.getNonConstVariableDomain(lhs_id, *this);
	VariableDomain& rhs_vd = bindings.getNonConstVariableDomain(rhs_id, variable);
	
	if (lhs_vd.makeEqualTo(rhs_vd))
	{
		bindings.postProcessMerge(lhs_vd, rhs_vd);
	}
	
	//std::cout << "Result: " << result << std::endl;
	
	assert (isTheSameAs(lhs_id, variable, rhs_id, bindings));
	
	return true;
}

bool Variable::makeDisjunctWith(StepID lhs_id, const Variable& variable, StepID rhs_id, Bindings& bindings) const
{
	VariableDomain& lhs_vd = bindings.getNonConstVariableDomain(lhs_id, *this);
	VariableDomain& rhs_vd = bindings.getNonConstVariableDomain(rhs_id, variable);
	return lhs_vd.makeUnequalTo(rhs_vd);
}

void Variable::bind(Bindings& bindings, StepID new_step_id) const
{
	bindings.createVariableDomain(new_step_id, *this);
}

void Variable::print(std::ostream& os, const Bindings& bindings, StepID id) const
{
	const std::vector<const Object*>& domain = getDomain(id, bindings);
	os << "{";
	for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
	{
		os << **ci;
		if (ci != domain.end() - 1)
		{
			os << ", ";
		}
	}
	os << "}";
}

/*************************
 * The TermManager class
 *************************/

TermManager::TermManager(const TypeManager& type_manager)
	: type_manager_(&type_manager)
{
	// During processing map the pddl symbols to our internal types for 
	// easy access during the parsing phase. This indexing is removed
	// once we don't need it anymore, i.e. after the parsing phase.
	term_indexing_ = new std::map<const VAL::symbol*, const Term*>();
	term_string_indexing_ = new std::map<string, const Term*>();
}

TermManager::~TermManager()
{
	delete term_indexing_;
	delete term_string_indexing_;
	//for (std::map<const Type*, std::vector<const Object*>*>::const_iterator ci = objects_per_type_.begin(); ci != objects_per_type_.end(); ci++)
	//	delete (*ci).second;
}

void TermManager::processActionVariables(const VAL::operator_list& operators)
{
	for (VAL::operator_list::const_iterator ci = operators.begin(); ci != operators.end(); ci++)
	{
		const VAL::operator_* op = *ci;
		const VAL::var_symbol_list* parameters = op->parameters;
		//int var_counter = 0;
		for (VAL::var_symbol_list::const_iterator i = parameters->begin(); i != parameters->end(); i++)
		{
			VAL::var_symbol* parameter = *i;

			// Get the type of the parameter.
			const Type* type = type_manager_->getType(parameter->type->getName());
			Variable* var = new Variable(*type, parameter->getName());
			addTerm(*parameter, *var);
		}
	}
}

void TermManager::addTerm(const VAL::symbol& symbol, Term& term)
{
	addManagableObject(&term);
	(*term_indexing_)[&symbol] = &term;
	(*term_string_indexing_)[symbol.getName()] = &term;
}

void TermManager::addTerm(const VAL::symbol& symbol, Object& object)
{
	addTerm(symbol, (Term&)object);
	domain_objects_.push_back(&object);
}

const Term* TermManager::getTerm(const VAL::symbol& symbol) const
{
	return (*term_indexing_)[&symbol];
}

const Term* TermManager::getTerm(const std::string& name) const
{
	return (*term_string_indexing_)[name];
}

std::ostream& operator<<(std::ostream& os, const TermManager& term_manager)
{
	os << " === Summary of all Objects in the current domain. === " << std::endl;
	for (std::vector<Term*>::const_iterator ci = term_manager.getManagableObjects().begin(); ci != term_manager.getManagableObjects().end(); ci++)
	{
//		if ((*ci)->isObject())
//		{
			os << **ci << std::endl;
//		}
	}
	os << " === End of Summary ===" << std::endl;
	return os;
}

};
