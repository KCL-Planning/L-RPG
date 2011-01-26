#include "term_manager.h"
#include "type_manager.h"
#include "logging.h"

namespace MyPOP {

/*************************
 * The Term class
 *************************/

Term::Term(bool is_object, const Object* object, const Variable* variable, const Type* type, const std::string& name)
	: is_object_(is_object), object_(object), variable_(variable), type_(type), name_(name)
{

}

std::ostream& operator<<(std::ostream& os, const Term& term)
{
	os << term.name_;
	//os << "[" << term.id_ << "] " << term.name_;
	//if (term.type_ != NULL)
	//	os << " : " << *term.type_;
	return os;
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
			Variable* var = new Variable(type, parameter->getName());
			addTerm(*parameter, *var);

			if (Logging::verbosity <= Logging::DEBUG)
			{
				std::cout << "!!!!!" << *var << std::endl;
			}
		}
	}
}

void TermManager::addTerm(const VAL::symbol& symbol, Term& term)
{
	addManagableObject(&term);
	(*term_indexing_)[&symbol] = &term;
	(*term_string_indexing_)[symbol.getName()] = &term;
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
		if ((*ci)->isObject())
		{
			os << **ci << std::endl;
		}
	}
	os << " === End of Summary ===" << std::endl;
	return os;
}

};
