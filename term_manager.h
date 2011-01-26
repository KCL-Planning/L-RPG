#ifndef MYPOP_TERM_MANAGER_H
#define MYPOP_TERM_MANAGER_H

#include <string>
#include <ostream>
#include <assert.h>
#include "VALfiles/ptree.h"
#include "manager.h"

namespace MyPOP {

class Type;
class TypeManager;
class Object;
class Variable;

/**
 * A term can either be an object in which case it is part of an atom
 * of in the domain of a variable, which is a parameter of an action
 * which contains a set of values it can take.
 */
class Term : public ManageableObject {//<Term> {
public:
	Term() {}

	virtual ~Term() {};

	// Get the type of this term.
	const Type* getType() const { return type_; }

	// Get the name of this term.
	const std::string& getName() const { return name_; }

	// Check if this term is an object, if not it is a variable.
	bool isObject() const { return is_object_; }

	// Check if this term is a variable, if not it is an object.
	bool isVariable() const { return !is_object_; }

	// Return the term as an object.
	const Object* asObject() const { assert(isObject()); return object_; }
	const Variable* asVariable() const { assert (isVariable()); return variable_; }

protected:
	Term(bool is_object, const Object* object, const Variable* variable, const Type* type, const std::string& name);

private:

	bool is_object_;

	// Stupid hack...
	const Object* object_;
	const Variable* variable_;

	const Type* type_;
	const std::string name_;


friend std::ostream& operator<<(std::ostream& os, const Term& term);
};

std::ostream& operator<<(std::ostream& os, const Term& term);

class Object : public Term {
public:
	Object() {}
	virtual ~Object() {}

	Object(const Type* type, const std::string& name)
		: Term(true, this, NULL, type, name) {}
};

class Variable : public Term {
public:
	Variable() {}
	virtual ~Variable() {}

	Variable(const Type* type, const std::string& name)
		: Term(false, NULL, this, type, name) {}
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

	// Get the term object linked to the VAL::symbol as processed by the parser. Note 
	// that this function can only be called during the parsing phase, afterwards all references
	// to VAL::symbol are deleted.
	const Term* getTerm(const VAL::symbol&) const;
	const Term* getTerm(const std::string& name) const;
	
	// Return the type manager.
	const TypeManager& getTypeManager() const { return *type_manager_; }

private:
	const TypeManager* type_manager_;

	// During construction of the types keep track of the indexing from the
	// symbol type to TermID.
	std::map<const VAL::symbol*, const Term*>* term_indexing_;
	std::map<std::string, const Term*>* term_string_indexing_;
};

std::ostream& operator<<(std::ostream& os, const TermManager& term_manager);

};

#endif
