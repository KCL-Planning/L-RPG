#ifndef MYPOP_ACTION_MANAGER
#define MYPOP_ACTION_MANAGER

#include <vector>
#include "VALfiles/ptree.h"
#include "manager.h"
#include "pointers.h"
#include "plan_types.h"

namespace MyPOP {

class TypeManager;
class TermManager;
class PredicateManager;
class Variable;
class Formula;
class Atom;
class Bindings;
class Term;

/**
 * PDDL Type.
 * Internally every type is assigned a bit in a bit array equal in length to the number
 * of the total number of types. Checks for super- / subtypes are done by bitcomparison,
 * check the relevant methods for a detailed explanation.
 */
class Action : public ManageableObject {

public:

	static Action* dummy_action;

	// Construct an action.
	Action(const std::string& precicate, const Formula& precondition, const std::vector<const Variable*>* variables, const std::vector<const Atom*>* effects);

	// Get the predicate.
	const std::string& getPredicate() const { return predicate_; }

	// Get the precondition of this actions.
	const Formula& getPrecondition() const { return *precondition_; }

	// Get the effects of this action.
	const std::vector<const Atom*>& getEffects() const { return *effects_; }

	// Get the variables of this action.
	const std::vector<const Variable*>& getVariables() const { return *variables_; }

	// Check which effects of this action can satisfy the given atom and add all these to the
	// vector 'achieving_effects'. This is a static check and will not consider the context 
	// (e.g. the domains of the variables).
	void getAchievingEffects(const Atom& atom, std::vector<const Atom*>& achieving_effects) const;
	
	// Get the index of an effect's term.
	unsigned int getActionVariable(unsigned int effect_index, unsigned int effect_term_index) const;
	
	// Get the index of the action variable which matches with the given term.
	unsigned int getActionVariable(const Term& term) const;

	// Destructor.
	virtual ~Action();

	// Print the action by subsituting the action variables with the set of objects.
	void print(std::ostream& os, const Bindings& bindings, StepID step_id) const;

	// Print the action in a human readable form.
	friend std::ostream& operator<<(std::ostream& os, const Action& action);

private:
	// The predicate.
	std::string predicate_;

	// The precondition.
	const Formula* precondition_;

	// The variables of the action.
	const std::vector<const Variable*>* variables_;

	// The effects.
	const std::vector<const Atom*>* effects_;
	
	// Mapping from variables to effects.
	std::vector<std::vector<unsigned int>* > effect_terms_to_action_variable_mappings_;
};

std::ostream& operator<<(std::ostream& os, const Action& action);

/**
 * All actions in the current domain are stored by this manager.
 */
class ActionManager : public Manager<Action> {

public:
	// Constructor.
	ActionManager(const TypeManager& type_manager, TermManager& term_manager, const PredicateManager& predicate_manager);
	virtual ~ActionManager();

	// After parsing the domain and problem files we pass all the types to the TypeManager
	// to store them into our own structure.
	void processActions(const VAL::operator_list& operators);

	// Return the set of actions which can accomplish a certain atom.
	void getAchievingActions(std::vector<std::pair<const Action*, const Atom*> >& actions, const Atom& atom) const;

	// For preprocessing purposes only! After the preprocessing is done this function should
	// not be called again. It retrieves the constructed action based on the given VAL::operator_.
	const Action& getAction(const VAL::operator_& val_operator) const;

	// Do the unthinkable! Ground an action. A grounded action will only have a single object
	// assigned to each of its variable domains.
	void ground(Bindings& bindings, std::vector<const Step*>& grounded_actions, const Action& action) const;

private:
	const TypeManager* type_manager_;
	TermManager* term_manager_;
	const PredicateManager* predicate_manager_;
	

	// For preprocess purposes we map the instances of VAL::operator to the Action objects
	// LolliPOP uses for planning.
	std::map<const VAL::operator_*, const Action*> action_indexing_;
};

};

#endif
