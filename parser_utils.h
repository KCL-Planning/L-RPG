#ifndef MYPOP_UTILITY_H
#define MYPOP_UTILITY_H

#include <vector>
#include "VALfiles/ptree.h"
#include "VALfiles/TimSupport.h"

namespace MyPOP {

class TypeManager;
class TermManager;
class PredicateManager;
class Atom;
class Formula;
class Predicate;
class Equality;

/**
 * The functions in this namespace are only used during the parsing phase when we need to translate
 * classes from the VAL parser into our own. Once the planning starts these functions won't be used
 * anymore.
 */
namespace Utility {

// Translate a VAL::goal into a formula used by our planner internaly.
const Formula* convertGoal(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::goal* precondition, bool make_negative);

// Convert a VAL::proposition into an atom used by our planner internaly.
Atom* convertToAtom(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::proposition& prop, bool make_negative);

// Convert a VAL::proposition into an atom used by our planner internaly.
Formula* convertPrecondition(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::proposition& prop, bool make_negative);

// Convert a set of effects into an array of pointers to Atoms. The return value is the size of the array.
// All possible effects are:
// * pc_list<simple_effect*> add_effects;
// * pc_list<simple_effect*> del_effects;
// * pc_list<forall_effect*> forall_effects; [not supported]
// * pc_list<cond_effect*>   cond_effects; [not supported]
// * pc_list<cond_effect*>   cond_assign_effects; [not supported]
// * pc_list<assignment*>    assign_effects; [not supported]
// * pc_list<timed_effect*>  timed_effects; [not supported]
void convertEffects(const TermManager& term_manager, const PredicateManager& predicate_manager, const VAL::effect_lists& effects, std::vector<const Atom*>& action_effects);

// Most of the time we want to access the preconditions of an action by looking at its Atoms
// this function will take a formula and return all the atoms which must be made true to satisfy
// the formula. However, not all preconditions are handled (e.g. the Equality precondition). So
// use with care!
void convertFormula(std::vector<const Atom*>& atoms, const Formula* formula);

void convertFormula(std::vector<const Atom*>& atoms, std::vector<const Equality*>& equalities, const Formula* formula);

// Take a TIM::Property and using the name of the predicate and the types of its arguments we
// can find the Predicate object we use internally.
//std::pair<unsigned int, const Predicate*> getPredicate(const TypeManager& type_manager, const PredicateManager& predicate_manager, const TIM::PropertyState& property_state);
const Predicate& getPredicate(const TypeManager& type_manager, const PredicateManager& predicate_manager, const TIM::Property& property);
};

};

#endif
