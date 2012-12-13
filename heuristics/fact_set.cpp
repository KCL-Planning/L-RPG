#include "fact_set.h"
#include <term_manager.h>
#include <type_manager.h>
#include <formula.h>
#include <action_manager.h>
#include <utility/memory_pool.h>
#include <parser_utils.h>

#include <set>
#include <map>
#include <predicate_manager.h>

//#define MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS

namespace MyPOP {

namespace HEURISTICS {

VariableDomain::VariableDomain()
{
	
}

VariableDomain::VariableDomain(const std::vector<const Object*>& variable_domain)
{
	variable_domain_.insert(variable_domain_.end(), variable_domain.begin(), variable_domain.end());
	std::sort(variable_domain_.begin(), variable_domain_.end());
}

VariableDomain::~VariableDomain()
{
	
}

bool VariableDomain::sharesObjectsWith(const VariableDomain& rhs) const
{
	for (std::vector<const Object*>::const_iterator ci = variable_domain_.begin(); ci != variable_domain_.end(); ++ci)
	{
		const Object* object = *ci;
		if (rhs.contains(*object))
		{
			return true;
		}
	}
	return false;
}

void VariableDomain::getIntersection(VariableDomain& result, const VariableDomain& rhs) const
{
	for (std::vector<const Object*>::const_iterator ci = variable_domain_.begin(); ci != variable_domain_.end(); ++ci)
	{
		const Object* object = *ci;
		if (rhs.contains(*object))
		{
			result.addObject(*object);
		}
	}
}

bool VariableDomain::contains(const Object& object) const
{
	for (std::vector<const Object*>::const_iterator ci = variable_domain_.begin(); ci != variable_domain_.end(); ++ci)
	{
		if (*ci == &object)
		{
			return true;
		}
	}
	
	return false;
}

void VariableDomain::set(const std::vector<const Object*>&  set)
{
	variable_domain_.clear();
	variable_domain_.insert(variable_domain_.end(), set.begin(), set.end());
	std::sort(variable_domain_.begin(), variable_domain_.end());
}

void VariableDomain::addObject(const Object& object)
{
	assert (std::find(variable_domain_.begin(), variable_domain_.end(), &object) == variable_domain_.end());
	variable_domain_.push_back(&object);
	std::sort(variable_domain_.begin(), variable_domain_.end());
}

bool VariableDomain::operator!=(const VariableDomain& rhs) const
{
	return !(*this == rhs);
}

bool VariableDomain::operator==(const VariableDomain& rhs) const
{
	if (variable_domain_.size() != rhs.variable_domain_.size())
	{
		return false;
	}
	
	for (unsigned int i = 0; i < variable_domain_.size(); ++i)
	{
		if (variable_domain_[i] != rhs.variable_domain_[i])
		{
			return false;
		}
	}
	
	return true;
}

std::ostream& operator<<(std::ostream& os, const VariableDomain& variable_domain)
{
	os << "{";
	for (std::vector<const Object*>::const_iterator ci = variable_domain.getVariableDomain().begin(); ci != variable_domain.getVariableDomain().end(); ++ci)
	{
		os << **ci << " ";
	}
	os << "}";
	return os;
}

Fact::Fact(const PredicateManager& predicate_manager, const Predicate& predicate, const std::vector<const VariableDomain*>& variable_domains)
{
	std::vector<const Type*> types;
	
	//variable_domains_.insert(variable_domains_.end(), variable_domains.begin(), variable_domains.end());
	for (std::vector<const VariableDomain*>::const_iterator ci = variable_domains.begin(); ci != variable_domains.end(); ++ci)
	{
		const VariableDomain* variable_domain = *ci;
		variable_domains_.push_back(new VariableDomain(variable_domain->getVariableDomain()));
		
		const Type* encompassing_type = NULL;
		for (std::vector<const Object*>::const_iterator ci = variable_domain->getVariableDomain().begin(); ci != variable_domain->getVariableDomain().end(); ++ci)
		{
			const Object* object = *ci;
			const Type* object_type = object->getType();
			if (encompassing_type == NULL)
			{
				encompassing_type = object_type;
			}
			else
			{
				while (!encompassing_type->isEqual(*object_type) && !encompassing_type->isSupertypeOf(*object_type))
				{
					encompassing_type = encompassing_type->getSupertype();
				}
			}
		}
		
		types.push_back(encompassing_type);
	}
	
	predicate_ = predicate_manager.getPredicate(predicate.getName(), types);
	assert (predicate_ != NULL);
}

Fact::Fact(const Fact& other)
	: predicate_(other.predicate_)
{
	for (std::vector<const VariableDomain*>::const_iterator ci = other.variable_domains_.begin(); ci != other.variable_domains_.end(); ++ci)
	{
		variable_domains_.push_back(new VariableDomain(**ci));
	}
}

Fact::~Fact()
{
	for (std::vector<const VariableDomain*>::const_iterator ci = variable_domains_.begin(); ci != variable_domains_.end(); ++ci)
	{
		delete *ci;
	}
}

void Fact::setVariableDomain(unsigned int term_index, const VariableDomain& variable_domain)
{
//		delete variable_domains_[term_index];
	assert (variable_domains_.size() > term_index);
	variable_domains_[term_index] = &variable_domain;
}

bool Fact::canUnifyWith(const Fact& fact) const
{
	if (predicate_->getName() != fact.predicate_->getName() ||
	    predicate_->getArity() != fact.predicate_->getArity())
	{
		return false;
	}
	
	for (unsigned int i = 0; i < predicate_->getArity(); ++i)
	{
		const VariableDomain* variable_domain = variable_domains_[i];
		const VariableDomain* other_variable_domain = fact.variable_domains_[i];
		
		if (!variable_domain->sharesObjectsWith(*other_variable_domain))
		{
			return false;
		}
	}
	return true;
}

bool Fact::operator==(const Fact& rhs) const
{
	if (predicate_->getArity() != rhs.predicate_->getArity() ||
	    predicate_->getName() != rhs.predicate_->getName())
	{
		return false;
	}
	
	for (unsigned int i = 0; i < variable_domains_.size(); ++i)
	{
		if (*variable_domains_[i] != *rhs.variable_domains_[i])
		{
			return false;
		}
	}
	return true;
}

std::ostream& operator<<(std::ostream& os, const Fact& fact)
{
	os << "(" << fact.getPredicate().getName();
	for (std::vector<const VariableDomain*>::const_iterator ci = fact.getVariableDomains().begin(); ci != fact.getVariableDomains().end(); ++ci)
	{
		os << **ci << " ";
	}
	os << ")";
	return os;
}

TransitionFact::TransitionFact(const PredicateManager& predicate_manager, const Predicate& predicate, const std::vector<const VariableDomain*>& variable_domains, const std::vector<const Term*>& variables)
	: Fact(predicate_manager, predicate, variable_domains)
{
	action_variables_.insert(action_variables_.end(), variables.begin(), variables.end());
}

TransitionFact::~TransitionFact()
{
	//for (
}

bool TransitionFact::operator==(const TransitionFact& rhs) const
{
	if (!Fact::operator==(rhs))
	{
		return false;
	}
	
	for (unsigned int i = 0; i < variable_domains_.size(); ++i)
	{
		for (unsigned int j = 0; j < variable_domains_.size(); ++j)
		{
			if ((variable_domains_[i] == variable_domains_[j] &&
			    rhs.variable_domains_[i] != rhs.variable_domains_[j]) ||
			    (variable_domains_[i] != variable_domains_[j] &&
			    rhs.variable_domains_[i] == rhs.variable_domains_[j]))
			{
				return false;
			}
		}
	}
	return true;
}

std::ostream& operator<<(std::ostream& os, const TransitionFact& transition_fact)
{
	os << "(" << transition_fact.getPredicate().getName();
	for (unsigned int i = 0; i < transition_fact.getVariableDomains().size(); ++i)
	{
		os << *transition_fact.getVariableDomains()[i] << "[" << transition_fact.action_variables_[i] << "] ";
	}
	os << ")";
	return os;
}

FactSet::FactSet()
{
	
}

FactSet::~FactSet()
{
	for (std::vector<const TransitionFact*>::const_iterator ci = getFacts().begin(); ci != getFacts().end(); ++ci)
	{
		delete *ci;
	}
}

const std::map<const TransitionFact*, const TransitionFact*>* FactSet::findBijection(const FactSet& other) const
{
	if (facts_.size() != other.facts_.size())
	{
		return NULL;
	}
/*
	std::cout << std::endl;
	std::cout << " === FactSet::findBijection === " << std::endl;
	std::cout << std::endl;
*/
//	assert (this != &other);
	
	std::map<const TransitionFact*, const TransitionFact*> variable_domain_bijection;
	std::map<const Term*, const Term*> variable_bijection;
	const std::map<const TransitionFact*, const TransitionFact*>* bijection = findBijection(0, other, variable_domain_bijection, variable_bijection);
	
/*
	if (bijection == NULL)
	{
		bool match = true;
		for (unsigned int i = 0; i < facts_.size(); ++i)
		{
			if ((const Fact*)(facts_[i]) != (const Fact*)(other.facts_[i]))
			{
				match = false;
				break;
			}
		}
		
		assert (!match);
	}
*/
	return bijection;
}

const std::map<const TransitionFact*, const TransitionFact*>* FactSet::findBijection(unsigned int current_fact_index, const FactSet& other, const std::map<const TransitionFact*, const TransitionFact*>& variable_domain_bijection, const std::map<const Term*, const Term*>& variable_bijection) const
{
/*	std::cout << current_fact_index << " - [FactSet::findBijection] Between" << std::endl << *this << std::endl << "And" << std::endl << other << std::endl;
	for (std::map<const TransitionFact*, const TransitionFact*>::const_iterator ci = variable_domain_bijection.begin(); ci != variable_domain_bijection.end(); ++ci)
	{
		std::cout << *(*ci).first << " <- transition fact -> " << *(*ci).second << "." << std::endl;
	}
	for (std::map<const Term*, const Term*>::const_iterator ci = variable_bijection.begin(); ci != variable_bijection.end(); ++ci)
	{
		std::cout << (*ci).first << " <- term -> " << (*ci).second << "." << std::endl;
	}
*/
	// Found a bijection return a mapping for each fact!
	if (current_fact_index == facts_.size())
	{
//		std::cout << "Found bijection!!!" << std::endl;
		return new std::map<const TransitionFact*, const TransitionFact*>(variable_domain_bijection);
	}
	
	const TransitionFact* current_fact = facts_[current_fact_index];
	for (std::vector<const TransitionFact*>::const_iterator ci = other.facts_.begin(); ci != other.facts_.end(); ++ci)
	{
		const TransitionFact* other_fact = *ci;
		
//		std::cout << "Check if " << *current_fact << " == " << *other_fact << std::endl;
		
		if (*current_fact == *other_fact)
		{
//			std::cout << "YES :D!" << std::endl;
			std::map<const TransitionFact*, const TransitionFact*> new_variable_domain_bijection(variable_domain_bijection);
			std::map<const Term*, const Term*> new_variable_bijection(variable_bijection);
			
			new_variable_domain_bijection[current_fact] = other_fact;
			new_variable_domain_bijection[other_fact] = current_fact;
			
			// Check if the make mappings are not violated.
			bool variables_mappings_match = true;
			for (unsigned int i = 0; i < current_fact->getActionVariables().size(); ++i)
			{
				const Term* current_fact_term = current_fact->getActionVariables()[i];
				const Term* other_fact_term = other_fact->getActionVariables()[i];
				
				std::map<const Term*, const Term*>::const_iterator current_variable_bindings_ci = new_variable_bijection.find(current_fact_term);
				std::map<const Term*, const Term*>::const_iterator other_variable_bindings_ci = new_variable_bijection.find(other_fact_term);
				
				if ((current_variable_bindings_ci != new_variable_bijection.end() &&
				    (*current_variable_bindings_ci).second != other_fact_term) ||
				    (other_variable_bindings_ci != new_variable_bijection.end() &&
				    (*other_variable_bindings_ci).second != current_fact_term))
				{
					variables_mappings_match = false;
					break;
				}
				
				new_variable_bijection[current_fact_term] = other_fact_term;
				new_variable_bijection[other_fact_term] = current_fact_term;
			}
			
			if (!variables_mappings_match)
			{
				continue;
			}
			
			const std::map<const TransitionFact*, const TransitionFact*>* result = findBijection(current_fact_index + 1, other, new_variable_domain_bijection, new_variable_bijection);
			if (result != NULL)
			{
				return result;
			}
		}
//		else
//		{
//			std::cout << "NO :(((" << std::endl;
//		}
	}
	
	return NULL;
}

void FactSet::addFact(const TransitionFact& fact)
{
	facts_.push_back(&fact);
}

std::ostream& operator<<(std::ostream& os, const FactSet& fact_set)
{
	os << "{";
	for (std::vector<const TransitionFact*>::const_iterator ci = fact_set.getFacts().begin(); ci != fact_set.getFacts().end(); ++ci)
	{
		os << **ci;
		if (ci + 1 != fact_set.getFacts().end())
		{
			os << ", ";
		}
	}
	os << "}(" << &fact_set << ")";
	return os;
}

void LiftedTransition::createLiftedTransitions(std::vector<LiftedTransition*>& created_lifted_transitions, const PredicateManager& predicate_manager, const TermManager& term_manager, const TypeManager& type_manager, const Action& action, const std::vector<const Atom*>& initial_facts, const std::vector<const Object*>& part_of_property_state)
{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
	std::cout << "Create lifted transitions from the action: " << action << std::endl;
	std::cout << " === Inititial facts: === " << std::endl;
	for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
	{
		(*ci)->print(std::cout);
		std::cout << std::endl;
	}
#endif
	
	// Determine which objects are different due to static constraints.
	std::map<const Object*, std::vector<const Atom*>* > object_to_static_constraints_mapping;
	for (std::vector<const Object*>::const_iterator ci = term_manager.getAllObjects().begin(); ci != term_manager.getAllObjects().end(); ++ci)
	{
		const Object* object = *ci;
		std::vector<const Atom*>* static_constraints = new std::vector<const Atom*>();
		object_to_static_constraints_mapping[object] = static_constraints;
		for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
		{
			const Atom* initial_fact = *ci;
			if (!initial_fact->getPredicate().isStatic())
			{
				continue;
			}
			
			for (std::vector<const Term*>::const_iterator ci = initial_fact->getTerms().begin(); ci != initial_fact->getTerms().end(); ++ci)
			{
				const Object* initial_fact_object = static_cast<const Object*>(*ci);
				//const std::vector<const Object*>& variable_domain = term->getDomain(Step::INITIAL_STEP, *bindings_);
				//if (std::find(variable_domain.begin(), variable_domain.end(), object) != variable_domain.end())
				if (initial_fact_object == object)
				{
					static_constraints->push_back(initial_fact);
					break;
				}
			}
		}
	}
	
	// Next, compare all the static constraints of all the objects and merge those which share the same static contraints.
	std::multimap<const Object*, const Object*> equivalent_relationships;
	for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
	{
		const Object* object = (*ci).first;
		const std::vector<const Atom*>* static_facts = (*ci).second;
		
		// Ignore all objects which are not part of a propery state.
		if (std::find(part_of_property_state.begin(), part_of_property_state.end(), object) == part_of_property_state.end())
		{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
			std::cout << *object << " is not part of a property state " << std::endl;
#endif
			continue;
		}
		
		for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
		{
			const Object* other_object = (*ci).first;
			const std::vector<const Atom*>* other_static_facts = (*ci).second;
			if (other_object == object || static_facts->size() != other_static_facts->size() || object->getType() != other_object->getType() ||
			    std::find(part_of_property_state.begin(), part_of_property_state.end(), other_object) == part_of_property_state.end())
			{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
				std::cout << *object << " cannot be equivalent to " << *other_object << " because of ";
				std::cout << static_facts->size() << " != " << other_static_facts->size() << std::endl;
				std::cout << object->getType() << " != " << other_object->getType() << std::endl;
			   if (std::find(part_of_property_state.begin(), part_of_property_state.end(), other_object) == part_of_property_state.end())
				{
					std::cout << "Not part of a property state!" << std::endl;
				}
				std::cout << "." << std::endl;
#endif
				continue;
			}
			
			// Make sure that all the static facts are shared and identical.
			bool all_static_constraints_shared = true;
			for (std::vector<const Atom*>::const_iterator ci = static_facts->begin(); ci != static_facts->end(); ++ci)
			{
				const Atom* static_fact = *ci;
				bool shares_static_constraint = false;
				for (std::vector<const Atom*>::const_iterator ci = other_static_facts->begin(); ci != other_static_facts->end(); ++ci)
				{
					const Atom* other_static_fact = *ci;
					if (static_fact->getArity() != other_static_fact->getArity() ||
					    static_fact->getPredicate().getName() != other_static_fact->getPredicate().getName())
					{
						continue;
					}
					
					bool terms_match = true;
					for (unsigned int i = 0; i < static_fact->getArity(); ++i)
					{
						const Object* o1 = static_cast<const Object*>(static_fact->getTerms()[i]);
						const Object* o2 = static_cast<const Object*>(other_static_fact->getTerms()[i]);
						if (o1 == object && o2 == other_object)
						{
							continue;
						}
						
						if (o1 != o2)
						{
							terms_match = false;
							break;
						}
					}
					
					if (terms_match)
					{
						shares_static_constraint = true;
						break;
					}
				}
				
				if (!shares_static_constraint)
				{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
					std::cout << *object << " cannot be equivalent to " << *other_object << " because of ";
					static_fact->print(std::cout);
					std::cout << "." << std::endl;
#endif
					all_static_constraints_shared = false;
					break;
				}
			}
			
			if (all_static_constraints_shared)
			{
				equivalent_relationships.insert(std::make_pair(object, other_object));
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
				std::cout << *object << " <-> " << *other_object << std::endl;
#endif
			}
		}
	}
	
	// Partially ground the variables based on which objects can be made equivalent.
	std::map<const Term*, std::vector<const VariableDomain*>*> action_variable_to_variable_domain_set;
	std::map<const Term*, unsigned int> action_variable_to_variable_index;
	std::vector<std::vector<const VariableDomain*>*> partially_grounded_action_variable_domains;
	for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ++ci)
	{
		const Variable* action_variable = *ci;
		std::vector<const Object*> objects_of_type;
		type_manager.getObjectsOfType(objects_of_type, *action_variable->getType());
		
		std::vector<const VariableDomain*>* action_variable_domain = new std::vector<const VariableDomain*>();
		partially_grounded_action_variable_domains.push_back(action_variable_domain);
		action_variable_to_variable_domain_set[action_variable] = action_variable_domain;
		action_variable_to_variable_index[action_variable] = std::distance(action.getVariables().begin(), ci);
		
		// Split the objects up.
		std::set<const Object*> processed_objects;
		for (std::vector<const Object*>::const_iterator ci = objects_of_type.begin(); ci != objects_of_type.end(); ++ci)
		{
			const Object* current_object = *ci;
			
			if (processed_objects.count(current_object) > 0)
			{
				continue;
			}
			
			processed_objects.insert(current_object);
			
			VariableDomain* current_variable_domain = new VariableDomain();
			current_variable_domain->addObject(*current_object);
			
			action_variable_domain->push_back(current_variable_domain);
			
			// Find all objects which are equivalent to current_object.
			std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator > eq_objects_range;
			eq_objects_range = equivalent_relationships.equal_range(current_object);
			
			// TODO: Make types more general so that we do not run into problems in domains like depots where there is no functional differences between the
			// depot and distributor types.
			for (std::multimap<const Object*, const Object*>::const_iterator ci = eq_objects_range.first; ci != eq_objects_range.second; ++ci)
			{
				const Object* equivalent_object = (*ci).second;
				
				if (equivalent_object->getType() != current_object->getType() ||
				    processed_objects.count(equivalent_object) > 0)
				{
					continue;
				}
				
				current_variable_domain->addObject(*equivalent_object);
				processed_objects.insert(equivalent_object);
			}
		}
	}
	
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
	std::cout << " === Paritally grounded objects: === " << std::endl;
	for (std::vector<std::vector<const VariableDomain*>*>::const_iterator ci = partially_grounded_action_variable_domains.begin(); ci != partially_grounded_action_variable_domains.end(); ++ci)
	{
		std::vector<const VariableDomain*>* variable_domains = *ci;
		std::cout << "{";
		for (std::vector<const VariableDomain*>::const_iterator ci = variable_domains->begin(); ci != variable_domains->end(); ++ci)
		{
			std::cout << **ci << "; ";
		}
		std::cout << "}" << std::endl;
	}
#endif
	
	unsigned int counter[partially_grounded_action_variable_domains.size()];
	memset(counter, 0, sizeof(unsigned int) * partially_grounded_action_variable_domains.size());
	
	// Split up all the preconditions and effects into disjunct fact sets.
	std::vector<const Atom*> preconditions;
	MyPOP::Utility::convertFormula(preconditions, &action.getPrecondition());
	std::vector<const Atom*> effects = action.getEffects();
	
	bool done = false;
	while (!done)
	{
		done = true;
		
		// Convert all the preconditions and effects into facts.
		std::vector<const TransitionFact*> transition_preconditions;
		std::vector<const Atom*> effects_and_persistent_preconditions(effects);
		bool violate_static_preconditions = false;
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
		{
			const Atom* precondition = *ci;
			std::vector<const VariableDomain*> atom_variable_domains;
			
			for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ++ci)
			{
				const Term* term = *ci;
				unsigned int action_variable_index = action_variable_to_variable_index[term];
				const std::vector<const VariableDomain*>* variable_domains = action_variable_to_variable_domain_set[term];
				const VariableDomain* current_variable_domain = (*variable_domains)[counter[action_variable_index]];
				atom_variable_domains.push_back(current_variable_domain);
			}
			TransitionFact* new_fact = new TransitionFact(predicate_manager, precondition->getPredicate(), atom_variable_domains, precondition->getTerms());
			
			if (new_fact->getPredicate().isStatic())
			{
				bool is_part_of_initial_state = false;
				for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
				{
					const Atom* initial_fact = *ci;
					
					if (new_fact->getPredicate().getName() != initial_fact->getPredicate().getName() ||
					    new_fact->getPredicate().getArity() != initial_fact->getPredicate().getArity())
					{
						continue;
					}
					
					bool variable_domains_match = true;
					for (unsigned int i = 0; i < new_fact->getPredicate().getArity(); ++i)
					{
						const Object* initial_fact_domain = static_cast<const Object*>(initial_fact->getTerms()[i]);
						const VariableDomain* action_variable_domain = new_fact->getVariableDomains()[i];
						
						if (std::find(action_variable_domain->getVariableDomain().begin(), action_variable_domain->getVariableDomain().end(), initial_fact_domain) == action_variable_domain->getVariableDomain().end())
						{
							variable_domains_match = false;
							break;
						}
					}
					if (variable_domains_match)
					{
						is_part_of_initial_state = true;
						break;
					}
				}
				
				delete new_fact;
				
				if (!is_part_of_initial_state)
				{
					violate_static_preconditions = true;
					break;
				}				
				
				continue;
			}
			transition_preconditions.push_back(new_fact);
			
			bool precondition_is_removed = false;
			for (std::vector<const Atom*>::const_iterator ci = effects_and_persistent_preconditions.begin(); ci != effects_and_persistent_preconditions.end(); ++ci)
			{
				const Atom* effect = *ci;
				if (!effect->isNegative() ||
				    effect->getArity() != precondition->getArity() ||
				    effect->getPredicate().getName() != precondition->getPredicate().getName())
				{
					continue;
				}
				bool terms_match = true;
				for (unsigned int i = 0; i < effect->getPredicate().getArity(); ++i)
				{
					if (precondition->getTerms()[i] != effect->getTerms()[i])
					{
						terms_match = false;
						break;
					}
				}
				
				if (terms_match)
				{
					precondition_is_removed = true;
					break;
				}
			}
			
			if (!precondition_is_removed)
			{
				effects_and_persistent_preconditions.push_back(precondition);
			}
		}
		
		if (!violate_static_preconditions)
		{
			std::vector<const TransitionFact*> transition_effects;
			for (std::vector<const Atom*>::const_iterator ci = effects_and_persistent_preconditions.begin(); ci != effects_and_persistent_preconditions.end(); ++ci)
			{
				const Atom* atom = *ci;
				if (atom->isNegative())
				{
					continue;
				}
				std::vector<const VariableDomain*> atom_variable_domains;
				
				for (std::vector<const Term*>::const_iterator ci = atom->getTerms().begin(); ci != atom->getTerms().end(); ++ci)
				{
					const Term* term = *ci;
					unsigned int action_variable_index = action_variable_to_variable_index[term];
					const std::vector<const VariableDomain*>* variable_domains = action_variable_to_variable_domain_set[term];
					const VariableDomain* current_variable_domain = (*variable_domains)[counter[action_variable_index]];
					atom_variable_domains.push_back(current_variable_domain);
				}
				TransitionFact* new_fact = new TransitionFact(predicate_manager, atom->getPredicate(), atom_variable_domains, atom->getTerms());
				transition_effects.push_back(new_fact);
			}
			
			// Split both groups up.
			std::vector<const FactSet*> split_preconditions;
			split(split_preconditions, transition_preconditions);
			
			std::vector<const FactSet*> split_effects;
			split(split_effects, transition_effects);
			
			std::vector<const VariableDomain*>* action_variable_domains = new std::vector<const VariableDomain*>();
			for (unsigned int variable_domain_index = 0; variable_domain_index < action.getVariables().size(); ++variable_domain_index)
			{
				action_variable_domains->push_back((*partially_grounded_action_variable_domains[variable_domain_index])[counter[variable_domain_index]]);
			}
			
			created_lifted_transitions.push_back(new LiftedTransition(action, *action_variable_domains, split_preconditions, split_effects));
		}
		else
		{
			for (std::vector<const TransitionFact*>::const_iterator ci = transition_preconditions.begin(); ci != transition_preconditions.end(); ++ci)
			{
				delete *ci;
			}
		}
		
		for (unsigned int i = 0; i < partially_grounded_action_variable_domains.size(); ++i)
		{
			if (counter[i] + 1 == partially_grounded_action_variable_domains[i]->size())
			{
				counter[i] = 0;
			}
			else
			{
				counter[i] = counter[i] + 1;
				done = false;
				break;
			}
		}
	}
	
	for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
	{
		delete (*ci).second;
	}
	
	for (std::vector<std::vector<const VariableDomain*>*>::const_iterator ci = partially_grounded_action_variable_domains.begin(); ci != partially_grounded_action_variable_domains.end(); ++ci)
	{
		const std::vector<const VariableDomain*>* variable_domains = *ci;
		for (std::vector<const VariableDomain*>::const_iterator ci = variable_domains->begin(); ci != variable_domains->end(); ++ci)
		{
			delete *ci;
		}
		delete variable_domains;
	}
}

void LiftedTransition::mergeFactSets(const std::vector<LiftedTransition*>& all_lifted_transitions)
{
	std::vector<const FactSet*> merged_fact_sets;
	std::vector<const FactSet*> facts_to_remove;
	for (std::vector<LiftedTransition*>::const_iterator ci = all_lifted_transitions.begin(); ci != all_lifted_transitions.end(); ++ci)
	{
		LiftedTransition* lifted_transition = *ci;
		
		std::vector<const FactSet*> all_facts;
		all_facts.insert(all_facts.end(), lifted_transition->preconditions_.begin(), lifted_transition->preconditions_.end());
		all_facts.insert(all_facts.end(), lifted_transition->effects_.begin(), lifted_transition->effects_.end());
		
		//for (unsigned int i = 0; i < lifted_transition->preconditions_.size(); ++i)
		for (std::vector<const FactSet*>::const_iterator ci = all_facts.begin(); ci != all_facts.end(); ++ci)
		{
			//const FactSet* precondition_set = lifted_transition->preconditions_[i];
			const FactSet* fact_set = *ci;
			
			// Check if there is another fact set that can merge with this one.
			bool found_bijection = false;
			for (std::vector<const FactSet*>::const_iterator ci = merged_fact_sets.begin(); ci != merged_fact_sets.end(); ++ci)
			{
				const FactSet* merged_fact_set = *ci;
				//const std::map<const TransitionFact*, const TransitionFact*>* bijection = merged_fact_set->findBijection(*precondition_set);
				const std::map<const TransitionFact*, const TransitionFact*>* bijection = merged_fact_set->findBijection(*fact_set);
				
				if (bijection != NULL)
				{
					//std::cout << "Found a bijection between " << std::endl << *this << "and" << std::endl << *lifted_transition << std::endl;
					//lifted_transition->updateFactSet(*precondition_set, *merged_fact_set, *bijection);
					lifted_transition->updateFactSet(*fact_set, *merged_fact_set, *bijection);
					found_bijection = true;
					delete bijection;
					break;
				}
//				else
//				{
//					//std::cout << "Could not merge: " << std::endl << *precondition_set << "with" << *merged_fact_set << std::endl;
//					std::cout << "Could not merge: " << std::endl << *fact_set << "with" << *merged_fact_set << std::endl;
//				}
			}
			
			if (!found_bijection)
			{
				//std::cout << "=== ADD MERGED SET TO: " << std::endl << *precondition_set << std::endl;
//				std::cout << "=== ADD MERGED SET TO: " << std::endl << *fact_set << std::endl;
//				for (std::vector<const FactSet*>::const_iterator ci = merged_fact_sets.begin(); ci != merged_fact_sets.end(); ++ci)
//				{
//					std::cout << "* " << **ci << std::endl;
//				}
				//merged_fact_sets.push_back(precondition_set);
				merged_fact_sets.push_back(fact_set);
			}
			else
			{
				facts_to_remove.push_back(fact_set);
			}
		}
	}
	std::cerr << "Merged fact sets: " << merged_fact_sets.size() << std::endl;
}

void LiftedTransition::updateFactSet(const FactSet& my_fact_set, const FactSet& merged_fact_set, const std::map<const TransitionFact*, const TransitionFact*>& bijection)
{
	if (&my_fact_set == &merged_fact_set)
	{
		return;
	}
/*
	std::cout << "[LiftedTransition::updateFactSet] " << *this << std::endl;
	std::cout << "Fact to update is: " << std::endl << my_fact_set << std::endl;
	std::cout << "Update it with: " << std::endl << merged_fact_set << std::endl;
	
	std::cout << "Bijection found:" << std::endl;
	for (std::map<const TransitionFact*, const TransitionFact*>::const_iterator ci = bijection.begin(); ci != bijection.end(); ++ci)
	{
		std::cout << *(*ci).first << "[" << (*ci).first << "] -> " << *(*ci).second << "[" << (*ci).second << "]" << std::endl;
	}
*/
	
	// Find all the facts sets which match with my fact set.
	{
		std::vector<const FactSet*>::iterator i = std::find(preconditions_.begin(), preconditions_.end(), &my_fact_set);
		if (i != preconditions_.end())
		{
			const FactSet* precondition_set = *i;
			unsigned int precondition_index = std::distance(preconditions_.begin(), i);
			//preconditions_.erase(i);
			
			std::vector<std::vector<unsigned int>* >* fact_mappings = precondition_variable_domains_to_action_parameters_[precondition_set];
			precondition_variable_domains_to_action_parameters_.erase(precondition_set);
			
			std::vector<std::vector<unsigned int>* >* new_fact_mappings = new std::vector<std::vector<unsigned int>* >(fact_mappings->size());
			
			for (std::vector<const TransitionFact*>::const_iterator ci = merged_fact_set.getFacts().begin(); ci != merged_fact_set.getFacts().end(); ++ci)
			{
				const TransitionFact* new_fact = *ci;
				unsigned int new_fact_index = std::distance(merged_fact_set.getFacts().begin(), ci);
				const TransitionFact* fact_to_replace = (*bijection.find(new_fact)).second;
				
				unsigned int fact_to_replace_index = std::distance(precondition_set->getFacts().begin(), std::find(precondition_set->getFacts().begin(), precondition_set->getFacts().end(), fact_to_replace));
				(*new_fact_mappings)[new_fact_index] = (*fact_mappings)[fact_to_replace_index];
			}
			
			precondition_variable_domains_to_action_parameters_[&merged_fact_set] = new_fact_mappings;
			preconditions_[precondition_index] = &merged_fact_set;
			
			delete fact_mappings;
			delete precondition_set;
		}
	}
	
	{
		std::vector<const FactSet*>::iterator i = std::find(effects_.begin(), effects_.end(), &my_fact_set);
		if (i != effects_.end())
		{
			const FactSet* effect_set = *i;
			unsigned int effect_index = std::distance(effects_.begin(), i);
			//effects_.erase(i);
			
			std::vector<std::vector<unsigned int>* >* fact_mappings = effect_variable_domains_to_action_parameters_[effect_set];
			effect_variable_domains_to_action_parameters_.erase(effect_set);
			
			std::vector<std::vector<unsigned int>* >* new_fact_mappings = new std::vector<std::vector<unsigned int>* >(fact_mappings->size());
			
			for (std::vector<const TransitionFact*>::const_iterator ci = merged_fact_set.getFacts().begin(); ci != merged_fact_set.getFacts().end(); ++ci)
			{
				const TransitionFact* new_fact = *ci;
				unsigned int new_fact_index = std::distance(merged_fact_set.getFacts().begin(), ci);
				const TransitionFact* fact_to_replace = (*bijection.find(new_fact)).second;
				
				unsigned int fact_to_replace_index = std::distance(effect_set->getFacts().begin(), std::find(effect_set->getFacts().begin(), effect_set->getFacts().end(), fact_to_replace));
				(*new_fact_mappings)[new_fact_index] = (*fact_mappings)[fact_to_replace_index];
			}
			
			effect_variable_domains_to_action_parameters_[&merged_fact_set] = new_fact_mappings;
			effects_[effect_index] = &merged_fact_set;
			
			delete fact_mappings;
			delete effect_set;
		}
	}
	
/*
	std::cout << "=== begin END === " << std::endl;
	std::cout << *this << std::endl;
	std::cout << "=== end END === " << std::endl;
*/
}

void LiftedTransition::split(std::vector<const FactSet*>& result, const std::vector<const TransitionFact*>& facts)
{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
	std::cout << "[LiftedTransition::split] " << std::endl;
	for (std::vector<const TransitionFact*>::const_iterator ci = facts.begin(); ci != facts.end(); ++ci)
	{
		std::cout << "* " << **ci << "." << std::endl;
	}
#endif
	
	std::set<const TransitionFact*> processed_atoms;
	FactSet* fact_set = new FactSet();
	unsigned int fact_set_size = std::numeric_limits<unsigned int>::max();
	std::set<const Term*> lifted_terms;
	do
	{
		if (fact_set_size == fact_set->getFacts().size())
		{
			result.push_back(fact_set);
			fact_set = new FactSet();
			lifted_terms.clear();
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
			std::cout << "Start new fact set!" << std::endl;
#endif
		}
		fact_set_size = fact_set->getFacts().size();
		
		for (std::vector<const TransitionFact*>::const_iterator ci = facts.begin(); ci != facts.end(); ++ci)
		{
			const TransitionFact* fact = *ci;
			if (processed_atoms.find(fact) != processed_atoms.end())
			{
				continue;
			}
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
			std::cout << "Process the fact: " << *fact << std::endl;
#endif
			
			bool contains_lifted_fact = lifted_terms.empty() && fact_set->getFacts().empty();
			for (std::vector<const Term*>::const_iterator ci = fact->getActionVariables().begin(); ci != fact->getActionVariables().end(); ++ci)
			{
				if (std::find(lifted_terms.begin(), lifted_terms.end(), *ci) != lifted_terms.end())
				{
					contains_lifted_fact = true;
					break;
				}
			}
			
			// If the fact contains a lifted fact, update all the lifted facts.
			if (contains_lifted_fact)
			{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
				std::cout << "Add: " << *fact << " to the set " << *fact_set << "." << std::endl;
#endif
				processed_atoms.insert(fact);
				fact_set->addFact(*fact);
				
				for (unsigned int i = 0; i < fact->getActionVariables().size(); ++i)
				{
					const Term* action_variable = fact->getActionVariables()[i];
					const VariableDomain* variable_domain = fact->getVariableDomains()[i];
					
					if (variable_domain->size() > 1)
					{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
						std::cout << "New lifted term: " << action_variable << "." << std::endl;
#endif
						lifted_terms.insert(action_variable);
					}
				}
			}
		}
	}
	while (processed_atoms.size() != facts.size());
	
	assert (fact_set->getFacts().size() > 0);
	result.push_back(fact_set);
}

LiftedTransition::LiftedTransition(const Action& action, const std::vector<const VariableDomain*>& action_variable_domains, const std::vector<const FactSet*>& preconditions, const std::vector<const FactSet*>& effects)
	: action_(&action)
{
#ifdef MYPOP_HEURISTICS_LIFTED_TRANSITION_COMMENTS
	std::cout << "New lifted transition pre: " << preconditions.size() << "; eff: " << effects.size() << std::endl;
#endif

	for (std::vector<const VariableDomain*>::const_iterator ci = action_variable_domains.begin(); ci != action_variable_domains.end(); ++ci)
	{
		action_variable_domains_.push_back(new VariableDomain(**ci));
	}

	preconditions_.insert(preconditions_.end(), preconditions.begin(), preconditions.end());
	effects_.insert(effects_.end(), effects.begin(), effects.end());
	
	mapFactsToActionVariables(precondition_variable_domains_to_action_parameters_, preconditions);
	mapFactsToActionVariables(effect_variable_domains_to_action_parameters_, effects);
}

//void LiftedTransition::mapFactsToActionVariables(std::map<const FactSet*, std::vector<std::vector<const Term*>* >* >& fact_variable_domains_to_action_parameters, const std::vector<const FactSet*>& fact_sets)
void LiftedTransition::mapFactsToActionVariables(std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* >& fact_variable_domains_to_action_parameters, const std::vector<const FactSet*>& fact_sets)
{
	for (std::vector<const FactSet*>::const_iterator ci = fact_sets.begin(); ci != fact_sets.end(); ++ci)
	{
		const FactSet* preconditition_fact_set = *ci;
		//std::vector<std::vector<const Term*>*>* fact_index_to_action_variable = new std::vector<std::vector<const Term*>*>();
		std::vector<std::vector<unsigned int>*>* fact_index_to_action_variable = new std::vector<std::vector<unsigned int>*>();
		fact_variable_domains_to_action_parameters[preconditition_fact_set] = fact_index_to_action_variable;
		
		for (std::vector<const TransitionFact*>::const_iterator ci = preconditition_fact_set->getFacts().begin(); ci != preconditition_fact_set->getFacts().end(); ++ci)
		{
			const TransitionFact* fact = *ci;
			std::vector<unsigned int>* terms = new std::vector<unsigned int>();
			fact_index_to_action_variable->push_back(terms);
			
			for (std::vector<const Term*>::const_iterator ci = fact->getActionVariables().begin(); ci != fact->getActionVariables().end(); ++ci)
			{
				const Term* term = *ci;
				terms->push_back(std::distance(action_->getVariables().begin(), std::find(action_->getVariables().begin(), action_->getVariables().end(), term)));
			}
		}
	}
}

LiftedTransition::~LiftedTransition()
{
/*	for (std::vector<const FactSet*>::const_iterator ci = preconditions_.begin(); ci != preconditions_.end(); ++ci)
	{
		delete *ci;
	}
	for (std::vector<const FactSet*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ++ci)
	{
		delete *ci;
	}*/
	
	for (std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* >::const_iterator ci = precondition_variable_domains_to_action_parameters_.begin(); ci != precondition_variable_domains_to_action_parameters_.end(); ++ci)
	{
		std::vector<std::vector<unsigned int>* >* mapping = (*ci).second;
		for (std::vector<std::vector<unsigned int>* >::const_iterator ci = mapping->begin(); ci != mapping->end(); ++ci)
		{
			delete *ci;
		}
		delete mapping;
	}
	
	for (std::map<const FactSet*, std::vector<std::vector<unsigned int>* >* >::const_iterator ci = effect_variable_domains_to_action_parameters_.begin(); ci != effect_variable_domains_to_action_parameters_.end(); ++ci)
	{
		std::vector<std::vector<unsigned int>* >* mapping = (*ci).second;
		for (std::vector<std::vector<unsigned int>* >::const_iterator ci = mapping->begin(); ci != mapping->end(); ++ci)
		{
			delete *ci;
		}
		delete mapping;
	}
}

std::ostream& operator<<(std::ostream& os, const LiftedTransition& lifted_transition)
{
	os << "Lifted action: " << *lifted_transition.action_ << std::endl;
	os << " === PRECONDITIONS === " << std::endl;
	for (std::vector<const FactSet*>::const_iterator ci = lifted_transition.preconditions_.begin(); ci != lifted_transition.preconditions_.end(); ++ci)
	{
		const FactSet* fact_set = *ci;
		os << *fact_set << "(" << fact_set << ")" << std::endl;
	}
	
	os << " === EFFECTS === " << std::endl;
	for (std::vector<const FactSet*>::const_iterator ci = lifted_transition.effects_.begin(); ci != lifted_transition.effects_.end(); ++ci)
	{
		const FactSet* fact_set = *ci;
		os << *fact_set << std::endl;
	}
	
	return os;
}

};

};
