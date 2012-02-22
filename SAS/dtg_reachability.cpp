#include <cstring>
#include <iterator>
#include <sys/time.h>
#include <boost/bind.hpp>

#include "dtg_reachability.h"
#include "equivalent_object_group.h"
#include "dtg_manager.h"
#include "dtg_graph.h"
#include "dtg_node.h"
#include "property_space.h"
#include "transition.h"
#include "type_manager.h"
#include "reachable_tree.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
#define DTG_REACHABILITY_KEEP_TIME
namespace MyPOP {

namespace SAS_Plus {
	
unsigned int ReachableTransition::generated_new_reachable_facts = 0;
unsigned int ReachableTransition::accepted_new_reachable_facts = 0;

ReachableFact::ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
	: atom_(&bounded_atom.getAtom()), replaced_by_(NULL)
{
	term_domain_mapping_ = new EquivalentObjectGroup*[bounded_atom.getAtom().getArity()];
	
	for (std::vector<const Term*>::const_iterator ci = bounded_atom.getAtom().getTerms().begin(); ci != bounded_atom.getAtom().getTerms().end(); ci++)
	{
		const Term* term = *ci;
		const std::vector<const Object*>& domain = term->getDomain(bounded_atom.getId(), bindings);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (domain.size() == 1);
#endif
		
		EquivalentObjectGroup& corresponding_eog = eog_manager.getEquivalentObject(*domain[0]).getEquivalentObjectGroup();
		term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] = &corresponding_eog;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] != NULL);
#endif
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
#endif
}

ReachableFact::ReachableFact(const BoundedAtom& bounded_atom, const Bindings& bindings, EquivalentObjectGroup** term_domain_mapping)
	: atom_(&bounded_atom.getAtom()), term_domain_mapping_(term_domain_mapping), replaced_by_(NULL)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
#endif
}

ReachableFact::ReachableFact(const Atom& atom, EquivalentObjectGroup** term_domain_mapping)
	: atom_(&atom), term_domain_mapping_(term_domain_mapping), replaced_by_(NULL)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < atom.getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
#endif
}

ReachableFact::~ReachableFact()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	delete[] term_domain_mapping_;
#endif
}

bool ReachableFact::updateTermsToRoot()
{
	bool updated_domain = false;
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		EquivalentObjectGroup& root_node = term_domain_mapping_[i]->getRootNode();
		if (&root_node != term_domain_mapping_[i])
		{
			term_domain_mapping_[i] = &root_node;
			updated_domain = true;
		}
	}
	
	// assert(updated_domain);
	
	return updated_domain;
}

bool ReachableFact::isEquivalentTo(const ReachableFact& other) const
{
//	std::cout << "Are " << *this << " and " << other << " equivalent?" << std::endl;
	
	if (atom_->getArity() != other.atom_->getArity())
	{
//		std::cout << "Arities don't match up!" << std::endl;
		return false;
	}
	
//	char combined_mask = mask_ & other.mask_;
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
//		if (((0x1 << i) & combined_mask) != 0)
		if (!term_domain_mapping_[i]->isGrounded())
		{
			// Make sure the types match up.
			if (!term_domain_mapping_[i]->hasSameFingerPrint(*other.term_domain_mapping_[i]))
			{
//				std::cout << "The " << i << "th term does not have the same fingerprint!" << std::endl;
				return false;
			}
		}

		else if (!term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
		{
//			std::cout << "The " << i << "th term is at odds!" << std::endl;
			return false;
		}
	}
	return true;
}

bool ReachableFact::isIdenticalTo(const ReachableFact& other) const
{
	if (atom_->getArity() != other.atom_->getArity())
	{
		return false;
	}
	
	if (atom_->getPredicate().getName() != other.atom_->getPredicate().getName())
	{
		return false;
	}
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (term_domain_mapping_[i] != NULL);
		assert (other.term_domain_mapping_[i] != NULL);
#endif
//		if (&term_domain_mapping_[i]->getRootNode() != &other.term_domain_mapping_[i]->getRootNode())
		if (term_domain_mapping_[i] != other.term_domain_mapping_[i])
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			if (term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
			{
				std::cerr << "Could not check if " << *this << " is equivalent to " << other << std::endl;
				std::cerr << "WRONG!" << std::endl;
				assert (false);
			}
#endif
			return false;
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		if (!term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
		{
			std::cerr << "WRONG!" << std::endl;
			exit(1);
		}
#endif
	}
	return true;
}

void ReachableFact::printGrounded(std::ostream& os) const
{
	os << "Print grounded of: " << *this << std::endl;
	unsigned int counter[atom_->getArity()];
	memset (&counter[0], 0, sizeof(unsigned int) * atom_->getArity());
	
	bool done = false;
	while (!done)
	{
		os << atom_->getPredicate().getName() << " ";
		for (unsigned int i = 0; i < atom_->getArity(); i++)
		{
			const std::vector<EquivalentObject*>& objects = term_domain_mapping_[i]->getEquivalentObjects();
			
			os << *objects[counter[i]];
			
			if (i + 1 != atom_->getArity())
			{
				os << " ";
			}
		}
		os << std::endl;
		
		// Update counters or stop if all objects have been printed.
		for (unsigned int i = 0; i < atom_->getArity(); i++)
		{
			if (counter[i] + 1 == term_domain_mapping_[i]->getEquivalentObjects().size())
			{
				if (i + 1 == atom_->getArity())
				{
					done = true;
					break;
				}
				
				counter[i] = 0;
				continue;
			}
			
			++counter[i];
			break;
		}
	}
}

void ReachableFact::getAllReachableFacts(std::vector<const BoundedAtom*>& results) const
{
	unsigned int counter[atom_->getArity()];
	memset (&counter[0], 0, sizeof(unsigned int) * atom_->getArity());
	
	bool done = false;
	while (!done)
	{
		std::vector<const Term*>* terms = new std::vector<const Term*>();
		
		for (unsigned int i = 0; i < atom_->getArity(); i++)
		{
			const std::vector<EquivalentObject*>& objects = term_domain_mapping_[i]->getEquivalentObjects();
			terms->push_back(&objects[counter[i]]->getObject());
		}
		
		// Update counters or stop if all objects have been printed.
		for (unsigned int i = 0; i < atom_->getArity(); i++)
		{
			if (counter[i] + 1 == term_domain_mapping_[i]->getEquivalentObjects().size())
			{
				if (i + 1 == atom_->getArity())
				{
					done = true;
					break;
				}
				
				counter[i] = 0;
				continue;
			}
			
			++counter[i];
			break;
		}
		
		Atom* new_atom = new Atom(atom_->getPredicate(), *terms, false);
		results.push_back(new BoundedAtom(Step::INITIAL_STEP, *new_atom));
	}
}

void ReachableFact::replaceBy(ReachableFact& replacement)
{
//	assert (replaced_by_ == NULL);
	replaced_by_ = &replacement;
	
	assert (replaced_by_->replaced_by_ != this);
}

//bool isMarkedForRemoval() const { return removed_flag_; }
//inline bool ReachableFact::isMarkedForRemoval() const { return replaced_by_ != NULL; }

const ReachableFact& ReachableFact::getReplacement() const
{
	if (replaced_by_ == NULL) return *this;
	
	assert (replaced_by_->replaced_by_ != this);
	
	return replaced_by_->getReplacement();
}

std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact)
{
	os << "Reachable fact: (" << reachable_fact.atom_->getPredicate().getName() << " ";
	for (unsigned int i = 0; i < reachable_fact.atom_->getArity(); i++)
	{
		const std::vector<EquivalentObject*>& objects = reachable_fact.term_domain_mapping_[i]->getEquivalentObjects();
		os << "{";
		for (std::vector<EquivalentObject*>::const_iterator ci = objects.begin(); ci != objects.end(); ci++)
		{
			os << (*ci)->getObject();
			if (ci + 1 != objects.end())
			{
				os << ", ";
			}
		}
		os << "}";
		if (i + 1 != reachable_fact.atom_->getArity())
		{
			os << ", ";
		}
	}
//	os << ")" << "%" << &reachable_fact << "%" << reachable_fact.getAtom().getPredicate();
//	os << "[r=" << &reachable_fact.getReplacement() << "]";
	return os;
}

#include "reachable_tree.h"
/**
 * ResolvedBoundedAtom.
 */
ResolvedBoundedAtom::ResolvedBoundedAtom(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
	: id_(id), atom_(&atom)
{
	init(bindings, eog_manager, predicate_manager);
}

/*ResolvedBoundedAtom::ResolvedBoundedAtom(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
	 : id_(bounded_atom.getId()), atom_(&bounded_atom.getAtom())
{
	init(bindings, eog_manager, predicate_manager);
}*/

ResolvedBoundedAtom::~ResolvedBoundedAtom()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	delete corrected_atom_;
	delete[] is_grounded_;
#endif
}

void ResolvedBoundedAtom::init(const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
{
	is_grounded_ = new bool[atom_->getArity()];
	memset(is_grounded_, false, sizeof(bool) * atom_->getArity());
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		const std::vector<const Object*>& variable_domain = atom_->getTerms()[i]->getDomain(id_, bindings);
		variable_domains_.push_back(&variable_domain);
		if (variable_domain.size() == 1 && 
		    eog_manager.getEquivalentObject(*variable_domain[0]).getEquivalentObjectGroup().isGrounded())
		{
			is_grounded_[i] = true;
		}
	}
	
	// May need to update the atom to get the proper types...
	std::vector<const Type*>* best_types = new std::vector<const Type*>();
	std::vector<const Term*>* new_variables = new std::vector<const Term*>();
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		const Type* best_type = NULL;
		const std::vector<const Object*>& variable_domain = atom_->getTerms()[i]->getDomain(id_, bindings);
		
		for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ci++)
		{
			const Object* object = *ci;
			const Type* type = object->getType();
			
			if (type == NULL) continue;
			
			if (best_type == NULL)
			{
				best_type = type;
				continue;
			}
			
			while (!type->isEqual(*best_type) && !type->isSubtypeOf(*best_type))
			{
				best_type = best_type->getSupertype();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
				assert (best_type != NULL);
#endif
			}
		}
		
		best_types->push_back(best_type);
		new_variables->push_back(new Variable(*best_type, atom_->getTerms()[i]->getName()));
	}
	
	Predicate* new_predicate = new Predicate(atom_->getPredicate().getName(), *best_types, atom_->getPredicate().isStatic());
	corrected_atom_ = new Atom(*new_predicate, *new_variables, atom_->isNegative(), true);
	
	predicate_manager.addManagableObject(new_predicate);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	std::cout << "Created a resolved atom: " << *this << std::endl;
#endif
}
	
const std::vector<const Object*>& ResolvedBoundedAtom::getVariableDomain(unsigned int index) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (index < variable_domains_.size());
#endif
	return *variable_domains_[index];
}

bool ResolvedBoundedAtom::isGrounded(unsigned int index) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (index < variable_domains_.size());
#endif
	return is_grounded_[index];
}

bool ResolvedBoundedAtom::canUnifyWith(const ResolvedBoundedAtom& other) const
{
//	if (!corrected_atom_->getPredicate().canSubstitute(other.getCorrectedAtom().getPredicate())) return false;
//	if (!other.atom_->getPredicate().canSubstitute(getAtom().getPredicate())) return false;
	
	if (atom_->getPredicate().getName() != other.atom_->getPredicate().getName()) return false;
	if (atom_->getArity() != other.atom_->getArity()) return false;
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		// Check if the variable domains overlap.
		bool variable_domains_overlap = false;
		
		for (std::vector<const Object*>::const_iterator ci = variable_domains_[i]->begin(); ci != variable_domains_[i]->end(); ci++)
		{
			const Object* object1 = *ci;
			for (std::vector<const Object*>::const_iterator ci = other.variable_domains_[i]->begin(); ci != other.variable_domains_[i]->end(); ci++)
			{
				const Object* object2 = *ci;
				
				if (object1 == object2)
				{
					variable_domains_overlap = true;
					break;
				}	
			}
			
			if (variable_domains_overlap) break;
		}
/*		if (isGrounded(i) &&
			(
				!other.isGrounded(i) ||
				getVariableDomain(i)[0] != other.getVariableDomain(i)[0]
			))*/

		if (!variable_domains_overlap)
		{
			return false;
		}
	}
	
	return true;
}

bool ResolvedBoundedAtom::canSubstitude(const ReachableFact& reachable_fact) const
{
	if (!getCorrectedAtom().getPredicate().canSubstitute(reachable_fact.getAtom().getPredicate()))
	{
		for (unsigned int i = 0; i < reachable_fact.getAtom().getArity(); i++)
		{
			const Type* fact_set_type = getCorrectedAtom().getTerms()[i]->getType();
			const Type* reachable_fact_type = reachable_fact.getTermDomain(i).getEquivalentObjects()[0]->getObject().getType();
			
			if (!fact_set_type->isCompatible(*reachable_fact_type))
			{
				return false;
			}
		}
	}
	
	return true;
}

std::ostream& operator<<(std::ostream& os, const ResolvedBoundedAtom& resolved_bounded_atom)
{
	os << "(" << resolved_bounded_atom.getCorrectedAtom().getPredicate().getName();
	for (unsigned int i = 0; i < resolved_bounded_atom.getCorrectedAtom().getArity(); i++)
	{
		const std::vector<const Object*>& domain = resolved_bounded_atom.getVariableDomain(i);
		os << " { ";
		for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
		{
			os << **ci;
			os << " ";
		}
		os << " } ";
		
		if (resolved_bounded_atom.isGrounded(i))
			os << "[GROUNDED]";
	}
	os << " )";
	return os;
}

/**
 * ResolvedEffect.
 */
ResolvedEffect::ResolvedEffect(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, bool free_variables[], PredicateManager& predicate_manager)
	: ResolvedBoundedAtom(id, atom, bindings, eog_manager, predicate_manager), eog_manager_(&eog_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Process the resolved effect: ";
	atom.print(std::cout, bindings, id);
	std::cout << "." << std::endl;
#endif
	
	is_free_variable_ = new bool[atom.getArity()];
	memcpy(&is_free_variable_[0], &free_variables[0], sizeof(bool) * atom.getArity());
	
	// Map the index of a term to the relevant variable.
	index_to_variable_ = new int[atom.getArity()];
	
	// Record the number of unique variables which are free.
	for (unsigned int i = 0; i < atom.getArity(); i++)
	{
		if (!is_free_variable_[i]) continue;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "The " << i << "th term is free: " << std::endl;
#endif
		
		bool already_recorded = false;
		for (std::vector<const Term*>::const_iterator ci = free_variables_.begin(); ci != free_variables_.end(); ci++)
		{
			unsigned int term_index = std::distance(static_cast<std::vector<const Term*>::const_iterator>(free_variables_.begin()), ci);
			if (atom.getTerms()[i] == *ci)
			{
				already_recorded = true;
				index_to_variable_[i] = term_index;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Variable already recorded..." << std::endl;
#endif
				break;
			}
		}
		
		if (already_recorded) continue;
		
		index_to_variable_[i] = free_variables_.size();
		free_variables_.push_back(atom.getTerms()[i]);
		
		std::vector<EquivalentObjectGroup*>* possible_eogs = new std::vector<EquivalentObjectGroup*>();
		const std::vector<const Object*>& variable_domain = atom.getTerms()[i]->getDomain(id, bindings);
		
		for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ci++)
		{
			EquivalentObjectGroup& eog = eog_manager.getEquivalentObject(**ci).getEquivalentObjectGroup();
			
			if (std::find(possible_eogs->begin(), possible_eogs->end(), &eog) != possible_eogs->end()) continue;
			possible_eogs->push_back(&eog);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//			std::cout << "- " << eog << std::endl;
#endif
		}
		free_variable_domains_.push_back(possible_eogs);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Create a new effect: " << *this << "." << std::endl;
#endif
}

ResolvedEffect::~ResolvedEffect()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	delete[] is_free_variable_;
	
	for (std::vector<std::vector<EquivalentObjectGroup*>* >::const_iterator ci = free_variable_domains_.begin(); ci != free_variable_domains_.end(); ci++)
	{
		delete *ci;
	}
	
	delete[] index_to_variable_;
#endif
}

void ResolvedEffect::updateVariableDomains()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	unsigned int counter = 0;
	unsigned int amount = 0;
#endif
	for (std::vector<std::vector<EquivalentObjectGroup*>* >::const_iterator ci = free_variable_domains_.begin(); ci != free_variable_domains_.end(); ci++)
	{
		std::vector<EquivalentObjectGroup*>* free_variable_domain = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::vector<EquivalentObjectGroup*> free_variable_domain_clone(*free_variable_domain);
#endif

		for (std::vector<EquivalentObjectGroup*>::reverse_iterator ri = free_variable_domain->rbegin(); ri != free_variable_domain->rend(); ri++)
		{
			EquivalentObjectGroup* eog = *ri;
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			++amount;
#endif
			
			if (!eog->isRootNode())
			{
				free_variable_domain->erase(ri.base() - 1);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				++counter;
#endif
			}
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		if (free_variable_domain->size() != free_variable_domain_clone.size())
		{
			std::cout << "Prior to deleting: " << std::endl;
			for (std::vector<EquivalentObjectGroup*>::const_iterator ci = free_variable_domain_clone.begin(); ci != free_variable_domain_clone.end(); ci++)
			{
				std::cout << "* ";
				(*ci)->printObjects(std::cout);
				std::cout << std::endl;
			}
			std::cout << "After deleting: " << std::endl;
			for (std::vector<EquivalentObjectGroup*>::const_iterator ci = free_variable_domain->begin(); ci != free_variable_domain->end(); ci++)
			{
				std::cout << "* ";
				(*ci)->printObjects(std::cout);
				std::cout << std::endl;
			}
		}
#endif
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	std::cerr << "Removed: " << counter << " free variables out of " << amount << "!" << std::endl;
#endif
}

bool ResolvedEffect::containsFreeVariables() const
{
	return free_variables_.size() != 0;
}

bool ResolvedEffect::isFreeVariable(unsigned int index) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (index < variable_domains_.size());
#endif
	return is_free_variable_[index];
}

void ResolvedEffect::createReachableFacts(std::vector<ReachableFact*>& results, EquivalentObjectGroup** effect_domains) const
{
	// If no variables are free we are done!
	if (free_variables_.size() == 0)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		for (unsigned int i = 0; i < variable_domains_.size(); i++)
		{
			assert (is_free_variable_[i] == false);
		}
#endif
		results.push_back(new ReachableFact(getCorrectedAtom(), effect_domains));
		return;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout <<  "Create a reachable fact based on an effect with free variables!" << *this << std::endl;
#endif
	
	// Initialise the counter.
	unsigned int counter[free_variables_.size()];
	memset(&counter[0], 0, sizeof(unsigned int) * free_variables_.size());
	
	unsigned int max_values[free_variables_.size()];
	for (unsigned int i = 0; i < free_variable_domains_.size(); i++)
	{
		max_values[i] = free_variable_domains_[i]->size();
	}
	
	// TODO: This can be improved as objects are put in the same Equivalent Object Group we do not need to generate as many reachable facts.
	bool done = false;
	while (!done)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Create a new reachable fact!" << std::endl;
#endif
		EquivalentObjectGroup** new_effect_domains = new EquivalentObjectGroup*[atom_->getArity()];
		memcpy(new_effect_domains, effect_domains, sizeof(EquivalentObjectGroup*) * atom_->getArity());
		
		unsigned int processed_free_variables = 0;
		
		for (unsigned int i = 0; i < atom_->getArity(); i++)
		{
			if (!is_free_variable_[i])
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "The " << i << "th term isn't free!" << std::endl;
#endif
				continue;
			}
			
			std::vector<EquivalentObjectGroup*>* possible_values = free_variable_domains_[index_to_variable_[i]];
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "The " << i << "th term is linked to the " << index_to_variable_[i] << "th variable!" << std::endl;
			for (std::vector<EquivalentObjectGroup*>::const_iterator ci = possible_values->begin(); ci != possible_values->end(); ci++)
			{
				std::cout << " * " << **ci << std::endl;
			}
#endif
			new_effect_domains[i] = (*possible_values)[counter[processed_free_variables]];
			
			++processed_free_variables;
		}
		
		ReachableFact* new_reachable_fact = new ReachableFact(getCorrectedAtom(), new_effect_domains);
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "New reachable fact with free variables: " << *new_reachable_fact << "." << std::endl;
#endif
		
		results.push_back(new_reachable_fact);
		
		// Update the counter.
		done = true;
		for (unsigned int i = 0; i < free_variable_domains_.size(); i++)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Update the " << i << "th counter!" << std::endl;
#endif
			
			if (++counter[i] == max_values[i])
			{
				counter[i] = 0;
			}
			else
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Counter updated, continue!" << std::endl;
#endif
				done = false;
				break;
			}
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "New counter: ";
		for (unsigned int i = 0; i < free_variable_domains_.size(); i++)
		{
			std::cout << counter[i] << ", ";
		}
		std::cout << "." << std::endl;
		
		std::cout << "Max: ";
		for (unsigned int i = 0; i < free_variable_domains_.size(); i++)
		{
			std::cout << max_values[i] << ", ";
		}
		std::cout << "." << std::endl;
#endif
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	delete[] effect_domains;
#endif
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "DONE!!!" << std::endl;
#endif
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	std::cout << "* Reachable facts after resolving the free variables: " << std::endl;
	for (std::vector<ReachableFact*>::const_iterator ci = results.begin(); ci != results.end(); ci++)
	{
		std::cout << "* " << **ci << std::endl;
	}
	
	for (std::vector<ReachableFact*>::const_iterator ci = results.begin(); ci != results.end(); ci++)
	{
		for (std::vector<ReachableFact*>::const_iterator ci2 = ci + 1; ci2 != results.end(); ci2++)
		{
			assert (!(*ci)->isIdenticalTo(**ci2));
		}
	}
#endif
}

std::ostream& operator<<(std::ostream& os, const ResolvedEffect& resolved_effect)
{
	os << "Resolved Effect (" << resolved_effect.getCorrectedAtom().getPredicate().getName();
	for (unsigned int i = 0; i < resolved_effect.getCorrectedAtom().getArity(); i++)
	{
		const std::vector<const Object*>& domain = resolved_effect.getVariableDomain(i);
		os << " { ";
		for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
		{
			os << **ci;
			os << " ";
		}
		os << " } ";
		
		if (resolved_effect.isFreeVariable(i))
		{
			os << "*";
		}
	}
	os << " )";
	return os;
}

/**
 * ReachableSet.
 */
ReachableSet::ReachableSet(const EquivalentObjectGroupManager& eog_manager)
	: eog_manager_(&eog_manager), removed_(false), cached_reachability_tree_size_(0), cache_is_valid_(false)
{

}

ReachableSet::~ReachableSet()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	for (std::vector<const ResolvedBoundedAtom*>::iterator ci = facts_set_.begin(); ci != facts_set_.end(); ci++)
	{
		unsigned int fact_index = std::distance(facts_set_.begin(), ci);
		for (unsigned int i = 0; i < (*ci)->getCorrectedAtom().getArity(); i++)
		{
			delete (constraints_set_[fact_index])[i];
		}
		
		delete *ci;
	}
	
	for (std::vector<std::list<ReachableFact*>*>::const_iterator ci = reachable_set_.begin(); ci != reachable_set_.end(); ci++)
	{
		std::list<ReachableFact*>* reachable_list = *ci;
//		for (std::list<ReachableFact*>::const_iterator ci = reachable_list->begin(); ci != reachable_list->end(); ci++)
//		{
//			delete *ci;
//		}
		delete reachable_list;
	}
	
	for (std::vector<std::vector<std::pair<unsigned int, unsigned int> >** >::const_iterator ci = constraints_set_.begin(); ci != constraints_set_.end(); ci++)
	{
		delete[] *ci;
	}
	
	for (std::vector<ReachableTree*>::const_iterator ci = reachability_tree_.begin(); ci != reachability_tree_.end(); ci++)
	{
		delete *ci;
	}
#endif
}

bool ReachableSet::arePreconditionsEquivalent(const ReachableSet& other_set) const
{
	if (facts_set_.size() != other_set.facts_set_.size()) return false;
	
	if (facts_set_.size() == 0)
	{
		return true;
	}
	
	// Try to find a mapping.
	bool mask[facts_set_.size()];
	memset(mask, false, sizeof(bool) * facts_set_.size());
	return tryToFindMapping(mask, 0, other_set);
}

/*void ReachableSet::protectionMode(bool enter_protection_mode)
{
	if (enter_protection_mode == protection_mode_) return;
	
	protection_mode_ = enter_protection_mode;
	if (!enter_protection_mode)
	{
		reachability_tree_.insert(reachability_tree_.end(), protection_mode_reachability_tree_.begin(), protection_mode_reachability_tree_.end());
		protection_mode_reachability_tree_.clear();
	}
}*/

bool ReachableSet::tryToFindMapping(bool* mask, unsigned int index, const ReachableSet& other_set) const
{
	const ResolvedBoundedAtom* node_to_work_on = facts_set_[index];
	
	for (unsigned int i = 0; i < other_set.facts_set_.size(); i++)
	{
		if (mask[i]) continue;
		
		const ResolvedBoundedAtom* to_compare_with = other_set.facts_set_[i];
		
		if (node_to_work_on->canUnifyWith(*to_compare_with))
		{
			bool new_mask[facts_set_.size()];
			memcpy(new_mask, mask, sizeof(bool) * facts_set_.size());
			new_mask[i] = true;
			
			// TODO: Check if the same relationships holds between all the terms.
			if (index + 1 == facts_set_.size()) return true;
			
			if (tryToFindMapping(new_mask, index + 1, other_set))
			{
				return true;
			}
		}
	}
	
	return false;
}

void ReachableSet::initialiseInitialFacts(const std::vector< ReachableFact* >& initial_facts)
{
	/**
	 * Match all the initial facts with the facts in the set. We store the results only locally because we will use the
	 * processNewReachableFact to do the actual work for us.
	 */
	unsigned int index = 0;
	
	for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = facts_set_.begin(); ci != facts_set_.end(); ci++)
	{
		const ResolvedBoundedAtom* resolved_atom = *ci;
		
		// Check which initial facts can merge with the given atom.
		for (std::vector< ReachableFact* >::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
		{
			ReachableFact* initial_fact = *ci;
			if (initial_fact->isMarkedForRemoval()) continue;
			
			// The predicate of the fact in this set should be more general than the one we try to 'merge' with.
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			assert (resolved_atom->getCorrectedAtom().getPredicate().getId() != NO_INVARIABLE_INDEX);
			assert (initial_fact->getAtom().getPredicate().getId() != NO_INVARIABLE_INDEX);
#endif
			if (!resolved_atom->canSubstitude(*initial_fact))
			{
				continue;
			}
			
			processNewReachableFact(*initial_fact, index);
		}
		
		++index;
	}
}

void ReachableSet::addBoundedAtom(StepID step_id, const Atom& atom, const Bindings& bindings, PredicateManager& predicate_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[ReachableSet::addBoundedAtom] Add :";
	bounded_atom.print(std::cout, bindings);
	std::cout << " to :";
	print(std::cout);
	std::cout << "." << std::endl;
#endif

	ResolvedBoundedAtom* new_resolved_bounded_atom = new ResolvedBoundedAtom(step_id, atom, bindings, *eog_manager_, predicate_manager);
	facts_set_.push_back(new_resolved_bounded_atom);
	reachable_set_.push_back(new std::list<ReachableFact*>());
	
	// Generate the constraints sets.
	std::vector<std::pair<unsigned int, unsigned int> >** new_constraints_sets = new std::vector<std::pair<unsigned int, unsigned int> >*[atom.getArity()];
	for (unsigned int i = 0; i  < atom.getArity(); i++)
	{
		new_constraints_sets[i] = new std::vector<std::pair<unsigned int, unsigned int> >();
	}
	
	for (unsigned int i = 0; i < facts_set_.size() - 1; i++)
	{
		const ResolvedBoundedAtom* previous_resolved_bounded_atom = facts_set_[i];
		
		for (unsigned int j = 0; j < new_resolved_bounded_atom->getCorrectedAtom().getArity(); j++)
		{
			for (unsigned int k = 0; k < previous_resolved_bounded_atom->getCorrectedAtom().getArity(); k++)
			{
				if (&previous_resolved_bounded_atom->getVariableDomain(k) == &new_resolved_bounded_atom->getVariableDomain(j))
				{
					new_constraints_sets[j]->push_back(std::make_pair(i, k));
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "The " << j << "th term of " << *new_resolved_bounded_atom << " must match up with the " << k << "th term of " << *previous_resolved_bounded_atom << "." << std::endl;
#endif
				}
			}
		}
	}
	
	constraints_set_.push_back(new_constraints_sets);
}

void ReachableSet::equivalencesUpdated(unsigned int iteration)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	if (!isValid())
	{
		assert (false);
	}
#endif
	cache_is_valid_ = false;
	
	// Remove all sets which contains an out of date fact and add the fact which contains an up to date version.
	for (std::vector<std::list<ReachableFact*>*>::const_iterator ci = reachable_set_.begin(); ci != reachable_set_.end(); ci++)
	{
		std::list<ReachableFact*>* reachable_set = *ci;
		reachable_set->remove_if(boost::bind(&ReachableFact::isMarkedForRemoval, _1));
	}
	
	for (std::vector<ReachableTree*>::reverse_iterator ri = reachability_tree_.rbegin(); ri != reachability_tree_.rend(); ri++)
	{
		ReachableTree* reachable_tree = *ri;
		
		// All trees with reachable facts which only consists of the updated EOGs will remain and all other trees with reachable facts which
		// are marked as 'remove' and whose updated version is equal to that of the remaining trees will be merged with them.
		if (!reachable_tree->getRoot()->getReachableFact().isMarkedForRemoval())
		{
			reachable_tree->equivalencesUpdated(iteration, reachability_tree_);
		}
	}
	
	for (std::vector<ReachableTree*>::reverse_iterator ri = reachability_tree_.rbegin(); ri != reachability_tree_.rend(); ri++)
	{
		ReachableTree* reachable_tree = *ri;
		
		// All trees with reachable facts which only consists of the updated EOGs will remain and all other trees with reachable facts which
		// are marked as 'remove' and whose updated version is equal to that of the remaining trees will be merged with them.
		if (reachable_tree->getRoot()->getReachableFact().isMarkedForRemoval())
		{
			reachability_tree_.erase(ri.base() - 1);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
			delete reachable_tree;
#endif
		}
	}
	cached_reachability_tree_size_ = reachability_tree_.size();
}

bool ReachableSet::canSatisfyConstraints(const ReachableFact& reachable_fact, std::vector<ReachableFact*>& reachable_set) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[ReachableSet::canSatisfyConstraints] Add: " << reachable_fact << " to the set: " << std::endl;
	for (std::vector<ReachableFact*>::const_iterator ci = reachable_set.begin(); ci != reachable_set.end(); ci++)
	{
		ReachableFact* reachable_fact = *ci;
		std::cout << "* " << *reachable_fact << "." << std::endl;
	}
	std::cout << "Fact set: " << std::endl;
	for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = facts_set_.begin(); ci != facts_set_.end(); ci++)
	{
		std::cout << "* " << **ci << std::endl;
	}
#endif

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
/*	if (!facts_set_[reachable_set.size()]->getCorrectedAtom().getPredicate().canSubstitute(reachable_fact.getAtom().getPredicate()))
	{
		std::cout << facts_set_[reachable_set.size()]->getCorrectedAtom().getPredicate() << " can't substitute: " << reachable_fact.getAtom().getPredicate() << std::endl;
		assert (false);
	}
*/
	assert (reachable_fact.getAtom().getArity() == facts_set_[reachable_set.size()]->getCorrectedAtom().getArity());
#endif
	
	unsigned int index = reachable_set.size();
	std::vector<std::pair<unsigned int, unsigned int> >** constraints = constraints_set_[index];
	for (unsigned int i = 0; i < reachable_fact.getAtom().getArity(); i++)
	{
		std::vector<std::pair<unsigned int, unsigned int> >* variable_constraints = constraints[i];
		
		for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = variable_constraints->begin(); ci != variable_constraints->end(); ci++)
		{
			unsigned int fact_index = (*ci).first;
			unsigned int variable_index = (*ci).second;
			// Check if the relationship holds.
			if (&reachable_fact.getTermDomain(i) != &reachable_set[fact_index]->getTermDomain(variable_index))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "The " << i << "th term of : " << reachable_fact << " should match up with the " << variable_index << "th term of " << *reachable_set[fact_index] << ", but it doesn't!" << std::endl;
#endif
				return false;
			}
		}
	}
	return true;
}

bool ReachableSet::processNewReachableFact(ReachableFact& reachable_fact, unsigned int index)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	bool relevant = reachable_fact.getAtom().getPredicate().getName().compare(0, 2, "at") == 0 &&
	                reachable_fact.getTermDomain(0).getEquivalentObjects()[0]->getObject().getName().compare(0, 6, "rover1") == 0 &&
	                (reachable_fact.getTermDomain(1).getEquivalentObjects()[0]->getObject().getName().compare(0, 9, "waypoint0") == 0 ||
	                reachable_fact.getTermDomain(1).getEquivalentObjects()[0]->getObject().getName().compare(0, 9, "waypoint1") == 0) &&
	                index == 2 && facts_set_.size() == 5;
						 
	if (relevant)
	{
		std::cout << "[ReachableSet::processNewReachableFact] Add " << reachable_fact << "[" << index << "] to ";
		print(std::cout);
		std::cout << "." << std::endl;
	}
#endif
	// Need to be careful, if the predicate does not substitute than it might mean that the provided reachable fact might in fact 
	// not be part of this set!
	if (!facts_set_[index]->canSubstitude(reachable_fact))
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		if (relevant)
		{
			std::cout << "[ReachableSet::processNewReachableFact] Could not add because predicates do not match!" << std::endl;
		}
#endif
		return false;
	}
	
	// Check if the grounded constraints are satisfied.
	for (unsigned int i = 0; i < reachable_fact.getAtom().getArity(); i++)
	{
		if (facts_set_[index]->isGrounded(i) && 
			(
				!reachable_fact.getTermDomain(i).isGrounded() ||
				&reachable_fact.getTermDomain(i).getEquivalentObjects()[0]->getObject() != facts_set_[index]->getVariableDomain(i)[0]
			)
		)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			if (relevant)
			{
				std::cout << "[ReachableSet::processNewReachableFact] Grounded constraints are not satisfied!" << std::endl;
			}
#endif
			return false;
		}
	}
	reachable_set_[index]->push_back(&reachable_fact);
	
	// If the index is 0, it means it is the start of a new 'root'.
	if (index == 0)
	{
		ReachableTree* new_root = new ReachableTree(*this, constraints_set_);
		reachability_tree_.push_back(new_root);
		new_root->addFact(0, reachable_fact);
	}
	// Otherwise, we need to search for all sets the new node can be a part of and process these.
	else
	{
		for (std::vector<ReachableTree*>::const_iterator ci = reachability_tree_.begin(); ci != reachability_tree_.end(); ci++)
		{
			ReachableTree* reachable_tree = *ci;
			reachable_tree->addFact(index, reachable_fact);
		}
	}
	
	return true;
}

/**
 * ReachableNode
 */
ReachableNode::ReachableNode(const DomainTransitionGraphNode& dtg_node, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
	: ReachableSet(eog_manager), dtg_node_(&dtg_node)
{
	for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
	{
		addBoundedAtom((*ci)->getId(), (*ci)->getAtom(), dtg_node.getDTG().getBindings(), predicate_manager);
	}
}

ReachableNode::~ReachableNode()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transitions_.begin(); ci != reachable_transitions_.end(); ci++)
	{
		delete *ci;
	}
#endif
}


void ReachableNode::initialise(const std::vector<ReachableFact*>& initial_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (reachable_transitions_.size() > 0);
#endif
	initialiseInitialFacts(initial_facts);
	
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transitions_.begin(); ci != reachable_transitions_.end(); ci++)
	{
		ReachableTransition* reachable_transition = *ci;
		reachable_transition->initialise(initial_facts);
	}
}

void ReachableNode::addReachableTransition(ReachableTransition& reachable_transition)
{
	reachable_transitions_.push_back(&reachable_transition);
}

bool ReachableNode::propagateReachableFacts()
{	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (reachable_transitions_.size() > 0);
#endif
	// Find all those reachable transitions which also have fully reachable sets.
	bool could_propagate = false;
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transitions_.begin(); ci != reachable_transitions_.end(); ci++)
	{
		ReachableTransition* reachable_transition = *ci;
		
		if (reachable_transition->generateReachableFacts())
		{
			could_propagate = true;
		}
	}
	
	return could_propagate;
}

void ReachableNode::handleUpdatedEquivalences(unsigned iteration)
{
	if (!isValid())
	{
		assert (false);
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (reachable_transitions_.size() > 0);
#endif
	equivalencesUpdated(iteration);
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transitions_.begin(); ci != reachable_transitions_.end(); ci++)
	{
		ReachableTransition* reachable_transition = *ci;
		reachable_transition->handleUpdatedEquivalences(iteration);
	}
}

void ReachableNode::print(std::ostream& os) const
{
	//os << "ReachableNode: " << *dtg_node_ << std::endl;
	os << "ReachableNode: " << std::endl;
	
	for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = getFactsSet().begin(); ci != getFactsSet().end(); ci++)
	{
		os << **ci << "." << std::endl;
	}
}

std::ostream& operator<<(std::ostream& os, const ReachableNode& reachable_node)
{
	os << "ReachableNode: " << std::endl;
	return os;
}

/**
 * Reachable Transition.
 */
ReachableTransition::ReachableTransition(const MyPOP::SAS_Plus::Transition& transition, ReachableNode& from_node, const ReachableNode& to_node, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
	: ReachableSet(eog_manager), from_node_(&from_node), to_node_(&to_node), transition_(&transition), latest_processed_from_node_set_(0), latest_processed_transition_set_(0), use_previous_action_domains_(false), action_domains_(NULL)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "New reachable transition: " << transition << "." << std::endl;
#endif

	// Determine the set of grounded variables.
	std::set<const std::vector<const Object*>*> grounded_variables;
	for (std::vector<const Variable*>::const_iterator ci = transition.getAction().getVariables().begin(); ci != transition.getAction().getVariables().end(); ci++)
	{
		const Variable* variable = *ci;
		const std::vector<const Object*>& variable_domain = variable->getDomain(transition.getStepId(), transition.getFromNode().getDTG().getBindings());
		
		if (variable_domain.size() == 1)
		{
			const EquivalentObject& eo = eog_manager.getEquivalentObject(*variable_domain[0]);
			if (eo.getEquivalentObjectGroup().isGrounded())
			{
				grounded_variables.insert(&variable_domain);
			}
		}
	}

	// Find out which preconditions are not part of the from node.
	const std::vector<std::pair<const Atom*, InvariableIndex> >& all_preconditions = transition.getAllPreconditions();
	const Bindings& bindings = transition.getFromNode().getDTG().getBindings();
	
	std::vector<const std::vector<const Object*>* > transition_variable_domains;
	for (std::vector<const Variable*>::const_iterator ci = transition.getAction().getVariables().begin(); ci != transition.getAction().getVariables().end(); ci++)
	{
		const Variable* variable = *ci;
		const std::vector<const Object*>& variable_domain = variable->getDomain(transition.getStepId(), bindings);
		transition_variable_domains.push_back(&variable_domain);
	}
	bool processed_variable_domains[transition.getAction().getVariables().size()];
	memset(&processed_variable_domains[0], false, sizeof(bool) * transition.getAction().getVariables().size());
	
	for (unsigned int i = 0; i < transition.getAction().getVariables().size(); i++)
	{
		const std::vector<const Object*>* variable_domain = transition_variable_domains[i];
		domain_to_action_variable_mapping_[variable_domain] = i;
	}

	// Find out how the variables are linked to the facts in the from node and those in the set of preconditions which are not part of the 
	// from node.
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions.begin(); ci != all_preconditions.end(); ci++)
	{
		const Atom* precondition = (*ci).first;
		bool precondition_part_of_from_node = false;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the precondition: ";
		precondition->print(std::cout, bindings, transition.getStepId());
		std::cout << "." << std::endl;
#endif
		
		for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition.getFromNodePreconditions().begin(); ci != transition.getFromNodePreconditions().end(); ci++)
		{
			const Atom* from_node_precondition = (*ci).first;
			
			if (from_node_precondition == NULL) continue;
			
			unsigned int from_node_fact_index = std::distance(transition.getFromNodePreconditions().begin(), ci);

			const ResolvedBoundedAtom* resolved_bounded_atom = from_node.getFactsSet()[from_node_fact_index];
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			if (!bindings.canUnify(resolved_bounded_atom->getOriginalAtom(), resolved_bounded_atom->getId(), *from_node_precondition, transition.getStepId()))
			{
				std::cout << "Cannot unify: " << *resolved_bounded_atom << " with ";
				from_node_precondition->print(std::cout, bindings, transition.getStepId());
				std::cout << "." << std::endl;
			}
#endif
			
			if (bindings.areIdentical(resolved_bounded_atom->getOriginalAtom(), resolved_bounded_atom->getId(), *precondition, transition.getStepId()))
			{
				precondition_part_of_from_node = true;
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Process the from node precondition: ";
				from_node_precondition->print(std::cout, bindings, transition.getStepId());
				std::cout << "." << std::endl;
#endif
				
				// Compare all the variables of the precondition and see if they are linked to a variable of the action and link them accordingly.
				for (unsigned int i = 0; i < transition.getAction().getVariables().size(); i++)
				{
					if (processed_variable_domains[i]) continue;
					
					const std::vector<const Object*>* variable_domain = transition_variable_domains[i];
					
					for (unsigned int j = 0; j < resolved_bounded_atom->getCorrectedAtom().getArity(); j++)
					{
						if (from_node_precondition->getTerms()[j] == transition.getAction().getVariables()[i])
						{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "The " << i << "th variable is linked to the " << j << "th term of the " <<  from_node_fact_index << "th fact!" << std::endl;
#endif
							variable_to_values_mapping_[variable_domain] = new VariableToValues(from_node_fact_index, j, false);
							processed_variable_domains[i] = true;
							break;
						}
					}
				}
				
				break;
			}
		}
		
		if (precondition_part_of_from_node) continue;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Not part of the from node!" << std::endl;
#endif

		// Convert the precondition into a bounded atom.
		//BoundedAtom* bounded_precondition = new BoundedAtom(transition.getStepId(), *precondition);
		//addBoundedAtom(*bounded_precondition, bindings, predicate_manager);
		addBoundedAtom(transition.getStepId(), *precondition, bindings, predicate_manager);
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the precondition: ";
		bounded_precondition->print(std::cout, bindings, transition.getStepId());
		std::cout << "." << std::endl;
#endif
		
		// Check for the other facts are connected to the variables.
		for (unsigned int i = 0; i < transition.getAction().getVariables().size(); i++)
		{
			if (processed_variable_domains[i]) continue;
			
			const std::vector<const Object*>* variable_domain = transition_variable_domains[i];
			
			unsigned int precondition_index = getFactsSet().size() - 1;
			//for (unsigned int j = 0; j < bounded_precondition->getAtom().getArity(); j++)
			for (unsigned int j = 0; j < precondition->getArity(); j++)
			{
				if (precondition->getTerms()[j] == transition.getAction().getVariables()[i])
				{
					variable_to_values_mapping_[variable_domain] = new VariableToValues(precondition_index, j, true);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "The " << i << "th variable is linked to the " << j << "th term of the " <<  precondition_index << "th precondition!" << std::endl;
#endif
					processed_variable_domains[i] = true;
					break;
				}
			}
		}
//		delete bounded_precondition;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	// At the end all variables which are not bounded are free variables.
	for (unsigned int i = 0; i < transition.getAction().getVariables().size(); i++)
	{
		if (!processed_variable_domains[i])
		{
//			std::cout << "The " << i << "th variable of the transition " << transition << " is a free variable!" << std::endl;
			std::cout << "The " << i << "th variable is a free variable!" << std::endl;
		}
	}
#endif
	
	/**
	 * Process the effects, we need to be carefull because the way we construct the LTGs. To reduce the number of nodes and disconnected
	 * graphs we allow two LTG nodes to be merged even if the way the terms connect to the variables is different. E.g. we allow the following
	 * two nodes to merge in the Zeno domain.
	 * 
	 * (at plane city)                  --- Fly --=>     (at plane city')
	 * (fuel-level plane fl^)                            (fuel-level plane fl'^)
	 * 
	 * AND
	 * 
	 * (at plane city)                  - Refuel -=>     (at plane city)
	 * (fuel-level plane fl^)                            (fuel-level plane fl'^)
	 * 
	 * (^) = grounded
	 * 
	 * In the second case the cities are bound to the same variable domain which confuses things. So instead we need to look at the actual variables
	 * terms are linked to. This is only a problem for lifted terms so if this appears in practice the effects can be treated as free variables.
	 */
	const std::vector<std::pair<const Atom*, InvariableIndex> >& effects = transition_->getAllEffects();
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		const Atom* effect = (*ci).first;
		if (effect->isNegative()) continue;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the effect: ";
		effect->print(std::cout, bindings, transition_->getStepId());
		std::cout << "." << std::endl;
#endif
		
		// Check if any of the effect's terms are free variables.
		bool free_variables[effect->getArity()];
		memset(&free_variables[0], false, sizeof(bool) * effect->getArity());
		
		for (unsigned int i = 0; i < transition.getAction().getVariables().size(); i++)
		{
			if (!processed_variable_domains[i])
			{
				for (std::vector<const Term*>::const_iterator ci = effect->getTerms().begin(); ci != effect->getTerms().end(); ci++)
				{
					const Term* term = *ci;
					unsigned int term_index = std::distance(static_cast<std::vector<const Term*>::const_iterator>(effect->getTerms().begin()), ci);
					if (term == transition.getAction().getVariables()[i])
					{
						// Term is a free variable.
						free_variables[term_index] = true;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
						std::cout << "The " << i << "th term is free!" << std::endl;
#endif
					}
				}
			}
		}
		
		ResolvedEffect* resolved_effect = new ResolvedEffect(transition.getStepId(), *effect, bindings, eog_manager, free_variables, predicate_manager);
		effects_.push_back(resolved_effect);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Created new reachable transition: " << transition << "." << std::endl;
	std::cout << "Preconditions hold by the from node: " << std::endl;
	for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = from_node_->getFactsSet().begin(); ci != from_node_->getFactsSet().end(); ci++)
	{
		std::cout << " * " << **ci << std::endl;
	}
	
	std::cout << "Preconditions hold by the transition: " << std::endl;
	for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = getFactsSet().begin(); ci != getFactsSet().end(); ci++)
	{
		std::cout << " * " << **ci << std::endl;
	}
	
	std::cout << "Transition variables: ";
	for (std::vector<const Variable*>::const_iterator ci = transition.getAction().getVariables().begin(); ci != transition.getAction().getVariables().end(); ci++)
	{
		std::cout << *ci << ", ";
	}
	std::cout << "." << std::endl;
	
	std::cout << "Effects: " << std::endl;
	for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
	{
		ResolvedBoundedAtom* rba = *ci;
		std::cout << " * " << **ci;
		
		std::cout << "{";
		for (unsigned int i = 0; i < rba->getCorrectedAtom().getArity(); i++)
		{
			std::cout << &rba->getVariableDomain(i);
			std::cout << "|" << rba->getOriginalAtom().getTerms()[i];
			std::cout << ", ";
		}
		std::cout << "}";
		
		std::cout << std::endl;
		
	}
#endif
}

ReachableTransition::~ReachableTransition()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
	{
		delete *ci;
	}
	
	for (std::map<const std::vector<const Object*>*, VariableToValues*>::const_iterator ci = variable_to_values_mapping_.begin(); ci != variable_to_values_mapping_.end(); ci++)
	{
		delete (*ci).second;
	}
	
	for (std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator ci = effect_propagation_listeners_.begin(); ci != effect_propagation_listeners_.end(); ci++)
	{
		delete *ci;
	}
	
	// Deleted by the 
	for (std::vector<EquivalentObjectGroup**>::const_iterator ci = processed_groups_.begin(); ci != processed_groups_.end(); ci++)
	{
		delete[] *ci;
	}
	
	if (use_previous_action_domains_)
	{
		delete[] action_domains_;
	}
#endif
}

void ReachableTransition::finalise(const std::vector<ReachableSet*>& all_reachable_sets)
{
	if (!isValid())
	{
		assert (false);
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Link all the effects of " << *this << " to all the sets which can be unified with them." << std::endl;
#endif
	for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
	{
		const ResolvedEffect* effect = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the effect: " << *effect << std::endl;
#endif
		std::vector<std::pair<ReachableSet*, unsigned int> >* preconditions_reached_by_effect_ = new std::vector<std::pair<ReachableSet*, unsigned int> >();
		effect_propagation_listeners_.push_back(preconditions_reached_by_effect_);
		
		// Find all preconditions which match the effect.
		for (std::vector<ReachableSet*>::const_iterator ci = all_reachable_sets.begin(); ci != all_reachable_sets.end(); ci++)
		{
			ReachableSet* reachable_set = *ci;
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Process the set: " << std::endl;
			reachable_set->print(std::cout);
			std::cout << std::endl;
#endif
			
			const std::vector<const ResolvedBoundedAtom*>& preconditions = reachable_set->getFactsSet();
			
			for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const ResolvedBoundedAtom* precondition = *ci;
				if (precondition->canUnifyWith(*effect))
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "Accepted candidate: " << *precondition << "." << std::endl;
#endif
					preconditions_reached_by_effect_->push_back(std::make_pair(reachable_set, std::distance(preconditions.begin(), ci)));
				}
			}
		}
	}
}

void ReachableTransition::initialise(const std::vector<ReachableFact*>& initial_facts)
{
	initialiseInitialFacts(initial_facts);
}

bool ReachableTransition::generateReachableFacts()
{
	unsigned int current_number_of_from_node_trees = from_node_->getCachedReachableTreesSize();
	unsigned int current_number_of_transitions_trees = getCachedReachableTreesSize();
	
	bool new_facts_reached = false;

	for (unsigned int from_tree_index = 0; from_tree_index < current_number_of_from_node_trees; ++from_tree_index)
	{
		ReachableTree* reachable_from_tree = from_node_->getReachableTrees()[from_tree_index];
		assert (reachable_from_tree != NULL);
		unsigned int nr_of_leafs_from_tree = reachable_from_tree->getCachedNumberOfLeafs();
		
		if (getFactsSet().empty())
		{
			for (unsigned int leaf_index = 0; leaf_index < nr_of_leafs_from_tree; ++leaf_index)
			{
				assert (leaf_index < reachable_from_tree->getLeaves().size());
				assert (&reachable_from_tree->getLeaves()[leaf_index]->getTree() == reachable_from_tree);
				
				const ReachableTreeNode* leaf_node = reachable_from_tree->getLeaves()[leaf_index];
				if (leaf_node->hasBeenProcessed()) continue;
				
				for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
				{
					unsigned int effect_index = std::distance(static_cast<std::vector<ResolvedEffect*>::const_iterator>(effects_.begin()), ci);
					const ResolvedEffect* effect = *ci;
					if (createNewReachableFact(*effect, effect_index, *leaf_node, NULL))
					{
						new_facts_reached = true;
					}
				}
			}
		}
		else
		{
			for (unsigned int transition_tree_index = 0; transition_tree_index < current_number_of_transitions_trees; ++transition_tree_index)
			{
				ReachableTree* reachable_transition_tree = getReachableTrees()[transition_tree_index];
				assert (reachable_transition_tree != NULL);
				unsigned int nr_of_leafs_transition_tree = reachable_transition_tree->getCachedNumberOfLeafs();
				
				for (unsigned int node_leaf_index = 0; node_leaf_index < nr_of_leafs_from_tree; ++node_leaf_index)
				{
					const ReachableTreeNode* from_leaf_node = reachable_from_tree->getLeaves()[node_leaf_index];
					assert (&reachable_from_tree->getLeaves()[node_leaf_index]->getTree() == reachable_from_tree);
					for (unsigned int transition_leaf_index = 0; transition_leaf_index < nr_of_leafs_transition_tree; ++transition_leaf_index)
					{
						assert (&reachable_transition_tree->getLeaves()[transition_leaf_index]->getTree() == reachable_transition_tree);
						const ReachableTreeNode* transition_leaf_node = reachable_transition_tree->getLeaves()[transition_leaf_index];
						
						if (from_leaf_node->hasBeenProcessed() && transition_leaf_node->hasBeenProcessed()) continue;
						
						for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
						{
							unsigned int effect_index = std::distance(static_cast<std::vector<ResolvedEffect*>::const_iterator>(effects_.begin()), ci);
							const ResolvedEffect* effect = *ci;
					
							// We've got a new pair!
							if (createNewReachableFact(*effect, effect_index, *from_leaf_node, transition_leaf_node))
							{
								new_facts_reached = true;
							}
						}
					}
				}
			}
		}
	}
	return new_facts_reached;
}

void ReachableTransition::handleUpdatedEquivalences(unsigned int iteration)
{
	if (!isValid())
	{
		assert (false);
	}
	equivalencesUpdated(iteration);
	
	for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
	{
		(*ci)->updateVariableDomains();
	}

	for (std::vector<EquivalentObjectGroup**>::const_iterator ci = processed_groups_.begin(); ci != processed_groups_.end(); ci++)
	{
		EquivalentObjectGroup** processed_group = *ci;
		for (unsigned int i = 0; i < transition_->getAction().getVariables().size(); i++)
		{
			if (processed_group[i] == NULL) continue;
			processed_group[i] = &processed_group[i]->getRootNode();
		}
	}
}

bool ReachableTransition::createNewReachableFact(const ResolvedEffect& effect, unsigned int effect_index, const ReachableTreeNode& from_reachable_node, const ReachableTreeNode* transition_reachable_node)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << transition_->getAction().getPredicate() << " - Try to create new facts for: " << effect << std::endl;
	std::cout << "From node: " << from_reachable_node << std::endl;
	if (transition_reachable_node != NULL)
	{
		std::cout << "Transition node: " << *transition_reachable_node << std::endl;
	}
#endif
	EquivalentObjectGroup** effect_domains = new EquivalentObjectGroup*[effect.getCorrectedAtom().getArity()];
	
	if (!use_previous_action_domains_)
	{
		action_domains_ = new EquivalentObjectGroup*[transition_->getAction().getVariables().size()];
	}
	memset(action_domains_, 0, transition_->getAction().getVariables().size() * sizeof(EquivalentObjectGroup*));

	bool new_facts_reached = false;
	
	for (unsigned int i = 0; i < effect.getCorrectedAtom().getArity(); i++)
	{
		if (effect.isFreeVariable(i))
		{
			continue;
		}
		
		VariableToValues* values = variable_to_values_mapping_[&effect.getVariableDomain(i)];
		if (values->is_transition_)
		{
			const ReachableTreeNode& rtn = *(transition_reachable_node->cbegin() + (transition_reachable_node->getLevel() - values->fact_index_));
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "[Transition node] Translate " << values->fact_index_ << " to: " << (transition_reachable_node->getLevel() - values->fact_index_) << " -> " << rtn << std::endl;
#endif
			effect_domains[i] = &rtn.getReachableFact().getTermDomain(values->term_index_);
		}
		else
		{
			const ReachableTreeNode& rtn = *(from_reachable_node.cbegin() + (from_reachable_node.getLevel() - values->fact_index_));
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "[From node] Translate " << values->fact_index_ << " to: " << (from_reachable_node.getLevel() - values->fact_index_) << " -> " << rtn << std::endl;
#endif
			effect_domains[i] = &rtn.getReachableFact().getTermDomain(values->term_index_);
		}
		action_domains_[domain_to_action_variable_mapping_[&effect.getVariableDomain(i)]] = effect_domains[i];
	}

	bool already_processed = false;
	for (std::vector<EquivalentObjectGroup**>::const_iterator ci = processed_groups_.begin(); ci != processed_groups_.end(); ci++)
	{
		EquivalentObjectGroup** processed_group = *ci;

		bool is_equivalent = true;
		for (unsigned int i = 0; i < transition_->getAction().getVariables().size(); i++)
		{
			if (processed_group[i] != action_domains_[i])
			{
				is_equivalent = false;
				break;
			}
		}
		
		if (is_equivalent)
		{
			already_processed = true;
			break;
		}
	}
	
	if (already_processed)
	{
		use_previous_action_domains_ = true;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
		delete[] effect_domains;
#endif
		return false;
	}
	use_previous_action_domains_ = false;
	processed_groups_.push_back(action_domains_);

	std::vector<ReachableFact*> new_reachable_facts;
	effect.createReachableFacts(new_reachable_facts, effect_domains);

#ifdef DTG_REACHABILITY_KEEP_TIME
	ReachableTransition::generated_new_reachable_facts += new_reachable_facts.size();
#endif
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	if (effect.getCorrectedAtom().getPredicate().getName().compare(0, 10, "fuel-level") == 0)
	{
		std::cout << "Process the resolved effect: " << effect << " yielded " << new_reachable_facts.size() << " effects!" << std::endl;
		std::cout << "From node tree: " << std::endl;
		from_reachable_node.printCompleteTree(std::cout);
		if (transition_reachable_node != NULL)
		{
			std::cout << "Transition node tree: " << std::endl;
			transition_reachable_node->printCompleteTree(std::cout);
		}
	}
#endif

	for (std::vector<ReachableFact*>::const_iterator ci = new_reachable_facts.begin(); ci != new_reachable_facts.end(); ci++)
	{
		ReachableFact* new_reachable_fact = *ci;
		// Make sure the fact hasn't been reached before!
		const EquivalentObjectGroup* best_eog = NULL;
		bool zero_arity_reached_fact = new_reachable_fact->getAtom().getArity() == 0;
		if (!zero_arity_reached_fact)
		{
			for (unsigned int i = 0; i < new_reachable_fact->getAtom().getArity(); i++)
			{
				const EquivalentObjectGroup& eog = new_reachable_fact->getTermDomain(i);
				if (best_eog == NULL)
				{
					best_eog = &eog;
				}
				
				else if (best_eog->getReachableFacts().size() > eog.getReachableFacts().size())
				{
					best_eog = &eog;
				}
			}
		}
		else
		{
			best_eog = &eog_manager_->getZeroArityEOG();
		}
		
		bool already_reached = false;
		for (std::vector<ReachableFact*>::const_iterator ci = best_eog->getReachableFacts().begin(); ci != best_eog->getReachableFacts().end(); ci++)
		{
			if ((*ci)->isIdenticalTo(*new_reachable_fact))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "New reachable effect: " << *new_reachable_fact << " already achieved by " << **ci << "." << std::endl;
#endif
				already_reached = true;
				break;
			}
		}
		if (already_reached)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
			delete new_reachable_fact;
#endif
			continue;
		}
#ifdef DTG_REACHABILITY_KEEP_TIME
		++ReachableTransition::accepted_new_reachable_facts;
#endif
		std::vector<std::pair<ReachableSet*, unsigned int> >* listeners = effect_propagation_listeners_[effect_index];
		
		for (std::vector<std::pair<ReachableSet*, unsigned int> >::const_iterator ci = listeners->begin(); ci != listeners->end(); ci++)
		{
			(*ci).first->processNewReachableFact(*new_reachable_fact, (*ci).second);
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "New reachable effect: " << *new_reachable_fact << "." << std::endl;
		std::cerr << "New reachable effect: " << *new_reachable_fact << "." << std::endl;
#endif
		
		new_facts_reached = true;
		
		// Update the relevant equivalent object groups.
		if (!zero_arity_reached_fact)
		{
			for (unsigned int i = 0; i < new_reachable_fact->getAtom().getArity(); i++)
			{
				// Make sure not to add the fact to the same EOG!
				EquivalentObjectGroup& to_add_to = new_reachable_fact->getTermDomain(i);
				
				bool already_added = false;
				for (unsigned int j = 0; j < i; j++)
				{
					EquivalentObjectGroup& previously_added_to = new_reachable_fact->getTermDomain(j);
					if (&to_add_to == &previously_added_to)
					{
						already_added = true;
						break;
					}
				}
				
				if (!already_added)
				{
					new_reachable_fact->getTermDomain(i).addReachableFact(*new_reachable_fact);
				}
			}
		}
		else
		{
			eog_manager_->getZeroArityEOG().addReachableFact(*new_reachable_fact);
		}
	}
	
	return new_facts_reached;
}

void ReachableTransition::print(std::ostream& os) const
{
	os << "Reachable transition: ";
	transition_->getAction().print(os, transition_->getFromNode().getDTG().getBindings(), transition_->getStepId());
	os << std::endl;
	os << " Fact set: " << std::endl;
	for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = getFactsSet().begin(); ci != getFactsSet().end(); ci++)
	{
		os << **ci << "." << std::endl;
	}
	
	os << "FROM: ";
	from_node_->print(os);
	os << "TO: ";
	to_node_->print(os);
}

std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition)
{
	os << "Reachable transition: " << reachable_transition.getTransition() << "." << std::endl;
	return os;
}

/*******************************
 * DTGReachability
*******************************/

DTGReachability::DTGReachability(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::SAS_Plus::DomainTransitionGraph& dtg_graph, const MyPOP::TermManager& term_manager, PredicateManager& predicate_manager)
	: term_manager_(&term_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "DTG Reachability on graph: " << dtg_graph << "." << std::endl;
#endif

	// Initialise the individual groups per object.
	equivalent_object_manager_ = new EquivalentObjectGroupManager(dtg_manager, dtg_graph, term_manager);
	
	std::map<const DomainTransitionGraphNode*, ReachableNode*> node_mapping;
	std::vector<ReachableSet*> all_reachable_sets;
	std::vector<ReachableTransition*> all_reachable_transitions;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << *dtg_node << std::endl;
		dtg_node->print(std::cout);
#endif
		ReachableNode* reachable_node = new ReachableNode(*dtg_node, *equivalent_object_manager_, predicate_manager);
		node_mapping[dtg_node] = reachable_node;
		
		// DTG nodes which have no transitions, we do not care what facts can be made true for them.
//		if (dtg_node->getTransitions().size() > 0)
//		{
			all_reachable_sets.push_back(reachable_node);
//		}
	}
	
	for (std::map<const DomainTransitionGraphNode*, ReachableNode*>::const_iterator ci = node_mapping.begin(); ci != node_mapping.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		ReachableNode* reachable_from_node = (*ci).second;
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			ReachableNode* reachable_to_node = node_mapping[&transition->getToNode()];
			ReachableTransition* reachable_transition = new ReachableTransition(**ci, *reachable_from_node, *reachable_to_node, *equivalent_object_manager_, predicate_manager);
			 
			reachable_from_node->addReachableTransition(*reachable_transition);

			all_reachable_sets.push_back(reachable_transition);
			
			// For transitions which have a to node with no transitions we still need to create a mapping from its effects to other nodes (with transitions!) 
			// which have these effects as preconditions.
			all_reachable_transitions.push_back(reachable_transition);
		}
	}

	std::cerr << "Before: " << all_reachable_sets.size() << std::endl;
	
	// Search for a reachable node which contains the same nodes as a reachable transition and check if the node has a transition which contains the same 
	// facts as the from node of the found transition.
	std::set<const ReachableSet*> reachable_set_to_remove;
	for (std::map<const DomainTransitionGraphNode*, ReachableNode*>::const_iterator ci = node_mapping.begin(); ci != node_mapping.end(); ci++)
	{
		ReachableNode* reachable_from_node = (*ci).second;
		
		for (std::vector<ReachableTransition*>::reverse_iterator ri = all_reachable_transitions.rbegin(); ri != all_reachable_transitions.rend(); ri++)
		{
			ReachableTransition* reachable_transition = *ri;
			
			if (reachable_set_to_remove.count(reachable_transition) != 0) continue;
			
			if (reachable_from_node->arePreconditionsEquivalent(*reachable_transition))
			{
				// Check if the reachable from node has a transition which contains the same facts as the from node of the transition.
				for (std::vector<ReachableTransition*>::reverse_iterator ri2 = reachable_from_node->getReachableTransitions().rbegin(); ri2 != reachable_from_node->getReachableTransitions().rend(); ri2++)
				{
					ReachableTransition* from_node_reachable_transition = *ri2;
					
					if (reachable_set_to_remove.count(from_node_reachable_transition) != 0) continue;

					if (from_node_reachable_transition->arePreconditionsEquivalent(reachable_transition->getFromNode()))
					{
						// For now, we remove the transition of the node with the lowest out bound!
						if (from_node_reachable_transition->getFromNode().getReachableTransitions().size() < reachable_from_node->getReachableTransitions().size())
						{
							reachable_set_to_remove.insert(from_node_reachable_transition);
							from_node_reachable_transition->markAsRemoved();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "[DTGReachability::DTGReachability] Remove the transition: " << std::endl;
							from_node_reachable_transition->print(std::cout);
							std::cout << std::endl;
							std::cout << "In favour of: ";
							reachable_transition->print(std::cout);
							std::cout << "." << std::endl;
#endif
						}
						else
						{
							reachable_set_to_remove.insert(reachable_transition);
							reachable_transition->markAsRemoved();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
							std::cout << "[DTGReachability::DTGReachability] Remove the transition: " << std::endl;
							reachable_transition->print(std::cout);
							std::cout << std::endl;
							std::cout << "In favour of: ";
							from_node_reachable_transition->print(std::cout);
							std::cout << "." << std::endl;
#endif
							break;
						}
					}
				}
			}
		}
	}

	// Remove all the transitions which have been marked for removal.
	for (std::vector<ReachableTransition*>::reverse_iterator ri = all_reachable_transitions.rbegin(); ri != all_reachable_transitions.rend(); ri++)
	{
		ReachableTransition* transition = *ri;
		if (reachable_set_to_remove.count(transition) != 0)
		{
			all_reachable_transitions.erase(ri.base() - 1);
		}
	}
	
	// Remove all the nodes which have no transitions!
	for (std::map<const DomainTransitionGraphNode*, ReachableNode*>::const_iterator ci = node_mapping.begin(); ci != node_mapping.end(); ci++)
	{
		ReachableNode* reachable_from_node = (*ci).second;
		
		for (std::vector<ReachableTransition*>::reverse_iterator ri = reachable_from_node->getReachableTransitions().rbegin(); ri != reachable_from_node->getReachableTransitions().rend(); ri++)
		{
			if (reachable_set_to_remove.count(*ri) != 0)
			{
				reachable_from_node->getReachableTransitions().erase(ri.base() - 1);
//				delete *ri;
			}
		}
		
		bool mark_for_removal = reachable_from_node->getReachableTransitions().size() == 0;
		if (mark_for_removal)
		{
			// Check if no transition is going to this node.
			for (std::vector<ReachableTransition*>::reverse_iterator ri = all_reachable_transitions.rbegin(); ri != all_reachable_transitions.rend(); ri++)
			{
				ReachableTransition* transition = *ri;
				
				if (&transition->getFromNode() == reachable_from_node)
				{
					mark_for_removal = false;
					break;
				}
			}

			if (mark_for_removal)
			{
				reachable_set_to_remove.insert(reachable_from_node);
				reachable_from_node->markAsRemoved();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "[DTGReachability::DTGReachability] Remove the node: " << std::endl;
				reachable_from_node->print(std::cout);
				std::cout << std::endl;
#endif
			}
		}
		
		if (!mark_for_removal)
		{
			reachable_nodes_.push_back(reachable_from_node);
		}
	}
	
	// Remove all the nodes which have no transitions!
	for (std::vector<ReachableSet*>::reverse_iterator ri = all_reachable_sets.rbegin(); ri != all_reachable_sets.rend(); ri++)
	{
		ReachableSet* reachable_set = *ri;
		if (reachable_set_to_remove.count(reachable_set) != 0)
		{
			all_reachable_sets.erase(ri.base() - 1);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
			delete reachable_set;
#endif
		}
	}
	
	std::cerr << "After: " << all_reachable_sets.size() << std::endl;

	for (std::vector<ReachableTransition*>::const_iterator ci = all_reachable_transitions.begin(); ci != all_reachable_transitions.end(); ci++)
	{
		(*ci)->finalise(all_reachable_sets);
	}
	
	// All predicate should have number at this point. Next we record which predicate can substitute other predicates.
	for (std::vector<Predicate*>::const_iterator ci = predicate_manager.getManagableObjects().begin(); ci != predicate_manager.getManagableObjects().end(); ci++)
	{
		(*ci)->initCache(predicate_manager.getManagableObjects());
	}
	
	//predicate_id_to_reachable_sets_mapping_ = new std::vector<std::pair<ReachableSet*, unsigned int> >*[predicate_manager.getManagableObjects().size()];
	predicate_id_to_reachable_sets_mapping_ = new std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >(predicate_manager.getManagableObjects().size());
	for (unsigned int i = 0; i < predicate_manager.getManagableObjects().size(); i++)
	{
		(*predicate_id_to_reachable_sets_mapping_)[i] = new std::vector<std::pair<ReachableSet*, unsigned int> >();
		Predicate* corresponding_predicate = predicate_manager.getManagableObjects()[i];
		
		// Find all facts of the reachable sets whose predicate can substitute for this predicate.
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			ReachableNode* reachable_node = *ci;
			for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = reachable_node->getFactsSet().begin(); ci != reachable_node->getFactsSet().end(); ci++)
			{
				unsigned int index = std::distance(reachable_node->getFactsSet().begin(), ci);
				const ResolvedBoundedAtom* resolved_bounded_atom = *ci;
				
				if (resolved_bounded_atom->getCorrectedAtom().getPredicate().canSubstitute(*corresponding_predicate) ||
				    corresponding_predicate->canSubstitute(resolved_bounded_atom->getCorrectedAtom().getPredicate()))
				{
					(*predicate_id_to_reachable_sets_mapping_)[i]->push_back(std::make_pair(reachable_node, index));
				}
			}
		}
		
		// Same for the transitions.
		for (std::vector<ReachableTransition*>::const_iterator ci = all_reachable_transitions.begin(); ci != all_reachable_transitions.end(); ci++)
		{
			ReachableTransition* reachable_transition = *ci;
			for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = reachable_transition->getFactsSet().begin(); ci != reachable_transition->getFactsSet().end(); ci++)
			{
				unsigned int index = std::distance(reachable_transition->getFactsSet().begin(), ci);
				const ResolvedBoundedAtom* resolved_bounded_atom = *ci;
				if (resolved_bounded_atom->getCorrectedAtom().getPredicate().canSubstitute(*corresponding_predicate))
				{
					(*predicate_id_to_reachable_sets_mapping_)[i]->push_back(std::make_pair(reachable_transition, index));
				}
			}
		}
	}
}


DTGReachability::~DTGReachability()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_CLEANUP
	delete equivalent_object_manager_;
	for (std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator ci = predicate_id_to_reachable_sets_mapping_->begin(); ci != predicate_id_to_reachable_sets_mapping_->end(); ci++)
	{
		delete *ci;
	}
	delete predicate_id_to_reachable_sets_mapping_;
	
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		delete *ci;
	}
#endif
}


void DTGReachability::performReachabilityAnalysis(std::vector<const ReachableFact*>& result, const std::vector<const BoundedAtom*>& initial_facts, const Bindings& bindings)
{
//	double time_propagating = 0;
//	double time_iterating = 0;
//	double time_establishing_equivalances = 0;
//	unsigned int amount_of_iterating = 0;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Start performing reachability analysis." << std::endl;
#endif

#ifdef DTG_REACHABILITY_KEEP_TIME
	struct timeval start_time_eog;
	gettimeofday(&start_time_eog, NULL);
#endif
	
	// Transform the set of initial facts into reachable facts, which means we drop the variable domains
	// and work solely with equivalent object groups.
	std::vector<ReachableFact*> established_reachable_facts;
	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		ReachableFact* initial_reachable_fact = new ReachableFact(**ci, bindings, *equivalent_object_manager_);
		established_reachable_facts.push_back(initial_reachable_fact);
	}

	equivalent_object_manager_->initialise(established_reachable_facts);
#ifdef DTG_REACHABILITY_KEEP_TIME
	unsigned int total_number_of_eog = equivalent_object_manager_->getNumberOfEquivalentGroups();
#endif
	
	equivalent_object_manager_->updateEquivalences();
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		(*ci)->handleUpdatedEquivalences(0);
	}
	
#ifdef DTG_REACHABILITY_KEEP_TIME
	unsigned int total_number_of_eog_after_update = equivalent_object_manager_->getNumberOfEquivalentGroups();
#endif

#ifdef DTG_REACHABILITY_KEEP_TIME
	struct timeval end_time_eog;
	gettimeofday(&end_time_eog, NULL);

	double time_spend_eog = end_time_eog.tv_sec - start_time_eog.tv_sec + (end_time_eog.tv_usec - start_time_eog.tv_usec) / 1000000.0;
	std::cerr << "Initialise EOGs: " << time_spend_eog << " seconds. Total EOGs: " << total_number_of_eog << " after update: " << total_number_of_eog_after_update << "." << std::endl;
	
	struct timeval start_time_init;
	gettimeofday(&start_time_init, NULL);
#endif
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Find initial supported DTG nodes." << std::endl;
#endif
	
	mapInitialFactsToReachableSets(established_reachable_facts);
	
#ifdef DTG_REACHABILITY_KEEP_TIME
	struct timeval end_time_init;
	gettimeofday(&end_time_init, NULL);

	double time_spend_initial = end_time_init.tv_sec - start_time_init.tv_sec + (end_time_init.tv_usec - start_time_init.tv_usec) / 1000000.0;
	std::cerr << "Converting initial facts for " << reachable_nodes_.size() << " nodes: " << time_spend_initial << " seconds. Average = " << (time_spend_initial / reachable_nodes_.size()) << std::endl;
#endif
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "All DTG nodes after adding the initial facts: " << std::endl;
	
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		ReachableNode* reachable_node = *ci;
		reachable_node->print(std::cout);
		std::cout << std::endl;
	}
	equivalent_object_manager_->print(std::cout);
#endif
	
	// Now for every LTG node for which we have found a full set we check if their reachable transitions have the same property and we
	// can generate new reachable facts from these.
	bool done = false;
	unsigned int iteration = 1;
	while (!done)
	{
#ifdef DTG_REACHABILITY_KEEP_TIME
		struct timeval start_time_iteration;
		gettimeofday(&start_time_iteration, NULL);
#endif
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Start propagating reachable facts." << std::endl;
#endif
		done = true;
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			if ((*ci)->propagateReachableFacts())
			{
				done = false;
			}
		}

		if (!done)
		{
			equivalent_object_manager_->updateEquivalences();
			for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
			{
				(*ci)->handleUpdatedEquivalences(iteration);
			}
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "End of the iteration. Results so far: " << std::endl;
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			(*ci)->print(std::cout);
			std::cout << std::endl;
		}
		std::cout << "EOGs: ";
		equivalent_object_manager_->print(std::cout);
		std::cout << std::endl;
#endif

#ifdef DTG_REACHABILITY_KEEP_TIME
		
		struct timeval end_time_iteration;
		gettimeofday(&end_time_iteration, NULL);

		double time_spend_on_iteration = end_time_iteration.tv_sec - start_time_iteration.tv_sec + (end_time_iteration.tv_usec - start_time_iteration.tv_usec) / 1000000.0;
		std::cerr << iteration << "th iteration. Number of EOGs: " << equivalent_object_manager_->getNumberOfEquivalentGroups() << ". Time spend: " << time_spend_on_iteration << "." << std::endl;
		
		unsigned int nr_leaves = 0;
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			ReachableNode* reachable_node = *ci;
			for (std::vector<ReachableTree*>::const_iterator ci = reachable_node->getReachableTrees().begin(); ci != reachable_node->getReachableTrees().end(); ci++)
			{
				nr_leaves += (*ci)->getTotalNumberOfLeafs();
			}
			for (std::vector<ReachableTransition*>::const_iterator ci = reachable_node->getReachableTransitions().begin(); ci != reachable_node->getReachableTransitions().end(); ci++)
			{
				ReachableTransition* reachable_transition = *ci;
				
				for (std::vector<ReachableTree*>::const_iterator ci = reachable_transition->getReachableTrees().begin(); ci != reachable_transition->getReachableTrees().end(); ci++)
				{
					nr_leaves += (*ci)->getTotalNumberOfLeafs();
				}
			}
		}
		std::cerr << "Total number of complete sets: " << nr_leaves << std::endl;
#endif
		
		++iteration;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "DONE! All the equivalent objects: " << std::endl;
	equivalent_object_manager_->printAll(std::cout);
	std::cout << std::endl;

	std::cout << "DONE! All resulting nodes: " << std::endl;
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		std::cout << "* ";
		(*ci)->print(std::cout);
		std::cout << "." << std::endl;
	}
#endif
	
#ifdef DTG_REACHABILITY_KEEP_TIME
	std::cerr << "Generated facts / Accepted facts [%] - " << ReachableTransition::generated_new_reachable_facts << " / " << ReachableTransition::accepted_new_reachable_facts << " [" << (((double)(ReachableTransition::accepted_new_reachable_facts) / ReachableTransition::generated_new_reachable_facts) * 100) << "%]" << std::endl;
	std::cerr << "Compression rate " << 100 - ((double)equivalent_object_manager_->getNumberOfEquivalentGroups() / (double)total_number_of_eog) * 100 << std::endl;
#endif
	
	equivalent_object_manager_->getAllReachableFacts(result);
}

void DTGReachability::mapInitialFactsToReachableSets(const std::vector<ReachableFact*>& initial_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "MAP INITIAL FACTS!" << std::endl;
#endif
	
	for (std::vector<ReachableFact*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		ReachableFact* initial_fact = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the initial fact: " << *initial_fact << " - marked? " << initial_fact->isMarkedForRemoval() << ". ID: " << initial_fact->getAtom().getPredicate().getId() << std::endl;
#endif
		if (initial_fact->isMarkedForRemoval()) continue;
		
		std::vector<std::pair<ReachableSet*, unsigned int> >* reachable_sets = (*predicate_id_to_reachable_sets_mapping_)[initial_fact->getAtom().getPredicate().getId()];
		
		assert (reachable_sets != NULL);
		
		for (std::vector<std::pair<ReachableSet*, unsigned int> >::const_iterator ci = reachable_sets->begin(); ci != reachable_sets->end(); ci++)
		{
			ReachableSet* reachable_set = (*ci).first;
			unsigned int fact_index = (*ci).second;
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Add it to: ";
			reachable_set->print(std::cout);
			std::cout << " - index: " <<fact_index << std::endl;
#endif
			
			reachable_set->processNewReachableFact(*initial_fact, fact_index);
		}
	}
}


};
	
};
