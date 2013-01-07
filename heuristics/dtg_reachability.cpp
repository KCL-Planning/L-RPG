#include <cstring>
#include <iterator>
#include <sys/time.h>
#include <boost/bind.hpp>
#include <queue>

#include "dtg_reachability.h"
#include "equivalent_object_group.h"
#include "sas/property_space.h"
#include "action_manager.h"
#include "type_manager.h"
#include "reachable_tree.h"
#include "predicate_manager.h"
#include "term_manager.h"
#include <fc_planner.h>
#include "heuristics/fact_set.h"

//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
//#define DTG_REACHABILITY_KEEP_TIME
//#define MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_SHOW_PLAN
namespace MyPOP {

void printVariableDomain(ostream& os, const std::vector<const Object*>& result)
{
	os << "{ ";
	for (std::vector<const Object*>::const_iterator ci = result.begin(); ci != result.end(); ci++)
	{
		os << **ci;
		if (ci + 1 != result.end())
		{
			os << ", ";
		}
	}
	os << "} ";
}

void takeIntersection(std::vector<const Object*>& result, const std::vector<const Object*>& set1, const std::vector<const Object*>& set2)
{
	for (std::vector<const Object*>::const_iterator ci = set1.begin(); ci != set1.end(); ci++)
	{
		for (std::vector<const Object*>::const_iterator ci2 = set2.begin(); ci2 != set2.end(); ci2++)
		{
			if (*ci == *ci2)
			{
				result.push_back(*ci);
				break;
			}
		}
	}
}

bool doVariableDomainsOverlap(const std::vector<const Object*>& set1, const std::vector<const Object*>& set2)
{
	for (std::vector<const Object*>::const_iterator ci = set1.begin(); ci != set1.end(); ci++)
	{
		for (std::vector<const Object*>::const_iterator ci2 = set2.begin(); ci2 != set2.end(); ci2++)
		{
			if (*ci == *ci2) return true;
		}
	}
	return false;
}

namespace REACHABILITY {
	
std::vector<const ReachableFact*> ReachableFact::all_created_reachable_facts_;

/*ReachableFact& ReachableFact::createReachableFact(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
{
	ReachableFact* reachable_fact = new ReachableFact(bounded_atom, bindings, eog_manager);
	all_created_reachable_facts_.push_back(reachable_fact);
	return *reachable_fact;
}*/
	
ReachableFact& ReachableFact::createReachableFact(const Predicate& predicate, std::vector<EquivalentObjectGroup*>& term_domain_mapping)
{
	ReachableFact* reachable_fact = new ReachableFact(predicate, term_domain_mapping);
	all_created_reachable_facts_.push_back(reachable_fact);
	return *reachable_fact;
}

ReachableFact& ReachableFact::createReachableFact(const GroundedAtom& grounded_atom, const EquivalentObjectGroupManager& eog_manager)
{
	ReachableFact* reachable_fact = new ReachableFact(grounded_atom, eog_manager);
	all_created_reachable_facts_.push_back(reachable_fact);
	return *reachable_fact;
}

ReachableFact& ReachableFact::createReachableFact(const ReachableFact& other)
{
	ReachableFact* reachable_fact = new ReachableFact(other);
	all_created_reachable_facts_.push_back(reachable_fact);
	return *reachable_fact;
}

void ReachableFact::deleteAllReachableFacts(const std::vector<REACHABILITY::ReachableFact*>& initial_facts)
{
	for (std::vector<const ReachableFact*>::reverse_iterator ri = all_created_reachable_facts_.rbegin(); ri != all_created_reachable_facts_.rend(); ++ri)
	{
		if (std::find(initial_facts.begin(), initial_facts.end(), *ri) == initial_facts.end())
		{
			delete *ri;
			all_created_reachable_facts_.erase(ri.base() - 1);
		}
	}
}


/*ReachableFact::ReachableFact(const SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
	: predicate_(&bounded_atom.getAtom().getPredicate()), replaced_by_(NULL)
{
	//term_domain_mapping_ = new EquivalentObjectGroup*[bounded_atom.getAtom().getArity()];
//	term_domain_mapping_ = EquivalentObjectGroup::allocateMemory(bounded_atom.getAtom().getArity());
	term_domain_mapping_ = new std::vector<EquivalentObjectGroup*>(bounded_atom.getAtom().getArity());
	
	for (std::vector<const Term*>::const_iterator ci = bounded_atom.getAtom().getTerms().begin(); ci != bounded_atom.getAtom().getTerms().end(); ci++)
	{
		const Term* term = *ci;
		const std::vector<const Object*>& domain = term->getDomain(bounded_atom.getId(), bindings);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (domain.size() == 1);
#endif
		
		EquivalentObjectGroup& corresponding_eog = eog_manager.getEquivalentObject(*domain[0]).getEquivalentObjectGroup();
		//term_domain_mapping_[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] = &corresponding_eog;
		//term_domain_mapping_.push_back(&corresponding_eog);
		(*term_domain_mapping_)[std::distance(bounded_atom.getAtom().getTerms().begin(), ci)] = &corresponding_eog;
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		assert ((*term_domain_mapping_)[i] != NULL);
	}
#endif
	assert (term_domain_mapping_->size() == bounded_atom.getAtom().getArity());
}*/

ReachableFact::ReachableFact(const Predicate& predicate, std::vector<EquivalentObjectGroup*>& term_domain_mapping)
	: predicate_(&predicate), term_domain_mapping_(&term_domain_mapping), replaced_by_(NULL)
{
	assert (term_domain_mapping.size() == predicate.getArity());
}
/*
ReachableFact::ReachableFact(const Atom& atom, EquivalentObjectGroup** term_domain_mapping)
	: atom_(&atom), replaced_by_(NULL)
{

	for (unsigned int i = 0; i < atom.getArity(); i++)
	{
		term_domain_mapping->push_back(term_domain_mapping[i]);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (term_domain_mapping_[i] != NULL);
#endif
	}
}
*/
ReachableFact::ReachableFact(const GroundedAtom& grounded_atom, const EquivalentObjectGroupManager& eog_manager)
	: predicate_(&grounded_atom.getAtom().getPredicate()), replaced_by_(NULL)
{
//	term_domain_mapping_ = EquivalentObjectGroup::allocateMemory(grounded_atom.getAtom().getArity());
	term_domain_mapping_ = new std::vector<EquivalentObjectGroup*>(grounded_atom.getAtom().getArity());
	for (unsigned int i = 0; i < grounded_atom.getAtom().getArity(); i++)
	{
//		term_domain_mapping_[i] = &eog_manager.getEquivalentObject(grounded_atom.getObject(i)).getEquivalentObjectGroup();
		(*term_domain_mapping_)[i] = &eog_manager.getEquivalentObject(grounded_atom.getObject(i)).getEquivalentObjectGroup();
		//term_domain_mapping_.push_back(&eog_manager.getEquivalentObject(grounded_atom.getObject(i)).getEquivalentObjectGroup());
	}
}

ReachableFact::ReachableFact(const ReachableFact& reachable_fact)
	: predicate_(&reachable_fact.getPredicate()), replaced_by_(NULL)
{
//	term_domain_mapping_ = EquivalentObjectGroup::allocateMemory(reachable_fact.atom_->getArity());
	term_domain_mapping_ = new std::vector<EquivalentObjectGroup*>(reachable_fact.predicate_->getArity());
	for (unsigned int i = 0; i < reachable_fact.predicate_->getArity(); i++)
	{
//		term_domain_mapping_[i] = reachable_fact.term_domain_mapping_[i];
		(*term_domain_mapping_)[i] = (*reachable_fact.term_domain_mapping_)[i];
		//term_domain_mapping_.push_back(reachable_fact.term_domain_mapping_[i]);
	}
}

ReachableFact::~ReachableFact()
{
	delete term_domain_mapping_;
}

/*void* ReachableFact::operator new (size_t size)
{
	return g_reachable_fact_memory_pool->allocate(size);
}
	
void ReachableFact::operator delete (void* p)
{
	g_reachable_fact_memory_pool->free(p);
}*/

bool ReachableFact::updateTermsToRoot()
{
	bool updated_domain = false;
	for (unsigned int i = 0; i < predicate_->getArity(); i++)
	{
		EquivalentObjectGroup& root_node = (*term_domain_mapping_)[i]->getRootNode();
		if (&root_node != (*term_domain_mapping_)[i])
		{
			(*term_domain_mapping_)[i] = &root_node;
			updated_domain = true;
		}
	}
	
	// assert(updated_domain);
	
	return updated_domain;
}

bool ReachableFact::isEquivalentTo(const ReachableFact& other, const EquivalentObjectGroup& variant_eog) const
{
//	std::cout << "Are " << *this << " and " << other << " equivalent?" << std::endl;
	
	if (predicate_->getArity() != other.predicate_->getArity())
	{
//		std::cout << "Arities don't match up!" << std::endl;
		return false;
	}
	
//	char combined_mask = mask_ & other.mask_;
	
	for (unsigned int i = 0; i < predicate_->getArity(); i++)
	{
//		if (!(*term_domain_mapping_)[i]->isGrounded() && (*term_domain_mapping_)[i]->isPartOfAPropertyState())
		if ((*term_domain_mapping_)[i] == &variant_eog)
		{
			// Make sure the types match up.
			if (!(*term_domain_mapping_)[i]->hasSameFingerPrint(*(*other.term_domain_mapping_)[i]))
			{
//				std::cout << "The " << i << "th term does not have the same fingerprint!" << std::endl;
				return false;
			}
		}

		else if (!(*term_domain_mapping_)[i]->isIdenticalTo(*(*other.term_domain_mapping_)[i]))
		{
//			std::cout << "The " << i << "th term is at odds!" << std::endl;
			return false;
		}
	}
	return true;
}

bool ReachableFact::isIdenticalTo(const ReachableFact& other) const
{
	if (predicate_->getArity() != other.predicate_->getArity())
	{
		return false;
	}
	
	if (predicate_->getName() != other.predicate_->getName())
	{
		return false;
	}
	
	for (unsigned int i = 0; i < predicate_->getArity(); i++)
	{
//		if (&(*term_domain_mapping_)[i]->getRootNode() != &(*other.term_domain_mapping_)[i]->getRootNode())
		if ((*term_domain_mapping_)[i] != (*other.term_domain_mapping_)[i])
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			if ((*term_domain_mapping_)[i]->isIdenticalTo(*(*other.term_domain_mapping_)[i]))
			{
				std::cerr << "Could not check if " << *this << " is equivalent to " << other << std::endl;
				std::cerr << "WRONG!" << std::endl;
				assert (false);
			}
#endif
			return false;
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		if (!(*term_domain_mapping_)[i]->isIdenticalTo(*(*other.term_domain_mapping_)[i]))
		{
			std::cerr << "WRONG!" << std::endl;
			exit(1);
		}
#endif
	}
	return true;
}

EquivalentObjectGroup& ReachableFact::getTermDomain(unsigned int index) const
{
	assert (index < predicate_->getArity());
	EquivalentObjectGroup* eog = (*term_domain_mapping_)[index];
	assert (eog != NULL);
	return *eog;
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

bool ReachableFact::canUnifyWith(const Atom& atom, StepID step_id, const Bindings& bindings, unsigned int iteration) const
{
	// Check if this effect can be unified with the goal we try to achieve.
	if (!atom.getPredicate().canSubstitute(getPredicate())) return false;
	
	for (unsigned int i = 0; i < atom.getArity(); i++)
	{
		bool variable_domains_overlap = false;
		const std::vector<const Object*>& variable_domain = atom.getTerms()[i]->getDomain(step_id, bindings);
		for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ci++)
		{
			const Object* object = *ci;
			if (getTermDomain(i).contains(*object, iteration))
			{
					variable_domains_overlap = true;
					break;
			}
		}
		
		if (!variable_domains_overlap) return false;
	}
	
	return true;
}

void ReachableFact::print(std::ostream& os, unsigned int iteration) const
{
	os << "Reachable fact: (" << predicate_->getName() << "[" << predicate_->getId() << "] ";
	for (unsigned int i = 0; i < predicate_->getArity(); i++)
	{
		os << "{";
		(*term_domain_mapping_)[i]->printObjects(os, iteration);
//		os << "(" << (*term_domain_mapping_)[i] << ")";
		os << "}";
		if (i + 1 != predicate_->getArity())
		{
			os << ", ";
		}
	}
}

std::ostream& operator<<(std::ostream& os, const ReachableFact& reachable_fact)
{
	os << "Reachable fact: (" << reachable_fact.getPredicate().getName() << "[" << reachable_fact.getPredicate() << "] ";
	for (unsigned int i = 0; i < reachable_fact.getPredicate().getArity(); i++)
	{
		const std::vector<EquivalentObject*>& objects = (*reachable_fact.term_domain_mapping_)[i]->getEquivalentObjects();
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
		if (i + 1 != reachable_fact.predicate_->getArity())
		{
			os << ", ";
		}
	}
//	os << ")" << "%" << &reachable_fact << "%" << reachable_fact.getAtom().getPredicate();
//	os << "[r=" << &reachable_fact.getReplacement() << "]";
	return os;
}

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
	delete corrected_atom_;
	delete[] is_grounded_;
}

void ResolvedBoundedAtom::init(const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, PredicateManager& predicate_manager)
{
	is_grounded_ = new bool[atom_->getArity()];
	memset(is_grounded_, false, sizeof(bool) * atom_->getArity());
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		const std::vector<const Object*>& variable_domain = atom_->getTerms()[i]->getDomain(id_, bindings);
		variable_domains_.push_back(&variable_domain);
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
	if (!getCorrectedAtom().getPredicate().canSubstitute(reachable_fact.getPredicate()))
	{
		for (unsigned int i = 0; i < reachable_fact.getPredicate().getArity(); i++)
		{
			const Type* fact_set_type = getCorrectedAtom().getTerms()[i]->getType();
			const Type* reachable_fact_type = reachable_fact.getTermDomain(i).getEquivalentObjects()[0]->getObject().getType();
			
			//if (!fact_set_type->isCompatible(*reachable_fact_type))
			if (!fact_set_type->isSupertypeOf(*reachable_fact_type) && !fact_set_type->isEqual(*reachable_fact_type))
			{
				return false;
			}
		}
	}
	
	return true;
}

std::ostream& operator<<(std::ostream& os, const ResolvedBoundedAtom& resolved_bounded_atom)
{
	os << "(" << resolved_bounded_atom.getCorrectedAtom().getPredicate();
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
 *
ResolvedEffect::ResolvedEffect(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, bool free_variables[], PredicateManager& predicate_manager)
	: ResolvedBoundedAtom(id, atom, bindings, eog_manager, predicate_manager)
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
				assert (false);
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
			std::cout << "- " << eog << std::endl;
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
	delete[] is_free_variable_;
	
	for (std::vector<std::vector<EquivalentObjectGroup*>* >::const_iterator ci = free_variable_domains_.begin(); ci != free_variable_domains_.end(); ci++)
	{
		delete *ci;
	}
	
	delete[] index_to_variable_;
}

void ResolvedEffect::reset()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Reset the resolved effect..." << *this << std::endl;
#endif
	for (std::vector<std::vector<EquivalentObjectGroup*>* >::const_iterator ci = free_variable_domains_.begin(); ci != free_variable_domains_.end(); ci++)
	{
		std::vector<EquivalentObjectGroup*>* free_eogs = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Reset the free eogs: ";
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci = free_eogs->begin(); ci != free_eogs->end(); ci++)
		{
			std::cout << **ci << ", ";
		}
		std::cout << std::endl;
#endif
		
		unsigned int size = free_eogs->size();
		for (unsigned int i = 0; i < size; i++)
		{
			EquivalentObjectGroup* eog = (*free_eogs)[i];
			for (unsigned j = 1; j < eog->getEquivalentObjects().size(); j++)
			{
				free_eogs->push_back(&eog->getEquivalentObjects()[j]->getEquivalentObjectGroup());
			}
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Result: ";
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci = free_eogs->begin(); ci != free_eogs->end(); ci++)
		{
			std::cout << **ci << ", ";
		}
		std::cout << std::endl;
#endif
	}
}

void ResolvedEffect::updateVariableDomains()
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	unsigned int counter = 0;
//	unsigned int amount = 0;
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
//			++amount;
#endif
			
			if (!eog->isRootNode())
			{
				free_variable_domain->erase(ri.base() - 1);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//				++counter;
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

bool ResolvedEffect::isFreeVariable(unsigned int index) const
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (index < variable_domains_.size());
#endif
	return is_free_variable_[index];
}

//void ResolvedEffect::createReachableFacts(std::vector<ReachableFact*>& results, EquivalentObjectGroup** effect_domains) const
void ResolvedEffect::createReachableFacts(std::vector<ReachableFact*>& results, std::vector<EquivalentObjectGroup*>& effect_domains) const
{
	// If no variables are free we are done!
	if (free_variables_.size() == 0)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "There are no free variables..." << std::endl;
#endif
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		for (unsigned int i = 0; i < variable_domains_.size(); i++)
		{
			assert (is_free_variable_[i] == false);
		}
#endif
		results.push_back(&ReachableFact::createReachableFact(getCorrectedAtom(), effect_domains));
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
		//EquivalentObjectGroup** new_effect_domains = new EquivalentObjectGroup*[atom_->getArity()];
		//EquivalentObjectGroup** new_effect_domains = EquivalentObjectGroup::allocateMemory(atom_->getArity());
		std::vector<EquivalentObjectGroup*>* new_effect_domains = new std::vector<EquivalentObjectGroup*>(effect_domains);
		//memcpy(new_effect_domains, effect_domains, sizeof(EquivalentObjectGroup*) * atom_->getArity());
		
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
			(*new_effect_domains)[i] = (*possible_values)[counter[processed_free_variables]];
			
			++processed_free_variables;
		}
		
		ReachableFact& new_reachable_fact = ReachableFact::createReachableFact(getCorrectedAtom(), *new_effect_domains);
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "New reachable fact with free variables: " << *new_reachable_fact << "." << std::endl;
#endif
		
		results.push_back(&new_reachable_fact);
		
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
	
//	delete[] effect_domains;
	
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
	delete &effect_domains;
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
*/

/**
 * ReachableSet.
 */
ReachableSet::ReachableSet(const EquivalentObjectGroupManager& eog_manager, const HEURISTICS::FactSet& fact_set)
	: eog_manager_(&eog_manager), fact_set_(&fact_set), cached_reachability_tree_size_(0), cache_is_valid_(false)
{
	std::map<const Term*, std::pair<unsigned int, unsigned int> > term_to_indexes_mappings;
	for (unsigned int i = 0; i < fact_set.getFacts().size(); ++i)
	{
		std::vector<std::pair<unsigned int, unsigned int> >* constraint_set = new std::vector<std::pair<unsigned int, unsigned int> >();
		constraints_set_.push_back(constraint_set);
		
		const HEURISTICS::TransitionFact* fact = fact_set.getFacts()[i];
		for (std::vector<const Term*>::const_iterator ci = fact->getActionVariables().begin(); ci != fact->getActionVariables().end(); ++ci)
		{
			const Term* current_term = *ci;
			unsigned int term_index = std::distance(fact->getActionVariables().begin(), ci);
			
			// Check which of the previous facts share this term.
			std::map<const Term*, std::pair<unsigned int, unsigned int> >::const_iterator found_term_ci = term_to_indexes_mappings.find(current_term);
			if (found_term_ci == term_to_indexes_mappings.end())
			{
				term_to_indexes_mappings[current_term] = std::make_pair(i, term_index);
				constraint_set->push_back(std::make_pair(i, term_index));
			}
			else
			{
				constraint_set->push_back((*found_term_ci).second);
			}
		}
	}
	
	for (std::vector<const HEURISTICS::TransitionFact*>::const_iterator ci = fact_set.getFacts().begin(); ci != fact_set.getFacts().end(); ++ci)
	{
		reachable_set_.push_back(new std::list<ReachableFact*>());
	}
	
//	std::cout << *this << std::endl;
}

void ReachableSet::reset()
{
	for (std::vector<ReachableTree*>::const_iterator ci = reachability_tree_.begin(); ci != reachability_tree_.end(); ci++)
	{
		delete *ci;
	}
	reachability_tree_.clear();
	for (std::vector<std::list<ReachableFact*>* >::const_iterator ci = reachable_set_.begin(); ci != reachable_set_.end(); ci++)
	{
		(*ci)->clear();
	}

	cache_is_valid_ = false;
//	std::cout << "Reset cache!" << std::endl;
	cached_reachability_tree_size_ = 0;
}

ReachableSet::~ReachableSet()
{
	for (std::vector<std::list<ReachableFact*>*>::const_iterator ci = reachable_set_.begin(); ci != reachable_set_.end(); ci++)
	{
		std::list<ReachableFact*>* reachable_list = *ci;
		delete reachable_list;
	}
/*
	for (std::vector<std::vector<std::pair<unsigned int, unsigned int> >** >::const_iterator ci = constraints_set_.begin(); ci != constraints_set_.end(); ci++)
	{
		delete[] *ci;
	}
*/
	for (std::vector<ReachableTree*>::const_iterator ci = reachability_tree_.begin(); ci != reachability_tree_.end(); ci++)
	{
		delete *ci;
	}
}

unsigned int ReachableSet::getCachedReachableTreesSize()
{
	if (!cache_is_valid_)
	{
		cached_reachability_tree_size_ = reachability_tree_.size();
		cache_is_valid_ = true;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "New cache size of " << this << " is " << cached_reachability_tree_size_ << std::endl;
#endif
		for (std::vector<ReachableTree*>::const_iterator ci = reachability_tree_.begin(); ci != reachability_tree_.end(); ++ci)
		{
			ReachableTree* tree = *ci;
			tree->getCachedNumberOfLeafs();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << " === TREE === (" << tree << ") Leaf = " << tree->getLeaves().size() << std::endl;
			for (std::vector<ReachableTreeNode*>::const_iterator ci = tree->getLeaves().begin(); ci != tree->getLeaves().end(); ++ci)
			{
				ReachableTreeNode* leaf = *ci;
				std::cout << " === LEAFS === " << std::endl;
				while (leaf != NULL)
				{
					std::cout << *leaf << "(" << leaf << ")" << std::endl;
					leaf = leaf->getParent();
				}
			}
#endif
		}

	}
	
	return cached_reachability_tree_size_;
}
/*
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
*/
void ReachableSet::initialiseInitialFacts(const std::vector< ReachableFact* >& initial_facts)
{
	/**
	 * Match all the initial facts with the facts in the set. We store the results only locally because we will use the
	 * processNewReachableFact to do the actual work for us.
	 */
	for (unsigned int index = 0; index < fact_set_->getFacts().size(); ++index)
	{
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
//			if (!resolved_atom->canSubstitude(*initial_fact))
//			{
//				continue;
//			}
			
			processNewReachableFact(*initial_fact, index);
		}
	}
}
/*
void ReachableSet::addBoundedAtom(StepID step_id, const Atom& atom, const Bindings& bindings, PredicateManager& predicate_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[ReachableSet::addBoundedAtom] Add :";
	atom.print(std::cout, bindings, step_id);
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
*/
void ReachableSet::equivalencesUpdated(unsigned int iteration)
{
	//cache_is_valid_ = false;
	cache_is_valid_ = true;
//	std::cout << "Reset cache!" << std::endl;

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
		if (reachable_tree->getRoot()->getReachableFact().isMarkedForRemoval())
		{
			reachability_tree_.erase(ri.base() - 1);
			delete reachable_tree;
		}
		else
		{
			reachable_tree->equivalencesUpdated(iteration, reachability_tree_);
			reachable_tree->getCachedNumberOfLeafs();
		}
	}
	
/*
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
			delete reachable_tree;
		}
	}
	
	for (std::vector<ReachableTree*>::const_iterator ci = reachability_tree_.begin(); ci != reachability_tree_.end(); ci++)
	{
		ReachableTree* reachable_tree = *ci;
		reachable_tree->getCachedNumberOfLeafs();
	}
*/

	cached_reachability_tree_size_ = reachability_tree_.size();
}
/*
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
*/
bool ReachableSet::processNewReachableFact(ReachableFact& reachable_fact, unsigned int index)
{
	const HEURISTICS::TransitionFact* fact = fact_set_->getFacts()[index];

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << *this << std::endl;
	std::cout << "(" << this << ")123 " << reachable_fact << " ; index = " << index << ". Fact: " << *fact << std::endl;
	
	std::cout << "[ReachableSet::processNewReachableFact] " << reachable_fact << " ; index = " << index << std::endl;
	std::cout << "Fact: " << *fact << std::endl;
#endif
	
	// Check if it can be added.
	if (reachable_fact.getPredicate().getName() != fact->getPredicate().getName() ||
	    reachable_fact.getPredicate().getArity() != fact->getPredicate().getArity())
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Predicate does not match up!" << std::endl;
#endif
		return false;
	}
	
/*
	if (!fact->getPredicate().canSubstitute(reachable_fact.getAtom().getPredicate()))
	{
		for (unsigned int i = 0; i < reachable_fact.getAtom().getArity(); i++)
		{
			const Type* fact_set_type = fact->getActionVariables()[i]->getType();
			const Type* reachable_fact_type = reachable_fact.getTermDomain(i).getEquivalentObjects()[0]->getObject().getType();
			
			if (!fact_set_type->isSupertypeOf(*reachable_fact_type) && !fact_set_type->isEqual(*reachable_fact_type))
			{
				return false;
			}
		}
	}
*/

	for (unsigned int i = 0; i < reachable_fact.getPredicate().getArity(); ++i)
	{
		const HEURISTICS::VariableDomain* variable_domain = fact->getVariableDomains()[i];
		const EquivalentObjectGroup& eog = reachable_fact.getTermDomain(i);
		
		for (std::vector<EquivalentObject*>::const_iterator ci = eog.getEquivalentObjects().begin(); ci != eog.getEquivalentObjects().end(); ++ci)
		{
			if (!variable_domain->contains((*ci)->getObject()))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Variable domain does not add up!" << std::endl;
#endif
				return false;
			}
		}
	}
	
	for (std::list<ReachableFact*>::const_iterator ci = reachable_set_[index]->begin(); ci != reachable_set_[index]->end(); ++ci)
	{
		const ReachableFact* existing_fact = *ci;
		if (reachable_fact.isIdenticalTo(*existing_fact))
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Is identical to " << *existing_fact << std::endl;
#endif
			return false;
		}
	}
	reachable_set_[index]->push_back(&reachable_fact);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[ReachableSet::processNewReachableFact] " << reachable_fact << " ; index = " << index << std::endl;
#endif
	
	// If the index is 0, it means it is the start of a new 'root'.
	if (index == 0)
	{
		ReachableTree* new_root = new ReachableTree(*this);
		reachability_tree_.push_back(new_root);
		new_root->addFact(0, reachable_fact);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "New root! Result: " << std::endl << *this << std::endl;
#endif
	}
	// Otherwise, we need to search for all sets the new node can be a part of and process these.
	else
	{
		for (std::vector<ReachableTree*>::const_iterator ci = reachability_tree_.begin(); ci != reachability_tree_.end(); ci++)
		{
			ReachableTree* reachable_tree = *ci;
			reachable_tree->addFact(index, reachable_fact);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Added the fact to an existing tree! Result: " << std::endl << *this << std::endl;
#endif
		}
	}
	
	return true;
}

std::ostream& operator<<(std::ostream& os, const ReachableSet& reachable_set)
{
	os << "[ReachableSet]" << std::endl;
	for (unsigned int i = 0; i < reachable_set.fact_set_->getFacts().size(); ++i)
	{
		const HEURISTICS::TransitionFact* transition_fact = reachable_set.fact_set_->getFacts()[i];
		assert (transition_fact != NULL);
		os << *transition_fact << std::endl;
		
		for (std::list<ReachableFact*>::const_iterator ci = reachable_set.reachable_set_[i]->begin(); ci != reachable_set.reachable_set_[i]->end(); ++ci)
		{
			std::cout << "* " << **ci << std::endl;
		}
	}
	return os;
}

std::vector<const AchievingTransition*> AchievingTransition::all_created_achieving_transitions_;

AchievingTransition::AchievingTransition(unsigned int effect_index, unsigned int effect_set_index, const std::vector< const MyPOP::REACHABILITY::ReachableFact* >& preconditions, MyPOP::REACHABILITY::ReachableFact& fact, const MyPOP::REACHABILITY::ReachableTransition& achiever, const std::vector<HEURISTICS::VariableDomain*>& variable_assignments, const ReachableFactLayer& fact_layer)
	: effect_index_(effect_index), effect_set_index_(effect_set_index), preconditions_(preconditions), reachable_fact_(&fact), achiever_(&achiever), variable_assignments_(variable_assignments)
{
	for (std::vector< const MyPOP::REACHABILITY::ReachableFact* >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
	{
//		assert (fact_layer.getPreviousLayer() != NULL);
		const ReachableFactLayerItem* reachable_fact_layer_item = fact_layer.findPrecondition(**ci);
		if (reachable_fact_layer_item == NULL)
		{
			std::cout << fact_layer << std::endl;
			if (achiever_ != NULL)
			{
				std::cout << "Achiever: " << achiever << std::endl;
			}
			else
			{
				std::cout << "NULL" << std::endl;
			}
			std::cout << "Could not find a layer with the fact: " << **ci << std::endl;
			assert (false);
		}
		preconditions_fact_layer_items_.push_back(reachable_fact_layer_item);
	}
	all_created_achieving_transitions_.push_back(this);
	
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		HEURISTICS::VariableDomain* vd = *ci;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci2 = variable_assignments_.begin(); ci2 != variable_assignments_.end(); ++ci2)
		{
			if (ci == ci2)
			{
				continue;
			}
			if (vd == *ci2)
			{
				std::cerr << "VARIABLE PRESENT TWICE!!!" << std::endl;
			}
			assert (vd != *ci2);
		}
	}
}

AchievingTransition::AchievingTransition(const AchievingTransition& achieving_transition, bool remove_copy_automatically)
	: effect_index_(achieving_transition.effect_index_), effect_set_index_(achieving_transition.effect_set_index_), preconditions_(achieving_transition.preconditions_), preconditions_fact_layer_items_(achieving_transition.preconditions_fact_layer_items_), reachable_fact_(achieving_transition.reachable_fact_), achiever_(achieving_transition.achiever_)
{
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = achieving_transition.variable_assignments_.begin(); ci != achieving_transition.variable_assignments_.end(); ++ci)
	{
		HEURISTICS::VariableDomain* new_variable_domain = new HEURISTICS::VariableDomain(**ci);
		variable_assignments_.push_back(new_variable_domain);
	}
	if (remove_copy_automatically)
	{
		all_created_achieving_transitions_.push_back(this);
	}
	
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		HEURISTICS::VariableDomain* vd = *ci;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci2 = variable_assignments_.begin(); ci2 != variable_assignments_.end(); ++ci2)
		{
			if (ci == ci2)
			{
				continue;
			}
			if (vd == *ci2)
			{
				std::cerr << "VARIABLE PRESENT TWICE!!!" << std::endl;
			}
			assert (vd != *ci2);
		}
	}
}

AchievingTransition::AchievingTransition(const AchievingTransition& achieving_transition, const std::vector<HEURISTICS::VariableDomain*>& variable_assignments, bool remove_copy_automatically)
	: effect_index_(achieving_transition.effect_index_), effect_set_index_(achieving_transition.effect_set_index_), preconditions_(achieving_transition.preconditions_), preconditions_fact_layer_items_(achieving_transition.preconditions_fact_layer_items_), reachable_fact_(achieving_transition.reachable_fact_), achiever_(achieving_transition.achiever_), variable_assignments_(variable_assignments)
{
	if (remove_copy_automatically)
	{
		all_created_achieving_transitions_.push_back(this);
	}
/*	
	std::cout << achieving_transition.getAchiever()->getTransition().getAction() << std::endl;
	
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments.begin(); ci != variable_assignments.end(); ++ci)
	{
		std::cout << **ci << ", ";
	}
	std::cout << "." << std::endl;
	
	std::cout << *this << std::endl;
*/
}

AchievingTransition& AchievingTransition::createNoop(const std::vector<const ReachableFactLayerItem*>& preconditions)
{
	AchievingTransition* achieving_transition = new AchievingTransition(preconditions);
	return *achieving_transition;
}


void AchievingTransition::removeAllAchievingTransitions()
{
	for (std::vector<const AchievingTransition*>::const_iterator ci = all_created_achieving_transitions_.begin(); ci != all_created_achieving_transitions_.end(); ++ci)
	{
		delete *ci;
	}
	all_created_achieving_transitions_.clear();
}

AchievingTransition::AchievingTransition(const std::vector<const ReachableFactLayerItem*>& preconditions)
	: effect_index_(0), preconditions_fact_layer_items_(preconditions), reachable_fact_(NULL), achiever_(NULL)
{
	for (std::vector< const MyPOP::REACHABILITY::ReachableFactLayerItem* >::const_iterator ci = preconditions_fact_layer_items_.begin(); ci != preconditions_fact_layer_items_.end(); ++ci)
	{
		assert (*ci != NULL);
	}
	all_created_achieving_transitions_.push_back(this);
}

AchievingTransition::~AchievingTransition()
{
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		HEURISTICS::VariableDomain* vd = *ci;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci2 = variable_assignments_.begin(); ci2 != variable_assignments_.end(); ++ci2)
		{
			if (ci == ci2)
			{
				continue;
			}
			if (vd == *ci2)
			{
				std::cerr << "VARIABLE PRESENT TWICE!!!" << std::endl;
			}
			assert (vd != *ci2);
		}
	}
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		delete *ci;
	}
}

void AchievingTransition::getNeededSubstitutes(vector< std::pair< const MyPOP::REACHABILITY::EquivalentObject*, const MyPOP::REACHABILITY::EquivalentObject* > >& needed_substituted, const MyPOP::REACHABILITY::ReachableFactLayerItem& reachable_fact, std::vector< const MyPOP::Object* >** object_bindings, const MyPOP::REACHABILITY::EquivalentObjectGroupManager& eog_manager, unsigned int effect_set_index, unsigned int effect_index) const
{
	const HEURISTICS::LiftedTransition& lifted_transition = achiever_->getTransition();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	const HEURISTICS::TransitionFact* effect = (*achiever_->getTransition().getEffects()[effect_set_index_]).getFacts()[effect_index_];
	std::cout << "[AchievingTransition::getNeededSubstitutes] " << reachable_fact << std::endl;
	std::cout << "Effect: " << *effect << std::endl;
#endif
	std::vector<const EquivalentObject*> lhs_eos, rhs_eos;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << "Variables: " << std::endl;
#endif
	
	unsigned int overal_effect_index = 0;
	std::vector<std::vector<unsigned int>* >* effect_parameter_to_action_variables = (*lifted_transition.getEffectMappings().find(achiever_->getTransition().getEffects()[effect_set_index])).second;
	for (std::vector<unsigned int>::const_iterator ci = (*effect_parameter_to_action_variables)[effect_index]->begin(); ci != (*effect_parameter_to_action_variables)[effect_index]->end(); ++ci)
	{
		HEURISTICS::VariableDomain& action_variable_domain = *variable_assignments_[*ci];
//		std::vector<const Object*>* effect_variable_domain = object_bindings[effect_index];
		bool intersection_is_empty = true;
		std::vector<const Object*>* effect_variable_domain = object_bindings[overal_effect_index];
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
		std::cout << "* " << action_variable_domain << " <-> ";
		printVariableDomain(std::cout, *effect_variable_domain);
		std::cout << std::endl;
#endif

		for (std::vector<const Object*>::const_iterator ci = effect_variable_domain->begin(); ci != effect_variable_domain->end(); ++ci)
		{
			const Object* object = *ci;
			if (action_variable_domain.contains(*object))
			{
				intersection_is_empty = false;
				break;
			}
		}
		
		if (intersection_is_empty)
		{
			for (std::vector<const Object*>::const_iterator ci = effect_variable_domain->begin(); ci != effect_variable_domain->end(); ++ci)
			{
				const Object* object = *ci;
				const EquivalentObject& lhs_eo = eog_manager.getEquivalentObject(*object);
				if (std::find(lhs_eos.begin(), lhs_eos.end(), &lhs_eo) == lhs_eos.end())
				{
					lhs_eos.push_back(&lhs_eo);
				}
			}
			for (std::vector<const Object*>::const_iterator ci = action_variable_domain.getVariableDomain().begin(); ci != action_variable_domain.getVariableDomain().end(); ++ci)
			{
				const EquivalentObject& rhs_eo = eog_manager.getEquivalentObject(**ci);
				if (std::find(rhs_eos.begin(), rhs_eos.end(), &rhs_eo) == rhs_eos.end())
				{
					rhs_eos.push_back(&rhs_eo);
				}
			}
			
			for (std::vector<const EquivalentObject*>::const_iterator ci = lhs_eos.begin(); ci != lhs_eos.end(); ++ci)
			{
				const EquivalentObject* lhs_eo = *ci;
				for (std::vector<const EquivalentObject*>::const_iterator ci = rhs_eos.begin(); ci != rhs_eos.end(); ++ci)
				{
					const EquivalentObject* rhs_eo = *ci;
					
					needed_substituted.push_back(std::make_pair(lhs_eo, rhs_eo));
				}
			}
		}
		++overal_effect_index;
	}
}

std::pair<unsigned int, unsigned int> AchievingTransition::getEffectIndexAchieving(const ReachableFactLayerItem& reachable_fact, std::vector<const Object*>** object_bindings) const
{
	const HEURISTICS::LiftedTransition& lifted_transition = achiever_->getTransition();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	const HEURISTICS::TransitionFact* effect = (*achiever_->getTransition().getEffects()[effect_set_index_]).getFacts()[effect_index_];
	std::cout << "[AchievingTransition::canAchieve] " << reachable_fact << std::endl;
	std::cout << "Effect: " << *effect << std::endl;
	
	std::cout << "Variables: " << std::endl;
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
#endif
	
	// Check each effect and check if it could achieve the reachable fact.
	for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = lifted_transition.getEffects().begin(); ci !=lifted_transition.getEffects().end(); ++ci)
	{
		unsigned int effect_set_index = std::distance(lifted_transition.getEffects().begin(), ci);
		const HEURISTICS::FactSet* fact_set = *ci;
		std::vector<std::vector<unsigned int>* >* effect_parameter_to_action_variables = (*lifted_transition.getEffectMappings().find(lifted_transition.getEffects()[effect_set_index])).second;
		for (std::vector<const HEURISTICS::TransitionFact*>::const_iterator ci = fact_set->getFacts().begin(); ci != fact_set->getFacts().end(); ++ci)
		{
			unsigned int effect_index = std::distance(fact_set->getFacts().begin(), ci);
			const HEURISTICS::TransitionFact* effect = *ci;

			if (effect->getPredicate().getArity() != reachable_fact.getReachableFactCopy().getPredicate().getArity() ||
			    effect->getPredicate().getName() != reachable_fact.getReachableFactCopy().getPredicate().getName())
			{
				continue;
			}
			
			bool variable_domains_match = true;
			unsigned int overal_effect_index = 0;
			for (std::vector<unsigned int>::const_iterator ci = (*effect_parameter_to_action_variables)[effect_index]->begin(); ci != (*effect_parameter_to_action_variables)[effect_index]->end(); ++ci)
			{
				HEURISTICS::VariableDomain& action_variable_domain = *variable_assignments_[*ci];
				assert (&action_variable_domain != NULL);
				std::vector<const Object*>* effect_variable_domain = object_bindings[overal_effect_index];
				assert (effect_variable_domain != NULL);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "* " << action_variable_domain << " <-> ";
				printVariableDomain(std::cout, *effect_variable_domain);
				std::cout << std::endl;
#endif
				
				bool intersection_is_empty = true;
				for (std::vector<const Object*>::const_iterator ci = effect_variable_domain->begin(); ci != effect_variable_domain->end(); ++ci)
				{
					const Object* object = *ci;
					assert (object != NULL);
					if (action_variable_domain.contains(*object))
					{
						intersection_is_empty = false;
						break;
					}
				}
				if (intersection_is_empty)
				{
					variable_domains_match = false;
					break;
				}
				++overal_effect_index;
			}
			
			if (variable_domains_match)
			{
				return std::make_pair(effect_set_index, effect_index);
			}
		}
	}
	return std::make_pair(std::numeric_limits<unsigned int>::max(), std::numeric_limits<unsigned int>::max());
}

std::pair<unsigned int, unsigned int> AchievingTransition::getEffectIndexAchieving(const ReachableFactLayerItem& reachable_fact, const std::vector<const HEURISTICS::VariableDomain*>& object_bindings) const
{
	const HEURISTICS::LiftedTransition& lifted_transition = achiever_->getTransition();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	const HEURISTICS::TransitionFact* effect = (*achiever_->getTransition().getEffects()[effect_set_index_]).getFacts()[effect_index_];
	std::cout << "[AchievingTransition::canAchieve] " << reachable_fact << std::endl;
	std::cout << "Effect: " << *effect << std::endl;
	
	std::cout << "Variables: " << std::endl;
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
#endif
	
	// Check each effect and check if it could achieve the reachable fact.
	for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = lifted_transition.getEffects().begin(); ci !=lifted_transition.getEffects().end(); ++ci)
	{
		unsigned int effect_set_index = std::distance(lifted_transition.getEffects().begin(), ci);
		const HEURISTICS::FactSet* fact_set = *ci;
		std::vector<std::vector<unsigned int>* >* effect_parameter_to_action_variables = (*lifted_transition.getEffectMappings().find(lifted_transition.getEffects()[effect_set_index])).second;
		for (std::vector<const HEURISTICS::TransitionFact*>::const_iterator ci = fact_set->getFacts().begin(); ci != fact_set->getFacts().end(); ++ci)
		{
			unsigned int effect_index = std::distance(fact_set->getFacts().begin(), ci);
			const HEURISTICS::TransitionFact* effect = *ci;

			if (effect->getPredicate().getArity() != reachable_fact.getReachableFactCopy().getPredicate().getArity() ||
			    effect->getPredicate().getName() != reachable_fact.getReachableFactCopy().getPredicate().getName())
			{
				continue;
			}
			
			bool variable_domains_match = true;
			unsigned int overal_effect_index = 0;
			for (std::vector<unsigned int>::const_iterator ci = (*effect_parameter_to_action_variables)[effect_index]->begin(); ci != (*effect_parameter_to_action_variables)[effect_index]->end(); ++ci)
			{
				HEURISTICS::VariableDomain& action_variable_domain = *variable_assignments_[*ci];
				assert (&action_variable_domain != NULL);
				const std::vector<const Object*>& effect_variable_domain = object_bindings[overal_effect_index]->getVariableDomain();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "* " << action_variable_domain << " <-> ";
				printVariableDomain(std::cout, *effect_variable_domain);
				std::cout << std::endl;
#endif
				
				bool intersection_is_empty = true;
				for (std::vector<const Object*>::const_iterator ci = effect_variable_domain.begin(); ci != effect_variable_domain.end(); ++ci)
				{
					const Object* object = *ci;
					assert (object != NULL);
					if (action_variable_domain.contains(*object))
					{
						intersection_is_empty = false;
						break;
					}
				}
				if (intersection_is_empty)
				{
					variable_domains_match = false;
					break;
				}
				++overal_effect_index;
			}
			
			if (variable_domains_match)
			{
				return std::make_pair(effect_set_index, effect_index);
			}
		}
	}
	return std::make_pair(std::numeric_limits<unsigned int>::max(), std::numeric_limits<unsigned int>::max());
}

void AchievingTransition::updateVariablesToAchieve(const ReachableFactLayerItem& reachable_fact, std::vector<const Object*>** object_bindings, unsigned int effect_set_index, unsigned int effect_index) const
{
	assert (effect_set_index != std::numeric_limits<unsigned int>::max());
	assert (effect_index != std::numeric_limits<unsigned int>::max());
	
	const HEURISTICS::LiftedTransition& lifted_transition = achiever_->getTransition();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	
	std::cout << effect_set_index << ", " << effect_index << std::endl;
	
	const HEURISTICS::TransitionFact* effect = (*achiever_->getTransition().getEffects()[effect_set_index]).getFacts()[effect_index];
	std::cout << "[AchievingTransition::updateVariablesToAchieve] " << reachable_fact << std::endl;
	std::cout << "Effect: " << *effect << std::endl;
	
	std::cout << "Variables: " << std::endl;
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
#endif

	unsigned int overal_effect_index = 0;
	std::vector<std::vector<unsigned int>* >* effect_parameter_to_action_variables = (*lifted_transition.getEffectMappings().find(achiever_->getTransition().getEffects()[effect_set_index])).second;
	for (std::vector<unsigned int>::const_iterator ci = (*effect_parameter_to_action_variables)[effect_index]->begin(); ci != (*effect_parameter_to_action_variables)[effect_index]->end(); ++ci)
	{
		HEURISTICS::VariableDomain& action_variable_domain = *variable_assignments_[*ci];
		std::vector<const Object*>* effect_variable_domain = object_bindings[overal_effect_index];
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
		std::cout << "* " << action_variable_domain << " <-> ";
		printVariableDomain(std::cout, *effect_variable_domain);
		std::cout << std::endl;
#endif

		std::vector<const Object*> new_domain;
		for (std::vector<const Object*>::const_iterator ci = effect_variable_domain->begin(); ci != effect_variable_domain->end(); ++ci)
		{
			const Object* object = *ci;
			if (action_variable_domain.contains(*object))
			{
				new_domain.push_back(object);
			}
		}
		if (new_domain.size() > 0)
		{
			action_variable_domain.set(new_domain);
		}
		++overal_effect_index;
	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << "POST: " << std::endl;
	std::cout << *this << std::endl;
#endif
}

void AchievingTransition::getVariablesToAchieve(std::vector<HEURISTICS::VariableDomain*>& variable_assignments_to_achieve_effect, const ReachableFactLayerItem& reachable_fact, std::vector<const Object*>** object_bindings, unsigned int effect_set_index, unsigned int effect_index) const
{
	assert (effect_set_index != std::numeric_limits<unsigned int>::max());
	assert (effect_index != std::numeric_limits<unsigned int>::max());
	
	const HEURISTICS::LiftedTransition& lifted_transition = achiever_->getTransition();
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_.begin(); ci != variable_assignments_.end(); ++ci)
	{
		variable_assignments_to_achieve_effect.push_back(new HEURISTICS::VariableDomain(**ci));
	}

	unsigned int overal_effect_index = 0;
	std::vector<std::vector<unsigned int>* >* effect_parameter_to_action_variables = (*lifted_transition.getEffectMappings().find(achiever_->getTransition().getEffects()[effect_set_index])).second;
	for (std::vector<unsigned int>::const_iterator ci = (*effect_parameter_to_action_variables)[effect_index]->begin(); ci != (*effect_parameter_to_action_variables)[effect_index]->end(); ++ci)
	{
		HEURISTICS::VariableDomain& action_variable_domain = *variable_assignments_to_achieve_effect[*ci];
		std::vector<const Object*>* effect_variable_domain = object_bindings[overal_effect_index];

		if (effect_variable_domain->size() > 0)
		{
			action_variable_domain.set(*effect_variable_domain);
		}
		++overal_effect_index;
	}
}

std::ostream& operator<<(std::ostream& os, const AchievingTransition& executed_action)
{
	if (executed_action.getAchiever() != NULL)
	{
		assert (executed_action.getVariableAssignments().size() == executed_action.getAchiever()->getTransition().getAction().getVariables().size());
		os << "Executed action: " << executed_action.getAchiever()->getTransition().getAction().getPredicate() << " ";
		for (unsigned int i = 0; i < executed_action.getAchiever()->getTransition().getAction().getVariables().size(); i++)
		{
			os << *executed_action.getVariableAssignments()[i];
/*
		const Object* object = executed_action.getActionDomains()[i];
		if (object == NULL)
		{
			os << "FREE ";
		}
		else
		{
			os << *object << " ";
		}
*/
		}
		
	}
	else
	{
		os << "NOOP action.";
	}
	os << std::endl;
	return os;
}



ReachableTransition::ReachableTransition(const MyPOP::HEURISTICS::LiftedTransition& lifted_transition, const std::vector< MyPOP::REACHABILITY::ReachableSet* >& preconditions, const std::vector< MyPOP::REACHABILITY::ReachableSet* >& effects)
	: transition_(&lifted_transition), preconditions_reachable_sets_(&preconditions), effect_reachable_sets_(&effects)
{

}
	
ReachableTransition::~ReachableTransition()
{
	for (std::vector<std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >* >::const_iterator ci = effect_propagation_listeners_.begin(); ci != effect_propagation_listeners_.end(); ++ci)
	{
		std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >* sets = *ci;
		for (std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator ci = sets->begin(); ci != sets->end(); ++ci)
		{
			delete *ci;
		}
		delete sets;
	}
	delete preconditions_reachable_sets_;
	delete effect_reachable_sets_;
	for (std::vector<const std::vector<EquivalentObjectGroup*>* >::const_iterator ci = processed_groups_.begin(); ci != processed_groups_.end(); ++ci)
	{
		delete *ci;
	}
}

void ReachableTransition::reset()
{
	for (std::vector<const std::vector<EquivalentObjectGroup*>* >::const_iterator ci = processed_groups_.begin(); ci != processed_groups_.end(); ++ci)
	{
		delete *ci;
	}
	processed_groups_.clear();
}

void ReachableTransition::finalise(const std::vector<ReachableSet*>& all_reachable_sets)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Link all the effects of " << *this << " to all the sets which can be unified with them." << std::endl;
#endif
	for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = transition_->getEffects().begin(); ci != transition_->getEffects().end(); ++ci)
	{
		const HEURISTICS::FactSet* effects_set = *ci;
		
		std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >* preconditions_reached_by_effect_set = new std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >();
		effect_propagation_listeners_.push_back(preconditions_reached_by_effect_set);
		for (std::vector<const HEURISTICS::TransitionFact*>::const_iterator ci = effects_set->getFacts().begin(); ci != effects_set->getFacts().end(); ++ci)
		{
			const HEURISTICS::TransitionFact* effect = *ci;
//			std::cout << "Process effect: " << *effect << std::endl;
			
			std::vector<std::pair<ReachableSet*, unsigned int> >* preconditions_reached_by_effect = new std::vector<std::pair<ReachableSet*, unsigned int> >();
			preconditions_reached_by_effect_set->push_back(preconditions_reached_by_effect);
			
			// Find all preconditions which are achieved by the effect.
			for (std::vector<ReachableSet*>::const_iterator ci = all_reachable_sets.begin(); ci != all_reachable_sets.end(); ci++)
			{
				ReachableSet* reachable_set = *ci;
				
				for (unsigned int fact_index = 0; fact_index < reachable_set->getFactSet().getFacts().size(); ++fact_index)
				{
					const HEURISTICS::TransitionFact* precondition_fact = reachable_set->getFactSet().getFacts()[fact_index];
					
					if (precondition_fact->canUnifyWith(*effect))
					{
						preconditions_reached_by_effect->push_back(std::make_pair(reachable_set, fact_index));
//						std::cout << "Link to " << *reachable_set << "(" << fact_index << ")" << std::endl;
					}
				}
			}
		}
	}
}

bool ReachableTransition::generateReachableFacts(const EquivalentObjectGroupManager& eog_manager, ReachableFactLayer& fact_layer, const std::vector<const ReachableFact*>& persistent_facts)
{
	assert (fact_layer.getPreviousLayer() != NULL);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
	std::cout << "[ReachableTransition::generateReachableFacts] " << *this << std::endl << "Cached tree sizes: " << std::endl;
	for (std::vector<ReachableSet*>::const_iterator ci = preconditions_reachable_sets_->begin(); ci != preconditions_reachable_sets_->end(); ++ci)
	{
		std::cout << " === PRECONDITION === " << std::endl;
		ReachableSet* reachable_set = *ci;
		std::cout << *reachable_set << std::endl;
		std::cout << "Trees(" << reachable_set->getReachableTrees().size() << " - cached" << reachable_set->getCachedReachableTreesSize() << "): " << std::endl;
		for (std::vector<ReachableTree*>::const_iterator ci = reachable_set->getReachableTrees().begin(); ci != reachable_set->getReachableTrees().end(); ++ci)
		{
			std::cout << **ci << std::endl;
		}
		std::cout << " =*= PRECONDITION =*= " << std::endl;
	}
#endif

	std::vector<EquivalentObjectGroup*> variable_assignments(transition_->getAction().getVariables().size(), NULL);
	std::vector<const ReachableFact*> preconditions;
	std::vector<const AchievingTransition*> newly_created_reachable_facts;
	generateReachableFacts(eog_manager, newly_created_reachable_facts, preconditions, variable_assignments, 0, *fact_layer.getPreviousLayer());

	bool new_facts_reached = false;
	for (std::vector<const AchievingTransition*>::const_iterator ci = newly_created_reachable_facts.begin(); ci != newly_created_reachable_facts.end(); ++ci)
	{
		const AchievingTransition* created_effect = *ci;

		// Check if this action removes a fact we want to preserve.
		bool deletes_persistent_node = false;
		for (std::vector<const Atom*>::const_iterator ci = created_effect->getAchiever()->getTransition().getAction().getEffects().begin(); ci != created_effect->getAchiever()->getTransition().getAction().getEffects().end(); ++ci)
		{
			const Atom* effect = *ci;
			if (!effect->isNegative())
			{
				continue;
			}
			
			// Figure out the mapping from the index of the effects to the 
			unsigned int effect_index = std::distance(created_effect->getAchiever()->getTransition().getAction().getEffects().begin(), ci);
			
			for (std::vector<const ReachableFact*>::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ++ci)
			{
				const ReachableFact* reachable_fact = *ci;
				if (effect->getArity() != reachable_fact->getPredicate().getArity() ||
				    effect->getPredicate().getName() != reachable_fact->getPredicate().getName())
				{
					continue;
				}
				
				bool terms_match = true;
				for (unsigned int term_index = 0; term_index < effect->getArity(); ++term_index)
				{
					EquivalentObjectGroup& persistent_eog = reachable_fact->getTermDomain(term_index);
					const HEURISTICS::VariableDomain* action_variable_domain = created_effect->getVariableAssignments()[created_effect->getAchiever()->getTransition().getAction().getActionVariable(effect_index, term_index)];
					
					bool term_matches = false;
					for (std::vector<const Object*>::const_iterator ci = action_variable_domain->getVariableDomain().begin(); ci != action_variable_domain->getVariableDomain().end(); ++ci)
					{
						if (persistent_eog.contains(**ci))
						{
							term_matches = true;
							break;
						}
					}
					
					if (!term_matches)
					{
						terms_match = false;
						break;
					}
				}
				
				if (terms_match)
				{
					deletes_persistent_node = true;
					break;
				}
			}
			
			if (deletes_persistent_node)
			{
				break;
			}
		}
		
		if (deletes_persistent_node)
		{
//			delete created_effect;
			continue;
		}

/*		ReachableFact& new_reachable_fact = created_effect->getReachableFact();
		unsigned int effect_index = created_effect->getEffectIndex();
		std::vector<const ReachableFact*> preconditions = created_effect->getPreconditions();
		const std::vector<const HEURISTICS::VariableDomain*> variable_domains = created_effect->getVariableAssignments();*/

		// Make sure the fact hasn't been reached before!
		const EquivalentObjectGroup* best_eog = NULL;
		bool zero_arity_reached_fact = created_effect->getReachableFact().getPredicate().getArity() == 0;
		if (!zero_arity_reached_fact)
		{
			for (unsigned int i = 0; i < created_effect->getReachableFact().getPredicate().getArity(); i++)
			{
				const EquivalentObjectGroup& eog = created_effect->getReachableFact().getTermDomain(i);
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
			best_eog = &eog_manager.getZeroArityEOG();
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
		if (!created_effect->getReachableFact().getPredicate().isStatic())
		{
			std::cout << "New reachable effect: " << created_effect->getReachableFact() << "." << std::endl;
		}
#endif
		
		bool already_reached = false;
		for (std::vector<ReachableFact*>::const_iterator ci = best_eog->getReachableFacts().begin(); ci != best_eog->getReachableFacts().end(); ci++)
		{
			if ((*ci)->isIdenticalTo(created_effect->getReachableFact()))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "New reachable effect: " << created_effect->getReachableFact() << " already achieved by " << **ci << "." << std::endl;
#endif
				already_reached = true;
				break;
			}
		}
		if (already_reached)
		{
			fact_layer.addFact(*created_effect, true);
//			delete &new_reachable_fact;
			continue;
		}
#ifdef DTG_REACHABILITY_KEEP_TIME
		++ReachableTransition::accepted_new_reachable_facts;
#endif
		std::vector<std::pair<ReachableSet*, unsigned int> >* listeners = (*effect_propagation_listeners_[created_effect->getEffectSetIndex()])[created_effect->getEffectIndex()];
/*		std::cout << created_effect->getEffectIndex() << ": NEW RE: " << created_effect->getReachableFact() << " listeners: " << listeners->size() << std::endl;
		
		for (std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator ci = effect_propagation_listeners_.begin(); ci != effect_propagation_listeners_.end(); ++ci)
		{
			const std::vector<std::pair<ReachableSet*, unsigned int> >* listeners = *ci;
			std::cout << "====" << std::endl;
			for (std::vector<std::pair<ReachableSet*, unsigned int> >::const_iterator ci = listeners->begin(); ci != listeners->end(); ++ci)
			{
				std::cout << *(*ci).first << "(" << (*ci).second << ")" << std::endl;
			}
			std::cout << "****" << std::endl;
		}
*/
		for (std::vector<std::pair<ReachableSet*, unsigned int> >::const_iterator ci = listeners->begin(); ci != listeners->end(); ci++)
		{
			(*ci).first->processNewReachableFact(created_effect->getReachableFact(), (*ci).second);
		}

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
		if (!created_effect->getReachableFact().getPredicate().isStatic())
		{
			std::cout << "New reachable effect: " << created_effect->getReachableFact() << "." << std::endl;
		}
#endif

		new_facts_reached = true;
		
		// Update the relevant equivalent object groups.
		if (!zero_arity_reached_fact)
		{
			for (unsigned int i = 0; i < created_effect->getReachableFact().getPredicate().getArity(); i++)
			{
				// Make sure not to add the fact to the same EOG!
				EquivalentObjectGroup& to_add_to = created_effect->getReachableFact().getTermDomain(i);
				
				bool already_added = false;
				for (unsigned int j = 0; j < i; j++)
				{
					EquivalentObjectGroup& previously_added_to = created_effect->getReachableFact().getTermDomain(j);
					if (&to_add_to == &previously_added_to)
					{
						already_added = true;
						break;
					}
				}
				
				if (!already_added)
				{
					created_effect->getReachableFact().getTermDomain(i).addReachableFact(created_effect->getReachableFact());
				}
//				else
//				{
//					std::cout << created_effect->getReachableFact() << " was already added: " << std::endl;
//					std::cout << created_effect->getReachableFact().getTermDomain(i) << std::endl;
//				}
			}
		}
		else
		{
			eog_manager.getZeroArityEOG().addReachableFact(created_effect->getReachableFact());
		}
		
		// Add the fact to the current fact layer.
		fact_layer.addFact(*created_effect, false);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
	std::cout << "[ReachableTransition::generateReachableFacts] Done generating facts. Did we make some new facts? " << new_facts_reached << std::endl;
#endif
	
	return new_facts_reached;
}

void ReachableTransition::generateReachableFacts(const EquivalentObjectGroupManager& eog_manager, std::vector<const AchievingTransition*>& newly_created_reachable_facts, std::vector<const ReachableFact*>& preconditions, std::vector<EquivalentObjectGroup*>& current_variable_assignments, unsigned int precondition_index, const MyPOP::REACHABILITY::ReachableFactLayer& fact_layer)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
	std::cout << "[ReachableTransition::generateReachableFacts] (" << transition_->getAction().getPredicate();
	for (std::vector<EquivalentObjectGroup*>::const_iterator ci = current_variable_assignments.begin(); ci != current_variable_assignments.end(); ++ci)
	{
		if (*ci != NULL)
			(*ci)->printObjects(std::cout);
	}
	std::cout << ")" << std::endl;
	
	std::cout << "Preconditions: " << std::endl;
	for (std::vector<const ReachableFact*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
#endif

	// Found a full set of preconditions!
	if (precondition_index == preconditions_reachable_sets_->size())
	{
		// Check if this has been created before.
		for (std::vector<const std::vector<EquivalentObjectGroup*>*>::const_iterator ci = processed_groups_.begin(); ci != processed_groups_.end(); ++ci)
		{
			const std::vector<EquivalentObjectGroup*>* previous_created_set = *ci;
			bool matches = true;
			for (unsigned int i = 0; i < previous_created_set->size(); ++i)
			{
				EquivalentObjectGroup* previous_eog = (*previous_created_set)[i];
				EquivalentObjectGroup* current_eog = current_variable_assignments[i];
				if (previous_eog != NULL)
				{
					previous_eog = &previous_eog->getRootNode();
				}
				if (current_eog != NULL)
				{
					current_eog = &current_eog->getRootNode();
				}

				if (previous_eog != current_eog)
				{
					matches = false;
					break;
				}
			}
			
			if (matches)
			{
				return;
			}
		}

		// Store cache!
		processed_groups_.push_back(new std::vector<EquivalentObjectGroup*>(current_variable_assignments));
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
		std::cout << "Possible transition: (" << transition_->getAction().getPredicate();
		for (unsigned int i = 0; i < transition_->getAction().getVariables().size(); ++i)
		{
			if (current_variable_assignments[i] == NULL)
			{
				std::cout << "NULL";
			}
			else
			{
				current_variable_assignments[i]->printObjects(std::cout, fact_layer.getLayerNumber() - 1);
			}
			std::cout << " ";
		}
		std::cout << ")" << std::endl;
		std::cout << "Created effects: " << std::endl;
#endif
		//for (std::vector<ReachableSet*>::const_iterator ci = effect_reachable_sets_->begin(); ci != effect_reachable_sets_->end(); ++ci)
		for (unsigned int fact_set_index = 0; fact_set_index < effect_reachable_sets_->size(); ++fact_set_index)
		{
			//ReachableSet* effect = *ci;
			ReachableSet* effect = (*effect_reachable_sets_)[fact_set_index];
			const HEURISTICS::FactSet& effect_fact_set = effect->getFactSet();
			std::vector<std::vector<unsigned int>* >* effects_mappings = (*transition_->getEffectMappings().find(&effect_fact_set)).second;
			
			for (unsigned int fact_index = 0; fact_index < effect_fact_set.getFacts().size(); ++fact_index)
			{
				const HEURISTICS::TransitionFact* fact = effect_fact_set.getFacts()[fact_index];
				std::vector<unsigned int>* effect_mappings = (*effects_mappings)[fact_index];
				
				std::vector<std::vector<EquivalentObjectGroup*>*> possible_domains_per_term;
				
				for (unsigned int term_index = 0; term_index < fact->getVariableDomains().size(); ++term_index)
				{
					std::vector<EquivalentObjectGroup*>* possible_domains = new std::vector<EquivalentObjectGroup*>();
					possible_domains_per_term.push_back(possible_domains);
					EquivalentObjectGroup* eog = current_variable_assignments[(*effect_mappings)[term_index]];
					
					if (eog == NULL)
					{
						for (std::vector<const Object*>::const_iterator ci = fact->getVariableDomains()[term_index]->getVariableDomain().begin(); ci != fact->getVariableDomains()[term_index]->getVariableDomain().end(); ++ci)
						{
							EquivalentObjectGroup& eog = eog_manager.getEquivalentObject(**ci).getEquivalentObjectGroup();
							if (std::find(possible_domains->begin(), possible_domains->end(), &eog) == possible_domains->end())
							{
								possible_domains->push_back(&eog);
							}
						}
					}
					else
					{
						possible_domains->push_back(eog);
					}
				}
				
				// Create all possible effects, if a variable is equal to NULL it is not bounded by its preconditions.
				unsigned int counter[fact->getVariableDomains().size()];
				memset(&counter, 0, sizeof(unsigned int) * fact->getVariableDomains().size());
				
				bool created_all_possible_facts = false;
				while (!created_all_possible_facts)
				{
					created_all_possible_facts = true;
					
					std::vector<EquivalentObjectGroup*>* variable_domains = new std::vector<EquivalentObjectGroup*>();
					for (unsigned int i = 0; i < fact->getVariableDomains().size(); ++i)
					{
						variable_domains->push_back((*possible_domains_per_term[i])[counter[i]]);
					}
					
					ReachableFact& new_effect = ReachableFact::createReachableFact(fact->getPredicate(), *variable_domains);
//					if (effect->processNewReachableFact(new_effect, fact_index))
//					{
//						added_new_fact = true;
//					}
					
					std::vector<HEURISTICS::VariableDomain*> variable_assignments;
					for (unsigned int variable_index = 0; variable_index < current_variable_assignments.size(); ++variable_index)
					{
						HEURISTICS::VariableDomain* variable_domain = new HEURISTICS::VariableDomain();
						EquivalentObjectGroup* eog = current_variable_assignments[variable_index];
						
						if (eog == NULL)
						{
							for (std::vector<const Object*>::const_iterator ci = transition_->getActionVariables()[variable_index]->getVariableDomain().begin(); ci != transition_->getActionVariables()[variable_index]->getVariableDomain().end(); ++ci)
							{
								variable_domain->addObject(**ci);
							}
						}
						else
						{
							for (std::vector<EquivalentObject*>::const_iterator ci = eog->getEquivalentObjects().begin(); ci != eog->getEquivalentObjects().end(); ++ci)
							{
								variable_domain->addObject((*ci)->getObject());
							}
						}
						
						variable_assignments.push_back(variable_domain);
					}
					
					AchievingTransition* created_effect = new AchievingTransition(fact_index, fact_set_index, preconditions, new_effect, *this, variable_assignments, fact_layer);
					newly_created_reachable_facts.push_back(created_effect);

					for (unsigned int i = 0; i < fact->getVariableDomains().size(); ++i)
					{
						if (counter[i] + 1 == (*possible_domains_per_term[i]).size())
						{
							counter[i] = 0;
						}
						else
						{
							counter[i] = counter[i] + 1;
							created_all_possible_facts = false;
							break;
						}
					}
				}
				
				for (std::vector<std::vector<EquivalentObjectGroup*>*>::const_iterator ci = possible_domains_per_term.begin(); ci != possible_domains_per_term.end(); ++ci)
				{
					delete *ci;
				}
			}
		}
		return;
	}
	
	ReachableSet* precondition_reachable_set = (*preconditions_reachable_sets_)[precondition_index];
	std::vector<std::vector<unsigned int>* >* precondition_mappings = (*transition_->getPreconditionMappings().find(&precondition_reachable_set->getFactSet())).second;
	
	for (unsigned int tree_index = 0; tree_index < precondition_reachable_set->getCachedReachableTreesSize(); ++tree_index)
	{
		ReachableTree* current_tree = precondition_reachable_set->getReachableTrees()[tree_index];
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
		std::cout << *current_tree << " - Cached leafs: " << current_tree->getCachedNumberOfLeafs() << std::endl;
#endif
		
		for (unsigned int leaf_index = 0; leaf_index < current_tree->getCachedNumberOfLeafs(); ++leaf_index)
		{
			std::vector<EquivalentObjectGroup*> tmp_current_variable_assignments(current_variable_assignments);
			std::vector<const ReachableFact*> new_preconditions(preconditions);
			const ReachableTreeNode* leaf_node = current_tree->getLeaves()[leaf_index];
			for (unsigned int fact_index = 0; fact_index < (*precondition_mappings).size(); ++fact_index)
			{
				int current_index = (*precondition_mappings).size() - 1 - fact_index;
				
				const ReachableFact& reachable_fact = leaf_node->getReachableFact();
				std::vector<unsigned int>* variable_mappings = (*precondition_mappings)[current_index];
				new_preconditions.push_back(&reachable_fact);
				for (unsigned int term_index = 0; term_index < reachable_fact.getPredicate().getArity(); ++term_index)
				{
					tmp_current_variable_assignments[(*variable_mappings)[term_index]] = &reachable_fact.getTermDomain(term_index);
				}
				
				leaf_node = leaf_node->getParent();
			}
			
			generateReachableFacts(eog_manager, newly_created_reachable_facts, new_preconditions, tmp_current_variable_assignments, precondition_index + 1, fact_layer);
		}
	}
}

void ReachableTransition::equivalencesUpdated(unsigned int iteration)
{
	for (std::vector<const std::vector<EquivalentObjectGroup*>*>::const_iterator ci = processed_groups_.begin(); ci != processed_groups_.end(); ci++)
	{
		const std::vector<EquivalentObjectGroup*>* processed_group = *ci;
		//for (unsigned int i = 0; i < transition_->getAction().getVariables().size(); i++)
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci = processed_group->begin(); ci != processed_group->end(); ++ci)
		{
			EquivalentObjectGroup* eog = *ci;
			if (eog == NULL) continue;
			eog = &eog->getRootNode();
		}
	}
}


std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition)
{
	os << "(" << &reachable_transition << ") Reachable transition: " << reachable_transition.getTransition() << "." << std::endl;
	os << "Preconditions" << std::endl;
	for (std::vector<ReachableSet*>::const_iterator ci = reachable_transition.preconditions_reachable_sets_->begin(); ci != reachable_transition.preconditions_reachable_sets_->end(); ++ci)
	{
		os << **ci << std::endl;
	}
	os << "Effects" << std::endl;
	for (std::vector<ReachableSet*>::const_iterator ci = reachable_transition.effect_reachable_sets_->begin(); ci != reachable_transition.effect_reachable_sets_->end(); ++ci)
	{
		os << **ci << std::endl;
	}
	
	return os;
}

ReachableFactLayerItem::ReachableFactLayerItem(const ReachableFactLayer& reachable_fact_layer, const ReachableFact& reachable_fact)
	: reachable_fact_layer_(&reachable_fact_layer), link_to_actual_reachable_fact_(&reachable_fact)
{
	reachable_fact_copy_ = &ReachableFact::createReachableFact(reachable_fact);
}

ReachableFactLayerItem::~ReachableFactLayerItem()
{
//	for (std::vector<const AchievingTransition*>::const_iterator ci = achievers_.begin(); ci != achievers_.end(); ci++)
//	{
//		delete *ci;
//	}
}

bool ReachableFactLayerItem::canBeAchievedBy(const ResolvedBoundedAtom& precondition, StepID id, const Bindings& bindings, bool debug) const
{
	if (debug)
	{
		std::cout << "Can " << *reachable_fact_copy_ << " be achieved by: " << precondition << "?" << std::endl;
	}
	
	if (precondition.getCorrectedAtom().getPredicate().getName() != reachable_fact_copy_->getPredicate().getName()) return false;
	if (precondition.getCorrectedAtom().getArity() != reachable_fact_copy_->getPredicate().getArity()) return false;
	
	for (unsigned int i = 0; i < precondition.getCorrectedAtom().getArity(); i++)
	{
		const std::vector<const Object*>& precondition_variable_domain = precondition.getVariableDomain(i);
		if (debug)
		{
			std::cout << "Precondition's " << i << "th variable domain: ";
			printVariableDomain(std::cout, precondition_variable_domain);
			std::cout << "; Compare against: ";
			reachable_fact_copy_->getTermDomain(i).printObjects(std::cout, reachable_fact_layer_->getLayerNumber());
			std::cout << std::endl;
		}
		
		for (std::vector<EquivalentObject*>::const_iterator ci = reachable_fact_copy_->getTermDomain(i).begin(reachable_fact_layer_->getLayerNumber()); ci != reachable_fact_copy_->getTermDomain(i).end(reachable_fact_layer_->getLayerNumber()); ci++)
		{
			const EquivalentObject* eo = *ci;
//			std::cout << "Check out: " << eo->getObject() << std::endl;
			bool object_included = false;
			for (std::vector<const Object*>::const_iterator ci = precondition_variable_domain.begin(); ci != precondition_variable_domain.end(); ci++)
			{
				if (&eo->getObject() == *ci)
				{
//					std::cout << "Found object: " << **ci << std::endl;
					object_included = true;
					break;
				}
			}
			
			if (!object_included)
			{
				if (debug)
				{
					assert (eo != NULL);
					std::cout << "The object " << eo->getObject() << " of the term index " << i << " is not contained by the precondition's variable domain: {";
					for (std::vector<const Object*>::const_iterator ci = precondition_variable_domain.begin(); ci != precondition_variable_domain.end(); ci++)
					{
						std::cout << **ci << ", ";
					}
					std::cout << "." << std::endl;
				}
				return false;
			}
		}
	}
	
	return true;
}

void ReachableFactLayerItem::addAchiever(const AchievingTransition& achiever)
{
	achievers_.push_back(&achiever);
	for (std::vector<const ReachableFactLayerItem*>::const_iterator ci = achiever.getPreconditionFactLayerItems().begin(); ci != achiever.getPreconditionFactLayerItems().end(); ++ci)
	{
		const ReachableFactLayerItem* precondition = *ci;
		
		for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_fact_layer_->getReachableFacts().begin(); ci != reachable_fact_layer_->getReachableFacts().end(); ci++)
		{
			if (precondition == *ci)
			{
				std::cout << "Violating precondition: " << *precondition << std::endl;
				assert (false);
			}
		}
	}
}

void ReachableFactLayerItem::addNoop(const ReachableFactLayerItem& noop)
{
	std::vector<const ReachableFactLayerItem*> preconditions;// = new std::vector<const ReachableFactLayerItem*>();
	for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_fact_layer_->getReachableFacts().begin(); ci != reachable_fact_layer_->getReachableFacts().end(); ci++)
	{
		if (&noop == *ci)
		{
			assert (false);
		}
	}
	
	preconditions.push_back(&noop);
	achievers_.push_back(&AchievingTransition::createNoop(preconditions));
}

std::ostream& operator<<(std::ostream& os, const ReachableFactLayerItem& reachable_fact_layer)
{
	reachable_fact_layer.getReachableFactCopy().print(os, reachable_fact_layer.getReachableFactLayer().getLayerNumber());
	os << " - (" << &reachable_fact_layer.getActualReachableFact() << ")" << std::endl;
	os << "Achieved by the preconditions: {" << std::endl;
	for (std::vector<const AchievingTransition*>::const_iterator ci = reachable_fact_layer.getAchievers().begin(); ci != reachable_fact_layer.getAchievers().end(); ci++)
	{
		const AchievingTransition* achieving_transition = *ci;
		const std::vector<const ReachableFactLayerItem*>& preconditions = achieving_transition->getPreconditionFactLayerItems();
		
		if (achieving_transition->getAchiever() != NULL)
		{
			os << achieving_transition->getAchiever()->getTransition().getAction();
		}
		else
		{
			os << "NOOP ";
		}
		os << "\t->\t{";
		for (std::vector<const ReachableFactLayerItem*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			if (*ci == NULL)
			{
				os << "NULL";
			}
			else
			{
				(*ci)->getReachableFactCopy().print(os, reachable_fact_layer.getReachableFactLayer().getLayerNumber());
			}
			if (ci + 1 != preconditions.end())
			{
				os << ", ";
			}
		}
		os << "}, " << std::endl;
		os << "Variable domain: ";
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = achieving_transition->getVariableAssignments().begin(); ci != achieving_transition->getVariableAssignments().end(); ++ci)
		{
			os << **ci << ", ";
		}
		os << std::endl;
	}
	os << "}" << std::endl;
	return os;
}

ReachableFactLayer::ReachableFactLayer(unsigned int nr, const ReachableFactLayer* previous_layer)
	: nr_(nr), previous_layer_(previous_layer)
{
	if (previous_layer_ != NULL)
	{
		for (std::vector<ReachableFactLayerItem*>::const_iterator ci = previous_layer_->getReachableFacts().begin(); ci != previous_layer_->getReachableFacts().end(); ci++)
		{
			ReachableFactLayerItem* item_copy = new ReachableFactLayerItem(*this, (*ci)->getActualReachableFact().getReplacement());
			assert (&item_copy->getReachableFactCopy() != NULL);
			item_copy->addNoop(**ci);
			reachable_facts_.push_back(item_copy);
		}
		
		for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ++ci)
		{
			ReachableFactLayerItem* lhs = *ci;
			
			for (std::vector<ReachableFactLayerItem*>::const_iterator ci = previous_layer_->getReachableFacts().begin(); ci != previous_layer_->getReachableFacts().end(); ci++)
			{
				if (lhs == *ci)
				{
					assert (false);
				}
			}
		}
	}
}

ReachableFactLayer::~ReachableFactLayer()
{
	for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		delete *ci;
	}
	delete previous_layer_;
}
/*
void ReachableFactLayer::finalise()
{
	// Copy the facts from the previous layer and add those facts as precondition.
	if (previous_layer_ != NULL)
	{
		for (std::vector<ReachableFactLayerItem*>::const_iterator ci = previous_layer_->getReachableFacts().begin(); ci != previous_layer_->getReachableFacts().end(); ci++)
		{
			ReachableFactLayerItem* item_copy = new ReachableFactLayerItem(*this, (*ci)->getActualReachableFact().getReplacement());
			assert (&item_copy->getReachableFactCopy() != NULL);
			item_copy->addNoop(**ci);
			reachable_facts_.push_back(item_copy);
		}
	}
}
*/
void ReachableFactLayer::removeAllFacts()
{
	for (std::vector<ReachableFactLayerItem*>::const_iterator ci = getReachableFacts().begin(); ci != getReachableFacts().end(); ++ci)
	{
		delete *ci;
	}
	reachable_facts_.clear();
}

void ReachableFactLayer::addFact(const ReachableFact& reachable_fact)
{
	ReachableFactLayerItem* reachable_item = new ReachableFactLayerItem(*this, reachable_fact);
	reachable_facts_.push_back(reachable_item);
}

void ReachableFactLayer::addFact(const AchievingTransition& achieved_transition, bool already_exists)
{
	if (already_exists)
	{
		for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
		{
			ReachableFactLayerItem* item = *ci;
			if ((*ci)->getReachableFactCopy().isIdenticalTo(achieved_transition.getReachableFact()))
			{
				item->addAchiever(achieved_transition);
				return;
			}
		}
		std::cout << "Could not add " << achieved_transition.getReachableFact() << " to " << *this << std::endl;
		assert (false);
	}
	else
	{
		ReachableFactLayerItem* reachable_item = new ReachableFactLayerItem(*this, achieved_transition.getReachableFact());
		reachable_facts_.push_back(reachable_item);
		reachable_item->addAchiever(achieved_transition);
	}
}

void ReachableFactLayer::extractPreconditions(std::vector<const ReachableFactLayerItem*>& preconditions, const ReachableTreeNode& reachable_tree_node) const
{
	for (ConstReachableTreeIterator ci = reachable_tree_node.cbegin(); ci != reachable_tree_node.cend(); ci++)
	{
//		std::cout << "Find " << *ci << " in " << *this << std::endl;
		const ReachableFactLayerItem* precondition = findPrecondition((*ci).getReachableFact());
		if (precondition == NULL)
		{
			std::cout << "Could not find: " << *ci << std::endl;
			std::cout << *this << std::endl;
			assert (false);
			exit(1);
		}
		preconditions.push_back(precondition);
	}
}

const ReachableFactLayerItem* ReachableFactLayer::findPrecondition(const ReachableFact& reachable_fact) const
{
//	std::cout << "[ReachableFactLayerItem* ReachableFactLayer::findPrecondition(" << reachable_fact << ") const" << std::endl;
	// Always try to check the previous layer first.
	if (previous_layer_ != NULL)
	{
		const ReachableFactLayerItem* found_item = previous_layer_->findPrecondition(reachable_fact);
		if (found_item != NULL)
		{
//			std::cout << "Return: " << *found_item << std::endl;
			return found_item;
		}
	}
	
	for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		//if (&reachable_fact == &(*ci)->getActualReachableFact())
		// TODO: Inefficient way of doing it...
		if (reachable_fact.isIdenticalTo((*ci)->getActualReachableFact()))
		{
//			std::cout << "Found " << reachable_fact << "(" << &reachable_fact << " v.s. " << (*ci)->getActualReachableFact() << "(" << &(*ci)->getActualReachableFact() << ")" << std::endl;
			return *ci;
		}
//		std::cout << "Compare " << reachable_fact << "(" << &reachable_fact << " v.s. " << (*ci)->getActualReachableFact() << "(" << &(*ci)->getActualReachableFact() << ")" << std::endl;
	}
//	std::cout << "Nothing found :'(" << std::endl;
	// Nothing found :(.
	return NULL;
}

void ReachableFactLayer::equivalencesUpdated(unsigned int layer_nr)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << "[ReachableFactLayer::equivalencesUpdated]" << layer_nr << std::endl;
	std::cout << *this << std::endl;
#endif
	// Merge any reachable fact layer items which share the same facts.
	for (std::vector<ReachableFactLayerItem*>::reverse_iterator ri = reachable_facts_.rbegin(); ri != reachable_facts_.rend(); ++ri)
	{
		ReachableFactLayerItem* lhs_item = *ri;
		
		// Check if we can find a reachable fact that is the same as rfl_item.
		bool found_identical_item = false;
		for (std::vector<ReachableFactLayerItem*>::reverse_iterator ri2 = ri + 1; ri2 != reachable_facts_.rend(); ++ri2)
		{
			ReachableFactLayerItem* rhs_item = *ri2;
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
//			std::cout << "Compare " << lhs_item->getReachableFactCopy() << " and " << rhs_item->getReachableFactCopy() << std::endl;
#endif

			if (lhs_item->getActualReachableFact().isIdenticalTo(rhs_item->getActualReachableFact()))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
//				std::cout << "Matches!" << std::endl;
#endif
				found_identical_item = true;
				for (std::vector<const AchievingTransition*>::const_iterator ci = lhs_item->getAchievers().begin(); ci != lhs_item->getAchievers().end(); ++ci)
				{
					rhs_item->addAchiever(**ci);
				}
				break;
			}
		}
		
		if (found_identical_item)
		{
			for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ++ci)
			{
				ReachableFactLayerItem* item = *ci;
				
				for (std::vector<const AchievingTransition*>::const_iterator ci = item->getAchievers().begin(); ci != item->getAchievers().end(); ++ci)
				{
					const AchievingTransition* transition = *ci;
					for (std::vector<const ReachableFactLayerItem*>::const_iterator ci = transition->getPreconditionFactLayerItems().begin(); ci != transition->getPreconditionFactLayerItems().end(); ++ci)
					{
						if (*ci == lhs_item)
						{
							std::cout << "Found an item as a precondition which should not be one!" << std::endl;
							std::cout << *lhs_item << std::endl;
							assert (false);
						}
					}
				}
			}
			
			delete lhs_item;
			reachable_facts_.erase(ri.base() - 1);
		}
	}
}

const std::vector<ReachableFactLayerItem*>& ReachableFactLayer::getReachableFacts() const
{
	return reachable_facts_;
}

const ReachableFactLayerItem* ReachableFactLayer::contains(const Atom& atom) const
{
	for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_facts_.begin(); ci != reachable_facts_.end(); ci++)
	{
		const ReachableFactLayerItem* reachable_item = *ci;
		if (atom.getPredicate().getName() != reachable_item->getReachableFactCopy().getPredicate().getName()) continue;
		if (atom.getPredicate().getArity() != reachable_item->getReachableFactCopy().getPredicate().getArity()) continue;
		
		bool domain_match = true;
		for (unsigned int i = 0; i < reachable_item->getReachableFactCopy().getPredicate().getArity(); i++)
		{
			if (!reachable_item->getReachableFactCopy().getTermDomain(i).contains(*static_cast<const Object*>(atom.getTerms()[i]), nr_))
			{
				domain_match = false;
				break;
			}
		}
		if (!domain_match) continue;
		
		return reachable_item;
	}
	return NULL;
}

unsigned int ReachableFactLayer::getLayerNumber() const
{
	return nr_;
}

const ReachableFactLayer* ReachableFactLayer::getPreviousLayer() const
{
	return previous_layer_;
}

std::ostream& operator<<(std::ostream& os, const ReachableFactLayer& reachable_fact_layer)
{
	os << "Fact layer: " << reachable_fact_layer.getLayerNumber() << std::endl;
	for (std::vector<ReachableFactLayerItem*>::const_iterator ci = reachable_fact_layer.getReachableFacts().begin(); ci != reachable_fact_layer.getReachableFacts().end(); ci++)
	{
		const ReachableFactLayerItem* item = *ci;
		if ((*ci)->getActualReachableFact().getPredicate().isStatic())
		{
			continue;
		}
		bool achieved_by_noop = false;
		for (std::vector<const AchievingTransition*>::const_iterator ci = item->getAchievers().begin(); ci != item->getAchievers().end(); ci++)
		{
			if ((*ci)->getAchiever() == NULL)
			{
				achieved_by_noop = true;
				break;
			}
		}
		
		if (achieved_by_noop && reachable_fact_layer.getLayerNumber() != 0)
		{
//			continue;
		}
		os << *item << std::endl;
	}
	return os;
}

DTGReachability::DTGReachability(const std::vector< MyPOP::HEURISTICS::LiftedTransition* >& lifted_transitions, const MyPOP::TermManager& term_manager, MyPOP::PredicateManager& predicate_manager)
	: term_manager_(&term_manager), current_fact_layer_(NULL)
{
	std::vector<const HEURISTICS::FactSet*> fact_sets;
	std::set<const HEURISTICS::FactSet*> processed_fact_sets;
	for (std::vector<HEURISTICS::LiftedTransition*>::const_iterator ci = lifted_transitions.begin(); ci != lifted_transitions.end(); ++ci)
	{
		const HEURISTICS::LiftedTransition* lifted_transition = *ci;
		std::vector<const HEURISTICS::FactSet*> all_fact_sets(lifted_transition->getPreconditions());
		all_fact_sets.insert(all_fact_sets.end(), lifted_transition->getEffects().begin(), lifted_transition->getEffects().end());
		
		for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = all_fact_sets.begin(); ci != all_fact_sets.end(); ++ci)
		{
			const HEURISTICS::FactSet* fact_set = *ci;
			if (processed_fact_sets.find(fact_set) != processed_fact_sets.end())
			{
				continue;
			}
			
			processed_fact_sets.insert(fact_set);
			fact_sets.push_back(fact_set);
		}
	}
	
	// Initialise the individual groups per object.
	equivalent_object_manager_ = new EquivalentObjectGroupManager(fact_sets, term_manager, predicate_manager);
	
	// Create the reachable facts.
	std::vector<ReachableSet*> all_reachable_sets;
	for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = fact_sets.begin(); ci != fact_sets.end(); ++ci)
	{
		const HEURISTICS::FactSet* fact_set = *ci;
		ReachableSet* reachable_set = new ReachableSet(*equivalent_object_manager_, *fact_set);
		fact_set_to_reachable_set_[fact_set] = reachable_set;
		all_reachable_sets.push_back(reachable_set);
		
//		std::cout << "Map " << *fact_set << " -> " << reachable_set << std::endl;
	}

	for (std::vector<HEURISTICS::LiftedTransition*>::const_iterator ci = lifted_transitions.begin(); ci != lifted_transitions.end(); ++ci)
	{
		const HEURISTICS::LiftedTransition* lifted_transition = *ci;
		
		//std::cout << "Process the lifted transition: " << *lifted_transition << std::endl;

		std::vector<ReachableSet*>* precondition_reachable_sets = new std::vector<ReachableSet*>();
		for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = lifted_transition->getPreconditions().begin(); ci != lifted_transition->getPreconditions().end(); ++ci)
		{
			precondition_reachable_sets->push_back(fact_set_to_reachable_set_[*ci]);
		}
		
		std::vector<ReachableSet*>* effect_reachable_sets = new std::vector<ReachableSet*>();
		for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = lifted_transition->getEffects().begin(); ci != lifted_transition->getEffects().end(); ++ci)
		{
			effect_reachable_sets->push_back(fact_set_to_reachable_set_[*ci]);
		}
		
		reachable_transition_.push_back(new ReachableTransition(*lifted_transition, *precondition_reachable_sets, *effect_reachable_sets));
	}
	
	// Cache predicate ids to reachable sets which contain said predicate.
	predicate_id_to_reachable_sets_mapping_ = new std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >(predicate_manager.getManagableObjects().size());
	for (unsigned int i = 0; i < predicate_manager.getManagableObjects().size(); i++)
	{
		(*predicate_id_to_reachable_sets_mapping_)[i] = new std::vector<std::pair<ReachableSet*, unsigned int> >();
		Predicate* corresponding_predicate = predicate_manager.getManagableObjects()[i];
		
		// Find all facts of the reachable sets whose predicate can substitute for this predicate.
		for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
		{
			ReachableSet* reachable_set = (*ci).second;
			for (std::vector<const HEURISTICS::TransitionFact*>::const_iterator ci = reachable_set->getFactSet().getFacts().begin(); ci != reachable_set->getFactSet().getFacts().end(); ++ci)
			{
				unsigned int index = std::distance(reachable_set->getFactSet().getFacts().begin(), ci);
				const HEURISTICS::TransitionFact* fact = *ci;
				
				if (fact->getPredicate().getName() == corresponding_predicate->getName() &&
				    fact->getPredicate().getArity() == corresponding_predicate->getArity())
				{
					(*predicate_id_to_reachable_sets_mapping_)[i]->push_back(std::make_pair(reachable_set, index));
				}
			}
		}
	}
	
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transition_.begin(); ci != reachable_transition_.end(); ci++)
	{
		(*ci)->finalise(all_reachable_sets);
	}
}

DTGReachability::~DTGReachability()
{
	delete current_fact_layer_;
	delete equivalent_object_manager_;
	for (std::vector<std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator ci = predicate_id_to_reachable_sets_mapping_->begin(); ci != predicate_id_to_reachable_sets_mapping_->end(); ci++)
	{
		delete *ci;
	}
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transition_.begin(); ci != reachable_transition_.end(); ci++)
	{
		delete *ci;
	}
	
	for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
	{
		delete (*ci).second;
	}
	
	delete predicate_id_to_reachable_sets_mapping_;
	AchievingTransition::removeAllAchievingTransitions();
}

void DTGReachability::performReachabilityAnalysis(std::vector<const ReachableFact*>& result, const std::vector<REACHABILITY::ReachableFact*>& initial_facts, const std::vector<const GroundedAtom*>& persistent_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
	std::cout << "Start performing reachability analysis." << std::endl;
#endif

#ifdef DTG_REACHABILITY_KEEP_TIME
	struct timeval start_time_eog;
	gettimeofday(&start_time_eog, NULL);
#endif
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transition_.begin(); ci != reachable_transition_.end(); ++ci)
	{
		(*ci)->reset();
	}

	for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
	{
		ReachableSet* reachable_set = (*ci).second;
		reachable_set->reset();
	}
	
	// Reset the EOGs last because the previous state of the EOGs must be accessable by the reachable sets to revert the EOGs to their original state.
	equivalent_object_manager_->reset();
	ReachableFact::deleteAllReachableFacts(initial_facts);
	AchievingTransition::removeAllAchievingTransitions();
	
	std::vector<const REACHABILITY::ReachableFact*> reachable_persistent_facts;
	// Check which of the facts in the state correspond to the goal facts and prevent these from being deleted.
	for (std::vector<const GroundedAtom*>::const_iterator ci = persistent_facts.begin(); ci != persistent_facts.end(); ++ci)
	{
		const GroundedAtom* persistent_fact = *ci;
		REACHABILITY::ReachableFact& reachable_persistance_fact = REACHABILITY::ReachableFact::createReachableFact(*persistent_fact, *equivalent_object_manager_);
		reachable_persistent_facts.push_back(&reachable_persistance_fact);
		
		for (unsigned int i = 0; i < reachable_persistance_fact.getPredicate().getArity(); ++i)
		{
			reachable_persistance_fact.getTermDomain(i).setMergeable(false);
		}
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		ReachableNode* reachable_node = *ci;
		assert (reachable_node->getReachableTrees().size() == 0);
		for (std::vector<ReachableTransition*>::const_iterator ci = reachable_node->getReachableTransitions().begin(); ci != reachable_node->getReachableTransitions().end(); ci++)
		{
			assert ((*ci)->getReachableTrees().size() == 0);
		}
	}
#endif
	
	// Transform the set of initial facts into reachable facts, which means we drop the variable domains
	// and work solely with equivalent object groups.
	std::vector<ReachableFact*> established_reachable_facts(initial_facts);
	equivalent_object_manager_->initialise(established_reachable_facts);
#ifdef DTG_REACHABILITY_KEEP_TIME
	unsigned int total_number_of_eog = equivalent_object_manager_->getNumberOfEquivalentGroups();
#endif

	equivalent_object_manager_->updateEquivalences(0);
	for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
	{
		(*ci).second->equivalencesUpdated(0);
	}
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transition_.begin(); ci != reachable_transition_.end(); ++ci)
	{
		(*ci)->equivalencesUpdated(0);
	}
	
	delete current_fact_layer_;
	current_fact_layer_ = new ReachableFactLayer(0, NULL);
	
	// Map the initial facts to this fact layer.
	for (std::vector<ReachableFact*>::const_iterator ci = established_reachable_facts.begin(); ci != established_reachable_facts.end(); ci++)
	{
		if ((*ci)->isMarkedForRemoval()) continue;
		current_fact_layer_->addFact(**ci);
	}
	
//	std::cout << "Current layer: " << *current_fact_layer_ << std::endl;
//	std::cout << "EOG manager: " << *equivalent_object_manager_ << std::endl;
	
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
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
	std::cout << "Find initial supported DTG nodes." << std::endl;
#endif
	
	mapInitialFactsToReachableSets(established_reachable_facts);
	
#ifdef DTG_REACHABILITY_KEEP_TIME
	struct timeval end_time_init;
	gettimeofday(&end_time_init, NULL);

	double time_spend_initial = end_time_init.tv_sec - start_time_init.tv_sec + (end_time_init.tv_usec - start_time_init.tv_usec) / 1000000.0;
	std::cerr << "Converting initial facts for " << reachable_nodes_.size() << " nodes: " << time_spend_initial << " seconds. Average = " << (time_spend_initial / reachable_nodes_.size()) << std::endl;
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
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
		std::cout << "Start propagating reachable facts." << std::endl;
		std::cout << *current_fact_layer_ << std::endl;
#endif

		ReachableFactLayer* next_fact_layer = new ReachableFactLayer(iteration, current_fact_layer_);
		current_fact_layer_ = next_fact_layer;

		// Initialise the caches.
		for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
		{
			ReachableSet* reachable_set = (*ci).second;
			reachable_set->getCachedReachableTreesSize();
			for (std::vector<ReachableTree*>::const_iterator ci = reachable_set->getReachableTrees().begin(); ci != reachable_set->getReachableTrees().end(); ++ci)
			{
				ReachableTree* tree = *ci;
				tree->getCachedNumberOfLeafs();
			}
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
		std::cout << "=== POSSIBLE FACTS! ===" << std::endl;
		for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
		{
			ReachableSet* reachable_set = (*ci).second;
			
			for (unsigned int reachable_set_index = 0; reachable_set_index < reachable_set->getCachedReachableTreesSize(); ++reachable_set_index)
			{
				ReachableTree* tree = reachable_set->getReachableTrees()[reachable_set_index];
				std::cout << "=== TREE ===" << std::endl;
				unsigned int nr_leafs = tree->getCachedNumberOfLeafs();
				for (unsigned int leaf_index = 0; leaf_index < nr_leafs; ++leaf_index)
				{
					ReachableTreeNode* leaf = tree->getLeaves()[leaf_index];
					while (leaf != NULL)
					{
						std::cout << *leaf << std::endl;
						leaf = leaf->getParent();
					}
				}
			}
		}
#endif

		done = true;
		for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transition_.begin(); ci != reachable_transition_.end(); ++ci)
		{
			if ((*ci)->generateReachableFacts(*equivalent_object_manager_, *current_fact_layer_, reachable_persistent_facts))
			{
				done = false;
			}
		}

		if (!done)
		{
			equivalent_object_manager_->updateEquivalences(iteration);
			for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
			{
				(*ci).second->equivalencesUpdated(iteration);
			}
			for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transition_.begin(); ci != reachable_transition_.end(); ++ci)
			{
				(*ci)->equivalencesUpdated(iteration);
			}
			current_fact_layer_->equivalencesUpdated(iteration);
			
			// Finally add all the noops.
//			current_fact_layer_->finalise();
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
		std::cout << "End of the iteration. Results so far: " << std::endl;
		std::cout << *current_fact_layer_ << std::endl;
		std::cout << "More to go? " << done << std::endl;
/*
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			(*ci)->print(std::cout);
			std::cout << std::endl;
			ReachableNode* reachable_node = *ci;
			for (std::vector<ReachableTransition*>::const_iterator ci = reachable_node->getReachableTransitions().begin(); ci != reachable_node->getReachableTransitions().end(); ci++)
			{
				(*ci)->print(std::cout);
				std::cout << std::endl;
			}
		}
		std::cout << "EOGs: ";
		std::cout << *equivalent_object_manager_ << std::endl;
*/
#endif
		}
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
	
	// Ignore the last fact layer since it will be empty.
	current_fact_layer_->removeAllFacts();

/*
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
	std::cout << "DONE! All the equivalent objects: " << std::endl;
	std::cout << *equivalent_object_manager_ << std::endl;

	std::cout << "DONE! All resulting nodes: " << std::endl;
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		std::cout << "* ";
		(*ci)->print(std::cout);
		std::cout << "." << std::endl;
	}
#endif
*/
#ifdef DTG_REACHABILITY_KEEP_TIME
	std::cerr << "Generated facts / Accepted facts [%] - " << ReachableTransition::generated_new_reachable_facts << " / " << ReachableTransition::accepted_new_reachable_facts << " [" << (((double)(ReachableTransition::accepted_new_reachable_facts) / ReachableTransition::generated_new_reachable_facts) * 100) << "%]" << std::endl;
	std::cerr << "Compression rate " << 100 - ((double)equivalent_object_manager_->getNumberOfEquivalentGroups() / (double)total_number_of_eog) * 100 << std::endl;
#endif

//	for (std::vector<const REACHABILITY::ReachableFact*>::const_iterator ci = reachable_persistent_facts.begin(); ci != reachable_persistent_facts.end(); ++ci)
//	{
//		delete *ci;
//	}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_PERFORM_REACHABILITY_COMMENT
	std::cout << "Total lifted RPG: " << std::endl;
	const ReachableFactLayer* fl = current_fact_layer_;
	do
	{
		std::cout << *fl << std::endl;
		fl = fl->getPreviousLayer();
	} while (fl != NULL);
#endif
	equivalent_object_manager_->getAllReachableFacts(result);
}

std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> DTGReachability::createNewGoal(const Atom& resolved_goal)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << "Process the goal: ";
	resolved_goal.print(std::cout);
	std::cout << "." << std::endl;
#endif
	
	// Find the earliest layer where this goal is present.
	const ReachableFactLayer* tmp_fact_layer = current_fact_layer_;
	const ReachableFactLayerItem* earliest_known_achiever = NULL;
	while (tmp_fact_layer != NULL)
	{
//		std::cout << *tmp_fact_layer << std::endl;
		const ReachableFactLayerItem* reachable_goal = tmp_fact_layer->contains(resolved_goal);
		if (reachable_goal != NULL)
		{
			earliest_known_achiever = reachable_goal;
		}
		tmp_fact_layer = tmp_fact_layer->getPreviousLayer();
	}
	
	// Goal is unattainable!
	if (earliest_known_achiever == NULL)
	{
/*		std::cerr << "No known early achiever for ";
		resolved_goal.print(std::cout);
		std::cout << " :( " << std::endl;
		const ReachableFactLayer* tmp_fact_layer = current_fact_layer_;
		while (tmp_fact_layer != NULL)
		{
			std::cerr << *tmp_fact_layer << std::endl;
			tmp_fact_layer = tmp_fact_layer->getPreviousLayer();
		}
		
		std::cerr << *equivalent_object_manager_ << std::endl;
		
		assert (false);
*/
		return std::make_pair(static_cast<const ReachableFactLayerItem*>(NULL), static_cast<std::vector<const Object*>**>(NULL));
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << "Earliest achiever: " << *earliest_known_achiever << std::endl;
#endif
	std::vector<const Object*>** grounded_objects = new std::vector<const Object*>*[resolved_goal.getArity()];
	for (unsigned int i = 0; i < resolved_goal.getArity(); i++)
	{
		std::vector<const Object*>* new_variable_domain = new std::vector<const Object*>();
		//new_variable_domain->push_back(goal->getVariableDomain(i, bindings)[0]);
		new_variable_domain->push_back(static_cast<const Object*>(resolved_goal.getTerms()[i]));
		grounded_objects[i] = new_variable_domain;
	}
	return std::make_pair(earliest_known_achiever, grounded_objects);
}

std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> DTGReachability::findFactWhichAchieves(const ReachableFactLayerItem& current_goal, std::vector<const Object*>** object_bindings, std::set<std::pair<const EquivalentObject*, const EquivalentObject*> >& combined_eogs_)
{
	// Check if the substitutions have already been made.
	bool substitutions_have_already_been_made = true;
	for (unsigned int i = 0; i < current_goal.getReachableFactCopy().getPredicate().getArity(); ++i)
	{
		const std::vector<const Object*>* goal_variable_domain = object_bindings[i];
		const EquivalentObjectGroup& fact_variable_domain = current_goal.getReachableFactCopy().getTermDomain(i);
		bool substitution_found = false;
		for (std::vector<const Object*>::const_iterator ci = goal_variable_domain->begin(); ci != goal_variable_domain->end(); ++ci)
		{
			const EquivalentObject& goal_eo = equivalent_object_manager_->getEquivalentObject(**ci);
			for (std::vector<EquivalentObject*>::const_iterator ci = fact_variable_domain.begin(current_goal.getReachableFactLayer().getLayerNumber()); ci != fact_variable_domain.end(current_goal.getReachableFactLayer().getLayerNumber()); ++ci)
			{
				if (combined_eogs_.find(std::make_pair(&goal_eo, *ci)) != combined_eogs_.end())
				{
					substitution_found = true;
					break;
				}
			}
			if (substitution_found)
			{
				break;
			}
		}
		if (!substitution_found)
		{
			substitutions_have_already_been_made = false;
			break;
		}
	}
	
	if (substitutions_have_already_been_made)
	{
		return std::make_pair(static_cast<const ReachableFactLayerItem*>(NULL), static_cast<std::vector<const Object*>**>(NULL));
	}
/*
	// Else make the substitutions now.
	for (unsigned int i = 0; i < current_goal.getReachableFactCopy().getPredicate().getArity(); ++i)
	{
		const std::vector<const Object*>* goal_variable_domain = object_bindings[i];
		const EquivalentObjectGroup& fact_variable_domain = current_goal.getReachableFactCopy().getTermDomain(i);
		for (std::vector<const Object*>::const_iterator ci = goal_variable_domain->begin(); ci != goal_variable_domain->end(); ++ci)
		{
			const EquivalentObject& goal_eo = equivalent_object_manager_->getEquivalentObject(**ci);
			for (std::vector<EquivalentObject*>::const_iterator ci = fact_variable_domain.begin(current_goal.getReachableFactLayer().getLayerNumber()); ci != fact_variable_domain.end(current_goal.getReachableFactLayer().getLayerNumber()); ++ci)
			{
				combined_eogs_.insert(std::make_pair(*ci, &goal_eo));
				combined_eogs_.insert(std::make_pair(&goal_eo, *ci));
			}
		}
	}
*/
	// Add a new goal based on the value we expected to find.
	const ReachableFactLayer* tmp_layer = current_fact_layer_;
	const ReachableFactLayerItem* matching_fact_item_layer = NULL;
	while (tmp_layer != NULL)
	{
		for (std::vector<ReachableFactLayerItem*>::const_iterator ci = tmp_layer->getReachableFacts().begin(); ci != tmp_layer->getReachableFacts().end(); ++ci)
		{
			const ReachableFactLayerItem* layer_item = *ci;
			const ReachableFact& reachable_fact = layer_item->getReachableFactCopy();
			
			if (reachable_fact.getPredicate().getArity() != current_goal.getActualReachableFact().getPredicate().getArity() ||
			    reachable_fact.getPredicate().getName() != current_goal.getActualReachableFact().getPredicate().getName())
			{
				continue;
			}
			
			bool terms_match = true;
			for (unsigned int i = 0; i < reachable_fact.getPredicate().getArity(); ++i)
			{
				const std::vector<const Object*>* goal_variable_domain = object_bindings[i];
				const EquivalentObjectGroup& fact_variable_domain = reachable_fact.getTermDomain(i);
				
				for (std::vector<const Object*>::const_iterator ci = goal_variable_domain->begin(); ci != goal_variable_domain->end(); ++ci)
				{
					const Object* object = *ci;
					if (!fact_variable_domain.contains(*object, tmp_layer->getLayerNumber()))
					{
						terms_match = false;
						break;
					}
				}
				if (!terms_match)
				{
					break;
				}
			}
			
			if (terms_match)
			{
				matching_fact_item_layer = layer_item;
				break;
			}
		}
		
		tmp_layer = tmp_layer->getPreviousLayer();
	}
	assert (matching_fact_item_layer != NULL);
	
	return std::make_pair(matching_fact_item_layer, object_bindings);
}

unsigned int DTGReachability::makeSubstitutions(const ReachableFactLayerItem& current_goal, std::vector< const MyPOP::Object* >** object_bindings, std::set< std::pair< const EquivalentObject*, const EquivalentObject* > >& made_substitutions)
{
	unsigned int substitution_cost = 0;
	// Check if the variables still match up.
	for (unsigned int term_index = 0; term_index < current_goal.getReachableFactCopy().getPredicate().getArity(); ++term_index)
	{
		std::vector<const Object*> intersection;
		const std::vector<const Object*>* current_variable_domains = object_bindings[term_index];
		
//		std::cout << "Check ";
//		printVariableDomain(std::cout, *current_variable_domains);
//		std::cout << " v.s. ";
//		current_goal.getReachableFactCopy().getTermDomain(term_index).printObjects(std::cout, current_goal.getReachableFactLayer().getLayerNumber());
//		std::cout << std::endl;
		
		for (std::vector<const Object*>::const_iterator ci = current_variable_domains->begin(); ci != current_variable_domains->end(); ++ci)
		{
			if (current_goal.getReachableFactCopy().getTermDomain(term_index).contains(**ci, current_goal.getReachableFactLayer().getLayerNumber()))
			{
				intersection.push_back(*ci);
			}
		}
		
		if (intersection.empty())
		{
			bool substitution_made = false;
			for (std::vector<const Object*>::const_iterator ci = current_variable_domains->begin(); ci != current_variable_domains->end(); ++ci)
			{
				const EquivalentObject& lhs_eo = equivalent_object_manager_->getEquivalentObject(**ci);
				for (std::vector<EquivalentObject*>::const_iterator ci = current_goal.getReachableFactCopy().getTermDomain(term_index).begin(current_goal.getReachableFactLayer().getLayerNumber()); ci != current_goal.getReachableFactCopy().getTermDomain(term_index).end(current_goal.getReachableFactLayer().getLayerNumber()); ++ci)
				{
					const EquivalentObject* rhs_eo = *ci;
					if (made_substitutions.count(std::make_pair(&lhs_eo, rhs_eo)) == 0)
					{
						/*
						const EquivalentObjectGroup& lhs_eog = lhs_eo.getEquivalentObjectGroup().getEOGAtLayer(current_goal.getReachableFactLayer().getLayerNumber());
						for (std::vector<EquivalentObject*>::const_iterator ci = lhs_eog.begin(current_goal.getReachableFactLayer().getLayerNumber()); ci != lhs_eog.end(current_goal.getReachableFactLayer().getLayerNumber()); ++ci)
						{
							const EquivalentObject* all_lhs_eo = *ci;
							made_substitutions.insert(std::make_pair(all_lhs_eo, rhs_eo));
						}
						*/
						for (unsigned int layer_number = 0; layer_number < current_fact_layer_->getLayerNumber(); layer_number++)
						{
							if (lhs_eo.getEquivalentObjectGroup().contains(rhs_eo->getObject(), layer_number))
							{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
								std::cout << "Add " << layer_number << " to the total heuristic." << std::endl;
#endif
								made_substitutions.insert(std::make_pair(rhs_eo, &lhs_eo));
								made_substitutions.insert(std::make_pair(&lhs_eo, rhs_eo));
								substitution_cost += layer_number;
								substitution_made = true;
								break;
							}
						}
						if (substitution_made)
						{
							break;
						}
					}
				}
				
				if (substitution_made)
				{
					break;
				}
			}
		}
	}
	
	return substitution_cost;
}

unsigned int DTGReachability::substitute(const EquivalentObjectGroup& objects_to_be_substituted, unsigned int fact_layer, const std::vector<const Object*>& substitution)
{
	for (std::vector<const Object*>::const_iterator ci = substitution.begin(); ci != substitution.end(); ci++)
	{
		const EquivalentObject& eo = equivalent_object_manager_->getEquivalentObject(**ci);
		for (std::vector<EquivalentObject*>::const_iterator ci = objects_to_be_substituted.begin(fact_layer); ci != objects_to_be_substituted.end(fact_layer); ci++)
		{
			if (combined_eogs_.count(std::make_pair(&eo, *ci)) == 1)
			{
				return 0;
			}
		}
	}

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << "Need to make a substitution from: ";
	objects_to_be_substituted.printObjects(std::cerr, fact_layer);
	std::cout << "to ";
	printVariableDomain(std::cerr, substitution);
	std::cout << std::endl;
#endif
	
	// For now we simply take the first layer at which they become equivalent!
	for (unsigned int layer_number = 0; layer_number < current_fact_layer_->getLayerNumber(); layer_number++)
	{
		for (std::vector<const Object*>::const_iterator ci = substitution.begin(); ci != substitution.end(); ci++)
		{
			if (objects_to_be_substituted.contains(**ci, layer_number))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "Add " << layer_number << " to the heuristic!" << std::endl;
#endif

				for (std::vector<const Object*>::const_iterator ci = substitution.begin(); ci != substitution.end(); ci++)
				{
					const EquivalentObject& eo = equivalent_object_manager_->getEquivalentObject(**ci);
					for (std::vector<EquivalentObject*>::const_iterator ci = objects_to_be_substituted.begin(fact_layer); ci != objects_to_be_substituted.end(fact_layer); ci++)
					{
						combined_eogs_.insert(std::make_pair(&eo, *ci));
						combined_eogs_.insert(std::make_pair(*ci, &eo));
					}
				}
				return layer_number;
			}
		}
	}
	
	// We should always find a layer number at which the substitution can be made.
	std::cerr << "Could not make the substitution!" << std::endl;
	objects_to_be_substituted.printObjects(std::cerr, fact_layer);
	std::cout << "to ";
	printVariableDomain(std::cerr, substitution);
	std::cout << std::endl;
	assert (false);
	return 0;
}

void DTGReachability::substitute(const EquivalentObject& lhs, const EquivalentObject& rhs, std::priority_queue<std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**>, std::vector<std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> >, compareReachableFactLayerItem>& open_list)
{
	if (combined_eogs_.find(std::make_pair(&lhs, &rhs)) != combined_eogs_.end())
	{
		return;
	}
	
	const ReachableFactLayer* first_fact_layer = current_fact_layer_;
	while (first_fact_layer->getPreviousLayer() != NULL)
	{
		first_fact_layer = first_fact_layer->getPreviousLayer();
	}
	
	// Find for all facts that contain the lhs object.
	for (std::vector<ReachableFactLayerItem*>::const_iterator ci = first_fact_layer->getReachableFacts().begin(); ci != first_fact_layer->getReachableFacts().end(); ++ci)
	{
		const ReachableFactLayerItem* initial_item = *ci;
		bool contains_lhs = false;
		
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci = initial_item->getReachableFactCopy().getTermDomains().begin(); ci != initial_item->getReachableFactCopy().getTermDomains().end(); ++ci)
		{
			EquivalentObjectGroup* eog = *ci;
			if (eog->contains(lhs.getObject(), 0))
			{
				contains_lhs = true;
				break;
			}
		}
		
		if (!contains_lhs)
		{
			continue;
		}
		
		std::vector<EquivalentObjectGroup*>* domains = new std::vector<EquivalentObjectGroup*>();
		
		std::vector<const Object*>** variable_domains = new std::vector<const Object*>*[initial_item->getReachableFactCopy().getTermDomains().size()];
		
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci = initial_item->getReachableFactCopy().getTermDomains().begin(); ci != initial_item->getReachableFactCopy().getTermDomains().end(); ++ci)
		{
			unsigned int term_index = std::distance(initial_item->getReachableFactCopy().getTermDomains().begin(), ci);
			std::vector<const Object*>* variable_domain = new std::vector<const Object*>();
			variable_domains[term_index] = variable_domain;
			EquivalentObjectGroup* eog = *ci;
			if (eog->contains(lhs.getObject(), 0))
			{
				domains->push_back(&rhs.getEquivalentObjectGroup());
				variable_domain->push_back(&rhs.getObject());
			}
			else
			{
				domains->push_back(eog);
				for (std::vector<EquivalentObject*>::const_iterator ci = eog->begin(0); ci != eog->end(0); ++ci)
				{
					variable_domain->push_back(&(*ci)->getObject());
				}
			}
		}
			
		ReachableFact reachable_fact(initial_item->getReachableFactCopy().getPredicate(), *domains);
		
		// Find a fact layer where this reachable fact is true.
		const ReachableFactLayerItem* found_layer_item = NULL;
		
		const ReachableFactLayer* tmp_reachable_fact_layer = current_fact_layer_;
		while (tmp_reachable_fact_layer != NULL)
		{
			const ReachableFactLayerItem* found_layer_item_tmp = tmp_reachable_fact_layer->findPrecondition(reachable_fact);
			if (found_layer_item_tmp != NULL)
			{
				found_layer_item = found_layer_item_tmp;
			}
			tmp_reachable_fact_layer = tmp_reachable_fact_layer->getPreviousLayer();
		}
		
		assert (found_layer_item != NULL);
		open_list.push(std::make_pair(found_layer_item, variable_domains));
	}
}

unsigned int DTGReachability::getHeuristic(const std::vector<const GroundedAtom*>& bounded_goal_facts, PredicateManager& predicate_manager, bool allow_new_goals_added, bool create_helpful_actions, bool instantiate_actions)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << " ************************************************************** " << std::endl;
	std::cout << " ********************* GET HEURISTIC ************************** " << std::endl;
	std::cout << " ************************************************************** " << std::endl;
#endif
	combined_eogs_.clear();
	
	std::priority_queue<std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**>, std::vector<std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> >, compareReachableFactLayerItem> open_list;

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
	std::cout << "Fact layers: " << std::endl;
	const ReachableFactLayer* rfl = current_fact_layer_;
	while (rfl != NULL)
	{
		std::cout << *rfl << std::endl;
		rfl = rfl->getPreviousLayer();
	}
	std::cout << "Get the heuristic for " << bounded_goal_facts.size() << " goals!" << std::endl;
#endif

//	std::vector<const std::vector<const Object*>* > variable_domains_of_goals;
	for (std::vector<const GroundedAtom*>::const_iterator ci = bounded_goal_facts.begin(); ci != bounded_goal_facts.end(); ci++)
	{
		const Atom& resolved_goal = (*ci)->getAtom();
 		std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> goal = createNewGoal(resolved_goal);
		if (goal.first != NULL)
		{
			open_list.push(goal);
		}
		else
		{
			return std::numeric_limits<unsigned int>::max();
		}
	}

	unsigned int heuristic = 0;
 	std::vector<const AchievingTransition*> executed_actions;
	std::set<std::pair<const ReachableFact*, unsigned int> > closed_list;
	
	std::vector<std::pair<const Predicate*, std::vector<const Object*>**> > newly_added_goals;
	
	while (!open_list.empty())
	{
		const ReachableFactLayerItem* current_goal = open_list.top().first;
		std::vector<const Object*>** object_bindings = open_list.top().second;
		open_list.pop();
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
		std::cout << "Work on the goal: " << *current_goal << "(" << current_goal->getReachableFactLayer().getLayerNumber() << ")" << std::endl;
		std::cout << "Bindings of the variables: ";
		for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); i++)
		{
			printVariableDomain(std::cout, *object_bindings[i]);
			
//			if (object_bindings[i] == NULL) std::cout << "FREE ";
//			else std::cout << *object_bindings[i] << " ";
		}
		std::cout << std::endl;
#endif
		
/*
		// If the goal has NOOPs which achieve it, backtrace all the noops until we reach a fact which does not contain a noop.
//		const ReachableFactLayerItem* noop_source = current_goal;
		bool has_noop = true;
		while (has_noop)
		{
			has_noop = false;
			for (std::vector<const AchievingTransition*>::const_iterator ci = current_goal->getAchievers().begin(); ci != current_goal->getAchievers().end(); ci++)
			{
				const AchievingTransition* transition = *ci;
				if (transition->getAchiever() == NULL)
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "Found a NOOP achieving: " << current_goal->getReachableFactCopy() << " >>>==--> " << *(*ci)->getPreconditionFactLayerItems()[0] << std::endl;
#endif

//					std::cout << "No substitutions necessary!" << std::endl;
//					current_goal = (*ci)->getPreconditionFactLayerItems()[0];
//					has_noop = true;
					
//					unsigned int cost_to_make_substitutions = makeSubstitutions(*current_goal, object_bindings, combined_eogs_);
//					std::cout << "Add " << cost_to_make_substitutions << " to the total cost!" << std::endl;
//					heuristic += cost_to_make_substitutions;

					// Check if the NOOP breaks any variables.
					std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> noop_goal = findFactWhichAchieves(*(*ci)->getPreconditionFactLayerItems()[0], object_bindings, combined_eogs_);

					if (noop_goal.first == NULL || current_goal->getAchievers().size() == 1)
					{
//						std::cout << "No substitutions necessary!" << std::endl;
						current_goal = (*ci)->getPreconditionFactLayerItems()[0];
						has_noop = true;
						
						unsigned int cost_to_make_substitutions = makeSubstitutions(*current_goal, object_bindings, combined_eogs_);
//						std::cout << "Add " << cost_to_make_substitutions << " to the total cost!" << std::endl;
						heuristic += cost_to_make_substitutions;
					}
*/
/*					// If the NOOP breaks variables check if there is any achiever which doesn't. If there is ignore the NOOP. If there are no
					// achievers which do not break the variable domains than we stick with the NOOPs.
					else
					{
						std::cout << "Need substitutions!" << std::endl;
						bool contains_non_destructive_achiever = false;
						for (std::vector<const AchievingTransition*>::const_iterator ci = current_goal->getAchievers().begin(); ci != current_goal->getAchievers().end(); ci++)
						{
							const AchievingTransition* transition = *ci;
							if (transition->getAchiever() == NULL)
							{
								continue;
							}
							
							if (transition->canAchieve(*current_goal, object_bindings))
							{
								contains_non_destructive_achiever = true;
								break;
							}
						}
						
						if (!contains_non_destructive_achiever)
						{
							std::cout << "NOOP breaks bindings, but could not find an achiever which does not do the same..." << std::endl;
							current_goal = transition->getPreconditionFactLayerItems()[0];
							
							
							unsigned int cost_to_make_substitutions = makeSubstitutions(*current_goal, object_bindings, combined_eogs_);
							heuristic += cost_to_make_substitutions;
*/

/*
							// Check if the variables still match up.
							for (unsigned int term_index = 0; term_index < current_goal->getReachableFactCopy().getPredicate().getArity(); ++term_index)
							{
								std::vector<const Object*> intersection;
								const std::vector<const Object*>* current_variable_domains = object_bindings[term_index];
								
								std::cout << "Check ";
								printVariableDomain(std::cout, *current_variable_domains);
								std::cout << " v.s. ";
								current_goal->getReachableFactCopy().getTermDomain(term_index).printObjects(std::cout, current_goal->getReachableFactLayer().getLayerNumber());
								std::cout << std::endl;
								
								for (std::vector<const Object*>::const_iterator ci = current_variable_domains->begin(); ci != current_variable_domains->end(); ++ci)
								{
									if (current_goal->getReachableFactCopy().getTermDomain(term_index).contains(**ci, current_goal->getReachableFactLayer().getLayerNumber()))
									{
										intersection.push_back(*ci);
									}
								}
								
								if (intersection.empty())
								{
									for (std::vector<const Object*>::const_iterator ci = current_variable_domains->begin(); ci != current_variable_domains->end(); ++ci)
									{
										const EquivalentObject& lhs_eo = equivalent_object_manager_->getEquivalentObject(**ci);
										for (std::vector<EquivalentObject*>::const_iterator ci = current_goal->getReachableFactCopy().getTermDomain(term_index).begin(current_goal->getReachableFactLayer().getLayerNumber()); ci != current_goal->getReachableFactCopy().getTermDomain(term_index).end(current_goal->getReachableFactLayer().getLayerNumber()); ++ci)
										{
											const EquivalentObject* rhs_eo = *ci;
//											if (combined_eogs_.count(std::make_pair(&lhs_eo, rhs_eo)) == 0)
											{
												combined_eogs_.insert(std::make_pair(&lhs_eo, rhs_eo));
												for (unsigned int layer_number = 0; layer_number < current_fact_layer_->getLayerNumber(); layer_number++)
												{
													if (lhs_eo.getEquivalentObjectGroup().contains(rhs_eo->getObject(), layer_number))
													{
														std::cout << "Add " << layer_number << " to the total heuristic." << std::endl;
														heuristic += layer_number;
														break;
													}
												}
											}
										}
									}
								}
							}
							has_noop = true;
						}
						else
						{
							assert (false);
							std::cout << "Ignore the NOOP achieving: " << *current_goal << " >>>==--> " << *transition->getPreconditionFactLayerItems()[0] << std::endl;
							std::cout << "New goal: " << std::endl;
							for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); i++)
							{
								printVariableDomain(std::cout, *object_bindings[i]);
							}
						}
					}
*/
/*
					break;
				}
			}
		}
*/
		// If it's part of the initial state, we're done!
		if (current_goal->getReachableFactLayer().getLayerNumber() == 0)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
			std::cout << "The goal " << *current_goal << " is part of the initial state!" << std::endl;
			std::cout << "Found bindings: ";
			for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); i++)
			{
				printVariableDomain(std::cout, *object_bindings[i]);
			}
			std::cout << "Actual bindings: " << current_goal->getActualReachableFact() << std::endl;
#endif

			if (!allow_new_goals_added)
			{
				unsigned int cost_to_make_substitutions = makeSubstitutions(*current_goal, object_bindings, combined_eogs_);
	//			std::cout << "Add " << cost_to_make_substitutions << " for the substitutions" << std::endl;
				heuristic += cost_to_make_substitutions;
				
				for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); ++i)
				{
					delete object_bindings[i];
				}
				
				delete[] object_bindings;
				continue;
			}
			else
			{
				bool variable_domains_overlap = true;
				for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); i++)
				{
					// Check if there is an overlap.
					bool variable_domain_overlaps = false;
					for (std::vector<const Object*>::const_iterator ci = (object_bindings[i])->begin(); ci != (object_bindings[i])->end(); ci++)
					{
						if (current_goal->getReachableFactCopy().getTermDomain(i).contains(**ci, 0))
						{
							variable_domain_overlaps = true;
							break;
						}
					}
					
					if (!variable_domain_overlaps)
					{
						variable_domains_overlap = false;
						break;
					}
				}
				if (variable_domains_overlap)
				{
					for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); ++i)
					{
						delete object_bindings[i];
					}
					
					delete[] object_bindings;
					continue;
				}
				
				// Add a new goal based on the value we expected to find.
				std::pair<const ReachableFactLayerItem*, std::vector<const Object*>**> new_goal = findFactWhichAchieves(*current_goal, object_bindings, combined_eogs_);
				if (new_goal.first == NULL && new_goal.first != current_goal)
				{
					for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); ++i)
					{
						delete object_bindings[i];
					}
					
					delete[] object_bindings;
				}
				else
				{
	#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "Old goal " << *current_goal << std::endl;
					for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); i++)
					{
						printVariableDomain(std::cout, *object_bindings[i]);
					}
					
					std::cout << "New goal " << *new_goal.first << std::endl;
					for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); i++)
					{
						printVariableDomain(std::cout, *object_bindings[i]);
					}
	#endif
					
					const Predicate& predicate = new_goal.first->getReachableFactCopy().getPredicate();
					
					// Make sure that we have not added this goal in the past. If this is the case than we are stuck in a loop and break out of it
					// by estimating the cost of making the substitution.
					bool has_been_substituted_before = false;
					for (std::vector<std::pair<const Predicate*, std::vector<const Object*>** > >::const_iterator ci = newly_added_goals.begin(); ci != newly_added_goals.end(); ++ci)
					{
						if (predicate.getArity() != (*ci).first->getArity() ||
							predicate.getName() != (*ci).first->getName())
						{
							continue;
						}
						
						bool terms_match = true;
						for (unsigned int term_index = 0; term_index < (*ci).first->getArity(); ++term_index)
						{
							const std::vector<const Object*>* variable_domain = (*ci).second[term_index];
							const std::vector<const Object*>* object_binding = object_bindings[term_index];
							
							// Check if these two domains are equal.
							HEURISTICS::VariableDomain lhs(*variable_domain);
							HEURISTICS::VariableDomain rhs(*object_binding);
							
							if (lhs != rhs)
							{
								terms_match = false;
								break;
							}
						}
						
						// If the terms match than we have performed this substitution in the past and are now trapped in a loop.
						if (terms_match)
						{
							has_been_substituted_before = true;
							unsigned int cost_to_make_substitutions = makeSubstitutions(*current_goal, object_bindings, combined_eogs_);
	//						std::cout << "Add " << cost_to_make_substitutions << " for the substitutions" << std::endl;
							heuristic += cost_to_make_substitutions;
							
							for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); ++i)
							{
								delete object_bindings[i];
							}
							
							delete[] object_bindings;
							break;
						}
					}
					if (has_been_substituted_before)
					{
						continue;
					}
					
					std::vector<const Object*>** variable_domain_copy = new std::vector<const Object*>*[predicate.getArity()];
					for (unsigned int term_index = 0; term_index < predicate.getArity(); ++term_index)
					{
						variable_domain_copy[term_index] = new std::vector<const Object*>(*object_bindings[term_index]);
					}
					newly_added_goals.push_back(std::make_pair(&predicate, variable_domain_copy));
					
					open_list.push(new_goal);
				}
				continue;
			}
		}

		// Select cheapest achiever.
		const AchievingTransition* cheapest_achiever = NULL;
		unsigned long cheapest_achiever_cost = std::numeric_limits<unsigned int>::max();
		bool cheapest_needs_to_make_a_substitution = true;
		for (std::vector<const AchievingTransition*>::const_iterator ci = current_goal->getAchievers().begin(); ci != current_goal->getAchievers().end(); ++ci)
		{
			const AchievingTransition* achiever = *ci;
			unsigned long precondition_cost = 0;
			unsigned long need_to_make_a_substitution = 0;
			
			if (achiever->getAchiever() == NULL)
			{
				// Check if the NOOP breaks any variable.
				const ReachableFactLayerItem* precondition_layer_item = achiever->getPreconditionFactLayerItems()[0];
				const ReachableFact& precondition_reachable_fact = precondition_layer_item->getReachableFactCopy();
				for (unsigned int term_index = 0; term_index < current_goal->getReachableFactCopy().getPredicate().getArity(); ++term_index)
				{
					std::vector<const Object*> intersection;
					const std::vector<const Object*>* current_variable_domains = object_bindings[term_index];

					for (std::vector<const Object*>::const_iterator ci = current_variable_domains->begin(); ci != current_variable_domains->end(); ++ci)
					{
						//if (current_goal->getReachableFactCopy().getTermDomain(term_index).contains(**ci, current_goal->getReachableFactLayer().getLayerNumber()))
						if (precondition_reachable_fact.getTermDomain(term_index).contains(**ci, precondition_layer_item->getReachableFactLayer().getLayerNumber()))
						{
							intersection.push_back(*ci);
						}
					}
					
					if (intersection.empty())
					{
						need_to_make_a_substitution = true;
						break;
					}
				}
			}
			else
			{
				// Check if we need to subsitute any variables.
				std::vector<std::pair<const EquivalentObject*, const EquivalentObject*> > needed_substituting;
				achiever->getNeededSubstitutes(needed_substituting, *current_goal, object_bindings, *equivalent_object_manager_, achiever->getEffectSetIndex(), achiever->getEffectIndex());
				
				if (needed_substituting.size() > 0)
				{
					need_to_make_a_substitution = true;
				}
/*
				for (std::vector<std::pair<const EquivalentObject*, const EquivalentObject*> >::const_iterator ci = needed_substituting.begin(); ci != needed_substituting.end(); ++ci)
				{
					const EquivalentObject* lhs_eo = (*ci).first;
					const EquivalentObject* rhs_eo = (*ci).second;
					if (combined_eogs_.find(std::make_pair(lhs_eo, rhs_eo)) == combined_eogs_.end())
					{
						need_to_make_a_substitution = true;
						break;
///
						std::cout << "Substitute: " << lhs_eo->getObject() << " -> " << rhs_eo->getObject() << " costs ???" << std::endl;
						for (unsigned int layer_number = 0; layer_number < current_fact_layer_->getLayerNumber(); layer_number++)
						{
							if (lhs_eo->getEquivalentObjectGroup().contains(rhs_eo->getObject(), layer_number))
							{
								substitution_cost += layer_number;
								std::cout << "Substitute: " << lhs_eo->getObject() << " -> " << rhs_eo->getObject() << " costs " << layer_number << std::endl;
								break;
							}
						}
///
					}
				}
*/

				for (std::vector<const ReachableFactLayerItem*>::const_iterator ci = achiever->getPreconditionFactLayerItems().begin(); ci != achiever->getPreconditionFactLayerItems().end(); ++ci)
				{
					precondition_cost += (*ci)->getReachableFactLayer().getLayerNumber();
	//				std::cout << "+costs: " << (*ci)->getReachableFactLayer().getLayerNumber() << ": " << **ci << std::endl;
				}
			}
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
			std::cout << "Achiever: " << *achiever << " costs=" << precondition_cost << " = need substition?" << need_to_make_a_substitution << std::endl;
#endif
			
//			std::cout << "Total costs: " << cost << std::endl;
			
			// We prefer achievers which do not need any substitutes, otherwise we pick the achiever with the lowest cost.
			if ((!need_to_make_a_substitution && cheapest_needs_to_make_a_substitution) ||
			    (need_to_make_a_substitution == cheapest_needs_to_make_a_substitution && precondition_cost < cheapest_achiever_cost)
			   )
//			if (precondition_cost/* + precondition_cost * substitution_cost */< cheapest_achiever_cost)
			{
//				std::cout << "It's cheaper!" << std::endl;
				cheapest_achiever = achiever;
				cheapest_achiever_cost = precondition_cost;
				//cheapest_subsituting_cost = substitution_cost;
				cheapest_needs_to_make_a_substitution = need_to_make_a_substitution;
			}
		}
		
		// Check if this action has not already been executed.
		if (cheapest_achiever == NULL)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
			std::cout << "Could find no achiever for the goal :(." << std::endl;
#endif
			continue;
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
		std::cout << "Selected cheapest achiever: " << *cheapest_achiever << "(cost=" << cheapest_achiever_cost << ")" << std::endl;
#endif
		if (cheapest_achiever->getAchiever() == NULL)
		{
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
			std::cout << "Found a NOOP achieving: " << current_goal->getReachableFactCopy() << " >>>==--> " << *cheapest_achiever->getPreconditionFactLayerItems()[0] << std::endl;
#endif

			const ReachableFactLayerItem* precondition_layer_item = cheapest_achiever->getPreconditionFactLayerItems()[0];
			if (!allow_new_goals_added)
			{
				// Check if the NOOP breaks any variable.
				const ReachableFact& precondition_reachable_fact = precondition_layer_item->getReachableFactCopy();
				for (unsigned int term_index = 0; term_index < current_goal->getReachableFactCopy().getPredicate().getArity(); ++term_index)
				{
					std::vector<const Object*> intersection;
					const std::vector<const Object*>* current_variable_domains = object_bindings[term_index];

					for (std::vector<const Object*>::const_iterator ci = current_variable_domains->begin(); ci != current_variable_domains->end(); ++ci)
					{
						//if (current_goal->getReachableFactCopy().getTermDomain(term_index).contains(**ci, current_goal->getReachableFactLayer().getLayerNumber()))
						if (precondition_reachable_fact.getTermDomain(term_index).contains(**ci, precondition_layer_item->getReachableFactLayer().getLayerNumber()))
						{
							intersection.push_back(*ci);
						}
					}
					
					if (intersection.empty())
					{
						for (std::vector<const Object*>::const_iterator ci = current_variable_domains->begin(); ci != current_variable_domains->end(); ++ci)
						{
							const EquivalentObject& lhs_eo = equivalent_object_manager_->getEquivalentObject(**ci);
							for (std::vector<EquivalentObject*>::const_iterator ci = current_goal->getReachableFactCopy().getTermDomain(term_index).begin(current_goal->getReachableFactLayer().getLayerNumber()); ci != current_goal->getReachableFactCopy().getTermDomain(term_index).end(current_goal->getReachableFactLayer().getLayerNumber()); ++ci)
							{
								const EquivalentObject* rhs_eo = *ci;
								if (combined_eogs_.count(std::make_pair(&lhs_eo, rhs_eo)) == 0)
								{
									combined_eogs_.insert(std::make_pair(&lhs_eo, rhs_eo));
									for (unsigned int layer_number = 0; layer_number < current_fact_layer_->getLayerNumber(); layer_number++)
									{
										if (lhs_eo.getEquivalentObjectGroup().contains(rhs_eo->getObject(), layer_number))
										{
	//										std::cout << "Add " << layer_number << " to the total heuristic." << std::endl;
											heuristic += layer_number;
											break;
										}
									}
								}
							}
						}
					}
				}
			}
			
			// Add the precondition as a new goal to be achieved.
			open_list.push(std::make_pair(precondition_layer_item, object_bindings));
			continue;
		}
		
		// Pretend that the action can achieve the desired effect - what would the variable domains be?
		std::vector<HEURISTICS::VariableDomain*> variable_assignments_to_achieve_effect;
		
		const AchievingTransition* action_to_execute = NULL;
		std::pair<unsigned int, unsigned int> effect_indexes_achieving_effect;
		for (std::vector<const AchievingTransition*>::const_iterator ci = executed_actions.begin(); ci != executed_actions.end(); ci++)
		{
			const AchievingTransition* executed_action = *ci;
			if (executed_action->getPreconditions().size() != cheapest_achiever->getPreconditions().size())
			{
				continue;
			}
			
			bool same_action = true;
			for (unsigned int i = 0; i < executed_action->getPreconditions().size(); i++)
			{
				if (&executed_action->getPreconditionFactLayerItems()[i]->getActualReachableFact() != &cheapest_achiever->getPreconditionFactLayerItems()[i]->getActualReachableFact() ||
				    executed_action->getPreconditionFactLayerItems()[i]->getReachableFactLayer().getLayerNumber() != cheapest_achiever->getPreconditionFactLayerItems()[i]->getReachableFactLayer().getLayerNumber())
				{
					same_action = false;
					break;
				}
			}
			
			if (same_action)
			{
				effect_indexes_achieving_effect = executed_action->getEffectIndexAchieving(*current_goal, object_bindings);
				//if (executed_action->canAchieve(*current_goal, object_bindings))
				if (effect_indexes_achieving_effect.first != std::numeric_limits<unsigned int>::max())
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "The action: " << *executed_action << " could satisfy it as well..." << std::endl;
#endif
					if (instantiate_actions)
					{
						executed_action->updateVariablesToAchieve(*current_goal, object_bindings, effect_indexes_achieving_effect.first, effect_indexes_achieving_effect.second);
					}
					executed_action->getVariablesToAchieve(variable_assignments_to_achieve_effect, *current_goal, object_bindings, effect_indexes_achieving_effect.first, effect_indexes_achieving_effect.second);
					action_to_execute = executed_action;
					break;
				}
			}
		}

		if (action_to_execute == NULL)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
			std::cout << "Execute: " << *cheapest_achiever;
			std::cout << " with preconditions: " << std::endl;
			for (std::vector<const ReachableFactLayerItem*>::const_iterator ci = cheapest_achiever->getPreconditionFactLayerItems().begin(); ci != cheapest_achiever->getPreconditionFactLayerItems().end(); ci++)
			{
				std::cout << "* ";
				(*ci)->getReachableFactCopy().print(std::cout, (*ci)->getReachableFactLayer().getLayerNumber());
				std::cout << std::endl;
			}
			std::cout << "to achieve: ";
			current_goal->getReachableFactCopy().print(std::cout, current_goal->getReachableFactLayer().getLayerNumber());
			std::cout << "." << std::endl;
			
			std::cout << "Actual achiever: " << *cheapest_achiever->getAchiever() << std::endl;
#endif
			if (instantiate_actions)
			{
				// Update the variable domains to take into account the grounded variables.
				action_to_execute = new AchievingTransition(*cheapest_achiever, true);
				//std::cout << "Pre: " << *action_to_execute << std::endl;
				//action_to_execute->updateVariablesToAchieve(*current_goal, object_bindings);
				//std::cout << "Post: " << *action_to_execute << std::endl;
				
				// Only add the action if it actually achieves something!
				action_to_execute->updateVariablesToAchieve(*current_goal, object_bindings, action_to_execute->getEffectSetIndex(), action_to_execute->getEffectIndex());
				action_to_execute->getVariablesToAchieve(variable_assignments_to_achieve_effect, *current_goal, object_bindings, action_to_execute->getEffectSetIndex(), action_to_execute->getEffectIndex());
			}
			else
			{
				action_to_execute = cheapest_achiever;
			}
			
			//if (action_to_execute->canAchieve(*current_goal, object_bindings))
			{
				executed_actions.push_back(action_to_execute);
			}
			effect_indexes_achieving_effect = std::make_pair(action_to_execute->getEffectSetIndex(), action_to_execute->getEffectIndex());
			// But still count it towards the heuristic.
			++heuristic;
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
		std::cout << "Selected achiever: " << *action_to_execute << "." << std::endl;
		std::cout << "To achieve: " << *current_goal << std::endl;
		for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); i++)
		{
			printVariableDomain(std::cout, *object_bindings[i]);
		}
//		if (!action_to_execute->canAchieve(*current_goal, object_bindings))
//		{
//			std::cout << "Need to make some substitutions!" << std::endl;
//		}
#endif
/*
		// Check if we need to make any substitutions in order to achieve the effects.
		const HEURISTICS::TransitionFact* effect = action_to_execute->getAchiever()->getTransition().getEffects()[effect_indexes_achieving_effect.first]->getFacts()[effect_indexes_achieving_effect.second];
		for (unsigned int i = 0; i < current_goal->getReachableFactCopy().getTermDomains().size(); ++i)
		{
			effect->getVariableDomains();
			substitute(current_goal->getReachableFactCopy().getTermDomain(i), current_goal->getReachableFactLayer().getLayerNumber());
			action_to_execute->getAchiever();
		}
*/
		std::vector<std::pair<const EquivalentObject*, const EquivalentObject*> > substitutions_to_make;
		action_to_execute->getNeededSubstitutes(substitutions_to_make, *current_goal, object_bindings, *equivalent_object_manager_, effect_indexes_achieving_effect.first, effect_indexes_achieving_effect.second);
		for (std::vector<std::pair<const EquivalentObject*, const EquivalentObject*> >::const_iterator ci = substitutions_to_make.begin(); ci != substitutions_to_make.end(); ++ci)
		{
			const EquivalentObject* lhs_eo = (*ci).first;
			const EquivalentObject* rhs_eo = (*ci).second;
			
//			std::cout << "SUBSTITUTE " << lhs_eo->getObject() << " - " << rhs_eo->getObject() << std::endl;
			if (combined_eogs_.count(std::make_pair(lhs_eo, rhs_eo)) == 0)
			{
				combined_eogs_.insert(std::make_pair(lhs_eo, rhs_eo));
				combined_eogs_.insert(std::make_pair(rhs_eo, lhs_eo));
/*
				for (std::vector<EquivalentObject*>::const_iterator ci = lhs_eo->getEquivalentObjectGroup().begin(current_goal->getReachableFactLayer().getLayerNumber()); ci != lhs_eo->getEquivalentObjectGroup().end(current_goal->getReachableFactLayer().getLayerNumber()); ++ci)
				{
					const EquivalentObject* all_lhs_eo = *ci;
					for (std::vector<EquivalentObject*>::const_iterator ci = rhs_eo->getEquivalentObjectGroup().begin(current_goal->getReachableFactLayer().getLayerNumber()); ci != rhs_eo->getEquivalentObjectGroup().end(current_goal->getReachableFactLayer().getLayerNumber()); ++ci)
					{
						const EquivalentObject* all_rhs_eo = *ci;
						combined_eogs_.insert(std::make_pair(all_lhs_eo, all_rhs_eo));
						combined_eogs_.insert(std::make_pair(all_rhs_eo, all_lhs_eo));
					}
				}
*/
				for (unsigned int layer_number = 0; layer_number < current_fact_layer_->getLayerNumber(); layer_number++)
				{
					if (lhs_eo->getEquivalentObjectGroup().contains(rhs_eo->getObject(), layer_number))
					{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
						std::cout << "Add " << layer_number << " to the total heuristic." << std::endl;
#endif
						heuristic += layer_number;
						break;
					}
				}
			}
		}
		
//		std::cout << "New transition: " << *action_to_execute << std::endl;

		for (unsigned int precondition_index = 0; precondition_index < action_to_execute->getPreconditions().size(); ++precondition_index)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
			std::cout << "Process the " << precondition_index << "th precondition" << std::endl;
#endif
//			const HEURISTICS::TransitionFact* transition_fact = NULL;
			std::vector<unsigned int>* links_to_action_variables = NULL;

			// We need to find the precondition of the original action so we can update the variable domains of the action selected to achieve
			// the goal. The preconditions are added to the domain in reverse order (we traverse the trees from the leafs to the roots).
			unsigned int executed_action_precondition_index = 0;
			for (std::vector<const HEURISTICS::FactSet*>::const_iterator ci = action_to_execute->getAchiever()->getTransition().getPreconditions().begin(); ci != action_to_execute->getAchiever()->getTransition().getPreconditions().end(); ++ci)
			{
				const HEURISTICS::FactSet* precondition_fact_set = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "Check the fact set: " << *precondition_fact_set << "; (size=" << precondition_fact_set->getFacts().size() << ")" << std::endl;
#endif
				if (executed_action_precondition_index + precondition_fact_set->getFacts().size() <= precondition_index)
				{
					executed_action_precondition_index += precondition_fact_set->getFacts().size();
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "Skip! " << std::endl;
#endif
					continue;
				}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "Assign! " << *precondition_fact_set << "(" << precondition_fact_set->getFacts().size() << " - (" << precondition_index << " - " << executed_action_precondition_index << ") - " << 1 << " = " << (precondition_fact_set->getFacts().size() - (precondition_index - executed_action_precondition_index) - 1) << ")" << std::endl;
#endif
				unsigned int fact_index = precondition_fact_set->getFacts().size() - (precondition_index - executed_action_precondition_index) - 1;
//				transition_fact = precondition_fact_set->getFacts()[fact_index];
				
				const std::map<const HEURISTICS::FactSet*, std::vector<std::vector<unsigned int>* >* >& precondition_map = action_to_execute->getAchiever()->getTransition().getPreconditionMappings();
				const std::map<const HEURISTICS::FactSet*, std::vector<std::vector<unsigned int>* >* >::const_iterator precondition_mappings = precondition_map.find(precondition_fact_set);
				
				assert (precondition_mappings != precondition_map.end());
				links_to_action_variables = (*(*precondition_mappings).second)[fact_index];
				break;
			}
			
			if (instantiate_actions)
			{
				const ReachableFact* new_action_precondition = action_to_execute->getPreconditions()[precondition_index];
				const ReachableFactLayerItem* new_action_precondition_item = action_to_execute->getPreconditionFactLayerItems()[precondition_index];
				
				std::vector<const Object*>** precondition_object_bindings = new std::vector<const Object*>*[new_action_precondition->getPredicate().getArity()];
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "Precondition: " << std::endl;
				std::cout << *new_action_precondition << std::endl;
				std::cout << *new_action_precondition_item << std::endl;
	//			std::cout << *transition_fact << std::endl;
				for (unsigned int term_index = 0; term_index < new_action_precondition->getPredicate().getArity(); ++term_index)
				{
					std::cout << "Term " << term_index << " -> " << (*links_to_action_variables)[term_index] << "(" << *action_to_execute->getVariableAssignments()[(*links_to_action_variables)[term_index]] << ")" << std::endl;
				}
#endif
				
				// For each term of the precondition we either prune the variable domain of the action or --- if that is not possible due to
				// the mixing of objects --- we need to add the cost of substituting one object for another.
				for (unsigned int term_index = 0; term_index < new_action_precondition->getPredicate().getArity(); ++term_index)
				{
					EquivalentObjectGroup* fact_layer_precondition_eog = new_action_precondition_item->getReachableFactCopy().getTermDomains()[term_index];
					
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT

					for (unsigned int term_index2 = 0; term_index2 < new_action_precondition->getPredicate().getArity(); ++term_index2)
					{
						std::cout << "Term " << term_index2 << " -> " << (*links_to_action_variables)[term_index2] << "(" << *action_to_execute->getVariableAssignments()[(*links_to_action_variables)[term_index2]] << ")" << std::endl;
					}
#endif
					std::vector<const Object*>* precondition_term_domain = new std::vector<const Object*>();
					precondition_object_bindings[term_index] = precondition_term_domain;
					
					//const HEURISTICS::VariableDomain* action_to_execute_variable_domain = action_to_execute->getVariableAssignments()[(*links_to_action_variables)[term_index]];
					const HEURISTICS::VariableDomain* action_to_execute_variable_domain = variable_assignments_to_achieve_effect[(*links_to_action_variables)[term_index]];
					assert (variable_assignments_to_achieve_effect.size() == action_to_execute->getVariableAssignments().size());
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "Compare: " << *action_to_execute_variable_domain << " v.s. " << *fact_layer_precondition_eog << std::endl;
#endif
					
					// Check if the variable domain overlaps with the preconditions. If not we need to make substitutions.
					std::vector<const Object*> intersection;
					for (std::vector<const Object*>::const_iterator ci = action_to_execute_variable_domain->getVariableDomain().begin(); ci != action_to_execute_variable_domain->getVariableDomain().end(); ++ci)
					{
						const Object* object = *ci;
						if (fact_layer_precondition_eog->contains(*object, new_action_precondition_item->getReachableFactLayer().getLayerNumber()))
						{
							intersection.push_back(object);
						}
					}
					
					// Reduce the variable domains.
					if (intersection.size() > 0)
					{
						action_to_execute->getVariableAssignments()[(*links_to_action_variables)[term_index]]->set(intersection);
						precondition_term_domain->insert(precondition_term_domain->end(), intersection.begin(), intersection.end());
					}
					// Otherwise make a substitution.
					else
					{
						const HEURISTICS::VariableDomain* action_to_execute_variable_domain_achieving_the_effect = variable_assignments_to_achieve_effect[(*links_to_action_variables)[term_index]];
						
						// Construct a new goal with this precondition.
						
						
						// Precondition (must be substituted),
						if (allow_new_goals_added)
						{
							substitute(*fact_layer_precondition_eog, new_action_precondition_item->getReachableFactLayer().getLayerNumber(), action_to_execute_variable_domain->getVariableDomain());
						}
						else
						{
							heuristic += substitute(*fact_layer_precondition_eog, new_action_precondition_item->getReachableFactLayer().getLayerNumber(), action_to_execute_variable_domain->getVariableDomain());
							for (std::vector<const Object*>::const_iterator ci = action_to_execute_variable_domain->getVariableDomain().begin(); ci != action_to_execute_variable_domain->getVariableDomain().end(); ++ci)
							{
								const Object* object = *ci;
								EquivalentObject& equivalent_object = equivalent_object_manager_->getEquivalentObject(*object);
								bool subsitution_made = false;
								//for (std::vector<EquivalentObject*>::const_iterator ci = fact_layer_precondition_eog->begin(new_action_precondition_item->getReachableFactLayer().getLayerNumber()) getEquivalentObjects().begin(); ci != fact_layer_precondition_eog->getEquivalentObjects().end(); ++ci)
								for (std::vector<EquivalentObject*>::const_iterator ci = fact_layer_precondition_eog->begin(new_action_precondition_item->getReachableFactLayer().getLayerNumber()); ci != fact_layer_precondition_eog->end(new_action_precondition_item->getReachableFactLayer().getLayerNumber()); ++ci)
								{
									if (combined_eogs_.count(std::make_pair(&equivalent_object, *ci)) == 1)
									{
										subsitution_made = true;
										break;
									}
								}
								
								if (!subsitution_made)
								{
									bool made_substitution = false;
									//for (std::vector<EquivalentObject*>::const_iterator ci = fact_layer_precondition_eog->getEquivalentObjects().begin(); ci != fact_layer_precondition_eog->getEquivalentObjects().end(); ++ci)
									for (std::vector<EquivalentObject*>::const_iterator ci = fact_layer_precondition_eog->begin(new_action_precondition_item->getReachableFactLayer().getLayerNumber()); ci != fact_layer_precondition_eog->end(new_action_precondition_item->getReachableFactLayer().getLayerNumber()); ++ci)
									{
										if (combined_eogs_.count(std::make_pair(&equivalent_object, *ci)) == 0)
										{
											combined_eogs_.insert(std::make_pair(&equivalent_object, *ci));
											combined_eogs_.insert(std::make_pair(*ci, &equivalent_object));
											
											for (unsigned int layer_number = 0; layer_number < current_fact_layer_->getLayerNumber(); layer_number++)
											{
												if (equivalent_object.getEquivalentObjectGroup().contains((*ci)->getObject(), layer_number))
												{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
													std::cout << "Add " << layer_number << " to the total heuristic." << std::endl;
													std::cerr << "Cannot happen!" << std::endl;
#endif
													heuristic += layer_number;
													made_substitution = true;
													break;
												}
											}
										}
										if (made_substitution)
										{
											break;
										}
									}
								}
							}
						}

						if (allow_new_goals_added)
						{
							precondition_term_domain->insert(precondition_term_domain->end(), action_to_execute_variable_domain_achieving_the_effect->getVariableDomain().begin(), action_to_execute_variable_domain_achieving_the_effect->getVariableDomain().end());
						}
						else
						{
						for (std::vector<EquivalentObject*>::const_iterator ci = fact_layer_precondition_eog->getEquivalentObjects().begin(); ci != fact_layer_precondition_eog->getEquivalentObjects().end(); ++ci)
	//					for (std::vector<EquivalentObject*>::const_iterator ci = fact_layer_precondition_eog->begin(new_action_precondition_item->getReachableFactLayer().getLayerNumber()); ci != fact_layer_precondition_eog->end(new_action_precondition_item->getReachableFactLayer().getLayerNumber()); ++ci)
							{
								precondition_term_domain->push_back(&(*ci)->getObject());
							}
						}
					}
				}
				
				// Add the precondition as a new goal.
				open_list.push(std::make_pair(new_action_precondition_item, precondition_object_bindings));
			}
			else
			{
				const ReachableFact* precondition = action_to_execute->getPreconditions()[precondition_index];
				const ReachableFactLayerItem* precondition_item = action_to_execute->getPreconditionFactLayerItems()[precondition_index];
				std::vector<const Object*>** precondition_object_bindings = new std::vector<const Object*>*[action_to_execute->getPreconditions()[precondition_index]->getPredicate().getArity()];
				
				for (unsigned int term_index = 0; term_index < precondition->getPredicate().getArity(); ++term_index)
				{
					EquivalentObjectGroup* fact_layer_precondition_eog = precondition_item->getReachableFactCopy().getTermDomains()[term_index];

					std::vector<const Object*>* precondition_term_domain = new std::vector<const Object*>();
					precondition_object_bindings[term_index] = precondition_term_domain;
					
					for (std::vector<EquivalentObject*>::const_iterator ci = fact_layer_precondition_eog->begin(precondition_item->getReachableFactLayer().getLayerNumber()); ci != fact_layer_precondition_eog->end(precondition_item->getReachableFactLayer().getLayerNumber()); ++ci)
					{
						precondition_term_domain->push_back(&(*ci)->getObject());
					}
				}
				open_list.push(std::make_pair(action_to_execute->getPreconditionFactLayerItems()[precondition_index], precondition_object_bindings));
			}
		}
		
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_assignments_to_achieve_effect.begin(); ci != variable_assignments_to_achieve_effect.end(); ++ci)
		{
			delete *ci;
		}
		for (unsigned int i = 0; i < current_goal->getActualReachableFact().getPredicate().getArity(); ++i)
		{
			delete object_bindings[i];
		}
		delete[] object_bindings;
	}

	helpful_actions_.clear();
	if (create_helpful_actions)
	{
		const ReachableFactLayer* first_fact_layer = current_fact_layer_;
		while (first_fact_layer->getLayerNumber() > 1)
		{
			first_fact_layer = first_fact_layer->getPreviousLayer();
		}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
		std::cout << "(" << executed_actions.size() << ") Find helpful actions in: " << std::endl;
		const ReachableFactLayer* fact_layer = current_fact_layer_;
		while (fact_layer != NULL)
		{
			std::cout << *fact_layer << std::endl;
			fact_layer = fact_layer->getPreviousLayer();
		}
#endif
		//std::vector<const ReachableFactLayerItem*> relevant_preconditions;
		std::vector<std::pair<const ReachableFactLayerItem*, const std::vector<const HEURISTICS::VariableDomain*>* > > relevant_preconditions;
		for (std::vector<const AchievingTransition*>::const_iterator ci = executed_actions.begin(); ci != executed_actions.end(); ci++)
		{
			const AchievingTransition* action = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
			std::cout << "Executed action: " << **ci << std::endl;
#endif
			
			const std::vector<const ReachableFactLayerItem*>& preconditions = action->getPreconditionFactLayerItems();
			for (std::vector<const ReachableFactLayerItem*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
			{
				const ReachableFactLayerItem* precondition = *ci;
				
				if (precondition->getReachableFactLayer().getLayerNumber() == 1)
				{
					
					std::vector<const HEURISTICS::VariableDomain*>* variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
					for (unsigned int term_index = 0; term_index < precondition->getReachableFactCopy().getTermDomains().size(); ++term_index)
					{
						EquivalentObjectGroup& eog = precondition->getReachableFactCopy().getTermDomain(term_index);
						HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
						
						for (std::vector<EquivalentObject*>::const_iterator ci = eog.begin(precondition->getReachableFactLayer().getLayerNumber()); ci != eog.end(precondition->getReachableFactLayer().getLayerNumber()); ++ci)
						{
							vd->addObject((*ci)->getObject());
						}
						variable_domains->push_back(vd);
					}
					
					//relevant_preconditions.push_back(precondition);
					relevant_preconditions.push_back(std::make_pair(precondition, variable_domains));
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "Relevant precondition: " << *precondition << std::endl;
#endif
				}
			}
		}
		
		// Find all preconditions in the first fact layer which correspond to one of the goals.
		for (std::vector<ReachableFactLayerItem*>::const_iterator ci = first_fact_layer->getReachableFacts().begin(); ci != first_fact_layer->getReachableFacts().end(); ++ci)
		{
			const ReachableFactLayerItem* fact_item = *ci;
			const ReachableFact& fact = (*ci)->getReachableFactCopy();
			for (std::vector<const GroundedAtom*>::const_iterator ci = bounded_goal_facts.begin(); ci != bounded_goal_facts.end(); ++ci)
			{
				const GroundedAtom* goal = *ci;
				if (goal->getAtom().getArity() != fact.getPredicate().getArity() ||
					goal->getAtom().getPredicate().getName() != fact.getPredicate().getName())
				{
					continue;
				}
				
				bool fact_matches_goal = true;
				for (unsigned int i = 0; i < fact.getPredicate().getArity(); ++i)
				{
					EquivalentObjectGroup& fact_variable_domain = fact.getTermDomain(i);
					const Object* goal_object = static_cast<const Object*>(goal->getAtom().getTerms()[i]);
					
					if (!fact_variable_domain.contains(*goal_object, fact_item->getReachableFactLayer().getLayerNumber()))
					{
						fact_matches_goal = false;
						break;
					}
				}
				if (fact_matches_goal)
				{
					std::vector<const HEURISTICS::VariableDomain*>* variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
					for (unsigned int term_index = 0; term_index < goal->getAtom().getArity(); ++term_index)
					{
						HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
						vd->addObject(goal->getObject(term_index));
						variable_domains->push_back(vd);
					}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "!Relevant precondition for goal: " << *goal << " = " << *fact_item << std::endl;
#endif
					relevant_preconditions.push_back(std::make_pair(fact_item, variable_domains));
//					break;
				}
			}
			
			// Do the same for goals which have been added due to having to substitute objects.
			for (std::vector<std::pair<const Predicate*, std::vector<const Object*>**> >::const_iterator ci = newly_added_goals.begin(); ci != newly_added_goals.end(); ++ci)
			{
				const Predicate* goal_predicate = (*ci).first;
				std::vector<const Object*>** object_bindings = (*ci).second;
				
				if (goal_predicate->getArity() != fact.getPredicate().getArity() ||
				    goal_predicate->getName() != fact.getPredicate().getName())
				{
					continue;
				}
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "Check: " << goal_predicate->getName();
				for (unsigned int i = 0; i < fact.getPredicate().getArity(); ++i)
				{
					const std::vector<const Object*>* goal_variable_domain = object_bindings[i];
					std::cout << "{";
					for (std::vector<const Object*>::const_iterator ci = goal_variable_domain->begin(); ci != goal_variable_domain->end(); ++ci)
					{
						std::cout << **ci << " ";
					}
					std::cout << "}, ";
				}
				std::cout << " v.s. " << std::endl;
				std::cout << *fact_item << " ";
				for (unsigned int i = 0; i < fact.getPredicate().getArity(); ++i)
				{
					EquivalentObjectGroup& fact_variable_domain = fact.getTermDomain(i);
					
					fact_variable_domain.printObjects(std::cout, fact_item->getReachableFactLayer().getLayerNumber());
					std::cout << ", ";
				}
				std::cout << std::endl;
#endif
				
				bool fact_matches_goal = true;
				for (unsigned int i = 0; i < fact.getPredicate().getArity(); ++i)
				{
					EquivalentObjectGroup& fact_variable_domain = fact.getTermDomain(i);
					const std::vector<const Object*>* goal_variable_domain = object_bindings[i];
					
					bool term_overlaps = false;
					for (std::vector<const Object*>::const_iterator ci = goal_variable_domain->begin(); ci != goal_variable_domain->end(); ++ci)
					{
						const Object* object = *ci;
						if (fact_variable_domain.contains(*object, fact_item->getReachableFactLayer().getLayerNumber()))
						{
							term_overlaps = true;
							break;
						}
					}
					
					if (!term_overlaps)
					{
						fact_matches_goal = false;
						break;
					}
				}
				
				if (fact_matches_goal)
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
					std::cout << "Relevant precondition for goal: " << goal_predicate->getName();
					for (unsigned int i = 0; i < fact.getPredicate().getArity(); ++i)
					{
						const std::vector<const Object*>* goal_variable_domain = object_bindings[i];
						std::cout << "{";
						for (std::vector<const Object*>::const_iterator ci = goal_variable_domain->begin(); ci != goal_variable_domain->end(); ++ci)
						{
							std::cout << **ci << " ";
						}
						std::cout << "}, ";
					}
					std::cout << " = " << *fact_item << std::endl;
#endif
					std::vector<const HEURISTICS::VariableDomain*>* variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
					for (unsigned int term_index = 0; term_index < goal_predicate->getArity(); ++term_index)
					{
						HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain(*object_bindings[term_index]);
						variable_domains->push_back(vd);
					}

					relevant_preconditions.push_back(std::make_pair(fact_item, variable_domains));
					break;
				}
			}
		}

		for (std::vector<std::pair<const ReachableFactLayerItem*, const std::vector<const HEURISTICS::VariableDomain*>* > >::const_iterator ci = relevant_preconditions.begin(); ci != relevant_preconditions.end(); ++ci)
		{
			const ReachableFactLayerItem* precondition = (*ci).first;
			const std::vector<const HEURISTICS::VariableDomain*>* variable_domains = (*ci).second;
/*
			std::cout << "Process the precondition: " << precondition->getReachableFactCopy() << " with domains: ";
			for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = variable_domains->begin(); ci != variable_domains->end(); ++ci)
			{
				std::cout << **ci << ", ";
			}
			std::cout << "." << std::endl;
*/
			for (std::vector<const AchievingTransition*>::const_iterator ci = precondition->getAchievers().begin(); ci != precondition->getAchievers().end(); ++ci)
			{
				const AchievingTransition* achieving_transition = *ci;
					
				// Ignore NOOPs.
				if (achieving_transition->getAchiever() == NULL)
				{
					continue;
				}
				
				// Check if the variable domains match up.
				bool terms_match_up = true;
				
				achieving_transition->getAchiever()->getTransition().getEffectMappings();
				
				std::pair<unsigned int, unsigned int> effect_mappings = achieving_transition->getEffectIndexAchieving(*precondition, *variable_domains);
				if (effect_mappings.first == std::numeric_limits<unsigned int>::max())
				{
					terms_match_up = false;
					break;
				}
				
				std::vector<HEURISTICS::VariableDomain*> new_variable_domains;
				for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = achieving_transition->getVariableAssignments().begin(); ci != achieving_transition->getVariableAssignments().end(); ++ci)
				{
					new_variable_domains.push_back(new HEURISTICS::VariableDomain(**ci));
				}
				
				const HEURISTICS::FactSet* fact_set = achieving_transition->getAchiever()->getTransition().getEffects()[effect_mappings.first];
				
				const std::vector<std::vector<unsigned int>* >* effect_parameter_to_action_variables = (*achieving_transition->getAchiever()->getTransition().getEffectMappings().find(fact_set)).second;
				std::vector<unsigned int>* effect_term_to_action_variable_mappings = (*effect_parameter_to_action_variables)[effect_mappings.second];
				
				for (unsigned int term_index = 0; term_index < precondition->getReachableFactCopy().getPredicate().getArity(); ++term_index)
				{
					//const HEURISTICS::VariableDomain* action_variable_domain = achieving_transition->getVariableAssignments()[term_index];
					const HEURISTICS::VariableDomain* action_variable_domain = achieving_transition->getVariableAssignments()[(*effect_term_to_action_variable_mappings)[term_index]];
					const HEURISTICS::VariableDomain* goal_variable_domain = (*variable_domains)[term_index];
					
					HEURISTICS::VariableDomain intersection;
					action_variable_domain->getIntersection(intersection, *goal_variable_domain);
					
					if (intersection.size() == 0)
					{
						terms_match_up = false;
						break;
					}
					new_variable_domains[(*effect_term_to_action_variable_mappings)[term_index]]->set(intersection.getVariableDomain());
				}
				
				if (!terms_match_up)
				{
					for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = new_variable_domains.begin(); ci != new_variable_domains.end(); ++ci)
					{
						delete *ci;
					}
					continue;
				}
/*
				std::cout << "Action: " << achieving_transition->getAchiever()->getTransition().getAction().getPredicate() << " with domains: ";
				for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = new_variable_domains.begin(); ci != new_variable_domains.end(); ++ci)
				{
					std::cout << **ci << ", ";
				}
				std::cout << "." << std::endl;
*/
				AchievingTransition* helpful_action = new AchievingTransition(*achieving_transition, new_variable_domains, false);
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_COMMENT
				std::cout << "Helpful action: " << *helpful_action << std::endl;
#endif

				// Ground the transition such that the action variables match it.
				//helpful_actions_.push_back(new AchievingTransition(*achieving_transition, false));
				helpful_actions_.push_back(helpful_action);
			}
		}
		
		for (std::vector<std::pair<const ReachableFactLayerItem*, const std::vector<const HEURISTICS::VariableDomain*>* > >::const_iterator ci = relevant_preconditions.begin(); ci != relevant_preconditions.end(); ++ci)
		{
			const std::vector<const HEURISTICS::VariableDomain*>* variable_domain = (*ci).second;
			for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ++ci)
			{
				delete *ci;
			}
			delete variable_domain;
		}
	}
	
	for (std::vector<std::pair<const Predicate*, std::vector<const Object*>**> >::const_iterator ci = newly_added_goals.begin(); ci != newly_added_goals.end(); ++ci)
	{
		std::vector<const Object*>** variable_domains = (*ci).second;
		for (unsigned int term_index = 0; term_index < (*ci).first->getArity(); ++term_index)
		{
			delete variable_domains[term_index];
		}
		delete[] variable_domains;
	}
	
/*
	if (heuristic != 0 && helpful_actions_.empty())
	{
		std::cerr << "Should at least include one helpful action!" << std::endl;
		assert (false);
	}
*/
/*
	// Test, must include driver1!
	bool includes_driver1 = false;
	for (std::vector<const AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		const AchievingTransition* achieving_transition = *ci;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = achieving_transition->getVariableAssignments().begin(); ci != achieving_transition->getVariableAssignments().end(); ++ci)
		{
			HEURISTICS::VariableDomain* variable_domain = *ci;
			for (std::vector<const Object*>::const_iterator ci = variable_domain->getVariableDomain().begin(); ci != variable_domain->getVariableDomain().end(); ++ci)
			{
				const Object* object = *ci;
				if (object->getName() == "driver1")
				{
					includes_driver1 = true;
					break;
				}
			}
		}
	}
	
	if (heuristic != 0 && !includes_driver1)
	{
		std::cout << "Wrong helpful actions!" << std::endl;
		assert (false);
	}
*/
/*
	if (heuristic == 2)
	{
//#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Given " << std::endl;
	
	const ReachableFactLayer* layer = current_fact_layer_;
	while (layer != NULL)
	{
		std::cout << *layer << std::endl;
		layer = layer->getPreviousLayer();
	}
	
	for (std::vector<const AchievingTransition*>::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		std::cout << "Helpful action: " << **ci << "." << std::endl;
	}
	
	for (std::vector<const AchievingTransition*>::const_iterator ci = executed_actions.begin(); ci != executed_actions.end(); ci++)
	{
		std::cout << "Executed action: " << **ci << std::endl;
	}
	exit(0);
	}
*/
//#endif
	return heuristic;
}

void DTGReachability::mapInitialFactsToReachableSets(const std::vector<ReachableFact*>& initial_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "MAP INITIAL FACTS!" << std::endl;
#endif
	
	for (std::vector<ReachableFact*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		ReachableFact* initial_fact = *ci;
		if (initial_fact->isMarkedForRemoval()) continue;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the initial fact: " << *initial_fact << " - marked? " << initial_fact->isMarkedForRemoval() << ". ID: " << initial_fact->getPredicate().getId() << std::endl;
#endif
		
		std::vector<std::pair<ReachableSet*, unsigned int> >* reachable_sets = (*predicate_id_to_reachable_sets_mapping_)[initial_fact->getPredicate().getId()];
		
		assert (reachable_sets != NULL);
		
		for (std::vector<std::pair<ReachableSet*, unsigned int> >::const_iterator ci = reachable_sets->begin(); ci != reachable_sets->end(); ci++)
		{
			ReachableSet* reachable_set = (*ci).first;
			unsigned int fact_index = (*ci).second;
			if (reachable_set->processNewReachableFact(*initial_fact, fact_index))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Add it to: " << *reachable_set << " - index: " << fact_index << std::endl << "ID=" << reachable_set << std::endl;
#endif
			}
			else
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Could not add it to: " << *reachable_set << " - index: " << fact_index << std::endl;
#endif
			}
		}
	}
	
	// After mapping all the initial facts to the reachable sets we cache the number of reachable facts. This way we 
	// make sure the fact layers are constructed based only on the facts from the previous fact layer and not from facts 
	// which were created during that same iteration.
	for (std::map<const HEURISTICS::FactSet*, ReachableSet*>::const_iterator ci = fact_set_to_reachable_set_.begin(); ci != fact_set_to_reachable_set_.end(); ++ci)
	{
		ReachableSet* reachable_set = (*ci).second;
		reachable_set->resetCachedReachableTreesSize();
	}
}


};
	
};
