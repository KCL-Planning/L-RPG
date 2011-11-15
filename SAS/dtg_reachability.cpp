#include <cstring>
#include <iterator>
#include <sys/time.h>

#include "dtg_reachability.h"
#include "equivalent_object_group.h"
#include "dtg_manager.h"
#include "dtg_graph.h"
#include "dtg_node.h"
#include "property_space.h"
#include "transition.h"
#include "type_manager.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

#define MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
#define MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
#define DTG_REACHABILITY_KEEP_TIME
namespace MyPOP {

namespace SAS_Plus {

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
	
	for (std::vector<const Property*>::const_iterator ci = bounded_atom.getProperties().begin(); ci != bounded_atom.getProperties().end(); ci++)
	{
		const Property* property = *ci;
		if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
		
		// Except when it has been grounded!
		if (term_domain_mapping_[property->getIndex()]->isGrounded()) continue;
		
		mask_ |= 0x1 << property->getIndex();
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
	for (std::vector<const Property*>::const_iterator ci = bounded_atom.getProperties().begin(); ci != bounded_atom.getProperties().end(); ci++)
	{
		const Property* property = *ci;
		if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
		
		// Except when it has been grounded!
		if (term_domain_mapping_[property->getIndex()]->isGrounded()) continue;
		
		mask_ |= 0x1 << property->getIndex();
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < bounded_atom.getAtom().getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
#endif
}

ReachableFact::ReachableFact(const Atom& atom, EquivalentObjectGroup** term_domain_mapping)
	: atom_(&atom), term_domain_mapping_(term_domain_mapping), replaced_by_(NULL), mask_(0)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	for (unsigned int i = 0; i < atom.getArity(); i++)
	{
		assert (term_domain_mapping_[i] != NULL);
	}
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
		
		if (!term_domain_mapping_[i]->isIdenticalTo(*other.term_domain_mapping_[i]))
		{
			return false;
		}
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
	assert (replaced_by_ == NULL);
	replaced_by_ = &replacement;
}

//bool isMarkedForRemoval() const { return removed_flag_; }
bool ReachableFact::isMarkedForRemoval() const { return replaced_by_ != NULL; }

ReachableFact& ReachableFact::getReplacement()
{
	if (replaced_by_ == NULL) return *this;
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
		//os << "- " << *reachable_fact.term_domain_mapping_[i]-> << "(" << reachable_fact.index_ << std::endl;
	}
	os << ")" << "%" << &reachable_fact << "%";
	
//	os << "%";
//	for (std::vector<const Property*>::const_iterator ci = reachable_fact.bounded_atom_->getProperties().begin(); ci != reachable_fact.bounded_atom_->getProperties().end(); ci++)
//	{
//		os << **ci << ", ";
//	}
	
//	os << "%" << std::endl;
	return os;
}

/**
 * ResolvedBoundedAtom.
 */
ResolvedBoundedAtom::ResolvedBoundedAtom(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
	: id_(id), atom_(&atom)
{
	init(bindings, eog_manager);
}

ResolvedBoundedAtom::ResolvedBoundedAtom(const BoundedAtom& bounded_atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
	 : id_(bounded_atom.getId()), atom_(&bounded_atom.getAtom())
{
	init(bindings, eog_manager);
}

void ResolvedBoundedAtom::init(const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager)
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
			
			if (type->isSubtypeOf(*best_type))
			{
				best_type = type;
			}
		}
		
		best_types->push_back(best_type);
		new_variables->push_back(new Variable(*best_type, atom_->getTerms()[i]->getName()));
	}
	
	Predicate* new_predicate = new Predicate(atom_->getPredicate().getName(), *best_types, atom_->getPredicate().isStatic());
	corrected_atom_ = new Atom(*new_predicate, *new_variables, atom_->isNegative());
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Created a resolved atom: " << *this << std::endl;
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
ResolvedEffect::ResolvedEffect(StepID id, const Atom& atom, const Bindings& bindings, const EquivalentObjectGroupManager& eog_manager, bool free_variables[])
	: ResolvedBoundedAtom(id, atom, bindings, eog_manager), eog_manager_(&eog_manager)
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
			std::cout << "- " << eog << std::endl;
#endif
		}
		free_variable_domains_.push_back(possible_eogs);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Create a new effect: " << *this << "." << std::endl;
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

//		std::vector<EquivalentObjectGroup*> updated_variable_domains;

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
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		for (std::vector<EquivalentObjectGroup*>::const_iterator ci = free_variable_domain->begin(); ci != free_variable_domain->end(); ci++)
		{
			EquivalentObjectGroup* eog = *ci;

			for (std::vector<EquivalentObjectGroup*>::const_iterator ci2 = ci + 1; ci2 != free_variable_domain->end(); ci2++)
			{
				EquivalentObjectGroup* eog2 = *ci2;
				
				assert (!eog->isIdenticalTo(*eog2));
			}
		}
	}
#endif
	
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
ReachableSet::ReachableSet(const MyPOP::SAS_Plus::EquivalentObjectGroupManager& eog_manager)
	: eog_manager_(&eog_manager)
{

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
			if (!resolved_atom->getCorrectedAtom().getPredicate().canSubstitute(initial_fact->getAtom().getPredicate()))
			{
				continue;
			}
			
			processNewReachableFact(*initial_fact, index);
		}
		
		++index;
	}
}

void ReachableSet::addBoundedAtom(const MyPOP::SAS_Plus::BoundedAtom& bounded_atom, const Bindings& bindings)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[ReachableSet::addBoundedAtom] Add :";
	bounded_atom.print(std::cout, bindings);
	std::cout << " to :";
	print(std::cout);
	std::cout << "." << std::endl;
#endif

	ResolvedBoundedAtom* new_resolved_bounded_atom = new ResolvedBoundedAtom(bounded_atom, bindings, *eog_manager_);
	facts_set_.push_back(new_resolved_bounded_atom);
	reachable_set_.push_back(new std::vector<ReachableFact*>());
	
	// Generate the constraints sets.
	std::vector<std::pair<unsigned int, unsigned int> >** new_constraints_sets = new std::vector<std::pair<unsigned int, unsigned int> >*[bounded_atom.getAtom().getArity()];
	for (unsigned int i = 0; i  < bounded_atom.getAtom().getArity(); i++)
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

void ReachableSet::equivalencesUpdated()
{
	// Sets which are not fully constructed yet.
	for (std::vector<std::vector<ReachableFact*>*>::reverse_iterator ri = wip_sets_.rbegin(); ri != wip_sets_.rend(); ri++)
	{
		std::vector<ReachableFact*>* reachable_set = *ri;
		
		bool remove = false;
		for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end(); ci++)
		{
			if ((*ci)->isMarkedForRemoval())
			{
				remove = true;
				break;
			}
		}
		
		if (remove) wip_sets_.erase(ri.base() - 1);
	}
	
	// Remove all sets which contains an out of date fact and add the fact which contains an up to date version.
	for (std::vector<std::vector<ReachableFact*>*>::const_iterator ci = reachable_set_.begin(); ci != reachable_set_.end(); ci++)
	{
		std::vector<ReachableFact*>* reachable_set = *ci;
		for (std::vector<ReachableFact*>::reverse_iterator ri = reachable_set->rbegin(); ri != reachable_set->rend(); ri++)
		{
			ReachableFact* reachable_fact = *ri;
			if (reachable_fact->isMarkedForRemoval())
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
				// Make sure there is a fact in the set remaining which is the updated version of that.
				reachable_fact->updateTermsToRoot();
				
				bool found_identical = false;
				for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end() - 1; ci++)
				{
					if ((*ci)->isIdenticalTo(*reachable_fact))
					{
						found_identical = true;
						break;
					}
				}
				
				if (!found_identical)
				{
					std::cout << "Removing " << *reachable_fact << " from the following list: " << std::endl;
					
					for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end() - 1; ci++)
					{
						std::cout << "* " << **ci << "." << std::endl;
					}
					
					std::cout << "But no super node found!" << std::endl;
					assert (false);
				}
#endif
				reachable_set->erase(ri.base() - 1);
			}
		}
	}
	
	// All sets which are completely unitable are stored in the fully_reachable_sets. We do not temper with the actual size of the vector
	// because ResolvedTransitions keep track of which sets facts they have already processed and chaning the size of the vector will mess
	// up this analysis. So we do lazy deletion.
	// TODO: This breaks... ?
	std::vector<std::vector<ReachableFact*>*> updated_reachable_sets;
	for (std::vector<std::vector<ReachableFact*>*>::iterator full_reachable_i = fully_reachable_sets_.begin(); full_reachable_i != fully_reachable_sets_.end(); full_reachable_i++)
	{
		std::vector<ReachableFact*>* reachable_set = *full_reachable_i;
		if (reachable_set == NULL) continue;
		
		bool mark_for_removal = false;
		for (std::vector<ReachableFact*>::iterator i = reachable_set->begin(); i != reachable_set->end(); i++)
		{
			if ((*i)->isMarkedForRemoval())
			{
				mark_for_removal = true;
				*i = &(*i)->getReplacement();
			}
		}
		
		if (mark_for_removal)
		{
			// Check if the updated set is identical to an already updated set.
			bool identical_set_found = false;
			for (std::vector<std::vector<ReachableFact*>*>::const_iterator ci = updated_reachable_sets.begin(); ci != updated_reachable_sets.end(); ci++)
			{
				std::vector<ReachableFact*>* already_updated_set = *ci;
				
				bool is_identical = true;
				for (unsigned int i = 0; i < already_updated_set->size(); i++)
				{
					if (!(*already_updated_set)[i]->isIdenticalTo(*(*reachable_set)[i]))
					{
						is_identical = false;
						break;
					}
				}
				
				if (is_identical)
				{
					identical_set_found = true;
					break;
				}
			}
			
			if (identical_set_found)
			{
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
				// Make sure there is a fact in the set remaining which is the updated version of that.
				bool found_identical = false;
				for (std::vector<std::vector<ReachableFact*>*>::const_iterator ci = fully_reachable_sets_.begin(); ci != fully_reachable_sets_.end(); ci++)
				{
					std::vector<ReachableFact*>* other_reachable_set = *ci;
					if (other_reachable_set == NULL) continue;
					if (other_reachable_set == reachable_set) continue;

					
					bool is_identical = true;
					unsigned int index = 0;
					for (std::vector<ReachableFact*>::const_iterator ci = other_reachable_set->begin(); ci != other_reachable_set->end(); ci++)
					{
						if (!(*ci)->isIdenticalTo(*(*reachable_set)[index]))
						{
							is_identical = false;
							break;
						}
						
						++index;
					}
					
					if (is_identical)
					{
						found_identical = true;
						break;
					}
				}
				
				if (!found_identical)
				{
					std::cout << "Removing ";
					for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end(); ci++)
					{
						std::cout << "* " << **ci << std::endl;
					}
					std::cout << " from the following list of sets: " << std::endl;
					
					for (std::vector<std::vector<ReachableFact*>*>::const_iterator ci = fully_reachable_sets_.begin(); ci != fully_reachable_sets_.end(); ci++)
					{
						std::cout << "{" << std::endl;
						std::vector<ReachableFact*>* other_reachable_set = *ci;
						if (other_reachable_set == NULL) continue;
						for (std::vector<ReachableFact*>::const_iterator ci = other_reachable_set->begin(); ci != other_reachable_set->end(); ci++)
						{
	//						(*ci)->updateTermsToRoot();
							std::cout << "* " << **ci << std::endl;
						}
						std::cout << "}" << std::endl;
					}

					
					std::cout << "But no super node found!" << std::endl;
					
					std::cout << "Reachable sets: " << std::endl;
					for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end() - 1; ci++)
					{
						std::cout << "* " << **ci << "." << std::endl;
					}
					
					print(std::cout);
					
	//				std::cout << "All equivalent object groups: " << std::endl;
	//				eog_manager_->print(std::cout);
					
					assert (false);
				}
#endif
			
				*full_reachable_i = NULL;
			}
			else
			{
				updated_reachable_sets.push_back(reachable_set);
			}
		}
	}
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
#endif

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (reachable_fact.getAtom().getPredicate().canSubstitute(facts_set_[reachable_set.size()]->getCorrectedAtom().getPredicate()));
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
			if (reachable_fact.getTermDomain(i) != reachable_set[fact_index]->getTermDomain(variable_index))
			{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "The " << i << "th term of : " << reachable_fact << " should match up with the " << variable_index << "th term of " << *reachable_set[fact_index] << ", but it doesn't!" << std::endl;
#endif
				return false;
			}
		}
	}
	
/*	// Check if the grounded constraints are satisfied too.
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
			std::cout << "The " << i << "th term of : " << reachable_fact << " should match up with the " << i << "th term of " << *facts_set_[index] << ", but it doesn't!" << std::endl;
#endif
			return false;
		}
	}*/
	
	return true;
}

bool ReachableSet::processNewReachableFact(ReachableFact& reachable_fact, unsigned int index)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[ReachableSet::processNewReachableFact] Add " << reachable_fact << "[index=" << index << "]" << std::endl;
	std::cout << "[ReachableSet::processNewReachableFact] To: ";
	print(std::cout);
	std::cout << std::endl;
#endif
	// Make sure the fact to be added can be unified with the fact at the given index.
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (facts_set_.size() > index);
	assert (facts_set_[index]->getCorrectedAtom().getPredicate().canSubstitute(reachable_fact.getAtom().getPredicate()));
#endif

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
			std::cout << "The " << i << "th term of : " << reachable_fact << " should match up with the " << i << "th term of " << *facts_set_[index] << ", but it doesn't!" << std::endl;
#endif
			return false;
		}
	}

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	// Add the fact to the reachable set, but make sure it isn't already part of it!
	std::vector<ReachableFact*>* reachable_set = reachable_set_[index];
	
	for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end(); ci++)
	{
		if (reachable_fact.isIdenticalTo(**ci))
		{
			std::cout << "[ReachableSet::processNewReachableFact] Already part of this set, move on!" << std::endl;
			assert (false);
		}
	}
#endif

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//	std::cout << "[ReachableSet::processNewReachableFact] " << reachable_fact << "[index=" << index << "] for " << std::endl;
//	print(std::cout);
//	std::cout << std::endl;
#endif

	reachable_set_[index]->push_back(&reachable_fact);
	
	// If the index is 0, it means it is the start of a new 'root'.
	if (index == 0)
	{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//		std::cout << "[ReachableSet::processNewReachableFact] Start a new root node!" << std::endl;
#endif
		std::vector<ReachableFact*>* new_reachable_set = new std::vector<ReachableFact*>();
		
		if (!canSatisfyConstraints(reachable_fact, *new_reachable_set)) return false;
		
		new_reachable_set->push_back(&reachable_fact);
		wip_sets_.push_back(new_reachable_set);
		generateNewReachableSets(*new_reachable_set);
	}
	// Otherwise, we need to search for all sets the new node can be a part of and process these.
	else
	{
//		std::vector<std::vector<ReachableFact*>* > wip_sets_copy(wip_sets_);
//		for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = wip_sets_copy.begin(); ci != wip_sets_copy.end(); ci++)
		for (unsigned int i = 0; i < wip_sets_.size(); i++)
		{
			//std::vector<ReachableFact*>* reachable_set = *ci;
			std::vector<ReachableFact*>* reachable_set = wip_sets_[i];
			if (reachable_set->size() != index) continue;
			
			// Check if the newly reachable fact satisfies all the constraints of the previous assignments.
			if (!canSatisfyConstraints(reachable_fact, *reachable_set)) continue;
			
			// If the constraints are satisfied, add the facts and search for new facts to add.
			std::vector<ReachableFact*>* new_reachable_set = new std::vector<ReachableFact*>(*reachable_set);
			new_reachable_set->push_back(&reachable_fact);
			
			wip_sets_.push_back(new_reachable_set);

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//			std::cout << "[ReachableSet::processNewReachableFact] Add to existing set!" << std::endl;
#endif

			generateNewReachableSets(*new_reachable_set);
		}
	}
	
	return true;
}

void ReachableSet::generateNewReachableSets(std::vector<ReachableFact*>& reachable_sets_to_process)
{
	unsigned int index = reachable_sets_to_process.size();
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "[ReachableSet::generateNewReachableSets] Process new reachable set, size=" << index << "." << std::endl;
	for (std::vector<ReachableFact*>::const_iterator ci = reachable_sets_to_process.begin(); ci != reachable_sets_to_process.end(); ci++)
	{
		ReachableFact* reachable_fact = *ci;
		std::cout << " * " << *reachable_fact << "." << std::endl;
	}
#endif
	
	
	// Check if we are done.
	if (index == facts_set_.size())
	{
		fully_reachable_sets_.push_back(&reachable_sets_to_process);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "[ReachableSet::generateNewReachableSets] Found a full set for ";
		print(std::cout);
		std::cout << "!" << std::endl;
		
		for (std::vector<ReachableFact*>::const_iterator ci = reachable_sets_to_process.begin(); ci != reachable_sets_to_process.end(); ci++)
		{
			std::cout << "* " << **ci << std::endl;
		}
#endif
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		std::cout << "Check if the full reachable set can be unified with the from facts: " << std::endl;
		for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = getFactsSet().begin(); ci != getFactsSet().end(); ci++)
		{
			const ResolvedBoundedAtom* resolved_bounded_atom = *ci;
			std::cout << "! " << *resolved_bounded_atom << "." << std::endl;
		}
		
		for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = getFactsSet().begin(); ci != getFactsSet().end(); ci++)
		{
			const ResolvedBoundedAtom* resolved_bounded_atom = *ci;
			unsigned int index = std::distance(static_cast<std::vector<const ResolvedBoundedAtom*>::const_iterator>(getFactsSet().begin()), ci);
			
			assert (resolved_bounded_atom->getCorrectedAtom().getPredicate().canSubstitute(reachable_sets_to_process[index]->getAtom().getPredicate()));
			
			for (unsigned int i = 0; i < resolved_bounded_atom->getCorrectedAtom().getArity(); i++)
			{
				const EquivalentObjectGroup& eog = reachable_sets_to_process[index]->getTermDomain(i);
				const std::vector<const Object*>& variable_domain = resolved_bounded_atom->getVariableDomain(i);
				
				for (std::vector<EquivalentObject*>::const_iterator ci = eog.getEquivalentObjects().begin(); ci != eog.getEquivalentObjects().end(); ci++)
				{
					const EquivalentObject* eo = *ci;
					bool found = false;
				
					for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ci++)
					{
						const Object* object = *ci;
						if (&eo->getObject() == object)
						{
							found = true;
							break;
						}
					}
					
					if (!found)
					{
						std::cout << "Trying to combine " << *reachable_sets_to_process[index] << " with " << *resolved_bounded_atom << "." << std::endl;
						assert(false);
					}
				}
			}
		}
#endif
		return;
	}
	
	// Try all possible facts which we have proven to be reachable for the 'index'th index.
	for (std::vector<ReachableFact*>::const_iterator ci = reachable_set_[index]->begin(); ci != reachable_set_[index]->end(); ci++)
	{
		ReachableFact* reachable_fact = *ci;

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Possible candidate for the index: " << index << " -> " << *reachable_fact << std::endl;
#endif
		
		if (!canSatisfyConstraints(*reachable_fact, reachable_sets_to_process))
		{
			continue;
		}
		
		// If the constraints are satisfied, add the facts and search for new facts to add.
		std::vector<ReachableFact*>* new_reachable_set = new std::vector<ReachableFact*>(reachable_sets_to_process);
		new_reachable_set->push_back(reachable_fact);
		
		if (index != facts_set_.size())
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "New WIP set: " << std::endl;
			for (std::vector<ReachableFact*>::const_iterator ci = new_reachable_set->begin(); ci != new_reachable_set->end(); ci++)
			{
				std::cout << "* " << **ci << std::endl;
			}
#endif
			wip_sets_.push_back(new_reachable_set);
		}
		
		generateNewReachableSets(*new_reachable_set);
	}
}

/**
 * ReachableNode
 */
ReachableNode::ReachableNode(const DomainTransitionGraphNode& dtg_node, const EquivalentObjectGroupManager& eog_manager)
	: ReachableSet(eog_manager), dtg_node_(&dtg_node)
{
	for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
	{
		addBoundedAtom(**ci, dtg_node.getDTG().getBindings());
	}
}

void ReachableNode::initialise(const std::vector<ReachableFact*>& initial_facts)
{
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

void ReachableNode::handleUpdatedEquivalences()
{
	equivalencesUpdated();
	for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transitions_.begin(); ci != reachable_transitions_.end(); ci++)
	{
		ReachableTransition* reachable_transition = *ci;
		reachable_transition->handleUpdatedEquivalences();
	}
}

void ReachableNode::print(std::ostream& os) const
{
	os << "ReachableNode: " << *dtg_node_ << std::endl;
	
	if (getFullyReachableSets().empty())
	{
		os << "No supported facts :((" << std::endl;
	}
	else
	{
		os << "Fully supported facts: " << std::endl;
		for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = getFullyReachableSets().begin(); ci != getFullyReachableSets().end(); ci++)
		{
			std::vector<ReachableFact*>* reachable_facts = *ci;
			if (reachable_facts == NULL) continue;
			std::cout << "{";
			for (std::vector<ReachableFact*>::const_iterator ci = reachable_facts->begin(); ci != reachable_facts->end(); ci++)
			{
				std::cout << **ci;
				if (ci + 1 != reachable_facts->end())
				{
					std::cout << ", ";
				}
			}
			std::cout << "}" << std::endl;
		}
	}
	
	os << " -= WIP: " << std::endl;
	for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci =getWIPSets().begin(); ci != getWIPSets().end(); ci++)
	{
		os << " === Start set === " << std::endl;
		std::vector<ReachableFact*>* wip_set = *ci;
		
		for (std::vector<ReachableFact*>::const_iterator ci = wip_set->begin(); ci != wip_set->end(); ci++)
		{
			ReachableFact* fact = *ci;
			os << " * " << *fact << std::endl;
		}
		os << " === END set === " << std::endl;
	}
	
	os << " -= Reachable facts per fact: " << std::endl;
	for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = getReachableSets().begin(); ci != getReachableSets().end(); ci++)
	{
		os << " === START === " << std::endl;
		std::vector<ReachableFact*>* reachable_set = *ci;
		
		for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end(); ci++)
		{
			ReachableFact* fact = *ci;
			os << " * " << *fact << std::endl;
		}
		os << " === END === " << std::endl;
	}
	
	if (reachable_transitions_.size() > 0)
	{
		std::cout << "All transitions: " << std::endl;
		for (std::vector<ReachableTransition*>::const_iterator ci = reachable_transitions_.begin(); ci != reachable_transitions_.end(); ci++)
		{
			(*ci)->print(os);
		}
	}
	else
	{
		std::cout << "No transitions..." << std::endl;
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
ReachableTransition::ReachableTransition(const MyPOP::SAS_Plus::Transition& transition, const ReachableNode& from_node, const ReachableNode& to_node, const EquivalentObjectGroupManager& eog_manager)
	: ReachableSet(eog_manager), from_node_(&from_node), to_node_(&to_node), transition_(&transition), latest_processed_from_node_set_(0), latest_processed_transition_set_(0)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "New reachable transition: " << transition << "." << std::endl;
#endif

	// Determine the set of grounded variables.
	std::set<const std::vector<const Object*>*> grounded_variables;
	for (std::vector<const Variable*>::const_iterator ci = transition.getStep()->getAction().getVariables().begin(); ci != transition.getStep()->getAction().getVariables().end(); ci++)
	{
		const Variable* variable = *ci;
		const std::vector<const Object*>& variable_domain = variable->getDomain(transition.getStep()->getStepId(), transition.getFromNode().getDTG().getBindings());
		
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
	for (std::vector<const Variable*>::const_iterator ci = transition.getStep()->getAction().getVariables().begin(); ci != transition.getStep()->getAction().getVariables().end(); ci++)
	{
		const Variable* variable = *ci;
		const std::vector<const Object*>& variable_domain = variable->getDomain(transition.getStep()->getStepId(), bindings);
		transition_variable_domains.push_back(&variable_domain);
	}
	bool processed_variable_domains[transition.getStep()->getAction().getVariables().size()];
	memset(&processed_variable_domains[0], false, sizeof(bool) * transition.getStep()->getAction().getVariables().size());

	// Find out how the variables are linked to the facts in the from node and those in the set of preconditions which are not part of the 
	// from node.
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = all_preconditions.begin(); ci != all_preconditions.end(); ci++)
	{
		const Atom* precondition = (*ci).first;
		bool precondition_part_of_from_node = false;
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the precondition: ";
		precondition->print(std::cout, bindings, transition.getStep()->getStepId());
		std::cout << "." << std::endl;
#endif
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		if (transition.getFromNodePreconditions().size() != from_node.getFactsSet().size())
		{
			std::cout << "Preconditions recorded by the transition: " << std::endl;
			for (std::vector<const Atom*>::const_iterator ci = transition.getFromNodePreconditions().begin(); ci != transition.getFromNodePreconditions().end(); ci++)
			{
				std::cout << "* ";
				(*ci)->print(std::cout, bindings, transition.getStep()->getStepId());
				std::cout << "." << std::endl;
			}
			
			std::cout << "Preconditions recorded by the from node: " << std::endl;
			for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = from_node.getFactsSet().begin(); ci != from_node.getFactsSet().end(); ci++)
			{
				std::cout << "* " << **ci << "." << std::endl;
			}
			assert (false);
		}
#endif
		
		for (std::vector<const Atom*>::const_iterator ci = transition.getFromNodePreconditions().begin(); ci != transition.getFromNodePreconditions().end(); ci++)
		{
			unsigned int from_node_fact_index = std::distance(transition.getFromNodePreconditions().begin(), ci);
			const Atom* from_node_precondition = *ci;
			const ResolvedBoundedAtom* resolved_bounded_atom = from_node.getFactsSet()[from_node_fact_index];
			
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			if (!bindings.canUnify(resolved_bounded_atom->getOriginalAtom(), resolved_bounded_atom->getId(), *from_node_precondition, transition.getStep()->getStepId()))
			{
				std::cout << "Cannot unify: " << *resolved_bounded_atom << " with ";
				from_node_precondition->print(std::cout, bindings, transition.getStep()->getStepId());
				std::cout << "." << std::endl;
			}
#endif
			
			if (bindings.areIdentical(resolved_bounded_atom->getOriginalAtom(), resolved_bounded_atom->getId(), *precondition, transition.getStep()->getStepId()))
			{
				precondition_part_of_from_node = true;
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Process the from node precondition: ";
				from_node_precondition->print(std::cout, bindings, transition.getStep()->getStepId());
				std::cout << "." << std::endl;
#endif
				
				// Compare all the variables of the precondition and see if they are linked to a variable of the action and link them accordingly.
				for (unsigned int i = 0; i < transition.getStep()->getAction().getVariables().size(); i++)
				{
					if (processed_variable_domains[i]) continue;
					
					const std::vector<const Object*>* variable_domain = transition_variable_domains[i];
					
					for (unsigned int j = 0; j < resolved_bounded_atom->getCorrectedAtom().getArity(); j++)
					{
//						if (&resolved_bounded_atom->getVariableDomain(j) == variable_domain)
						if (from_node_precondition->getTerms()[j] == transition.getStep()->getAction().getVariables()[i])
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
		std::vector<const Property*>* precondition_properties = new std::vector<const Property*>();
		BoundedAtom* bounded_precondition = new BoundedAtom(transition.getStep()->getStepId(), *precondition, *precondition_properties);
		addBoundedAtom(*bounded_precondition, bindings);
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the precondition: ";
		bounded_precondition->print(std::cout, bindings, transition.getStep()->getStepId());
		std::cout << "." << std::endl;
#endif
		
		// Check for the other facts are connected to the variables.
		for (unsigned int i = 0; i < transition.getStep()->getAction().getVariables().size(); i++)
		{
			if (processed_variable_domains[i]) continue;
			
			const std::vector<const Object*>* variable_domain = transition_variable_domains[i];
			
			unsigned int precondition_index = getFactsSet().size() - 1;
			for (unsigned int j = 0; j < bounded_precondition->getAtom().getArity(); j++)
			{
//				if (&bounded_precondition->getVariableDomain(j, bindings) == variable_domain)
				if (bounded_precondition->getAtom().getTerms()[j] == transition.getStep()->getAction().getVariables()[i])
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
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	// At the end all variables which are not bounded are free variables.
	for (unsigned int i = 0; i < transition.getStep()->getAction().getVariables().size(); i++)
	{
		if (!processed_variable_domains[i])
		{
			std::cout << "The " << i << "th variable of the transition " << transition << " is a free variable!" << std::endl;
//			assert (false);
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
	const std::vector<std::pair<const Atom*, InvariableIndex> >& effects = transition_->getEffects();
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
	{
		const Atom* effect = (*ci).first;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Process the effect: ";
		effect->print(std::cout, bindings, transition_->getStep()->getStepId());
		std::cout << "." << std::endl;
#endif
		
		// Check if any of the effect's terms are free variables.
		bool free_variables[effect->getArity()];
		memset(&free_variables[0], false, sizeof(bool) * effect->getArity());
		
		for (unsigned int i = 0; i < transition.getStep()->getAction().getVariables().size(); i++)
		{
			if (!processed_variable_domains[i])
			{
				for (std::vector<const Term*>::const_iterator ci = effect->getTerms().begin(); ci != effect->getTerms().end(); ci++)
				{
					const Term* term = *ci;
					unsigned int term_index = std::distance(static_cast<std::vector<const Term*>::const_iterator>(effect->getTerms().begin()), ci);
					if (term == transition.getStep()->getAction().getVariables()[i])
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
		
		ResolvedEffect* resolved_effect = new ResolvedEffect(transition.getStep()->getStepId(), *effect, bindings, eog_manager, free_variables);
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
	for (std::vector<const Variable*>::const_iterator ci = transition.getStep()->getAction().getVariables().begin(); ci != transition.getStep()->getAction().getVariables().end(); ci++)
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

void ReachableTransition::finalise(const std::vector<ReachableSet*>& all_reachable_sets)
{
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
			
			const std::vector<const ResolvedBoundedAtom*>& preconditions = reachable_set->getFactsSet();
			
			for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const ResolvedBoundedAtom* precondition = *ci;
				
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << "Potential candidate: " << *precondition << "." << std::endl;
#endif
				
				if (precondition->canUnifyWith(*effect))
				{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
					std::cout << "Accepted! :D" << std::endl;
#endif
					preconditions_reached_by_effect_->push_back(std::make_pair(reachable_set, std::distance(preconditions.begin(), ci)));
				}
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				else
				{
					std::cout << "Declined :((" << std::endl;
				}
#endif
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
	const std::vector<std::vector<ReachableFact*>* >& from_node_reachable_sets = from_node_->getFullyReachableSets();
	if (from_node_reachable_sets.size() == 0)
	{
		return false;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//		std::cout << "Found reachable sets in the from node! :)" << std::endl;
#endif
	
	// Special case if all the preconditions are part of the from node.
	const std::vector<std::vector<ReachableFact*>* >& transition_reachable_sets = getFullyReachableSets();
	if (this->getFactsSet().size() > 0 && transition_reachable_sets.size() == 0)
	{
		return false;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
//		std::cout << "Found reachable sets in the transition! :D" << std::endl;
#endif

#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Process the transition " << *this << std::endl;
#endif
	
	bool new_facts_reached = false;
	
	std::vector<std::vector<ReachableFact*>* > from_node_reachable_sets_copy(from_node_reachable_sets);
	std::vector<std::vector<ReachableFact*>* > transition_reachable_sets_copy(transition_reachable_sets);

	// Generate the || from_node_reachable_sets || * || transition_reachable_sets || effects.
	for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
	{
		unsigned int effect_index = std::distance(static_cast<std::vector<ResolvedEffect*>::const_iterator>(effects_.begin()), ci);
		const ResolvedEffect* effect = *ci;
		
		for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = from_node_reachable_sets_copy.begin(); ci != from_node_reachable_sets_copy.end(); ci++)
		{
			const std::vector<ReachableFact*>* from_node_reachable_set = *ci;
			if (from_node_reachable_set == NULL) continue;
			
			unsigned int from_node_set_index = std::distance(static_cast<std::vector<std::vector<ReachableFact*>* >::const_iterator>(from_node_reachable_sets_copy.begin()), ci);
			for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = transition_reachable_sets_copy.begin(); ci != transition_reachable_sets_copy.end(); ci++)
			{
				const std::vector<ReachableFact*>* transition_reachable_set = *ci;
				if (transition_reachable_set == NULL) continue;
				
				unsigned int transition_set_index = std::distance(static_cast<std::vector<std::vector<ReachableFact*>* >::const_iterator>(transition_reachable_sets_copy.begin()), ci);
				if (from_node_set_index < latest_processed_from_node_set_ && transition_set_index < latest_processed_transition_set_) continue;
				if (createNewReachableFact(*effect, effect_index, *from_node_reachable_set, *transition_reachable_set))
				{
					new_facts_reached = true;
				}
			}
			
			// Sometimes all the variables are defined by the from node.
			if (getFactsSet().empty())
			{
				if (from_node_set_index < latest_processed_from_node_set_) continue;
				const std::vector<ReachableFact*> transition_reachable_set;
				if (createNewReachableFact(*effect, effect_index, *from_node_reachable_set, transition_reachable_set))
				{
					new_facts_reached = true;
				}
			}
		}
	}
	
	latest_processed_from_node_set_ = from_node_reachable_sets_copy.size();
	latest_processed_transition_set_ = transition_reachable_sets_copy.size();
	
	return new_facts_reached;
}

void ReachableTransition::handleUpdatedEquivalences()
{
	equivalencesUpdated();
	
	for (std::vector<ResolvedEffect*>::const_iterator ci = effects_.begin(); ci != effects_.end(); ci++)
	{
		(*ci)->updateVariableDomains();
	}
}

bool ReachableTransition::createNewReachableFact(const ResolvedEffect& effect, unsigned int effect_index, const std::vector<ReachableFact*>& from_node_reachable_set, const std::vector<ReachableFact*>& transition_reachable_set)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Create new reachable fact of the effect: " << effect << "." << std::endl;
#endif
	EquivalentObjectGroup** effect_domains = new EquivalentObjectGroup*[effect.getCorrectedAtom().getArity()];
	bool new_facts_reached = false;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	if (getFactsSet().empty()) assert (transition_reachable_set.empty());
#endif
	
//	bool contains_free_variables = false;
	for (unsigned int i = 0; i < effect.getCorrectedAtom().getArity(); i++)
	{
		
		if (effect.isFreeVariable(i))
		{
//			contains_free_variables = true;
			continue;
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
		assert (variable_to_values_mapping_.find(&effect.getVariableDomain(i)) != variable_to_values_mapping_.end());
#endif
		
		VariableToValues* values = variable_to_values_mapping_[&effect.getVariableDomain(i)];
		if (values->is_transition_)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			assert (transition_reachable_set.size() > values->fact_index_);
			assert (transition_reachable_set[values->fact_index_]->getAtom().getArity() > values->term_index_);
#endif
			effect_domains[i] = &(transition_reachable_set)[values->fact_index_]->getTermDomain(values->term_index_);
		}
		else
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
			assert (from_node_reachable_set.size() > values->fact_index_);
			assert (from_node_reachable_set[values->fact_index_]->getAtom().getArity() > values->term_index_);
#endif
			effect_domains[i] = &(from_node_reachable_set)[values->fact_index_]->getTermDomain(values->term_index_);
		}
	}
	
	std::vector<ReachableFact*> new_reachable_facts;
	effect.createReachableFacts(new_reachable_facts, effect_domains);

	for (std::vector<ReachableFact*>::const_iterator ci = new_reachable_facts.begin(); ci != new_reachable_facts.end(); ci++)
	{
		ReachableFact* new_reachable_fact = *ci;
		bool fact_added = false;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "New reachable fact: " << *new_reachable_fact << std::endl;
		
		std::cout << "Combined: " << std::endl;
		for (std::vector<ReachableFact*>::const_iterator ci = from_node_reachable_set.begin(); ci != from_node_reachable_set.end(); ci++)
		{
			std::cout << " * " << **ci << std::endl;
		}
		std::cout << "and" << std::endl;
		for (std::vector<ReachableFact*>::const_iterator ci = transition_reachable_set.begin(); ci != transition_reachable_set.end(); ci++)
		{
			std::cout << " * " << **ci << std::endl;
		}
#endif

		// Make sure the fact hasn't been reached before!
		const EquivalentObjectGroup* best_eog = NULL;
		for (unsigned int i = 0; i < new_reachable_fact->getAtom().getArity(); i++)
		{
			const EquivalentObjectGroup& eog = new_reachable_fact->getTermDomain(i);
			if (best_eog == NULL)
			{
				best_eog = &eog;
				continue;
			}
			
			if (best_eog->getReachableFacts().size() > eog.getReachableFacts().size())
			{
				best_eog = &eog;
			}
		}
		
		assert (best_eog != NULL);
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Compare the new reachable fact against the reachable facts in the EOG: " << *best_eog << "." << std::endl;
#endif
		
		
		bool already_reached = false;
		for (std::vector<ReachableFact*>::const_iterator ci = best_eog->getReachableFacts().begin(); ci != best_eog->getReachableFacts().end(); ci++)
		{
			if ((*ci)->isIdenticalTo(*new_reachable_fact))
			{
				already_reached = true;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
				std::cout << *new_reachable_fact << " is identical to: " << **ci << " :((." << std::endl;
#endif
				break;
			}
		}
		if (already_reached) continue;
	
		std::vector<std::pair<ReachableSet*, unsigned int> >* listeners = effect_propagation_listeners_[effect_index];
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Number of listeners: " << listeners->size() << std::endl;
#endif
		
		std::set<ReachableSet*> processed;
		
		for (std::vector<std::pair<ReachableSet*, unsigned int> >::const_iterator ci = listeners->begin(); ci != listeners->end(); ci++)
		{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
			std::cout << "Add it to the following set: ";
			(*ci).first->print(std::cout);
			std::cout << "." << std::endl;
#endif
			
			assert (processed.count((*ci).first) == 0);
			processed.insert((*ci).first);
			
			// 0.18
			if ((*ci).first->processNewReachableFact(*new_reachable_fact, (*ci).second))
			{
				fact_added = true;
				new_facts_reached = true;
			}
		}
		
		// Update the relevant equivalent object groups.
		if (fact_added)
		{
			for (unsigned int i = 0; i < new_reachable_fact->getAtom().getArity(); i++)
			{
				new_reachable_fact->getTermDomain(i).addReachableFact(*new_reachable_fact);
			}
		}
	}
	
 	return new_facts_reached;
}

void ReachableTransition::print(std::ostream& os) const
{
	os << "Reachable transition: ";
	transition_->getStep()->getAction().print(std::cout, transition_->getFromNode().getDTG().getBindings(), transition_->getStep()->getStepId());

	if (getFullyReachableSets().empty())
	{
		os << "No supported facts :((" << std::endl;
	}
	else
	{
		os << "Fully supported facts: " << std::endl;
		for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = getFullyReachableSets().begin(); ci != getFullyReachableSets().end(); ci++)
		{
			std::vector<ReachableFact*>* reachable_facts = *ci;
			if (reachable_facts == NULL) continue;
			std::cout << "{";
			for (std::vector<ReachableFact*>::const_iterator ci = reachable_facts->begin(); ci != reachable_facts->end(); ci++)
			{
				std::cout << **ci;
				if (ci + 1 != reachable_facts->end())
				{
					std::cout << ", ";
				}
			}
			std::cout << "}" << std::endl;
		}
	}
	
	os << " -= WIP: " << std::endl;
	for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = getWIPSets().begin(); ci != getWIPSets().end(); ci++)
	{
		os << " === Start set === " << std::endl;
		std::vector<ReachableFact*>* wip_set = *ci;
		
		for (std::vector<ReachableFact*>::const_iterator ci = wip_set->begin(); ci != wip_set->end(); ci++)
		{
			ReachableFact* fact = *ci;
			os << " * " << *fact << std::endl;
		}
		os << " === END set === " << std::endl;
	}
	
	os << " -= Reachable facts per fact: " << std::endl;
	for (std::vector<std::vector<ReachableFact*>* >::const_iterator ci = getReachableSets().begin(); ci != getReachableSets().end(); ci++)
	{
		os << " === START === " << std::endl;
		std::vector<ReachableFact*>* reachable_set = *ci;
		
		for (std::vector<ReachableFact*>::const_iterator ci = reachable_set->begin(); ci != reachable_set->end(); ci++)
		{
			ReachableFact* fact = *ci;
			os << " * " << *fact << std::endl;
		}
		os << " === END === " << std::endl;
	}
}

std::ostream& operator<<(std::ostream& os, const ReachableTransition& reachable_transition)
{
	os << "Reachable transition: " << reachable_transition.getTransition() << "." << std::endl;
	return os;
}

/*******************************
 * DTGReachability
*******************************/

DTGReachability::DTGReachability(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::SAS_Plus::DomainTransitionGraph& dtg_graph, const MyPOP::TermManager& term_manager)
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
		
		ReachableNode* reachable_node = new ReachableNode(*dtg_node, *equivalent_object_manager_);
		reachable_nodes_.push_back(reachable_node);
		node_mapping[dtg_node] = reachable_node;
		all_reachable_sets.push_back(reachable_node);
		
		for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = reachable_node->getFactsSet().begin(); ci != reachable_node->getFactsSet().end(); ci++)
		{
			unsigned int index = std::distance(reachable_node->getFactsSet().begin(), ci);
			const ResolvedBoundedAtom* node_fact = *ci;
			const std::string& predicate_name = node_fact->getCorrectedAtom().getPredicate().getName();
			std::map<std::string, std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator found_mapping = predicate_to_reachable_set_mapping_.find((*ci)->getCorrectedAtom().getPredicate().getName());
			std::vector<std::pair<ReachableSet*, unsigned int> >* mapping = NULL;
			if (found_mapping == predicate_to_reachable_set_mapping_.end())
			{
				mapping = new std::vector<std::pair<ReachableSet*, unsigned int> >();
				predicate_to_reachable_set_mapping_[predicate_name] = mapping;
			}
			else
			{
				mapping = (*found_mapping).second;
			}
			mapping->push_back(std::make_pair(reachable_node, index));
		}
	}
	
	for (std::map<const DomainTransitionGraphNode*, ReachableNode*>::const_iterator ci = node_mapping.begin(); ci != node_mapping.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		ReachableNode* reachable_from_node = (*ci).second;
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			ReachableNode* reachable_to_node = node_mapping[&transition->getToNode()];
			ReachableTransition* reachable_transition = new ReachableTransition(**ci, *reachable_from_node, *reachable_to_node, *equivalent_object_manager_);
			reachable_transitions_[*ci] = reachable_transition;
			 
			reachable_from_node->addReachableTransition(*reachable_transition);
			all_reachable_sets.push_back(reachable_transition);
			all_reachable_transitions.push_back(reachable_transition);
			
			
			for (std::vector<const ResolvedBoundedAtom*>::const_iterator ci = reachable_transition->getFactsSet().begin(); ci != reachable_transition->getFactsSet().end(); ci++)
			{
				unsigned int index = std::distance(reachable_transition->getFactsSet().begin(), ci);
				const ResolvedBoundedAtom* transition_fact = *ci;
				const std::string& predicate_name = transition_fact->getCorrectedAtom().getPredicate().getName();
				std::map<std::string, std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator found_mapping = predicate_to_reachable_set_mapping_.find(predicate_name);
				std::vector<std::pair<ReachableSet*, unsigned int> >* mapping = NULL;
				if (found_mapping == predicate_to_reachable_set_mapping_.end())
				{
					mapping = new std::vector<std::pair<ReachableSet*, unsigned int> >();
					predicate_to_reachable_set_mapping_[predicate_name] = mapping;
				}
				else
				{
					mapping = (*found_mapping).second;
				}
				mapping->push_back(std::make_pair(reachable_transition, index));
			}
		}
	}
	
	for (std::vector<ReachableTransition*>::const_iterator ci = all_reachable_transitions.begin(); ci != all_reachable_transitions.end(); ci++)
	{
		(*ci)->finalise(all_reachable_sets);
	}
}

void DTGReachability::performReachabilityAnalsysis(std::vector<const ReachableFact*>& result, const std::vector<const BoundedAtom*>& initial_facts, const Bindings& bindings)
{
//	double time_propagating = 0;
//	double time_iterating = 0;
//	double time_establishing_equivalances = 0;
//	unsigned int amount_of_iterating = 0;
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Start performing reachability analysis." << std::endl;
#endif

	struct timeval start_time_eog;
	gettimeofday(&start_time_eog, NULL);
	
	// Transform the set of initial facts into reachable facts, which means we drop the variable domains
	// and work solely with equivalent object groups.
	std::vector<ReachableFact*> established_reachable_facts;
	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		ReachableFact* initial_reachable_fact = new ReachableFact(**ci, bindings, *equivalent_object_manager_);
		established_reachable_facts.push_back(initial_reachable_fact);
	}

	equivalent_object_manager_->initialise(established_reachable_facts);
	equivalent_object_manager_->updateEquivalences();
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		(*ci)->handleUpdatedEquivalences();
	}

	struct timeval end_time_eog;
	gettimeofday(&end_time_eog, NULL);

	double time_spend_eog = end_time_eog.tv_sec - start_time_eog.tv_sec + (end_time_eog.tv_usec - start_time_eog.tv_usec) / 1000000.0;
	std::cerr << "Initialise EOGs: " << time_spend_eog << " seconds" << std::endl;
	
	struct timeval start_time_init;
	gettimeofday(&start_time_init, NULL);
	
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "Find initial supported DTG nodes." << std::endl;
#endif
	
	mapInitialFactsToReachableSets(established_reachable_facts);
	
	struct timeval end_time_init;
	gettimeofday(&end_time_init, NULL);

	double time_spend_initial = end_time_init.tv_sec - start_time_init.tv_sec + (end_time_init.tv_usec - start_time_init.tv_usec) / 1000000.0;
	std::cerr << "Converting initial facts for " << reachable_nodes_.size() << " nodes: " << time_spend_initial << " seconds. Average = " << (time_spend_initial / reachable_nodes_.size()) << std::endl;
	
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
	
//	exit(0);
	
	// Now for every LTG node for which we have found a full set we check if their reachable transitions have the same property and we
	// can generate new reachable facts from these.
	bool done = false;
	unsigned int iteration = 0;
	while (!done)
	{
		struct timeval start_time_iteration;
		gettimeofday(&start_time_iteration, NULL);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Start propagating reachable facts iteration: " <<iteration << "." << std::endl;
#endif
		done = true;
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			if ((*ci)->propagateReachableFacts())
			{
				done = false;
			}
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "End of the " << iteration << "th iteration. Results so far: " << std::endl;
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			(*ci)->print(std::cout);
			std::cout << std::endl;
		}
#endif

		equivalent_object_manager_->updateEquivalences();
		for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
		{
			(*ci)->handleUpdatedEquivalences();
		}

		++iteration;
		
		struct timeval end_time_iteration;
		gettimeofday(&end_time_iteration, NULL);

		double time_spend_on_iteration = end_time_iteration.tv_sec - start_time_iteration.tv_sec + (end_time_iteration.tv_usec - start_time_iteration.tv_usec) / 1000000.0;
		std::cerr << iteration << "th iteration. Number of EOGs: " << equivalent_object_manager_->getNumberOfEquivalentGroups() << ". Time spend: " << time_spend_on_iteration << "." << std::endl;
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
		std::cout << "Equivalent objects after the " << iteration << "th iteration: ";
		equivalent_object_manager_->print(std::cout);
		std::cout << "." << std::endl;
#endif
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
	
	equivalent_object_manager_->getAllReachableFacts(result);
}

ReachableTransition& DTGReachability::getReachableTransition(const Transition& transition) const
{
	std::map<const Transition*, ReachableTransition*>::const_iterator ci = reachable_transitions_.find(&transition);
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_DEBUG
	assert (ci != reachable_transitions_.end());
#endif
	return *(*ci).second;
}

void DTGReachability::mapInitialFactsToReachableSets(const std::vector<ReachableFact*>& initial_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_COMMENT
	std::cout << "MAP INITIAL FACTS!" << std::endl;
#endif
/*	for (std::vector<ReachableFact*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		ReachableFact* initial_fact = *ci;
		
		if (initial_fact->isMarkedForRemoval()) continue;
		
		std::map<std::string, std::vector<std::pair<ReachableSet*, unsigned int> >* >::const_iterator found_mapping = predicate_to_reachable_set_mapping_.find(initial_fact->getAtom().getPredicate().getName());
		assert (found_mapping != predicate_to_reachable_set_mapping_.end());
		
		std::vector<std::pair<ReachableSet*, unsigned int> >* reachable_sets = predicate_to_reachable_set_mapping_[initial_fact->getAtom().getPredicate().getName()];
		
		assert (reachable_sets != NULL);
		
		for (std::vector<std::pair<ReachableSet*, unsigned int> >::const_iterator ci = reachable_sets->begin(); ci != reachable_sets->end(); ci++)
		{
			ReachableSet* reachable_set = (*ci).first;
			unsigned int fact_index = (*ci).second;
			
			// The predicate of the fact in this set should be more general than the one we try to 'merge' with.
			if (!reachable_set->getFactsSet()[fact_index]->getCorrectedAtom().getPredicate().canSubstitute(initial_fact->getAtom().getPredicate()))
			{
				continue;
			}
			
			std::cout << "Process: ";
			reachable_set->print(std::cout);
			std::cout << "." << std::endl;
			
			reachable_set->processNewReachableFact(*initial_fact, fact_index);
		}
	}*/
	
	for (std::vector<ReachableNode*>::const_iterator ci = reachable_nodes_.begin(); ci != reachable_nodes_.end(); ci++)
	{
		ReachableNode* reachable_node = *ci;
		reachable_node->initialise(initial_facts);
	}
}


};
	
};
