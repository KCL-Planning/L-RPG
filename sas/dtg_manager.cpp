#include <sys/time.h>
#include <set>
#include <queue>
#include <vector>
#include <algorithm>

#include <boost/bind.hpp>
#include <boost/lambda/lambda.hpp>
#include <boost/lambda/bind.hpp>

#include "dtg_manager.h"
#include "dtg_graph.h"
#include "dtg_node.h"
#include "transition.h"
#include "property_space.h"
#include "../VALfiles/TimSupport.h"
#include "../type_manager.h"
#include "../predicate_manager.h"
#include "../action_manager.h"
#include "../term_manager.h"
#include "../formula.h"
#include "../parser_utils.h"
#include "../plan_bindings.h"
#include "../bindings_propagator.h"
#include "../plan.h"
#include "recursive_function.h"

//#define MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
//#define MYPOP_SAS_PLUS_DTG_MANAGER_DEBUG
#define MYPOP_SAS_PLUS_DTG_MANAGER_DOT_OUTPUT
#define MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
#include <boost/concept_check.hpp>

namespace MyPOP {

namespace SAS_Plus {

/***********************
 * Bounded Atom...
 **********************/
BoundedAtom& BoundedAtom::createBoundedAtom(const Atom& atom, Bindings& bindings)
{
	StepID new_step_id = bindings.createVariableDomains(atom);
	return *(new BoundedAtom(new_step_id, atom));
}

BoundedAtom& BoundedAtom::createBoundedAtom(const Atom& atom, const Property& property, Bindings& bindings)
{
	StepID new_step_id = bindings.createVariableDomains(atom);
	std::vector<const Property*> properties;
	properties.push_back(&property);
	return *(new BoundedAtom(new_step_id, atom, properties));
}

BoundedAtom& BoundedAtom::createBoundedAtom(const Atom& atom, const std::vector<const Property*>& properties, Bindings& bindings)
{
	StepID new_step_id = bindings.createVariableDomains(atom);
	return *(new BoundedAtom(new_step_id, atom, properties));
}

BoundedAtom::BoundedAtom(const BoundedAtom& other, Bindings& bindings)
{
	atom_ = new Atom(other.getAtom());
	id_ = bindings.createVariableDomains(*atom_);
	
	// Make the variable domains equivalent to those of the given bounded atom.
	for (unsigned int i = 0; i < atom_->getArity(); ++i)
	{
		atom_->getTerms()[i]->makeDomainEqualTo(id_, other.getAtom().getTerms()[i]->getDomain(other.getId(), bindings), bindings);
	}
	properties_.insert(properties_.end(), other.properties_.begin(), other.properties_.end());
}

BoundedAtom::BoundedAtom(StepID id, const Atom& atom)
	: id_(id), atom_(&atom)
{
	
}

BoundedAtom::BoundedAtom(StepID id, const Atom& atom, const std::vector<const Property*>& properties)
	: id_(id), atom_(&atom)
{
	properties_.insert(properties_.end(), properties.begin(), properties.end());
	//resolveProperties();
}

BoundedAtom::~BoundedAtom()
{
	delete atom_;
}

StepID BoundedAtom::getId() const
{
	return id_;
}

const Atom& BoundedAtom::getAtom() const
{
	return *atom_;
}

void BoundedAtom::resolveProperties()
{
	properties_.clear();
	Property::getProperties(properties_, *atom_);
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "[BoundedAtom::resolveProperties] " << atom_->getPredicate() << std::endl;
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
#endif
}


const std::vector<const Property*>& BoundedAtom::getProperties() const
{
	return properties_;
}

unsigned int BoundedAtom::containsVariableDomain(const std::vector<const Object*>& variable_domain, const Bindings& bindings) const
{
	return atom_->containsVariableDomain(id_, variable_domain, bindings);
}
/*
bool BoundedAtom::addProperty(const Property& property)
{
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* existing_property = *ci;
		if (property == *existing_property)
			return false;
	}
	
	properties_.push_back(&property);
	return true;
}
*/
bool BoundedAtom::isBalanced(unsigned int term_index) const
{
	if (term_index == NO_INVARIABLE_INDEX) return false;
	
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* existing_property = *ci;
		if (existing_property->getIndex() == term_index) return true;
	}
	return false;
}

bool BoundedAtom::isMutexWith(const BoundedAtom& other, const Bindings& bindings) const
{
	// If either of the bounded atoms have any properties we can conclude that they cannot be mutex.
	if (properties_.size() == 0 || other.properties_.size() == 0)
	{
		return false;
	}
	
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* property = *ci;
		InvariableIndex invariable_index = property->getIndex();
		
		const Term* invariable_term = invariable_index != NO_INVARIABLE_INDEX ? atom_->getTerms()[invariable_index] : NULL;
		
		for (std::vector<const Property*>::const_iterator ci = other.properties_.begin(); ci != other.properties_.end(); ci++)
		{
			const Property* other_property = *ci;
			InvariableIndex other_property_index = other_property->getIndex();
			
			const Term* other_invariable_term = other_property_index != NO_INVARIABLE_INDEX ? other.atom_->getTerms()[other_property_index] : NULL;
			
			// If the properties are mutex, make sure the invariables match as well - if there are any.
			if (property->isMutexWith(other_property))
			{
				if (invariable_term == NULL || other_invariable_term == NULL)
				{
					return true;
				}
				
				//if (invariable_term->canUnify(id_, *other_invariable_term, other.id_, bindings))
				if (invariable_term->isTheSameAs(id_, *other_invariable_term, other.id_, bindings))
				{
					return true;
				}
			}
		}
	}
	
	return false;
}

bool BoundedAtom::isMutexWith(const Atom& atom, StepID step_id, const Bindings& bindings, InvariableIndex invariable_index) const
{
//	std::cout << "Check if: ";
//	print(std::cout, bindings);
//	std::cout << " is mutex with: ";
//	atom.print(std::cout, bindings, step_id);
//	std::cout << std::endl;
	
	// If an atom is negative it cannot be mutex!
	if (atom.isNegative()) return false;
	
	std::vector<const PropertySpace*> all_property_spaces;
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* property = *ci;
		const PropertySpace& property_space = property->getPropertyState().getPropertySpace();
		
		if (std::find(all_property_spaces.begin(), all_property_spaces.end(), &property_space) == all_property_spaces.end())
		{
			all_property_spaces.push_back(&property_space);
		}
	}
	
	// Search if there exists a property space which only contains the property for the atom and there exists no property state 
	// where both properties are part of.
	bool found_property_space_with_only_atom_property = false;
	for (std::vector<const PropertySpace*>::const_iterator ci = all_property_spaces.begin(); ci != all_property_spaces.end(); ++ci)
	{
		const PropertySpace* property_space = *ci;
//		std::cout << "Check the property space: " << *property_space << std::endl;
		
		for (std::vector<PropertyState*>::const_iterator ci = property_space->getPropertyStates().begin(); ci != property_space->getPropertyStates().end(); ++ci)
		{
			const PropertyState* property_state = *ci;
			bool contains_bounded_atom_property = false;
			bool contains_atom_property = false;
			
//			std::cout << "Process the property state: " << *property_state << std::endl;
			
			for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
			{
				const Property* property = *ci;
//				std::cout << "Process the property: " << *property << std::endl;
				for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ++ci)
				{
					if (**ci == *property)
					{
//						std::cout << "The property is contained by the bounded atom!" << std::endl;
						contains_bounded_atom_property = true;
					}
				}
					
				if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index)
				{
					// If both properties are in the same state than they cannot be mutex!
//					std::cout << "The property is contained by the atom!" << std::endl;
					contains_atom_property = true;
				}
			}
			
			// Both properties found in the same state space.
			if (contains_bounded_atom_property && contains_atom_property) return false;
			
			// Found only the precondition's property in this state space. If no state space exists where both properties are present then the 
			// precondition and bounded atoms are mutex!
			else if (!contains_bounded_atom_property && contains_atom_property) found_property_space_with_only_atom_property = true;
		}
	}
	
	return found_property_space_with_only_atom_property;
}

const std::vector<const Object*>& BoundedAtom::getVariableDomain(unsigned int term_index, const Bindings& bindings) const
{
	assert (term_index < atom_->getArity());
	return atom_->getTerms()[term_index]->getDomain(id_, bindings);
}

bool BoundedAtom::containsEmptyVariableDomain(const Bindings& bindings) const
{
	for (unsigned int i = 0; i < atom_->getArity(); ++i)
	{
		if (getVariableDomain(i, bindings).empty())
		{
			return true;
		}
	}
	return false;
}

bool BoundedAtom::isEquivalentTo(const BoundedAtom& other, const Bindings& lhs_bindings, const Bindings* rhs_bindings) const
{
	if (rhs_bindings == NULL)
	{
		rhs_bindings = &lhs_bindings;
	}
	
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		if (!atom_->getTerms()[i]->isEquivalentTo(id_, *other.getAtom().getTerms()[i], other.getId(), lhs_bindings, rhs_bindings))
			return false;
	}
	return true;
}

bool BoundedAtom::isIdenticalTo(const BoundedAtom& other, const Bindings& lhs_bindings) const
{
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		if (!atom_->getTerms()[i]->isTheSameAs(id_, *other.getAtom().getTerms()[i], other.getId(), lhs_bindings))
			return false;
	}
	return true;
}

bool BoundedAtom::isProperSubSetOf(const BoundedAtom& other, const Bindings& bindings) const
{
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	bool found_sub_set = false;
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		bool is_proper_sub_set = atom_->getTerms()[i]->isProperSubSetOf(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		bool is_equivalent_to = atom_->getTerms()[i]->isEquivalentTo(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		
		if (is_proper_sub_set)
			found_sub_set = true;
		
		if (!is_proper_sub_set && !is_equivalent_to)
			return false;
	}
	return found_sub_set;
}

bool BoundedAtom::isProperSuperSetOf(const BoundedAtom& other, const Bindings& bindings) const
{
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	bool found_super_set = false;
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		bool is_proper_super_set = atom_->getTerms()[i]->isProperSuperSetOf(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		bool is_equivalent_to = atom_->getTerms()[i]->isEquivalentTo(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		
		if (is_proper_super_set)
			found_super_set = true;
		
		if (!is_proper_super_set && !is_equivalent_to)
			return false;
	}
	return found_super_set;
}

bool BoundedAtom::canUnifyWith(const BoundedAtom& other, const Bindings& bindings) const
{
	return bindings.canUnify(getAtom(), getId(), other.getAtom(), other.getId());
}

bool BoundedAtom::canUnifyWith(StepID step_id, const Atom& atom, const Bindings& bindings) const
{
	return bindings.canUnify(getAtom(), getId(), atom, step_id);
}

void BoundedAtom::print(std::ostream& os, const Bindings& bindings, bool verbal) const
{
	atom_->print(os, bindings, id_, verbal);
	os << " $$$ ";
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		os << **ci;
		if (ci  + 1 != properties_.end())
			os << ", ";
	}
	os << " $$$ ";
}
	
/****************************************
 * void DomainTransitionGraphManager...
 ****************************************/
	
DomainTransitionGraphManager::DomainTransitionGraphManager(const PredicateManager& predicate_manager, const TypeManager& type_manager, const ActionManager& action_manager, const TermManager& term_manager, const std::vector<const Atom*>& initial_facts)
	: predicate_manager_(&predicate_manager), type_manager_(&type_manager), action_manager_(&action_manager), term_manager_(&term_manager), initial_facts_(&initial_facts)
{
	
}

DomainTransitionGraphManager::~DomainTransitionGraphManager()
{
//	for (std::map<const Predicate*, std::vector<DomainTransitionGraph*>* >::iterator i = dtg_mappings_.begin(); i != dtg_mappings_.end(); i++)
//	{
//		delete (*i).second;
//	}
}

void DomainTransitionGraphManager::getProperties(std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state) const
{
	for (std::multiset<TIM::Property*>::const_iterator lhs_properties_i = property_state.begin(); lhs_properties_i != property_state.end(); lhs_properties_i++)
	{
		const TIM::Property* property = *lhs_properties_i;

		const VAL::extended_pred_symbol* extended_property = property->root();
		const Predicate* predicate = predicate_manager_->getGeneralPredicate(extended_property->getName());
		assert (predicate != NULL);

		// Adding the predicate to the DTG will also create a lifted DTG node with that predicate.
		// Further refinements can be made to this DTG by splitting these nodes.
		predicates.push_back(std::make_pair(predicate, property->aPosn()));
	}
}

//const DomainTransitionGraph& 
void DomainTransitionGraphManager::generateDomainTransitionGraphsTIM(const VAL::pddl_type_list& types, Bindings& bindings)
{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval start_time_tim_translation;
	gettimeofday(&start_time_tim_translation, NULL);
#endif
	// Store temporary DTGs in this vector, during post processing they might get split again. Only then will we add the DTGs as a managable object (see Manager class).
	std::vector<DomainTransitionGraph*> tmp_dtgs;
	
	std::vector<TIM::PropertySpace*> property_spaces;
	property_spaces.insert(property_spaces.end(), TIM::TA->pbegin(), TIM::TA->pend());
//	property_spaces.insert(property_spaces.end(), TIM::TA->abegin(), TIM::TA->aend());
//	property_spaces.insert(property_spaces.end(), TIM::TA->sbegin(), TIM::TA->send());

//	assert (property_spaces.size() > 0);
	
	std::set<const Predicate*> state_valued_predicates;

	// Construct the DTGs by combining all properties which appear together in either the LHS or RHS of a transition rule.
	for (std::vector<TIM::PropertySpace*>::const_iterator property_space_i = property_spaces.begin(); property_space_i != property_spaces.end(); ++property_space_i)
	{
		TIM::PropertySpace* property_space = *property_space_i;
		
//		PropertySpace* dtg_property_space = new PropertySpace(property_space->obegin(), property_space->oend());
		PropertySpace& dtg_property_space = PropertySpace::createPropertySpace(*term_manager_, property_space->obegin(), property_space->oend());
		
		std::set<std::vector<std::pair<const Predicate*, unsigned int> > > processed_expressions;
		
		// The DTG where all predicates will be added to.
		DomainTransitionGraph* dtg = new DomainTransitionGraph(*this, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);

		// We need to augment some rules to get the full set of properties. If a property appears in the LHS of a rule $a$ and it is a proper subset
		// of another LHS $b$. Then add a new rule $b$ -> ($b.LHS$ \ $a.LHS$) + $a.RHS$.
		for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
		{
			TIM::TransitionRule* rule_a = *rules_i;
			
			// Combine the property states who appear in either the LHS of RHS of this rule.
			std::vector<std::pair<const Predicate*, unsigned int> > predicates_rule_a;
			getProperties(predicates_rule_a, *rule_a->getLHS());

			for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
			{
				TIM::TransitionRule* rule_b = *rules_i;
				
				// If rule_a is equal in size or larger it cannot be a proper subset.
				if (rule_a->getLHS()->size() >= rule_b->getLHS()->size())
				{
					continue;
				}
				
				std::multiset<TIM::Property*> intersection;
				std::set_intersection(rule_a->getLHS()->begin(), rule_a->getLHS()->end(), rule_b->getLHS()->begin(), rule_b->getLHS()->end(), std::inserter(intersection, intersection.begin()));
				
				// If the intersection is equal to the LHS of rule_a we know that it is a propper subset.
				if (intersection.size() == rule_a->getLHS()->size())
				{
					std::multiset<TIM::Property*> difference;
					std::set_difference(rule_b->getLHS()->begin(), rule_b->getLHS()->end(), rule_a->getLHS()->begin(), rule_a->getLHS()->end(), std::inserter(difference, difference.begin()));
					
					std::vector<std::pair<const Predicate*, unsigned int> > predicates_rhs;
					getProperties(predicates_rhs, *rule_a->getRHS());
					
//					std::cout << "!Rule: ";
//					rule_a->getLHS()->write(std::cout);
//					std::cout << " -> ";
//					rule_a->getRHS()->write(std::cout);
//					std::cout << " is a proper subset of: ";
//					rule_b->getLHS()->write(std::cout);
//					std::cout << " -> ";
//					rule_b->getRHS()->write(std::cout);
//					std::cout << std::endl;
					
//					std::cout << "Generate new rule: " << std::endl;
//					rule_b->getLHS()->write(std::cout);
//					std::cout << " =--> ";
//					rule_a->getRHS()->write(std::cout);
//					std::cout << " ++ ";
					
					std::multiset<TIM::Property*> duplicates;
					std::set_intersection(rule_a->getRHS()->begin(), rule_a->getRHS()->end(), rule_b->getLHS()->begin(), rule_b->getLHS()->end(), std::inserter(duplicates, duplicates.begin()));
					
					for (std::multiset<TIM::Property*>::const_iterator ci = difference.begin(); ci != difference.end(); ci++)
					{
						TIM::Property* property = *ci;
						const VAL::extended_pred_symbol* extended_property = property->root();
						const Predicate* predicate = predicate_manager_->getGeneralPredicate(extended_property->getName());
						assert (predicate != NULL);
						
						// Make sure we do not add duplicates:
						if (duplicates.count(property) != 0)
						{
							continue;
						}

						predicates_rhs.push_back(std::make_pair(predicate, property->aPosn()));
						
//						property->write(std::cout);
//						std::cout << " ++ ";
					}
//					std::cout << std::endl;
					
					if (processed_expressions.count(predicates_rhs) == 0)
					{
						///property_states.push_back(new PropertyState(*dtg_property_space, predicates_rhs));
						PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates_rhs);
						dtg_property_space.addPropertyState(*new_property_state);
						processed_expressions.insert(predicates_rhs);
						
						// We no longer need to process the LHS and RHS of rule_a, since it has been substituted by this rule.
						std::vector<std::pair<const Predicate*, unsigned int> > rule_a_rhs;
						getProperties(rule_a_rhs, *rule_a->getRHS());
						processed_expressions.insert(predicates_rule_a);
						processed_expressions.insert(rule_a_rhs);
					}
				}
			}
		}

		// After having augmented the rules for which the LHS formed a proper subset we finish constructing the DTGs for those rules
		// which do not have this property. The reason why this step has to be done last is because of the way we construct DTGs, if
		// we do the augmented rules before this, we might add a DTG node for a rule which is a strict subset. Then, when adding the
		// augmented rule, the DTG manager will reject adding the new node because it already exists.
		// TODO: Probably need to change this...
		for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
		{
			TIM::TransitionRule* rule = *rules_i;

			// Combine the property states who appear in either the LHS of RHS of this rule.
			std::vector<std::pair<const Predicate*, InvariableIndex> > predicates;
			getProperties(predicates, *rule->getLHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				// TODO: Memory leak.
				PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates);
				dtg_property_space.addPropertyState(*new_property_state);
				processed_expressions.insert(predicates);
			}
			
			predicates.clear();
			getProperties(predicates, *rule->getRHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				// TODO: Memory leak.
				PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates);
				dtg_property_space.addPropertyState(*new_property_state);
				processed_expressions.insert(predicates);
			}
		}
		
		dtg->addBalancedSet(dtg_property_space, true);
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all predicates and transitions (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif
		dtg->updateObjects(dtg_property_space);
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all objects (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif

		// Record all the state values predicates here so we know which ones are not yet processed later.
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
			{
				state_valued_predicates.insert(&(*ci)->getAtom().getPredicate());
			}
		}

		addManagableObject(dtg);
	}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_tim_translation;
	gettimeofday(&end_time_tim_translation, NULL);
	
	double time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "TIM transation took: " << time_spend << " seconds" << std::endl;

	struct timeval start_time_apply_rules;
	gettimeofday(&start_time_apply_rules, NULL);
#endif

	// Merge any two DTGs which are 1) State values and 2) Apply to the same object(s).
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cerr << "Start merging!" << std::endl;
#endif
	bool done_merging = true;
	while (!done_merging)
	{
		done_merging = true;
		for (std::vector<DomainTransitionGraph*>::iterator i_lhs = objects_.begin(); i_lhs != objects_.end() - 1; ++i_lhs)
		{
			DomainTransitionGraph* lhs = *i_lhs;
			
			for (std::vector<DomainTransitionGraph*>::iterator i_rhs = i_lhs + 1; i_rhs != objects_.end(); ++i_rhs)
			{
				const DomainTransitionGraph* rhs = *i_rhs;
				assert (lhs != rhs);
				
				DomainTransitionGraph* merged_dtg = DomainTransitionGraph::merge(*lhs, *rhs);
				
				if (merged_dtg != NULL)
				{
					// Delete the graphs which have been merged.
					delete lhs;
					delete rhs;
					objects_.erase(i_rhs);
					objects_.erase(i_lhs);
					
					// Add the merged dtg.
					objects_.push_back(merged_dtg);
					done_merging = false;
					std::cerr << "Merged, remaining " << objects_.size() << std::endl;
					break;
				}
			}
			
			if (!done_merging) break;
		}
	}

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cerr << "Done merging! " << objects_.size() << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ++ci)
	{
		std::cout<< **ci << std::endl;
	}
#endif

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_apply_rules;
	gettimeofday(&end_time_apply_rules, NULL);
	
	time_spend = end_time_apply_rules.tv_sec - start_time_apply_rules.tv_sec + (end_time_apply_rules.tv_usec - start_time_apply_rules.tv_usec) / 1000000.0;
	std::cerr << "Creating point to point transitions took: " << time_spend << " seconds" << std::endl;

	struct timeval start_time_unsupported_predicates;
	gettimeofday(&start_time_unsupported_predicates, NULL);
#endif
	/**
	 * Some predicates are not seen as DTGs by TIM, these come in two categories:
	 * - Static predicates - which cannot change, ever.
	 * - Predicates which can only be made true or false.
	 * 
	 * This bit of code constructs the DTGs for those predicates.
	 * 
	 * Note that we need to do this step before we check which DTG nodes need to be split due to the
	 * grounding of the static preconditions done above. The reason being is that when we see the need
	 * for a node to change its variables, we check for all possible values which are valid among the
	 * DTG nodes. If we have not included the static and those who can only be made true or false we
	 * might reach a false conclusion that a fact or transition's precondition cannot be satisfied and
	 * end up with wrong DTGs.
	 */
	std::vector<std::pair<const Predicate*, const Atom*> > unsupported_predicates;
	for (std::vector<Predicate*>::const_iterator ci = predicate_manager_->getManagableObjects().begin(); ci != predicate_manager_->getManagableObjects().end(); ci++)
	{
		const Predicate* predicate = *ci;

		bool is_supported = false;
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "Check if the predicate : " << *predicate << " is supported!" << std::endl;
#endif

		for (std::set<const Predicate*>::const_iterator ci = state_valued_predicates.begin(); ci != state_valued_predicates.end(); ci++)
		{
			const Predicate* state_valued_predicate = *ci;
			if (state_valued_predicate == predicate ||
			    state_valued_predicate->canSubstitute(*predicate))
			{
				is_supported = true;
				break;
			}
		}
		
		if (is_supported) continue;

		// Check if any of the DTG nodes supports the given predicate by making a dummy atom of it.
		std::vector<const Term*>* new_terms = new std::vector<const Term*>();
		for (std::vector<const Type*>::const_iterator ci = predicate->getTypes().begin(); ci != predicate->getTypes().end(); ci++)
		{
			const Type* type = *ci;
			new_terms->push_back(new Variable(*type, "test"));
		}
		Atom* possitive_atom = new Atom(*predicate, *new_terms, false, true);

		unsupported_predicates.push_back(std::make_pair(predicate, possitive_atom));
	}
	std::cerr << "Unsupported predicates checked..." << std::endl;
	for (std::vector<std::pair<const Predicate*, const Atom*> >::const_iterator ci = unsupported_predicates.begin(); ci != unsupported_predicates.end(); ci++)
	{
		const Predicate* predicate = (*ci).first;
		const Atom* possitive_atom = (*ci).second;
		
		/**
		 * Unsupported predicates come in two varieties:
		 * 1) The predicate is static in which case we can ignore it.
		 * 2) The predicate is not static, but can only be made true or false. This is encoded using two
		 * nodes and all relevant transitions between the two. The other node must contain the atom negated.
		 */
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "The predicate: " << *predicate << " is not processed yet!" << std::endl;
#endif
		// 1) The predicate is not static.
		if (!predicate->isStatic())
		{
			DomainTransitionGraph* new_unprocessed_dtg = new DomainTransitionGraph(*this, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);
			addManagableObject(new_unprocessed_dtg);

			// Find all transitions which can make this predicate true and false and add them as transitions.
			std::vector<std::pair<const Action*, const Atom*> > achievers;
			action_manager_->getAchievingActions(achievers, *possitive_atom);
			
			for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator ci = achievers.begin(); ci != achievers.end(); ci++)
			{
				//std::vector<std::pair<const Predicate*, unsigned int> >* predicates_to_add = new std::vector<std::pair<const Predicate*, unsigned int> >();
				std::vector<std::pair<const Predicate*, unsigned int> > predicates_to_add;
				predicates_to_add.push_back(std::make_pair(predicate, NO_INVARIABLE_INDEX));
				
				DomainTransitionGraphNode* possitive_new_unprocessed_dtg = new DomainTransitionGraphNode(*new_unprocessed_dtg);
				StepID possitive_atom_id = new_unprocessed_dtg->getBindings().createVariableDomains(*possitive_atom);
				
				// Check if there exists objects for all the parameters of the atom. If not we abort as the atom is invalid.
				bool atom_is_valid = true;
				for (unsigned int i = 0; i < possitive_atom->getArity(); ++i)
				{
					const std::vector<const Object*>& variable_domain = possitive_atom->getTerms()[i]->getDomain(possitive_atom_id, new_unprocessed_dtg->getBindings());
					if (variable_domain.empty())
					{
						atom_is_valid = false;
						break;
					}
				}
				if (!atom_is_valid)
				{
					break;
				}
				
				// Only memory leak here :P.
				//PropertySpace* property_space = new PropertySpace();
				PropertySpace& property_space = PropertySpace::createAttributeSpace();
				PropertyState* property_state = new PropertyState(property_space, predicates_to_add);
				property_space.addPropertyState(*property_state);
				
				Atom* new_possitive_atom = new Atom(*possitive_atom);
				BoundedAtom& fact = BoundedAtom::createBoundedAtom(*new_possitive_atom, property_state->getProperties(), bindings);
				
				bindings.unify(*new_possitive_atom, fact.getId(), *possitive_atom, possitive_atom_id);
				
				possitive_new_unprocessed_dtg->addAtom(fact, NO_INVARIABLE_INDEX);
				
				new_unprocessed_dtg->addNode(*possitive_new_unprocessed_dtg);

				// Add all preconditions which share a term with the unsupported predicate.
				DomainTransitionGraphNode* negative_new_unprocessed_dtg = new DomainTransitionGraphNode(*new_unprocessed_dtg);
				
				Atom* negative_atom = new Atom(*possitive_atom);
				negative_atom->makeNegative(true);
				BoundedAtom& bounded_negative_atom = BoundedAtom::createBoundedAtom(*negative_atom, property_state->getProperties(), bindings);
				
				bindings.unify(*negative_atom, bounded_negative_atom.getId(), *possitive_atom, possitive_atom_id);
				std::vector<const BoundedAtom*> atoms_add_to_from_node;
				atoms_add_to_from_node.push_back(&bounded_negative_atom);
				
				new_unprocessed_dtg->addNode(*negative_new_unprocessed_dtg);

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "Simple DTG : " << *new_unprocessed_dtg << " - achievers: " << achievers.size() << std::endl;
#endif
				const Action* achieving_action = (*ci).first;
				StepID new_action_step_id = bindings.createVariableDomains(*achieving_action);
				StepPtr new_step(new Step(new_action_step_id, *achieving_action));
				
				// Make sure this action actually achieves the unprocessed predicate!
				if ((*ci).second->getPredicate() != *predicate)
				{
					continue;
				}
				
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "Process the action: " << *achieving_action << std::endl;
#endif
				
				// Create a transition between the two nodes.
				Transition* transition = Transition::createSimpleTransition(new_step, *negative_new_unprocessed_dtg, *possitive_new_unprocessed_dtg);
				if (transition == NULL)
				{
					continue;
				}
				std::vector<Transition*> grounded_transitions;
				std::vector<const std::vector<const Object*>*> variable_domains_of_nodes;
				
				for (std::vector<BoundedAtom*>::const_iterator ci = negative_new_unprocessed_dtg->getAtoms().begin(); ci != negative_new_unprocessed_dtg->getAtoms().end(); ++ci)
				{
					const BoundedAtom* fact = *ci;
					for (unsigned int i = 0; i < fact->getAtom().getArity(); ++i)
					{
						const std::vector<const Object*>& variable_domain = fact->getVariableDomain(i, bindings);
						variable_domains_of_nodes.push_back(&variable_domain);
					}
				}
				for (std::vector<BoundedAtom*>::const_iterator ci = possitive_new_unprocessed_dtg->getAtoms().begin(); ci != possitive_new_unprocessed_dtg->getAtoms().end(); ++ci)
				{
					const BoundedAtom* fact = *ci;
					for (unsigned int i = 0; i < fact->getAtom().getArity(); ++i)
					{
						const std::vector<const Object*>& variable_domain = fact->getVariableDomain(i, bindings);
						variable_domains_of_nodes.push_back(&variable_domain);
					}
				}
				transition->ground(grounded_transitions, *initial_facts_, variable_domains_of_nodes);
				assert (transition != NULL);
				
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "Process the transition: " << *transition << std::endl;
#endif
//				std::cerr << "Yields: " << grounded_transitions.size() << " grounded transitions!" << std::endl;
				//negative_new_unprocessed_dtg->addTransition(*transition);
				for (std::vector<Transition*>::const_iterator ci = grounded_transitions.begin(); ci != grounded_transitions.end(); ++ci)
				{
					if (!negative_new_unprocessed_dtg->addTransition(**ci))
					{
//						std::cerr << "error adding grounded transition :(" << std::endl;
						delete *ci;
					}
				}
				
//				std::cerr << "Created node with " << negative_new_unprocessed_dtg->getTransitions().size() << " grounded transitions!" << std::endl;
				delete transition;
				delete &bounded_negative_atom;
			}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Resulting DTG: " << *new_unprocessed_dtg << std::endl;
#endif
		}
		
		delete possitive_atom;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_unsupported_predicates;
	gettimeofday(&end_time_unsupported_predicates, NULL);
	
	time_spend = end_time_unsupported_predicates.tv_sec - start_time_unsupported_predicates.tv_sec + (end_time_unsupported_predicates.tv_usec - start_time_unsupported_predicates.tv_usec) / 1000000.0;
	std::cerr << "Creating DTGs for unsupported predicates: " << time_spend << " seconds" << std::endl;
#endif
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "After creating all DTGs:" << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
#endif
	
	std::vector<const Object*> empty_object_set;
	for (unsigned int i = 0; i < objects_.size(); ++i)
	{
		if (objects_[i]->getPropertySpace() != NULL && objects_[i]->getPropertySpace()->isPropertySpace())
		{
			// Check which of the preconditions are part of property spaces and which are part of attribute spaces.
			std::vector<const Object*> objects_not_to_ground;
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = objects_[i]->getNodes().begin(); ci != objects_[i]->getNodes().end(); ++ci)
			{
				DomainTransitionGraphNode* node = *ci;
				
				for (std::vector<Transition*>::const_iterator ci = node->getTransitions().begin(); ci != node->getTransitions().end(); ++ci)
				{
					const Transition* transition = *ci;
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getAllPreconditions().begin(); ci != transition->getAllPreconditions().end(); ++ci)
					{
						const Atom* precondition = (*ci).first;
						std::vector<const DomainTransitionGraph*> supporting_dtgs;
						getDTGs(supporting_dtgs, transition->getStepId(), *precondition, bindings);
						
						//bool balanced = false;
						for (std::vector<const DomainTransitionGraph*>::const_iterator ci = supporting_dtgs.begin(); ci != supporting_dtgs.end(); ++ci)
						{
							if ((*ci)->getPropertySpace() != NULL && (*ci)->getPropertySpace()->isPropertySpace())
							{
								objects_not_to_ground.insert(objects_not_to_ground.end(), (*ci)->getPropertySpace()->getObjects().begin(), (*ci)->getPropertySpace()->getObjects().end());
							}
						}
					}
				}
			}
			
			objects_[i]->ground(objects_not_to_ground, *initial_facts_, *term_manager_);
		}
		else
		{
			objects_[i]->ground(empty_object_set, *initial_facts_, *term_manager_);
		}
		objects_[i]->setId(i);
		objects_[i]->split(*initial_facts_);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_generation;
	gettimeofday(&end_time_generation, NULL);
	
	time_spend = end_time_generation.tv_sec - start_time_tim_translation.tv_sec + (end_time_generation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "Initialize structures: " << time_spend << " seconds" << std::endl;
#endif

	std::cerr << "Number of bindings: " << bindings << std::endl;
	Graphviz::printToDot(*this);
}

void DomainTransitionGraphManager::getDTGs(std::vector<const DomainTransitionGraph*>& found_dtgs, StepID step_id, const Atom& atom, const Bindings& bindings, unsigned int index) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > dtg_nodes;
		(*ci)->getNodes(dtg_nodes, step_id, atom, bindings, index);

		if (dtg_nodes.size() > 0)
		{
			found_dtgs.push_back(*ci);
		}
	}
}

void DomainTransitionGraphManager::getDTGNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, StepID step_id, const Atom& atom, const Bindings& bindings, unsigned int index) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		///std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
		///(*ci)->getNodes(dtg_nodes, step_id, atom, bindings, index);
		///found_dtg_nodes.insert(found_dtg_nodes.end(), dtg_nodes.begin(), dtg_nodes.end());
		(*ci)->getNodes(found_dtg_nodes, step_id, atom, bindings, index);
	}
}

void DomainTransitionGraphManager::getDTGNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const Bindings& bindings) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
 	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		///std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
		///(*ci)->getNodes(dtg_nodes, initial_facts, bindings);
		///found_dtg_nodes.insert(found_dtg_nodes.end(), dtg_nodes.begin(), dtg_nodes.end());
		(*ci)->getNodes(found_dtg_nodes, initial_facts, bindings);
	}
}

};

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::Transition& transition, const Bindings& bindings)
{
	printToDot(ofs, transition.getFromNode());
	ofs << " -> ";
	printToDot(ofs, transition.getToNode());
	ofs << "[ label=\"";
	transition.getAction().print(ofs, bindings, transition.getStepId());
	for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition.getAllPreconditions().begin(); ci != transition.getAllPreconditions().end(); ++ci)
	{
			ofs << "\\n";
			(*ci).first->print(ofs, bindings, transition.getStepId());
	}
	ofs << "\"]" << std::endl;
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraphNode& dtg_node)
{
	ofs << "\"[" << &dtg_node << "](ID: " << dtg_node.getDTG().getId() << ")";
	for (std::vector<SAS_Plus::BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
	{
		(*ci)->print(ofs, dtg_node.getDTG().getBindings(), false);
		
		if (ci + 1 != dtg_node.getAtoms().end())
		{
			ofs << "\\n";
		}
	}
	ofs << "\"";
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg)
{
	// Declare the nodes.
	for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = dtg.getNodes().begin(); ci != dtg.getNodes().end(); ci++)
	{
		const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
		printToDot(ofs, *dtg_node);
		ofs << std::endl;
		
		// Create a dotted lines if this node is a copy of another.
		if (dtg_node->getCopy() != NULL)
		{
			printToDot(ofs, *dtg_node);
			ofs << " -> ";
			printToDot(ofs, *dtg_node->getCopy());
			ofs << " [style=dotted];" << std::endl;
		}
	}
	
	// Create the edges.
	for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = dtg.getNodes().begin(); ci != dtg.getNodes().end(); ci++)
	{
		const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
		const std::vector<SAS_Plus::Transition*>& transitions = dtg_node->getTransitions();

		for (std::vector<SAS_Plus::Transition*>::const_iterator transitions_ci = transitions.begin(); transitions_ci != transitions.end(); transitions_ci++)
		{
			const SAS_Plus::Transition* transition = *transitions_ci;
			printToDot(ofs, *transition, dtg.getBindings());
		}
	}
}

void Graphviz::printToDot(const SAS_Plus::DomainTransitionGraphManager& dtg_manager)
{
	std::ofstream ofs;
	ofs.open("dtgs.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = dtg_manager.getManagableObjects().begin(); ci != dtg_manager.getManagableObjects().end(); ci++)
	{
		Graphviz::printToDot(ofs, **ci);
	}
	
	ofs << "}" << std::endl;
	ofs.close();
}

void Graphviz::printPredicatesToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg)
{
		const std::vector<const MyPOP::SAS_Plus::Property*>& predicates = dtg.getPredicates();
		
		ofs << "\"[" << dtg.getId() << "] ";
		for (std::vector<const MyPOP::SAS_Plus::Property*>::const_iterator pred_ci = predicates.begin(); pred_ci != predicates.end(); pred_ci++)
		{
			ofs << (*pred_ci)->getPredicate();
			if (pred_ci + 1 != predicates.end())
			{
				ofs << ", ";
			}
		}
		ofs << "\"";
}

};
