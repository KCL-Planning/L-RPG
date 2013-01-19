#include "lifted_dtg.h"

#include <fstream>

#include "../VALfiles/ptree.h"
#include "../VALfiles/SASActions.h"
#include "../VALfiles/ToFunction.h"
#include "../action_manager.h"
#include "../plan_bindings.h"
#include "../formula.h"
#include "../term_manager.h"
#include "../predicate_manager.h"
#include "heuristics/fact_set.h"
#include "property_space.h"
#include <type_manager.h>
#include <parser_utils.h>

//#define MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT

namespace MyPOP
{
namespace SAS_Plus
{

MultiValuedTransition::MultiValuedTransition(const Action& action, MultiValuedValue& precondition, MultiValuedValue& effect, const std::vector<std::vector<unsigned int>* >& precondition_to_action_variable_mappings, const std::vector<std::vector<unsigned int>* >& effect_to_action_variable_mappings, const TypeManager& type_manager)
	: action_(&action), precondition_(&precondition), effect_(&effect), precondition_to_action_variable_mappings_(&precondition_to_action_variable_mappings), effect_to_action_variable_mappings_(&effect_to_action_variable_mappings)
{
	assert (precondition_->getValues().size() == precondition_to_action_variable_mappings_->size());
	assert (effect_->getValues().size() == effect_to_action_variable_mappings_->size());

	for (unsigned int action_variable_index = 0; action_variable_index < action.getVariables().size(); ++action_variable_index)
	{
		std::vector<const Object*> objects_in_variable_domain;
		type_manager.getObjectsOfType(objects_in_variable_domain, *action.getVariables()[action_variable_index]->getType());
		HEURISTICS::VariableDomain* new_variable_domain = new HEURISTICS::VariableDomain(objects_in_variable_domain);
		action_variable_domains_.push_back(new_variable_domain);
	}
	
	// Update the variable domains based on the preconditions and effects.
	for (unsigned int precondition_index = 0; precondition_index < precondition_to_action_variable_mappings.size(); ++precondition_index)
	{
		std::vector<unsigned int>* links_to_action_variables = precondition_to_action_variable_mappings[precondition_index];
		if (links_to_action_variables == NULL)
		{
			// Search for a fact in the to node that is identical to the ith precondition.
			const HEURISTICS::Fact* persitent_precondition = precondition.getValues()[precondition_index];
			for (std::vector<HEURISTICS::Fact*>::const_iterator ci = effect.getValues().begin(); ci != effect.getValues().end(); ++ci)
			{
				const HEURISTICS::Fact* fact = *ci;
				if (*persitent_precondition == *fact)
				{
					persitent_precondition_to_effect_mappings_.push_back(std::make_pair(precondition_index, std::distance(effect.getValues().begin(), ci)));
				}
			}
			continue;
		}
		for (unsigned int term_index = 0; term_index < links_to_action_variables->size(); ++term_index)
		{
			const HEURISTICS::VariableDomain* precondition_variable_domain = precondition.getValues()[precondition_index]->getVariableDomains()[term_index];
			HEURISTICS::VariableDomain* action_variable_domain = action_variable_domains_[(*links_to_action_variables)[term_index]];
			
			HEURISTICS::VariableDomain updated_action_variable_domain;
			action_variable_domain->getIntersection(updated_action_variable_domain, *precondition_variable_domain);
			action_variable_domain->set(updated_action_variable_domain.getVariableDomain());
		}
	}
	
	for (unsigned int effect_index = 0; effect_index < effect_to_action_variable_mappings.size(); ++effect_index)
	{
		std::vector<unsigned int>* links_to_action_variables = effect_to_action_variable_mappings[effect_index];
		if (links_to_action_variables == NULL)
		{
			continue;
		}
		for (unsigned int term_index = 0; term_index < links_to_action_variables->size(); ++term_index)
		{
			const HEURISTICS::VariableDomain* effect_variable_domain = effect.getValues()[effect_index]->getVariableDomains()[term_index];
			HEURISTICS::VariableDomain* action_variable_domain = action_variable_domains_[(*links_to_action_variables)[term_index]];
			
			HEURISTICS::VariableDomain updated_action_variable_domain;
			action_variable_domain->getIntersection(updated_action_variable_domain, *effect_variable_domain);
			action_variable_domain->set(updated_action_variable_domain.getVariableDomain());
		}
	}
}

MultiValuedTransition::~MultiValuedTransition()
{
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = precondition_to_action_variable_mappings_->begin(); ci != precondition_to_action_variable_mappings_->end(); ++ci)
	{
		delete *ci;
	}
	
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = effect_to_action_variable_mappings_->begin(); ci != effect_to_action_variable_mappings_->end(); ++ci)
	{
		delete *ci;
	}
	
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_domains_.begin(); ci != action_variable_domains_.end(); ++ci)
	{
		delete *ci;
	}
	
	delete precondition_to_action_variable_mappings_;
	delete effect_to_action_variable_mappings_;
}

bool MultiValuedTransition::isPreconditionIgnored(const Atom& precondition) const
{
	return std::find(preconditions_to_ignore_.begin(), preconditions_to_ignore_.end(), &precondition) != preconditions_to_ignore_.end();
}

bool MultiValuedTransition::isEffectIgnored(const Atom& effect) const
{
	return std::find(effects_to_ignore_.begin(), effects_to_ignore_.end(), &effect) != effects_to_ignore_.end();
}

void MultiValuedTransition::ignorePrecondition(const Atom& precondition)
{
	preconditions_to_ignore_.push_back(&precondition);
}

void MultiValuedTransition::ignoreEffect(const Atom& effect)
{
	effects_to_ignore_.push_back(&effect);
}

MultiValuedTransition* MultiValuedTransition::migrateTransition(MultiValuedValue& from_node, MultiValuedValue& to_node, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager) const
{
	std::cout << "Migrate the transition: " << *this << std::endl;
	std::cout << "From: " << from_node << std::endl;
	std::cout << "To: " << to_node << std::endl;
	std::vector<std::vector<unsigned int>* >* precondition_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
	std::vector<std::vector<unsigned int>* >* effect_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
	
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = precondition_to_action_variable_mappings_->begin(); ci != precondition_to_action_variable_mappings_->end(); ++ci)
	{
		if (*ci != NULL)
		{
			precondition_to_action_variable_mappings->push_back(new std::vector<unsigned int>(**ci));
		}
		else
		{
			precondition_to_action_variable_mappings->push_back(NULL);
		}
	}
	
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = effect_to_action_variable_mappings_->begin(); ci != effect_to_action_variable_mappings_->end(); ++ci)
	{
		if (*ci != NULL)
		{
			effect_to_action_variable_mappings->push_back(new std::vector<unsigned int>(**ci));
		}
		else
		{
			effect_to_action_variable_mappings->push_back(NULL);
		}
	}
	
	MultiValuedTransition* transition = new MultiValuedTransition(*action_, from_node, to_node, *precondition_to_action_variable_mappings, *effect_to_action_variable_mappings, type_manager);
	
	// Check that no static preconditions are violated.
//	bool all_static_precondition_statisfied = true;
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &transition->action_->getPrecondition());
	
	// Update the variable domains such that they conform to the static facts in the initial state.
	bool variable_domains_finished_updating = false;
	while (!variable_domains_finished_updating)
	{
		variable_domains_finished_updating = true;
	
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
		{
			const Atom* precondition = *ci;
			if (!precondition->getPredicate().isStatic())
			{
				continue;
			}
			
			std::vector<const HEURISTICS::VariableDomain*> precondition_variable_domains;
			std::vector<HEURISTICS::VariableDomain*> possible_precondition_variable_domains;
			for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ++ci)
			{
				const Term* precondition_term = *ci;
				possible_precondition_variable_domains.push_back(new HEURISTICS::VariableDomain());
				//for (std::vector<const Variable*>::const_iterator ci = transition->action_->getVariables().begin(); ci != transition->action_->getVariables().end(); ++ci)
				for (unsigned int action_variable_index = 0; action_variable_index < transition->action_->getVariables().size(); ++action_variable_index)
				{
					if (precondition_term == transition->action_->getVariables()[action_variable_index])
					{
						precondition_variable_domains.push_back(transition->action_variable_domains_[action_variable_index]);
						break;
					}
				}
			}
			
			// Check if the precondition is backed by one of the facts in the initial state.
//			bool found_matching_initial_fact = false;
			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
			{
				const Atom* initial_fact = *ci;
				if (initial_fact->getArity() != precondition->getArity() ||
					initial_fact->getPredicate().getName() != precondition->getPredicate().getName())
				{
					continue;
				}
				
				bool terms_match = true;
				for (unsigned int term_index = 0; term_index < initial_fact->getArity(); ++term_index)
				{
					if (!precondition_variable_domains[term_index]->contains(*static_cast<const Object*>(initial_fact->getTerms()[term_index])))
					{
						terms_match = false;
						break;
					}
				}
				
				if (!terms_match)
				{
					continue;
				}
				
				for (unsigned int term_index = 0; term_index < initial_fact->getArity(); ++term_index)
				{
					if (!possible_precondition_variable_domains[term_index]->contains(*static_cast<const Object*>(initial_fact->getTerms()[term_index])))
					{
						possible_precondition_variable_domains[term_index]->addObject(*static_cast<const Object*>(initial_fact->getTerms()[term_index]));
					}
				}
				
//				found_matching_initial_fact = true;
//				break;
			}
			
			// Update the action variables.
			for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ++ci)
			{
				const Term* precondition_term = *ci;
				unsigned int precondition_term_index = std::distance(precondition->getTerms().begin(), ci);
				
				//for (std::vector<const Variable*>::const_iterator ci = transition->action_->getVariables().begin(); ci != transition->action_->getVariables().end(); ++ci)
				for (unsigned int action_variable_index = 0; action_variable_index < transition->action_->getVariables().size(); ++action_variable_index)
				{
					if (precondition_term == transition->action_->getVariables()[action_variable_index])
					{
						unsigned int pre_size = transition->action_variable_domains_[action_variable_index]->size();
						HEURISTICS::VariableDomain intersection;
						transition->action_variable_domains_[action_variable_index]->getIntersection(intersection, *possible_precondition_variable_domains[precondition_term_index]);
						transition->action_variable_domains_[action_variable_index]->set(intersection.getVariableDomain());
						
						if (transition->action_variable_domains_[action_variable_index]->size() != pre_size)
						{
							variable_domains_finished_updating = false;
						}
						break;
					}
				}
			}
			
			for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = possible_precondition_variable_domains.begin(); ci != possible_precondition_variable_domains.end(); ++ci)
			{
				delete *ci;
			}
/*
			if (!found_matching_initial_fact)
			{
				all_static_precondition_statisfied = false;
				break;
			}
*/
		}
	}
/*
	if (!all_static_precondition_statisfied)
	{
		delete transition;
		return NULL;
	}
*/
	// Any fact in the from node that is not affected must be present in the to node. Any fact in the to node that is not affected by an effect
	// must be present in the from node and not affected in any way.
	for (std::vector<std::vector<unsigned int>* >::iterator ci = precondition_to_action_variable_mappings->begin(); ci != precondition_to_action_variable_mappings->end(); ++ci)
	{
		unsigned int precondition_index = std::distance(precondition_to_action_variable_mappings->begin(), ci);
		if (*ci == NULL)
		{
			bool found_matching_to_node = false;
			
			HEURISTICS::Fact* precondition = from_node.getValues()[precondition_index];
			
			// Check if a similar fact exists in the to node.
			for (std::vector<std::vector<unsigned int>* >::iterator ci = effect_to_action_variable_mappings->begin(); ci != effect_to_action_variable_mappings->end(); ++ci)
			{
				unsigned int effect_index = std::distance(effect_to_action_variable_mappings->begin(), ci);
				if (*ci == NULL)
				{
					HEURISTICS::Fact* effect = to_node.getValues()[effect_index];
					
					if (precondition->getPredicate().getArity() != effect->getPredicate().getArity() ||
					    precondition->getPredicate().getName() != effect->getPredicate().getName())
					{
						continue;
					}
					
					bool terms_match = true;
					for (unsigned int term_index = 0; term_index < effect->getPredicate().getArity(); ++term_index)
					{
						if (!precondition->getVariableDomains()[term_index]->sharesObjectsWith(*effect->getVariableDomains()[term_index]))
						{
							terms_match = false;
							break;
						}
					}
					
					if (terms_match)
					{
						found_matching_to_node = true;
						break;
					}
				}
			}
			
			if (!found_matching_to_node)
			{
//				std::cout << "Missing " << *precondition << std::endl;
				delete transition;
				return NULL;
			}
		}
	}
	
	// Check that none of the action variables are empty.
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = transition->action_variable_domains_.begin(); ci != transition->action_variable_domains_.end(); ++ci)
	{
		if ((*ci)->getVariableDomain().empty())
		{
//			std::cout << "Empty variable domain!" << std::endl;
			delete transition;
			return NULL;
		}
	}
	
//	std::cout << "From node: " << from_node << std::endl;
//	std::cout << "To node: " << to_node << std::endl;
//	std::cout << "New transition: " << *transition << std::endl;
	
	return transition;
}

const HEURISTICS::Fact* MultiValuedTransition::getEffectPersistentWith(const HEURISTICS::Fact& precondition) const
{
	for (unsigned int precondition_index = 0; precondition_index < precondition_->getValues().size(); ++precondition_index)
	{
		if (precondition_->getValues()[precondition_index] == &precondition)
		{
			for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = persitent_precondition_to_effect_mappings_.begin(); ci != persitent_precondition_to_effect_mappings_.end(); ++ci)
			{
				std::pair<unsigned int, unsigned int> persistent_set = *ci;
				if (persistent_set.first == precondition_index)
				{
					return effect_->getValues()[persistent_set.second];
				}
			}
		}
	}
	return NULL;
}

const HEURISTICS::Fact* MultiValuedTransition::getPreconditionPersistentWith(const HEURISTICS::Fact& effect) const
{
	for (unsigned int effect_index = 0; effect_index < effect_->getValues().size(); ++effect_index)
	{
		if (effect_->getValues()[effect_index] == &effect)
		{
			for (std::vector<std::pair<unsigned int, unsigned int> >::const_iterator ci = persitent_precondition_to_effect_mappings_.begin(); ci != persitent_precondition_to_effect_mappings_.end(); ++ci)
			{
				std::pair<unsigned int, unsigned int> persistent_set = *ci;
				if (persistent_set.second == effect_index)
				{
					return precondition_->getValues()[persistent_set.first];
				}
			}
		}
	}
	return NULL;
}

std::ostream& operator<<(std::ostream& os, const MultiValuedTransition& transition)
{
	os << *transition.action_ << " ";
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = transition.action_variable_domains_.begin(); ci != transition.action_variable_domains_.end(); ++ci)
	{
		os << **ci << " ";
	}
	os << std::endl;
	os << "Preconditions:" << std::endl;
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = transition.precondition_->getValues().begin(); ci != transition.precondition_->getValues().end(); ++ci)
	{
		unsigned int precondition_index = std::distance(transition.precondition_->getValues().begin(), ci);
		os << "* " << **ci << std::endl;
		std::vector<unsigned int>* mappings = (*transition.precondition_to_action_variable_mappings_)[precondition_index];
		if (mappings == NULL)
		{
			os << "No bindings!";
		}
		else
		{
			for (std::vector<unsigned int>::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
			{
				os << *ci << ", ";
			}
		}
		os << std::endl;
	}
	
	os << "Effects:" << std::endl;
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = transition.effect_->getValues().begin(); ci != transition.effect_->getValues().end(); ++ci)
	{
		unsigned int effects_index = std::distance(transition.effect_->getValues().begin(), ci);
		os << "* " << **ci << std::endl;
		std::vector<unsigned int>* mappings = (*transition.effect_to_action_variable_mappings_)[effects_index];
		if (mappings == NULL)
		{
			os << "No bindings!";
		}
		else
		{
			for (std::vector<unsigned int>::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
			{
				os << *ci << ", ";
			}
		}
		os << std::endl;
	}
	
	return os;
}

	
MultiValuedValue::MultiValuedValue(const LiftedDTG& lifted_dtg, std::vector<HEURISTICS::Fact*>& values, const PropertyState& property_state, bool is_copy)
	: lifted_dtg_(&lifted_dtg), values_(&values), property_state_(&property_state), is_copy_(is_copy)
{

}

MultiValuedValue::MultiValuedValue(const LiftedDTG& lifted_dtg, const MultiValuedValue& other, bool is_copy)
	: lifted_dtg_(&lifted_dtg), property_state_(other.property_state_), is_copy_(is_copy)
{
	values_ = new std::vector<HEURISTICS::Fact*>();
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = other.getValues().begin(); ci != other.getValues().end(); ++ci)
	{
		values_->push_back(new HEURISTICS::Fact(**ci));
	}
}
	
MultiValuedValue::~MultiValuedValue()
{
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = values_->begin(); ci != values_->end(); ++ci)
	{
		delete *ci;
	}
	delete values_;
	
		
	for (std::vector<const MultiValuedTransition*>::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ++ci)
	{
		delete *ci;
	}
}

void MultiValuedValue::findMappings(std::vector<std::vector<const HEURISTICS::Fact*>* >& found_mappings, const std::vector<const HEURISTICS::Fact*>& facts, const PredicateManager& predicate_manager) const
{
	std::vector<const HEURISTICS::Fact*> current_mappings;
	const HEURISTICS::VariableDomain invariable_domain(property_state_->getPropertySpace().getObjects());
	
	findMappings(found_mappings, current_mappings, invariable_domain, facts, predicate_manager);
}

void MultiValuedValue::findMappings(std::vector<std::vector<const HEURISTICS::Fact*>* >& found_mappings, const std::vector<const HEURISTICS::Fact*>& current_mappings, const HEURISTICS::VariableDomain& invariable_domain, const std::vector<const HEURISTICS::Fact*>& facts, const PredicateManager& predicate_manager) const
{
	unsigned int fact_index = current_mappings.size();
	
	// Found a full assignment!
	if (fact_index == getValues().size())
	{
		std::vector<const HEURISTICS::Fact*>* new_found_mapping = new std::vector<const HEURISTICS::Fact*>();
		for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = current_mappings.begin(); ci != current_mappings.end(); ++ci)
		{
			const HEURISTICS::Fact* grounded_atom = *ci;
			std::vector<const HEURISTICS::VariableDomain*> variable_domains;
			for (unsigned int i = 0; i < grounded_atom->getPredicate().getArity(); ++i)
			{
				HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
				vd->set(grounded_atom->getVariableDomains()[i]->getVariableDomain());
				variable_domains.push_back(vd);
			}
			new_found_mapping->push_back(new HEURISTICS::Fact(predicate_manager, grounded_atom->getPredicate(), variable_domains));
			
			for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = variable_domains.begin(); ci != variable_domains.end(); ++ci)
			{
				delete *ci;
			}
		}
		found_mappings.push_back(new_found_mapping);
		return;
	}
	
	const HEURISTICS::Fact* fact = getValues()[fact_index];
	const SAS_Plus::Property* property = getPropertyState().getProperties()[fact_index];
	
	// Check which facts from the state can be mapped to this fact.
	for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = facts.begin(); ci != facts.end(); ++ci)
	{
		const HEURISTICS::Fact* initial_fact = *ci;
		if (!fact->canUnifyWith(*initial_fact))
		{
			continue;
		}
		
		// Check if the invariable matches as well.
		HEURISTICS::VariableDomain new_invariable_domain;
		if (property->getIndex() != std::numeric_limits<unsigned int>::max())
		{
			invariable_domain.getIntersection(new_invariable_domain, *initial_fact->getVariableDomains()[property->getIndex()]);
			
			if (new_invariable_domain.getVariableDomain().empty())
			{
				continue;
			}
		}
		else
		{
			new_invariable_domain.set(invariable_domain.getVariableDomain());
		}
		
		// Found an assignment!
		std::vector<const HEURISTICS::Fact*> new_current_mappings(current_mappings);
		new_current_mappings.push_back(initial_fact);
		if (property->getIndex() != std::numeric_limits<unsigned int>::max())
		{
			new_invariable_domain.set(initial_fact->getVariableDomains()[property->getIndex()]->getVariableDomain());
			findMappings(found_mappings, new_current_mappings, new_invariable_domain, facts, predicate_manager);
		}
		else
		{
			findMappings(found_mappings, new_current_mappings, new_invariable_domain, facts, predicate_manager);
		}
	}
}

void MultiValuedValue::addTransition(const MultiValuedTransition& transition)
{
	transitions_.push_back(&transition);
}

void MultiValuedValue::split(std::vector<MultiValuedValue*>& split_nodes, const std::multimap<const Object*, const Object*>& equivalent_relationships, const PredicateManager& predicate_manager) const
{
	// Check if all the variable domains of the facts are coherent with the found equivalent relationships. If not then we will need to split them up.
	std::vector<const HEURISTICS::VariableDomain*> dummy_assignments_made;
	findAssignments(0, 0, split_nodes, dummy_assignments_made, equivalent_relationships, predicate_manager);
	
	std::cout << "========= START SPLIT =============" << std::endl;
	std::cout << "NODE: " << std::endl << *this << std::endl;
	std::cout << "Is split into: " << std::endl;
	for (std::vector<MultiValuedValue*>::const_iterator ci = split_nodes.begin(); ci != split_nodes.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
	std::cout << "========= END SPLIT =============" << std::endl;
}

void MultiValuedValue::findAssignments(unsigned int fact_index, unsigned int term_index, std::vector<MultiValuedValue*>& created_nodes, std::vector<const HEURISTICS::VariableDomain*>& assignments_made, const std::multimap<const Object*, const Object*>& equivalent_relationships, const PredicateManager& predicate_manager) const
{
	unsigned int total_facts = 0;
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = values_->begin(); ci != values_->end(); ++ci)
	{
		const HEURISTICS::Fact* value = *ci;
		total_facts += value->getVariableDomains().size();
	}
	
	// Found a full assignment!
	if (total_facts == assignments_made.size())
	{
		unsigned int index = 0;
		std::vector<HEURISTICS::Fact*>* new_nodes = new std::vector<HEURISTICS::Fact*>();
		
		HEURISTICS::VariableDomain invariable_domain(lifted_dtg_->getInvariableObjects());
		
		for (unsigned int fact_index = 0; fact_index < values_->size(); ++fact_index)
		{
			const HEURISTICS::Fact* value = (*values_)[fact_index];
			std::vector<const HEURISTICS::VariableDomain*>* new_fact_assignments = new std::vector<const HEURISTICS::VariableDomain*>();
			for (unsigned int assignments_made_index = 0; assignments_made_index < value->getPredicate().getArity(); ++assignments_made_index)
			{
				new_fact_assignments->push_back(new HEURISTICS::VariableDomain(assignments_made[index + assignments_made_index]->getVariableDomain()));
			}
			index += value->getPredicate().getArity();
			
			// Check if the invariable domain is respected.
			const SAS_Plus::Property* property = property_state_->getProperties()[fact_index];
			if (property->getIndex() != std::numeric_limits<unsigned int>::max())
			{
				const HEURISTICS::VariableDomain* vd = (*new_fact_assignments)[property->getIndex()];
				HEURISTICS::VariableDomain intersection;
				invariable_domain.getIntersection(intersection, *vd);
				
				if (intersection.getVariableDomain().empty())
				{
					return;
				}
				
				invariable_domain.set(intersection.getVariableDomain());
			}
			
			HEURISTICS::Fact* new_fact = new HEURISTICS::Fact(predicate_manager, value->getPredicate(), *new_fact_assignments);
			new_nodes->push_back(new_fact);
		}
		
		MultiValuedValue* mvv = new MultiValuedValue(*lifted_dtg_, *new_nodes, *property_state_, is_copy_);
		created_nodes.push_back(mvv);
		return;
	}
	
	const HEURISTICS::VariableDomain* vd = (*values_)[fact_index]->getVariableDomains()[term_index];
	std::set<const Object*> closed_list;
	for (std::vector<const Object*>::const_iterator ci = vd->getVariableDomain().begin(); ci != vd->getVariableDomain().end(); ++ci)
	{
		const Object* object = *ci;
		if (closed_list.find(object) != closed_list.end())
		{
			continue;
		}
		
		std::vector<const Object*> new_variable_domain;
		
		// Search for every other object that is equivalent to this one.
		for (std::vector<const Object*>::const_iterator ci = vd->getVariableDomain().begin(); ci != vd->getVariableDomain().end(); ++ci)
		{
			const Object* other_object = *ci;
			
			std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> equivalent_ci = equivalent_relationships.equal_range(object);
			
			bool is_equivalent_to_object = false;
			for (std::multimap<const Object*, const Object*>::const_iterator ci = equivalent_ci.first; ci != equivalent_ci.second; ++ci)
			{
				if ((*ci).second == other_object)
				{
					is_equivalent_to_object = true;
					break;
				}
			}
			
			if (is_equivalent_to_object)
			{
				new_variable_domain.push_back(other_object);
				closed_list.insert(other_object);
			}
		}
		
		unsigned int new_fact_index, new_term_index;
		
		if (term_index + 1 == (*values_)[fact_index]->getVariableDomains().size())
		{
			new_term_index = 0;
			new_fact_index = fact_index + 1;
		}
		else
		{
			new_term_index = term_index + 1;
			new_fact_index = fact_index;
		}
		
		HEURISTICS::VariableDomain vd(new_variable_domain);
		std::vector<const HEURISTICS::VariableDomain*> new_assignments_made(assignments_made);
		new_assignments_made.push_back(&vd);
		
		findAssignments(new_fact_index, new_term_index, created_nodes, new_assignments_made, equivalent_relationships, predicate_manager);
	}
}

void MultiValuedValue::addCopy(MultiValuedValue& copy)
{
	created_copies_.push_back(&copy);
}

void MultiValuedValue::printFacts(std::ostream& os) const
{
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = values_->begin(); ci != values_->end(); ++ci)
	{
		os << **ci << std::endl;
	}
}

std::ostream& operator<<(std::ostream& os, const MultiValuedValue& value)
{
	os << " === VALUE === " << std::endl;
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = value.values_->begin(); ci != value.values_->end(); ++ci)
	{
		os << **ci << std::endl;
	}
/*
	for (std::vector<const MultiValuedTransition*>::const_iterator ci = value.transitions_.begin(); ci != value.transitions_.end(); ++ci)
	{
		os << **ci << std::endl;
	}
*/
	return os;
}

void LiftedDTG::getProperties(const PredicateManager& predicate_manager, std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state)
{
	for (std::multiset<TIM::Property*>::const_iterator lhs_properties_i = property_state.begin(); lhs_properties_i != property_state.end(); lhs_properties_i++)
	{
		const TIM::Property* property = *lhs_properties_i;

		const VAL::extended_pred_symbol* extended_property = property->root();
		const Predicate* predicate = predicate_manager.getGeneralPredicate(extended_property->getName());
		assert (predicate != NULL);

		// Adding the predicate to the DTG will also create a lifted DTG node with that predicate.
		// Further refinements can be made to this DTG by splitting these nodes.
		predicates.push_back(std::make_pair(predicate, property->aPosn()));
	}
}

//std::vector<LiftedDTG*> LiftedDTG::all_lifted_dtgs_;

void LiftedDTG::createLiftedDTGs(std::vector< LiftedDTG* >& created_lifted_dtgs, const VAL::pddl_type_list& types, const PredicateManager& predicate_manager, const TypeManager& type_manager, const ActionManager& action_manager, const TermManager& term_manager, const std::vector<const Atom* >& initial_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval start_time_tim_translation;
	gettimeofday(&start_time_tim_translation, NULL);
#endif
	// Store temporary DTGs in this vector, during post processing they might get split again. Only then will we add the DTGs as a managable object (see Manager class).
	std::vector<TIM::PropertySpace*> property_spaces;
	property_spaces.insert(property_spaces.end(), TIM::TA->pbegin(), TIM::TA->pend());
	
	std::set<const Predicate*> state_valued_predicates;

	std::vector<PropertySpace*> all_property_spaces_;
	
	// Construct the DTGs by combining all properties which appear together in either the LHS or RHS of a transition rule.
	for (std::vector<TIM::PropertySpace*>::const_iterator property_space_i = property_spaces.begin(); property_space_i != property_spaces.end(); ++property_space_i)
	{
		TIM::PropertySpace* property_space = *property_space_i;
		SAS_Plus::PropertySpace& dtg_property_space = SAS_Plus::PropertySpace::createPropertySpace(term_manager, property_space->obegin(), property_space->oend());
		
		std::map<std::vector<std::pair<const Predicate*, unsigned int> >, PropertyState* > processed_expressions;

		// We need to augment some rules to get the full set of properties. If a property appears in the LHS of a rule $a$ and it is a proper subset
		// of another LHS $b$. Then add a new rule $b$ -> ($b.LHS$ \ $a.LHS$) + $a.RHS$.
		for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
		{
			TIM::TransitionRule* rule_a = *rules_i;
			
			// Combine the property states who appear in either the LHS of RHS of this rule.
			std::vector<std::pair<const Predicate*, unsigned int> > predicates_rule_a;
			getProperties(predicate_manager, predicates_rule_a, *rule_a->getLHS());

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
					getProperties(predicate_manager, predicates_rhs, *rule_a->getRHS());

					std::multiset<TIM::Property*> duplicates;
					std::set_intersection(rule_a->getRHS()->begin(), rule_a->getRHS()->end(), rule_b->getLHS()->begin(), rule_b->getLHS()->end(), std::inserter(duplicates, duplicates.begin()));
					
					for (std::multiset<TIM::Property*>::const_iterator ci = difference.begin(); ci != difference.end(); ci++)
					{
						TIM::Property* property = *ci;
						const VAL::extended_pred_symbol* extended_property = property->root();
						const Predicate* predicate = predicate_manager.getGeneralPredicate(extended_property->getName());
						assert (predicate != NULL);
						
						// Make sure we do not add duplicates:
						if (duplicates.count(property) != 0)
						{
							continue;
						}

						predicates_rhs.push_back(std::make_pair(predicate, property->aPosn()));
					}
					
					if (processed_expressions.count(predicates_rhs) == 0)
					{
						PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates_rhs);
						dtg_property_space.addPropertyState(*new_property_state);
						processed_expressions[predicates_rhs] = new_property_state;
						
						// We no longer need to process the LHS and RHS of rule_a, since it has been substituted by this rule.
						std::vector<std::pair<const Predicate*, unsigned int> > rule_a_rhs;
						getProperties(predicate_manager, rule_a_rhs, *rule_a->getRHS());
						processed_expressions[predicates_rule_a] = new_property_state;
						processed_expressions[rule_a_rhs] = new_property_state;
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
			getProperties(predicate_manager, predicates, *rule->getLHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				// TODO: Memory leak.
				PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates);
				dtg_property_space.addPropertyState(*new_property_state);
				processed_expressions[predicates] = new_property_state;
			}
			
			predicates.clear();
			getProperties(predicate_manager, predicates, *rule->getRHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				// TODO: Memory leak.
				PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates);
				dtg_property_space.addPropertyState(*new_property_state);
				processed_expressions[predicates] = new_property_state;
			}
		}
		
		dtg_property_space.addTransitions(predicate_manager, type_manager, action_manager, property_space->getRules());
	
		// Check if there is another property space with the same type.
		bool is_merged = false;

		for (std::vector<PropertySpace*>::reverse_iterator ri = all_property_spaces_.rbegin(); ri != all_property_spaces_.rend(); ++ri)
		{
			PropertySpace* processed_property_space = *ri;
			PropertySpace* merged_property_space = PropertySpace::merge(dtg_property_space, *processed_property_space);
			if (merged_property_space != NULL)
			{
				is_merged = true;
				all_property_spaces_.erase(ri.base() - 1);
				all_property_spaces_.push_back(merged_property_space);
				
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
				std::cout << "Merged: " << *merged_property_space << std::endl;
#endif
				
				break;
			}
		}

		if (!is_merged)
		{
			all_property_spaces_.push_back(&dtg_property_space);
		}
	}
	
	std::set<const Object*> objects_part_of_property_spaces;
	for (std::vector<PropertySpace*>::const_iterator ci = all_property_spaces_.begin(); ci != all_property_spaces_.end(); ++ci)
	{
		LiftedDTG* new_ldtg = new LiftedDTG(predicate_manager, type_manager, **ci);
		objects_part_of_property_spaces.insert(new_ldtg->property_space_->getObjects().begin(), new_ldtg->property_space_->getObjects().end());
		created_lifted_dtgs.push_back(new_ldtg);
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
		std::cout << "New LTG: " << std::endl << *new_ldtg << std::endl;
#endif
	}
	
	// Create the lifted DTGs for those predicates which have not been processed yet.
	for (std::vector<Predicate*>::const_iterator ci = predicate_manager.getManagableObjects().begin(); ci != predicate_manager.getManagableObjects().end(); ci++)
	{
		const Predicate* predicate = *ci;
		if (predicate->isStatic())
		{
			continue;
		}
		
		bool is_supported = false;
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "Check if the predicate : " << *predicate << " is supported!" << std::endl;
#endif
		for (std::vector<PropertySpace*>::const_iterator ci = all_property_spaces_.begin(); ci != all_property_spaces_.end(); ++ci)
		{
			const PropertySpace* property_space = *ci;
			for (std::vector<PropertyState*>::const_iterator ci = property_space->getPropertyStates().begin(); ci != property_space->getPropertyStates().end(); ++ci)
			{
				const PropertyState* property_state = *ci;
				for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
				{
					const Property* property = *ci;
					const Predicate& state_valued_predicate = property->getPredicate();
					if (&state_valued_predicate == predicate ||
							state_valued_predicate.canSubstitute(*predicate))
					{
						is_supported = true;
						break;
					}
				}
				if (is_supported)
				{
					break;
				}
			}
			if (is_supported)
			{
				break;
			}
		}
		
		if (is_supported) continue;
		
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
		std::cerr << "Unsupported predicate: " << *predicate << std::endl;
#endif
		
		// Create an attribute space.
		PropertySpace& attribute_space = PropertySpace::createAttributeSpace();
		
		PropertyState* property_state = new PropertyState(attribute_space);
		attribute_space.addPropertyState(*property_state);
		Property* property = new Property(*property_state, *predicate, std::numeric_limits<unsigned int>::max());
		property_state->addProperty(*property);
		
		PropertyState* empty_property_state = new PropertyState(attribute_space);
		attribute_space.addPropertyState(*empty_property_state);
		
		for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ++ci)
		{
			const Action* action = *ci;
			for (std::vector<const Atom*>::const_iterator ci = action->getEffects().begin(); ci != action->getEffects().end(); ++ci)
			{
				const Atom* effect = *ci;
				if (effect->isNegative())
				{
					continue;
				}
				
				if (effect->getArity() != predicate->getArity() ||
				    effect->getPredicate().getName() != predicate->getName())
				{
					continue;
				}
				
				std::vector<unsigned int>* effect_variable_mapping = new std::vector<unsigned int>();
				bool types_match = true;
				
				
				std::vector<HEURISTICS::VariableDomain*> tmp_action_variable_to_effect_mappings;
				for (std::vector<const Variable*>::const_iterator ci = action->getVariables().begin(); ci != action->getVariables().end(); ++ci)
				{
					std::vector<const Object*> variable_domain;
					type_manager.getObjectsOfType(variable_domain, *(*ci)->getType());
					tmp_action_variable_to_effect_mappings.push_back(new HEURISTICS::VariableDomain(variable_domain));
				}
				
				for (unsigned int term_index = 0; term_index < effect->getArity(); ++term_index)
				{
					const Type* effect_type = effect->getTerms()[term_index]->getType();
					const Type* predicate_type = predicate->getTypes()[term_index];
					
					if (!effect_type->isEqual(*predicate_type) && !effect_type->isSubtypeOf(*predicate_type) && !effect_type->isSupertypeOf(*predicate_type))
					{
						types_match = false;
						break;
					}
					
					// Find matching action variable and update the variable domain.
					for (unsigned int action_variable_index = 0; action_variable_index < action->getVariables().size(); ++action_variable_index)
					{
						if (action->getVariables()[action_variable_index] == effect->getTerms()[term_index])
						{
							effect_variable_mapping->push_back(action_variable_index);
							
							std::vector<const Object*> effect_objects;
							type_manager.getObjectsOfType(effect_objects, *effect->getTerms()[term_index]->getType());
							
							HEURISTICS::VariableDomain effect_variable_domain(effect_objects);
							HEURISTICS::VariableDomain intersection;
							effect_variable_domain.getIntersection(intersection, *tmp_action_variable_to_effect_mappings[action_variable_index]);
							
							tmp_action_variable_to_effect_mappings[action_variable_index]->set(intersection.getVariableDomain());
							break;
						}
					}
				}
				
				if (types_match)
				{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
					std::cerr << action->getPredicate() << " supports " << *predicate << "." << std::endl;
					for (std::vector<unsigned int>::const_iterator ci = effect_variable_mapping->begin(); ci != effect_variable_mapping->end(); ++ci)
					{
						std::cerr << *ci << " ";
					}
					std::cerr << std::endl;
#endif
					std::map<const Property*, std::vector<unsigned int>* >* precondition_mappings = new std::map<const Property*, std::vector<unsigned int>* >();
					std::map<const Property*, std::vector<unsigned int>* >* effect_mappings = new std::map<const Property*, std::vector<unsigned int>* >();
					(*effect_mappings)[property] = effect_variable_mapping;
					std::vector<const HEURISTICS::VariableDomain*>* action_variable_to_effect_mappings = new std::vector<const HEURISTICS::VariableDomain*>();
					
					for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = tmp_action_variable_to_effect_mappings.begin(); ci != tmp_action_variable_to_effect_mappings.end(); ++ci)
					{
						action_variable_to_effect_mappings->push_back(*ci);
					}
					
					PropertyStateTransition* transition = new PropertyStateTransition(*empty_property_state, *property_state, empty_property_state->getProperties(), property_state->getProperties(), *action, *precondition_mappings, *effect_mappings, *action_variable_to_effect_mappings);
					empty_property_state->addTransition(*transition);
				}
				else
				{
					delete effect_variable_mapping;
				}
			}
		}
		
		LiftedDTG* new_lifted_dtg = new LiftedDTG(predicate_manager, type_manager, attribute_space);
		created_lifted_dtgs.push_back(new_lifted_dtg);
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		(*ci)->createTransitions(created_lifted_dtgs, type_manager);
//		std::cout << "After adding transitions: " << **ci << std::endl;
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		(*ci)->ground(created_lifted_dtgs, initial_facts, term_manager, type_manager, objects_part_of_property_spaces);
//		std::cout << "After grounding: " << **ci << std::endl;
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		(*ci)->createCopies(initial_facts, type_manager);
//		std::cout << "After creating copies: " << **ci << std::endl;
	}
	
	std::vector<LiftedDTG*> split_dtgs;
	splitLiftedTransitionGraphs(split_dtgs, created_lifted_dtgs, term_manager, initial_facts, type_manager, predicate_manager);
	
/*
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		(*ci)->split(split_dtgs, initial_facts, type_manager, term_manager, predicate_manager);
//		std::cout << "After creating copies: " << **ci << std::endl;
	}
*/
	std::cout << " === SPLITTED DTGS === " << std::endl;
	for (std::vector<LiftedDTG*>::const_iterator ci = split_dtgs.begin(); ci != split_dtgs.end(); ++ci)
	{
		std::cout << **ci << std::endl;
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		delete *ci;
	}
	created_lifted_dtgs.clear();
	created_lifted_dtgs.insert(created_lifted_dtgs.end(), split_dtgs.begin(), split_dtgs.end());
}

void LiftedDTG::splitLiftedTransitionGraphs(std::vector<LiftedDTG*>& split_ltgs, const std::vector<LiftedDTG*>& created_ltgs, const TermManager& term_manager, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager, const PredicateManager& predicate_manager)
{
	// First of all split the LTG such that not connected parts are part of a seperate LTG.
	for (std::vector<LiftedDTG*>::const_iterator ci = created_ltgs.begin(); ci != created_ltgs.end(); ++ci)
	{
		LiftedDTG* lifted_dtg = *ci;
		std::set<const MultiValuedValue*> processed_nodes;
		
		while (processed_nodes.size() != lifted_dtg->getNodes().size())
		{
			MultiValuedValue* current_node = NULL;
			for (std::vector<MultiValuedValue*>::const_iterator ci = lifted_dtg->getNodes().begin(); ci != lifted_dtg->getNodes().end(); ++ci)
			{
				MultiValuedValue* node = *ci;
				if (processed_nodes.find(node) == processed_nodes.end())
				{
					current_node = node;
					break;
				}
			}
			
			if (current_node == NULL)
			{
				std::cout << "Processed: " << processed_nodes.size() << "/" << lifted_dtg->getNodes().size() << std::endl;
			}
			assert (current_node != NULL);
			
			// Find all the nodes that are connected to current node and all nodes it is connected to, etc.
			std::set<MultiValuedValue*> nodes_to_process;
			std::vector<MultiValuedValue*> connected_set;
			nodes_to_process.insert(current_node);
			
			while (nodes_to_process.size() > 0)
			{
				MultiValuedValue* node_to_process = *nodes_to_process.begin();
				nodes_to_process.erase(nodes_to_process.begin());
				
				if (processed_nodes.find(node_to_process) != processed_nodes.end())
				{
					continue;
				}
				processed_nodes.insert(node_to_process);
				connected_set.push_back(node_to_process);
				
				std::cout << "Process " << *node_to_process << std::endl;
				
				// Find all nodes that are connected to node_to_process.
				for (std::vector<const MultiValuedTransition*>::const_iterator ci = node_to_process->getTransitions().begin(); ci != node_to_process->getTransitions().end(); ++ci)
				{
					nodes_to_process.insert(&(*ci)->getToNode());
				}
				
				for (std::vector<MultiValuedValue*>::const_iterator ci = lifted_dtg->getNodes().begin(); ci != lifted_dtg->getNodes().end(); ++ci)
				{
					MultiValuedValue* node = *ci;
					if (node == node_to_process)
					{
						continue;
					}
					
					for (std::vector<const MultiValuedTransition*>::const_iterator ci = node->getTransitions().begin(); ci != node->getTransitions().end(); ++ci)
					{
						if (&(*ci)->getToNode() == node_to_process)
						{
							nodes_to_process.insert(&(*ci)->getToNode());
							break;
						}
					}
				}
			}
			
			// Create a new lifted DTG for the nodes.
			LiftedDTG* new_lifted_dtg = new LiftedDTG(*lifted_dtg, connected_set, initial_facts, type_manager, predicate_manager);
			split_ltgs.push_back(new_lifted_dtg);
		}
	}
	
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
				const Object* initial_fact_term = static_cast<const Object*>(*ci);
				if (object == initial_fact_term)
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
		equivalent_relationships.insert(std::make_pair(object, object));
		std::cerr << *object << "<=>" << *object << std::endl;
		
		const std::vector<const Atom*>* static_facts = (*ci).second;
		
		for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
		{
			const Object* other_object = (*ci).first;
			const std::vector<const Atom*>* other_static_facts = (*ci).second;
			if (other_object == object || static_facts->size() != other_static_facts->size() || object->getType() != other_object->getType())
			{
				continue;
			}
			
			// Make sure that both objects are part of the same lifted transition graphs.
			bool belong_to_the_same_ltgs = true;
			for (std::vector<LiftedDTG*>::const_iterator ci = split_ltgs.begin(); ci != split_ltgs.end(); ++ci)
			{
				const LiftedDTG* lifted_dtg = *ci;
				bool object_is_part = std::find(lifted_dtg->getInvariableObjects().begin(), lifted_dtg->getInvariableObjects().end(), object) != lifted_dtg->getInvariableObjects().end();
				bool other_object_is_part = std::find(lifted_dtg->getInvariableObjects().begin(), lifted_dtg->getInvariableObjects().end(), other_object) != lifted_dtg->getInvariableObjects().end();
				if (object_is_part != other_object_is_part)
				{
					belong_to_the_same_ltgs = false;
					break;
				}
			}
			
			if (!belong_to_the_same_ltgs)
			{
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
					all_static_constraints_shared = false;
					break;
				}
			}
			
			if (all_static_constraints_shared)
			{
				std::cerr << *object << "<=>" << *other_object << std::endl;
				equivalent_relationships.insert(std::make_pair(object, other_object));
			}
		}
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = split_ltgs.begin(); ci != split_ltgs.end(); ++ci)
	{
		(*ci)->splitNodes(equivalent_relationships, initial_facts, predicate_manager, type_manager);
	}
}

LiftedDTG::LiftedDTG(const PredicateManager& predicate_manager, const TypeManager& type_manager, const SAS_Plus::PropertySpace& property_space)
	: property_space_(&property_space)
{
	for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ++ci)
	{
		const PropertyState* property_state = *ci;
		std::vector<HEURISTICS::Fact*>* all_facts = new std::vector<HEURISTICS::Fact*>();
		for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
		{
			const Property* property = *ci;
			
			std::vector<const HEURISTICS::VariableDomain*>* variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
			bool contains_empty_variable_domain = false;
//			for (std::vector<const Type*>::const_iterator ci = property->getPredicate().getTypes().begin(); ci != property->getPredicate().getTypes().end(); ++ci)
			for (unsigned int term_index = 0; term_index < property->getPredicate().getArity(); ++term_index)
			{
				std::vector<const Object*> objects_of_type;
				if (property->getIndex() != term_index)
				{
					const Type* type = property->getPredicate().getTypes()[term_index];
					type_manager.getObjectsOfType(objects_of_type, *type);
				}
				else
				{
					objects_of_type.insert(objects_of_type.end(), property_space.getObjects().begin(), property_space.getObjects().end());
				}
				if (objects_of_type.empty())
				{
					contains_empty_variable_domain = true;
					break;
				}
				
				HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain(objects_of_type);
				variable_domains->push_back(vd);
			}
			if (contains_empty_variable_domain)
			{
				for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = variable_domains->begin(); ci != variable_domains->end(); ++ci)
				{
					delete *ci;
				}
				delete variable_domains;
				break;
			}
			
			HEURISTICS::Fact* fact = new HEURISTICS::Fact(predicate_manager, property->getPredicate(), *variable_domains);
			all_facts->push_back(fact);
		}
		
		if (all_facts->size() != property_state->getProperties().size())
		{
			for (std::vector<HEURISTICS::Fact*>::const_iterator ci = all_facts->begin(); ci != all_facts->end(); ++ci)
			{
				delete *ci;
			}
			delete all_facts;
			continue;
		}
		MultiValuedValue* mvv = new MultiValuedValue(*this, *all_facts, *property_state);
		nodes_.push_back(mvv);
		assert (mvv != NULL);
	}
	invariable_objects_.insert(invariable_objects_.end(), property_space_->getObjects().begin(), property_space_->getObjects().end());
}

LiftedDTG::LiftedDTG(const LiftedDTG& other, const PredicateManager& predicate_manager, const std::multimap<const Object*, const Object*>& equivalent_relationships, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager)
	: property_space_(other.property_space_)
{
	for (std::multimap<const Object*, const Object*>::const_iterator ci = equivalent_relationships.begin(); ci != equivalent_relationships.end(); ++ci)
	{
		std::cout << *(*ci).first << " -> {";
		std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> equivalent_objects_ci = equivalent_relationships.equal_range((*ci).first);
		for (std::multimap<const Object*, const Object*>::const_iterator ci = equivalent_objects_ci.first; ci != equivalent_objects_ci.second; ++ci)
		{
			std::cout << *(*ci).second << ", ";
		}
		std::cout << "}" << std::endl;
	}
	
	// Create a copy of other but restrict the variable domains of the state invariable to the objects in the invariable_variable_domain. We split every node that contains a subset of the 
	// objects which are equivalent.
	std::multimap<const MultiValuedValue*, MultiValuedValue*> old_to_new_mappings;
	std::map<MultiValuedValue*, const MultiValuedValue*> new_to_old_mappings;
	for (std::vector<MultiValuedValue*>::const_iterator ci = other.nodes_.begin(); ci != other.nodes_.end(); ++ci)
	{
		const MultiValuedValue* node = *ci;
		std::vector<const std::vector<const HEURISTICS::Fact*>* > possible_facts;
		
		// Check each node and split it for every combination of equivalent nodes.
		for (std::vector<HEURISTICS::Fact*>::const_iterator ci = node->getValues().begin(); ci != node->getValues().end(); ++ci)
		{
			const HEURISTICS::Fact* fact = *ci;
			std::cout << "break up the fact: " << *fact << std::endl;
			
			std::vector<const HEURISTICS::Fact*>* all_facts = new std::vector<const HEURISTICS::Fact*>();
			possible_facts.push_back(all_facts);
			
			std::vector<const std::vector<const HEURISTICS::VariableDomain*>* > possible_variable_domains_per_term;
			for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = fact->getVariableDomains().begin(); ci != fact->getVariableDomains().end(); ++ci)
			{
				const HEURISTICS::VariableDomain* vd = *ci;
				std::set<const Object*> processed_objects;
				
				std::vector<const HEURISTICS::VariableDomain*>* possible_variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
				
				for (std::vector<const Object*>::const_iterator ci = vd->getVariableDomain().begin(); ci != vd->getVariableDomain().end(); ++ci)
				{
					const Object* object = *ci;
					if (processed_objects.find(object) != processed_objects.end())
					{
						continue;
					}
					std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> equivalent_nodes = equivalent_relationships.equal_range(object);
					std::vector<const Object*> new_variable_domain;
					for (std::multimap<const Object*, const Object*>::const_iterator ci = equivalent_nodes.first; ci != equivalent_nodes.second; ++ci)
					{
						processed_objects.insert((*ci).second);
						new_variable_domain.push_back((*ci).second);
					}
					possible_variable_domains->push_back(new HEURISTICS::VariableDomain(new_variable_domain));
				}
				
				if (possible_variable_domains->empty())
				{
					delete possible_variable_domains;
					continue;
				}
				possible_variable_domains_per_term.push_back(possible_variable_domains);
			}
			
			//if (possible_variable_domains_per_term.size() != fact->getPredicate().getArity())
			//{
			//	delete
			//}
			
			// Construct all possible facts.
			unsigned int counter[possible_variable_domains_per_term.size()];
			memset(&counter, 0, sizeof(unsigned int) * possible_variable_domains_per_term.size());
			
			unsigned int max_counter[possible_variable_domains_per_term.size()];
			for (unsigned int i = 0; i < possible_variable_domains_per_term.size(); ++i)
			{
				max_counter[i] = possible_variable_domains_per_term[i]->size();
			}
			
			bool done = false;
			while (!done)
			{
				done = true;
				std::vector<const HEURISTICS::VariableDomain*> variable_domains;
				for (unsigned int term_index = 0; term_index < fact->getPredicate().getArity(); ++term_index)
				{
					variable_domains.push_back((*possible_variable_domains_per_term[term_index])[counter[term_index]]);
				}
				
				std::cout << "New fact: " << fact->getPredicate().getName() << std::endl;
				for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = variable_domains.begin(); ci != variable_domains.end(); ++ci)
				{
					std::cout << **ci << ", ";
				}
				std::cout << "." << std::endl;
				
				HEURISTICS::Fact* new_fact = new HEURISTICS::Fact(predicate_manager, fact->getPredicate(), variable_domains);
				all_facts->push_back(new_fact);
				
				// Update the counters.
				for (unsigned int i = 0; i < possible_variable_domains_per_term.size(); ++i)
				{
					if (counter[i] + 1 != max_counter[i])
					{
						counter[i] = counter[i] + 1;
						done = false;
						break;
					}
					else
					{
						counter[i] = 0;
					}
				}
			}
		}
		
		// Construct all possible nodes.
		unsigned int counter[possible_facts.size()];
		memset(&counter, 0, sizeof(unsigned int) * possible_facts.size());
		
		unsigned int max_counter[possible_facts.size()];
		for (unsigned int i = 0; i < possible_facts.size(); ++i)
		{
			max_counter[i] = possible_facts[i]->size();
		}
		
		bool done = false;
		while (!done)
		{
			done = true;
			std::vector<HEURISTICS::Fact*>* facts = new std::vector<HEURISTICS::Fact*>();
			for (unsigned int node_index = 0; node_index < possible_facts.size(); ++node_index)
			{
				HEURISTICS::Fact* new_fact = new HEURISTICS::Fact(*(*possible_facts[node_index])[counter[node_index]]);
				facts->push_back(new_fact);
			}
			
			MultiValuedValue* node_copy = new MultiValuedValue(*this, *facts, node->getPropertyState(), node->isCopy());
			old_to_new_mappings.insert(std::make_pair(node, node_copy));
			new_to_old_mappings[node_copy] = node;
			
			nodes_.push_back(node_copy);
			
			// Update the counters.
			for (unsigned int i = 0; i < possible_facts.size(); ++i)
			{
				if (counter[i] + 1 != max_counter[i])
				{
					counter[i] = counter[i] + 1;
					done = false;
					break;
				}
				else
				{
					counter[i] = 0;
				}
			}
		}
	}
	
	// Try to establish all the transitions.
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		MultiValuedValue* from_node = *ci;
		const MultiValuedValue* org_from_node = new_to_old_mappings[from_node];
		
		for (std::vector<const MultiValuedTransition*>::const_iterator ci = org_from_node->getTransitions().begin(); ci != org_from_node->getTransitions().end(); ++ci)
		{
			const MultiValuedTransition* org_transition = *ci;
			const MultiValuedValue* org_to_node = new_to_old_mappings[&org_transition->getToNode()];
			
			std::pair<std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator, std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator> new_to_nodes = old_to_new_mappings.equal_range(org_to_node);
			
			for (std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator ci = new_to_nodes.first; ci != new_to_nodes.second; ++ci)
			{
				MultiValuedTransition* new_transition = org_transition->migrateTransition(*from_node, *(*ci).second, initial_facts, type_manager);
				if (new_transition != NULL)
				{
					from_node->addTransition(*new_transition);
				}
			}
		}
	}
	findInvariableObjects(initial_facts, predicate_manager);
}

LiftedDTG::LiftedDTG(const LiftedDTG& other, const std::vector<MultiValuedValue*>& node_set, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager, const PredicateManager& predicate_manager)
	: property_space_(other.property_space_)
{
	std::cout << "Create a copy of: " << other << std::endl;
	std::cout << "Original nodes: " << std::endl;
	
	std::map<const MultiValuedValue*, MultiValuedValue*> old_to_new_node_mapping;
	for (std::vector<MultiValuedValue*>::const_iterator ci = node_set.begin(); ci != node_set.end(); ++ci)
	{
		std::cout << "* " << **ci << std::endl;
		MultiValuedValue* mvv = new MultiValuedValue(*this, **ci, (*ci)->isCopy());
		nodes_.push_back(mvv);
		old_to_new_node_mapping[*ci] = mvv;
	}
	
	for (std::vector<MultiValuedValue*>::const_iterator ci = node_set.begin(); ci != node_set.end(); ++ci)
	{
		MultiValuedValue* org_from_node = *ci;
		MultiValuedValue* new_from_org = old_to_new_node_mapping[org_from_node];
		
		for (std::vector<const MultiValuedTransition*>::const_iterator ci = org_from_node->getTransitions().begin(); ci != org_from_node->getTransitions().end(); ++ci)
		{
			const MultiValuedTransition* transition = *ci;
			MultiValuedValue* new_to_node = old_to_new_node_mapping[&transition->getToNode()];
			
			if (new_to_node == NULL)
			{
				continue;
			}
			const MultiValuedTransition* new_transition = transition->migrateTransition(*new_from_org, *new_to_node, initial_facts, type_manager);
			assert (new_transition != NULL);
			
			new_from_org->addTransition(*new_transition);
		}
	}
	
	findInvariableObjects(initial_facts, predicate_manager);
}

void LiftedDTG::findInvariableObjects(const std::vector<const Atom*>& initial_facts, const PredicateManager& predicate_manager)
{
	invariable_objects_.clear();
	std::vector<const HEURISTICS::Fact*> transformed_initial_facts;
	for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
	{
		const Atom* initial_fact = *ci;
		
		std::vector<const HEURISTICS::VariableDomain*> variable_domains;
		for (std::vector<const Term*>::const_iterator ci = initial_fact->getTerms().begin(); ci != initial_fact->getTerms().end(); ++ci)
		{
			const Term* term = *ci;
			HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain();
			vd->set(*static_cast<const Object*>(term));
			variable_domains.push_back(vd);
		}
		
		const HEURISTICS::Fact* fact = new HEURISTICS::Fact(predicate_manager, initial_fact->getPredicate(), variable_domains);
		transformed_initial_facts.push_back(fact);
	}
	
	// Find the objects which can be initialised from the initial state.
	invariable_objects_.clear();
	std::cout << "Invariable objects: ";
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		MultiValuedValue* mvv = new MultiValuedValue(*this, **ci, (*ci)->isCopy());
		
		std::vector<std::vector<const HEURISTICS::Fact*>* > found_mappings;
		mvv->findMappings(found_mappings, transformed_initial_facts, predicate_manager);
		
		unsigned int invariable_fact_index = std::numeric_limits<unsigned int>::max();
		unsigned int invariable_term_index = std::numeric_limits<unsigned int>::max();
		const SAS_Plus::PropertyState& property_state = mvv->getPropertyState();
		for (std::vector<const SAS_Plus::Property*>::const_iterator ci = property_state.getProperties().begin(); ci != property_state.getProperties().end(); ++ci)
		{
			const SAS_Plus::Property* property = *ci;
			unsigned int fact_index = std::distance(property_state.getProperties().begin(), ci);
			if (property->getIndex() != std::numeric_limits<unsigned int>::max())
			{
				invariable_fact_index = fact_index;
				invariable_term_index = property->getIndex();
				break;
			}
		}
		
		if (invariable_fact_index == std::numeric_limits<unsigned int>::max())
		{
			continue;
		}
		
		for (std::vector<std::vector<const HEURISTICS::Fact*>*>::const_iterator ci = found_mappings.begin(); ci != found_mappings.end(); ++ci)
		{
			std::vector<const HEURISTICS::Fact*>* fact = *ci;
			const HEURISTICS::VariableDomain* vd = (*fact)[invariable_fact_index]->getVariableDomains()[invariable_term_index];
			
			for (std::vector<const Object*>::const_iterator ci = vd->getVariableDomain().begin(); ci != vd->getVariableDomain().end(); ++ci)
			{
				if (std::find(invariable_objects_.begin(), invariable_objects_.end(), *ci) == invariable_objects_.end())
				{
					invariable_objects_.push_back(*ci);
					std::cout << **ci << ", ";
				}
			}
		}
	}
	
	std::cout << "." << std::endl;
}

LiftedDTG::~LiftedDTG()
{
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		delete *ci;
	}
}

void LiftedDTG::getNodes(std::vector<const MultiValuedValue*>& found_nodes, const HEURISTICS::Fact& fact_to_find) const
{
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		MultiValuedValue* value = *ci;
		assert (value != NULL);
		if (value->isCopy())
		{
 			continue;
		}
		
		for (std::vector<HEURISTICS::Fact*>::const_iterator ci = value->getValues().begin(); ci != value->getValues().end(); ++ci)
		{
			const HEURISTICS::Fact* fact = *ci;
			if (fact->canUnifyWith(fact_to_find))
			{
				found_nodes.push_back(value);
			}
		}
	}
}

void LiftedDTG::splitNodes(const std::multimap<const Object*, const Object*>& equivalent_relationships, const std::vector<const Atom*>& initial_facts, const PredicateManager& predicate_manager, const TypeManager& type_manager)
{
	std::map<MultiValuedValue*, const MultiValuedValue*> new_node_to_old_node_mapping;
	std::multimap<const MultiValuedValue*, MultiValuedValue*> old_node_to_new_nodes_mapping;
	
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		const MultiValuedValue* value = *ci;
		
		std::vector<MultiValuedValue*> splitted_nodes;
		value->split(splitted_nodes, equivalent_relationships, predicate_manager);
		
		for (std::vector<MultiValuedValue*>::const_iterator ci = splitted_nodes.begin(); ci != splitted_nodes.end(); ++ci)
		{
			new_node_to_old_node_mapping[*ci] = value;
			old_node_to_new_nodes_mapping.insert(std::make_pair(value, *ci));
		}
	}
	
	// Now that the nodes are split we need to reconnect all the transitions and reestablish what node is a copy of what other node.
	std::vector<MultiValuedValue*> new_nodes;
	for (std::map<MultiValuedValue*, const MultiValuedValue*>::const_iterator ci = new_node_to_old_node_mapping.begin(); ci != new_node_to_old_node_mapping.end(); ++ci)
	{
		MultiValuedValue* new_node = (*ci).first;
		const MultiValuedValue* org_node = (*ci).second;
		
		// Start with the connections.
		for (std::vector<const MultiValuedTransition*>::const_iterator ci = org_node->getTransitions().begin(); ci != org_node->getTransitions().end(); ++ci)
		{
			const MultiValuedTransition* transition = *ci;
			
			// Check what the new end points are.
			std::pair<std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator, std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator> new_node_mappings = old_node_to_new_nodes_mapping.equal_range(&transition->getToNode());
			for (std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator ci = new_node_mappings.first; ci != new_node_mappings.second; ++ci)
			{
				MultiValuedTransition* new_transition = transition->migrateTransition(*new_node, *(*ci).second, initial_facts, type_manager);
				if (new_transition != NULL)
				{
					new_node->addTransition(*new_transition);
				}
			}
		}
		
		// Update the copy information.
		for (std::vector<MultiValuedValue*>::const_iterator ci = org_node->getCopies().begin(); ci != org_node->getCopies().end(); ++ci)
		{
			const MultiValuedValue* org_copy = *ci;
			std::pair<std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator, std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator> new_node_mappings = old_node_to_new_nodes_mapping.equal_range(org_copy);
			for (std::multimap<const MultiValuedValue*, MultiValuedValue*>::const_iterator ci = new_node_mappings.first; ci != new_node_mappings.second; ++ci)
			{
				MultiValuedValue* potential_new_copy = (*ci).second;
				
				// TODO: In order for it to be a copy we must make sure that the invariable domains match.
				new_node->addCopy(*potential_new_copy);
			}
		}
		
		std::cout << " ==== FINALISED NODE: " << std::endl;
		std::cout << *new_node << std::endl;
		for (std::vector<const MultiValuedTransition*>::const_iterator ci = new_node->getTransitions().begin(); ci != new_node->getTransitions().end(); ++ci)
		{
			std::cout << **ci << std::endl;
		}
		
		new_nodes.push_back(new_node);
	}
	
	// Replace the old nodes with the new nodes!
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		delete *ci;
	}
	nodes_.clear();
	nodes_.insert(nodes_.end(), new_nodes.begin(), new_nodes.end());
}

void LiftedDTG::createCopies(const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager)
{
	std::vector<MultiValuedValue*> nodes_to_add;
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
	std::cout << "[LiftedDTG::createCopies]" << *this << std::endl;
#endif
	
	// Detect which terms contain more than a single value and which are not the state invariables.
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		MultiValuedValue* value = *ci;
		if (value->isCopy())
		{
			continue;
		}
//		std::cout << "Process: " << *value << std::endl;
		
		const PropertyState& property_state = value->getPropertyState();
		const std::vector<const Property*>& properties = property_state.getProperties();
		
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
		if (properties.size() != value->getValues().size())
		{
			std::cerr << *value << std::endl;
			std::cerr << "V.S." << std::endl;
			std::cerr << property_state << std::endl;
		}
#endif
		assert (properties.size() == value->getValues().size());
		
		std::vector<const HEURISTICS::Fact*> violating_facts;
		for (unsigned int value_index = 0; value_index < value->getValues().size(); ++value_index)
		{
			const HEURISTICS::Fact* fact = value->getValues()[value_index];
			const Property* property = properties[value_index];
			
//			std::cerr << "Fact: " << *fact << std::endl;
//			std::cerr << "Property: " << property->getIndex() << std::endl;
			
			for (unsigned int variable_domain_index = 0; variable_domain_index < fact->getVariableDomains().size(); ++variable_domain_index)
			{
				if (property->getIndex() == variable_domain_index)
				{
					continue;
				}
				
				const HEURISTICS::VariableDomain* variable_domain = fact->getVariableDomains()[variable_domain_index];
				assert (variable_domain->getVariableDomain().size() != 0);
				if (variable_domain->getVariableDomain().size() > 1)
				{
					violating_facts.push_back(fact);
//					std::cerr << "Need to create a copy of: " << *value << std::endl;
					break;
				}
			}
		}
		
		if (violating_facts.empty())
		{
			continue;
		}
		
//		std::cout << "Create a copy!" << std::endl;
		
		// We perform a breath-first search to find all the nodes which are connected to 'current node' which shares the violated facts.
		std::map<const MultiValuedValue*, MultiValuedValue*> copy_list;
		std::vector<const MultiValuedValue*> open_list;
		open_list.push_back(value);
		
		while (open_list.size() > 0)
		{
			const MultiValuedValue* current_node = open_list[0];
			open_list.erase(open_list.begin());
			
			if (copy_list.find(current_node) != copy_list.end() || current_node->isCopy())
			{
				continue;
			}
			
			MultiValuedValue* copy_current_node = new MultiValuedValue(*this, *current_node, true);
			value->addCopy(*copy_current_node);
			copy_list[current_node] = copy_current_node;
			
			// Check which of the state variables this variable is connected to via a transition shares an atom which contains multiple values.
			for (std::vector<const MultiValuedTransition*>::const_iterator ci = current_node->getTransitions().begin(); ci != current_node->getTransitions().end(); ++ci)
			{
				const MultiValuedTransition* transition = *ci;
				const MultiValuedValue& effect = transition->getToNode();
				
				bool is_shared[effect.getValues().size()];
				for (unsigned int fact_index = 0; fact_index < effect.getValues().size(); ++fact_index)
				{
					is_shared[fact_index] = false;
				}
				
				// Check if this effect has already been copied.
				if (copy_list.find(&effect) != copy_list.end() || effect.isCopy())
				{
					continue;
				}
				
				// Check if effect contains all the violated facts.
				bool contains_all_violated_facts = true;
				for (std::vector<const HEURISTICS::Fact*>::const_iterator ci = violating_facts.begin(); ci != violating_facts.end(); ++ci)
				{
					const HEURISTICS::Fact* violated_fact = *ci;
					bool found_match = false;
					
					for (std::vector<HEURISTICS::Fact*>::const_iterator ci = effect.getValues().begin(); ci != effect.getValues().end(); ++ci)
					{
						const HEURISTICS::Fact* effect_fact = *ci;
						if (violated_fact->canUnifyWith(*effect_fact))
						{
							is_shared[std::distance(effect.getValues().begin(), ci)] = true;
							found_match = true;
							break;
						}
					}
					
					if (!found_match)
					{
						contains_all_violated_facts = false;
						break;
					}
				}
				
				if (!contains_all_violated_facts)
				{
					continue;
				}
				
				// Make sure that the value contains a fact that has a variable domain which contains more than one object which is not the invariable.
				bool contains_unbalanced_fact = false;
				for (unsigned int value_index = 0; value_index < effect.getValues().size(); ++value_index)
				{
					const HEURISTICS::Fact* fact = effect.getValues()[value_index];
					const Property* property = effect.getPropertyState().getProperties()[value_index];
					
//					std::cerr << "Fact: " << *fact << std::endl;
//					std::cerr << "Property: " << property->getIndex() << std::endl;
					
					for (unsigned int variable_domain_index = 0; variable_domain_index < fact->getVariableDomains().size(); ++variable_domain_index)
					{
						if (property->getIndex() == variable_domain_index || is_shared[value_index])
						{
							continue;
						}
						
						const HEURISTICS::VariableDomain* variable_domain = fact->getVariableDomains()[variable_domain_index];
						assert (variable_domain->getVariableDomain().size() != 0);
						if (variable_domain->getVariableDomain().size() > 1)
						{
							contains_unbalanced_fact = true;
							break;
						}
					}
					
					if (contains_unbalanced_fact)
					{
						break;
					}
				}
				
				if (contains_unbalanced_fact)
				{
					open_list.push_back(&effect);
				}
			}
		}
		
		for (std::map<const MultiValuedValue*, MultiValuedValue*>::const_iterator ci = copy_list.begin(); ci != copy_list.end(); ++ci)
		{
			assert (!(*ci).first->isCopy());
			assert ((*ci).second->isCopy());
//			std::cout << "New copy: " << *(*ci).second << std::endl;
			nodes_to_add.push_back((*ci).second);
		}
		
		// After detecting which values should be copied, we reconnect all the transitions.
		for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
		{
			MultiValuedValue* from_variable = *ci;
			
			if (from_variable->isCopy() && copy_list.find(from_variable) == copy_list.end())
			{
				continue;
			}
			
			std::map<const MultiValuedValue*, MultiValuedValue*>::const_iterator from_copy_list_ci = copy_list.find(from_variable);
			std::vector<std::pair<MultiValuedValue*, MultiValuedTransition*> > transitions_to_add;
			
			for (std::vector<const MultiValuedTransition*>::const_iterator ci = from_variable->getTransitions().begin(); ci != from_variable->getTransitions().end(); ++ci)
			{
				const MultiValuedTransition* transition = *ci;
				MultiValuedValue& to_variable = transition->getToNode();
				
				if (to_variable.isCopy() && copy_list.find(&to_variable) == copy_list.end())
				{
					continue;
				}
				
				std::map<const MultiValuedValue*, MultiValuedValue*>::const_iterator to_copy_list_ci = copy_list.find(&to_variable);
				
				// If neither are copied then nothing changed.
				if (from_copy_list_ci == copy_list.end() && to_copy_list_ci == copy_list.end())
				{
					continue;
				}
				
				MultiValuedValue* from_copy = from_copy_list_ci != copy_list.end() ? (*from_copy_list_ci).second : from_variable;
				MultiValuedValue* to_copy = to_copy_list_ci != copy_list.end() ? (*to_copy_list_ci).second : &to_variable;
				
				// Create a copy between these two nodes.
				MultiValuedTransition* new_transition = transition->migrateTransition(*from_copy, *to_copy, initial_facts, type_manager);
				transitions_to_add.push_back(std::make_pair(from_copy, new_transition));
			}
			
			for (std::vector<std::pair<MultiValuedValue*, MultiValuedTransition*> >::const_iterator ci = transitions_to_add.begin(); ci != transitions_to_add.end(); ++ci)
			{
				(*ci).first->addTransition(*(*ci).second);
			}
		}
	}
	
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_to_add.begin(); ci != nodes_to_add.end(); ++ci)
	{
		nodes_.push_back(*ci);
		assert (*ci != NULL);
	}
}

void LiftedDTG::createTransitions(const std::vector<LiftedDTG*>& all_lifted_dtgs, const TypeManager& type_manager)
{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
	std::cout << "Create transitions for " << *this << std::endl;
#endif
	// Connect the transitions.
	for (std::vector<PropertyState*>::const_iterator ci = property_space_->getPropertyStates().begin(); ci != property_space_->getPropertyStates().end(); ++ci)
	{
		const PropertyState* property_state = *ci;
		for (std::vector<const PropertyStateTransition*>::const_iterator ci = property_state->getTransitions().begin(); ci != property_state->getTransitions().end(); ++ci)
		{
			const PropertyStateTransition* transition = *ci;
			
			MultiValuedValue* from_node = getMultiValuedValue(transition->getFromPropertyState());
			MultiValuedValue* to_node = getMultiValuedValue(transition->getToPropertyState());
			
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
			std::cout << "Create a transition from " << *from_node << " to " << *to_node << std::endl;
			std::cout << "Transition: " << *transition << std::endl;
#endif
			
			//const std::map<const Property*, std::vector<unsigned int>* >& precondition_mappings_to_action_variables = transition->getMappingToActionVariables();
			const std::vector<const HEURISTICS::VariableDomain*>& action_variables = transition->getActionVariableDomains();
			
			// We map each term of each value of each precondition to the variables of the action.
			std::vector<std::vector<unsigned int>* >* precondition_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
			
			// We map each action variable to each term of the effect.
			std::vector<std::vector<unsigned int>* >* effects_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
			
			const std::vector<HEURISTICS::Fact*>& from_values = from_node->getValues();
			for (unsigned int fact_index = 0; fact_index < from_values.size(); ++fact_index)
			{
				HEURISTICS::Fact* fact = from_values[fact_index];
				const Property* property = from_node->getPropertyState().getProperties()[fact_index];
				
				const std::vector<unsigned int>* mapping_to_action_variables = transition->getMappingsOfProperty(*property, true);
				
				//if (mappings_to_action_variables.find(property) == mappings_to_action_variables.end())
				if (mapping_to_action_variables == NULL)
				{
					precondition_to_action_variable_mappings->push_back(NULL);
					continue;
				}
				//assert (mappings_to_action_variables.find(property) != mappings_to_action_variables.end());
				
				std::vector<unsigned int>* precondition_mapping = new std::vector<unsigned int>();
				precondition_to_action_variable_mappings->push_back(precondition_mapping);
				
				for (unsigned int fact_term_index = 0; fact_term_index < fact->getVariableDomains().size(); ++fact_term_index)
				{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
					std::cout << "The " << fact_term_index << " is mapped to the " << (*mapping_to_action_variables)[fact_term_index] << "th action variable!" << std::endl;
#endif
					assert ((*mapping_to_action_variables).size() > fact_term_index);
					assert ((*mapping_to_action_variables)[fact_term_index] < action_variables.size());
					fact->setVariableDomain(fact_term_index, *action_variables[(*mapping_to_action_variables)[fact_term_index]]);
					precondition_mapping->push_back((*mapping_to_action_variables)[fact_term_index]);
				}
			}
			
			const std::vector<HEURISTICS::Fact*>& to_values = to_node->getValues();
			for (unsigned int fact_index = 0; fact_index < to_values.size(); ++fact_index)
			{
				HEURISTICS::Fact* fact = to_values[fact_index];
				const Property* property = to_node->getPropertyState().getProperties()[fact_index];
				
				const std::vector<unsigned int>* mapping_to_action_variables = transition->getMappingsOfProperty(*property, false);
				
				//if (mappings_to_action_variables.find(property) == mappings_to_action_variables.end())
				if (mapping_to_action_variables == NULL)
				{
					effects_to_action_variable_mappings->push_back(NULL);
					continue;
				}
				
				std::vector<unsigned int>* effect_to_action_variable_mappings = new std::vector<unsigned int>();
				effects_to_action_variable_mappings->push_back(effect_to_action_variable_mappings);
				
				for (unsigned int fact_term_index = 0; fact_term_index < fact->getVariableDomains().size(); ++fact_term_index)
				{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
					std::cout << "The " << fact_term_index << " is mapped to the " << (*mapping_to_action_variables)[fact_term_index] << "th action variable! (" << action_variables.size() << ")" << transition->getAction().getVariables().size() << std::endl;
#endif
					fact->setVariableDomain(fact_term_index, *action_variables[(*mapping_to_action_variables)[fact_term_index]]);
					effect_to_action_variable_mappings->push_back((*mapping_to_action_variables)[fact_term_index]);
				}
			}
			
			MultiValuedTransition* new_transition = new MultiValuedTransition(transition->getAction(), *from_node, *to_node, *precondition_to_action_variable_mappings, *effects_to_action_variable_mappings, type_manager);
			from_node->addTransition(*new_transition);
		}
	}
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
	std::cout << *this << std::endl;
#endif
}

void LiftedDTG::ground(const std::vector<LiftedDTG*>& all_lifted_dtgs, const std::vector<const Atom*>& initial_facts, const TermManager& term_manager, const TypeManager& type_manager, const std::set<const Object*>& objects_not_to_ground)
{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
	std::cout << "GROUND" << std::endl << *this << std::endl;
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
				const Object* o = static_cast<const Object*>(*ci);
				if (o == object)
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
		
		if (objects_not_to_ground.count(object) == 0)
		{
			continue;
		}
		
		
		for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
		{
			const Object* other_object = (*ci).first;
			
			if (objects_not_to_ground.count(other_object) == 0)
			{
				continue;
			}
			
			const std::vector<const Atom*>* other_static_facts = (*ci).second;
			if (other_object == object || static_facts->size() != other_static_facts->size() || object->getType() != other_object->getType())
			{
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
					all_static_constraints_shared = false;
					break;
				}
			}
			
			if (all_static_constraints_shared)
			{
				equivalent_relationships.insert(std::make_pair(object, other_object));
			}
		}
	}
/*
	std::cout << "All objects split up:" << std::endl;
	for (std::vector<const Object*>::const_iterator ci = term_manager.getAllObjects().begin(); ci != term_manager.getAllObjects().end(); ++ci)
	{
		std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> equivalent_objects = equivalent_relationships.equal_range(*ci);
		std::cout << **ci << " is mapped to: {";
		for (std::multimap<const Object*, const Object*>::const_iterator ci = equivalent_objects.first; ci != equivalent_objects.second; ++ci)
		{
			std::cout << *(*ci).second << " ";
		}
		std::cout << "}" << std::endl;
	}
*/
	for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
	{
		delete (*ci).second;
	}
	
	// Break the nodes up along the equivalent object sets.
	std::map<MultiValuedValue*, const MultiValuedValue*> new_to_old_node_mapping;
	std::map<const MultiValuedValue*, std::vector<MultiValuedValue*>*> old_to_new_node_mapping;
	
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		const MultiValuedValue* dtg_node = *ci;
		old_to_new_node_mapping[dtg_node] = new std::vector<MultiValuedValue*>();
		
		// Check if this node needs to be split up.
		std::set<const HEURISTICS::VariableDomain*> all_variable_domains;
		
		for (std::vector<HEURISTICS::Fact*>::const_iterator ci = dtg_node->getValues().begin(); ci != dtg_node->getValues().end(); ++ci)
		{
			HEURISTICS::Fact* fact = *ci;
			all_variable_domains.insert(fact->getVariableDomains().begin(), fact->getVariableDomains().end());
		}
		
		// Split the variable domains up based on the equivalence relationships.
		std::map<const HEURISTICS::VariableDomain*, std::vector<const HEURISTICS::VariableDomain*>* > split_up_variable_domains;
		std::map<const HEURISTICS::VariableDomain*, unsigned int> counters;
		for (std::set<const HEURISTICS::VariableDomain*>::const_iterator ci = all_variable_domains.begin(); ci != all_variable_domains.end(); ++ci)
		{
			const HEURISTICS::VariableDomain* variable_domain = *ci;
			if (split_up_variable_domains.find(variable_domain) != split_up_variable_domains.end())
			{
				continue;
			}
			
			counters[variable_domain] = 0;
			std::vector<const HEURISTICS::VariableDomain* >* split_up_variable_domain = new std::vector<const HEURISTICS::VariableDomain* >();
			split_up_variable_domains[variable_domain] = split_up_variable_domain;
			std::set<const Object*> processed_objects;
			
			for (std::vector<const Object*>::const_iterator ci = variable_domain->getVariableDomain().begin(); ci != variable_domain->getVariableDomain().end(); ++ci)
			{
				const Object* object = *ci;
				if (processed_objects.find(object) != processed_objects.end())
				{
					continue;
				}
				
				std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> equivalent_objects = equivalent_relationships.equal_range(object);
				
				std::vector<const Object*>* new_variable_domain = new std::vector<const Object*>();
				new_variable_domain->push_back(object);

				processed_objects.insert(object);
				for (std::multimap<const Object*, const Object*>::const_iterator ci = equivalent_objects.first; ci != equivalent_objects.second; ++ci)
				{
					processed_objects.insert((*ci).second);
					new_variable_domain->push_back((*ci).second);
				}
				split_up_variable_domain->push_back(new HEURISTICS::VariableDomain(*new_variable_domain));
			}
		}
/*
		std::cout << "Mappings: " << std::endl;
		for (std::map<const HEURISTICS::VariableDomain*, std::vector<const HEURISTICS::VariableDomain*>* >::const_iterator ci = split_up_variable_domains.begin(); ci != split_up_variable_domains.end(); ++ci)
		{
			std::cout << *(*ci).first << std::endl;
			std::cout << "Is mapped to: " << std::endl;
			
			std::vector<const HEURISTICS::VariableDomain*>* mappings = (*ci).second;
			for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
			{
				std::cout << "\t" << **ci << std::endl;
			}
		}
*/
		// For every possible split of the variable domains we crate a new DTG node.
		bool done = false;
		while (!done)
		{
			done = true;
			MultiValuedValue* dtg_node_copy = new MultiValuedValue(*this, *dtg_node);
			
			//for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node_copy->getAtoms().begin(); ci != dtg_node_copy->getAtoms().end(); ++ci)
			for (unsigned int i = 0; i < dtg_node_copy->getValues().size(); ++i)
			{
				const HEURISTICS::Fact* org_fact = dtg_node->getValues()[i];
				const HEURISTICS::Fact* copied_fact = dtg_node_copy->getValues()[i];
				
				for (unsigned int term_index = 0; term_index < org_fact->getVariableDomains().size(); ++term_index)
				{
					const HEURISTICS::VariableDomain* org_domain = org_fact->getVariableDomains()[term_index];
					const HEURISTICS::VariableDomain* to_map_to = (*split_up_variable_domains[org_domain])[counters[org_domain]];
					const_cast<HEURISTICS::VariableDomain*>(copied_fact->getVariableDomains()[term_index])->set(to_map_to->getVariableDomain());
				}
			}
			
			old_to_new_node_mapping[dtg_node]->push_back(dtg_node_copy);
			new_to_old_node_mapping[dtg_node_copy] = dtg_node;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Split up dtg node: " << std::endl << *dtg_node_copy << std::endl;
#endif
			
			// Update the counters.
			for (std::map<const HEURISTICS::VariableDomain*, unsigned int>::const_iterator ci = counters.begin(); ci != counters.end(); ++ci)
			{
				const HEURISTICS::VariableDomain* variable_domain = (*ci).first;
				unsigned int counter = (*ci).second;
				if (counter + 1 == split_up_variable_domains[variable_domain]->size())
				{
					counters[variable_domain] = 0;
				}
				else
				{
					counters[variable_domain] = counter + 1;
					done = false;
					break;
				}
			}
		}
		
		for (std::map<const HEURISTICS::VariableDomain*, std::vector<const HEURISTICS::VariableDomain*>* >::const_iterator ci = split_up_variable_domains.begin(); ci != split_up_variable_domains.end(); ++ci)
		{
			delete (*ci).second;
		}
	}
	
	// Remove the old nodes and add the new nodes.
	nodes_.clear();
	for (std::map<MultiValuedValue*, const MultiValuedValue*>::const_iterator ci = new_to_old_node_mapping.begin(); ci != new_to_old_node_mapping.end(); ++ci)
	{
		MultiValuedValue* new_node = (*ci).first;
		assert (new_node != NULL);
		nodes_.push_back(new_node);
		const MultiValuedValue* old_node = (*ci).second;
		
//		std::cout << *new_node << "->" << *old_node << std::endl;
		
		// Reestablish all the transitions.
		for (std::vector<const MultiValuedTransition*>::const_iterator ci = old_node->getTransitions().begin(); ci != old_node->getTransitions().end(); ++ci)
		{
			const MultiValuedTransition* transition = *ci;
			std::vector<MultiValuedValue*>* new_to_nodes = old_to_new_node_mapping[&transition->getToNode()];
			
			for (std::vector<MultiValuedValue*>::const_iterator ci = new_to_nodes->begin(); ci != new_to_nodes->end(); ++ci)
			{
				MultiValuedTransition* new_transition = transition->migrateTransition(*new_node, **ci, initial_facts, type_manager);
				if (new_transition != NULL)
				{
					new_node->addTransition(*new_transition);
				}
			}
		}
	}
	
	for (std::map<const MultiValuedValue*, std::vector<MultiValuedValue*>*>::const_iterator ci = old_to_new_node_mapping.begin(); ci != old_to_new_node_mapping.end(); ++ci)
	{
		delete (*ci).second;
	}
	
	// Finally we need to make copies of any node that contains more than a single lifted fact. Otherwise the heuristics will not be calculated correctly.
	
/*
	std::map<const DomainTransitionGraphNode*, std::vector<DomainTransitionGraphNode*>* > lifted_to_grounded_dtg_node_mappings;
	std::map<DomainTransitionGraphNode*, const DomainTransitionGraphNode* > grounded_to_lifted_dtg_node_mappings;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		
		// Determine which variables to ground.
		std::vector<const std::vector<const Object*> *> variable_domains_to_ground;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ++ci)
		{
			const BoundedAtom* fact = *ci;
			for (unsigned int i = 0; i < fact->getAtom().getArity(); ++i)
			{
				const std::vector<const Object*>& variable_domain = fact->getVariableDomain(i, *bindings_);
				
				// Check if this variable domain contains any objects which must be grounded.
				for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ++ci)
				{
					if (std::find(objects_not_to_ground.begin(), objects_not_to_ground.end(), *ci) == objects_not_to_ground.end())
					{
						variable_domains_to_ground.push_back(&variable_domain);
						break;
					}
				}
			}
		}
		std::sort(variable_domains_to_ground.begin(), variable_domains_to_ground.end());
		variable_domains_to_ground.erase(std::unique(variable_domains_to_ground.begin(), variable_domains_to_ground.end()), variable_domains_to_ground.end());
		
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "Ground the following variable domains: " << std::endl;
		for (std::vector<const std::vector<const Object*> *>::const_iterator ci = variable_domains_to_ground.begin(); ci != variable_domains_to_ground.end(); ++ci)
		{
			std::cout << "- " << *ci << std::endl;
		}
#endif

		std::vector<DomainTransitionGraphNode*>* grounded_nodes = new std::vector<DomainTransitionGraphNode*>();
		
		std::map<const std::vector<const Object*>*, const Object*> bound_objects;
		dtg_node->groundTerms(*grounded_nodes, variable_domains_to_ground, bound_objects);
		
		// Make copies of every grounded node if they contain more than a single lifted domain with the same values.
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_nodes->begin(); ci != grounded_nodes->end(); ++ci)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Grounded node: " << std::endl << *dtg_node << std::endl;
#endif
			
			for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ++ci)
			{
				
			}
		}
		
		lifted_to_grounded_dtg_node_mappings[dtg_node] = grounded_nodes;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_nodes->begin(); ci != grounded_nodes->end(); ++ci)
		{
			grounded_to_lifted_dtg_node_mappings[*ci] = dtg_node;
		}
	}
	
	std::vector<DomainTransitionGraphNode*> old_nodes(nodes_);
	nodes_.clear();
	for (std::map<const DomainTransitionGraphNode*, std::vector<DomainTransitionGraphNode*>* >::const_iterator ci = lifted_to_grounded_dtg_node_mappings.begin(); ci != lifted_to_grounded_dtg_node_mappings.end(); ++ci)
	{
		//grounded_dtg->nodes_.insert(grounded_dtg->nodes_.end(), (*ci).second->begin(), (*ci).second->end());
		nodes_.insert(nodes_.end(), (*ci).second->begin(), (*ci).second->end());
	}
	
	// Reestablish all the transitions.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		DomainTransitionGraphNode* grounded_from_dtg_node = *ci;
		assert (grounded_to_lifted_dtg_node_mappings.find(grounded_from_dtg_node) != grounded_to_lifted_dtg_node_mappings.end());
		const DomainTransitionGraphNode* lifted_parent = grounded_to_lifted_dtg_node_mappings[grounded_from_dtg_node];
		assert (lifted_parent != NULL);
		
		for (std::vector<Transition*>::const_iterator ci = lifted_parent->getTransitions().begin(); ci != lifted_parent->getTransitions().end(); ++ci)
		{
			const Transition* org_transition = *ci;
			
			// Try to migrate the transition to all the grounded to nodes.
			const std::vector<DomainTransitionGraphNode*>* grounded_to_nodes = lifted_to_grounded_dtg_node_mappings[&org_transition->getToNode()];
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_to_nodes->begin(); ci != grounded_to_nodes->end(); ++ci)
			{
				DomainTransitionGraphNode* grounded_to_dtg_node = *ci;

				// Migrate the original transition to the cloned nodes.
				Transition* transition = org_transition->migrateTransition(*grounded_from_dtg_node, *grounded_to_dtg_node, initial_facts);
				if (transition != NULL)
				{
					if (!transition->finalise(initial_facts))
					{
						delete transition;
						continue;
					}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cout << "Grounded transition: " << *transition << std::endl;
#endif
					grounded_from_dtg_node->addTransition(*transition);
				}
			}
		}
	}
	
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = old_nodes.begin(); ci != old_nodes.end(); ++ci)
	{
		delete *ci;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "Grounded DTG: " << std::endl;
	std::cout << *this << std::endl;
#endif
*/
//	std::cout << "Result: " << *this << std::endl;
}

MultiValuedValue* LiftedDTG::getMultiValuedValue(const PropertyState& property_state) const
{
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		if (&(*ci)->getPropertyState() == &property_state)
		{
			return *ci;
		}
	}
	assert (false);
	return NULL;
}

std::ostream& operator<<(std::ostream& os, const LiftedDTG& lifted_dtg)
{
	os << " === Lifted DTG === " << std::endl;
	os << "Invariable objects: ";
	for (std::vector<const Object*>::const_iterator ci = lifted_dtg.invariable_objects_.begin(); ci != lifted_dtg.invariable_objects_.end(); ++ci)
	{
		os << **ci << ", ";
	}
	os << std::endl;
	for (std::vector<MultiValuedValue*>::const_iterator ci = lifted_dtg.nodes_.begin(); ci != lifted_dtg.nodes_.end(); ++ci)
	{
		assert (*ci != NULL);
		os << **ci << std::endl;
	}
	return os;
}

};

void Graphviz::printToDot(const std::vector<SAS_Plus::LiftedDTG*>& all_lifted_dtgs)
{
	std::ofstream ofs;
	ofs.open("dtgs.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	for (std::vector<SAS_Plus::LiftedDTG*>::const_iterator ci = all_lifted_dtgs.begin(); ci != all_lifted_dtgs.end(); ci++)
	{
		assert (*ci != NULL);
		Graphviz::printToDot(ofs, **ci);
	}
	
	ofs << "}" << std::endl;
	ofs.close();
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::MultiValuedTransition& transition)
{
	printToDot(ofs, transition.getFromNode());
	ofs << " -> ";
	printToDot(ofs, transition.getToNode());
	ofs << "[ label=\"" << ofs << "\"]" << std::endl;
//	transition.getAction().print(ofs);
//	ofs << "\"]" << std::endl;
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::MultiValuedValue& dtg_node)
{
	ofs << "\"[" << &dtg_node << "]";
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = dtg_node.getValues().begin(); ci != dtg_node.getValues().end(); ci++)
	{
		assert (*ci != NULL);
		ofs << **ci;
		
		if (ci + 1 != dtg_node.getValues().end())
		{
			ofs << "\\n";
		}
	}
	ofs << "\"";
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::LiftedDTG& dtg)
{
	// Declare the nodes.
	for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = dtg.getNodes().begin(); ci != dtg.getNodes().end(); ci++)
	{
		assert (*ci != NULL);
		const SAS_Plus::MultiValuedValue* dtg_node = *ci;
		printToDot(ofs, *dtg_node);
		
		// Create a dotted lines if this node is a copy of another.
		if (dtg_node->isCopy())
		{
			ofs << " [style=dotted];" << std::endl;
		}
		ofs << std::endl;
	}
	
	// Create the edges.
	for (std::vector<SAS_Plus::MultiValuedValue*>::const_iterator ci = dtg.getNodes().begin(); ci != dtg.getNodes().end(); ci++)
	{
		assert (*ci != NULL);
		const SAS_Plus::MultiValuedValue* dtg_node = *ci;
		
		for (std::vector<const SAS_Plus::MultiValuedTransition*>::const_iterator transitions_ci = dtg_node->getTransitions().begin(); transitions_ci != dtg_node->getTransitions().end(); transitions_ci++)
		{
			const SAS_Plus::MultiValuedTransition* transition = *transitions_ci;
			printToDot(ofs, *transition);
		}
	}
}

};