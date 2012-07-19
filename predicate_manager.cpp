#include <assert.h>
#include <cctype>
#include <algorithm>
#include "VALfiles/TimSupport.h"
#include "VALfiles/TypedAnalyser.h"
#include "predicate_manager.h"
#include "action_manager.h"
#include "type_manager.h"
#include "formula.h"

///#define MYPOP_PREDICATE_COMMENTS

namespace MyPOP {

std::vector<const Predicate*> Predicate::all_predicates_;
std::map<std::pair<std::string, std::vector<const Type*> >, Predicate*> Predicate::predicate_map_;
	
//Predicate::Predicate(const std::string& name)
Predicate::Predicate(unsigned int id, const std::string& name, const std::vector<const Type*>& types, bool is_static)
	: id_(id), name_(name), types_(&types), is_static_(is_static), can_substitute_(NULL)
{

}

Predicate::~Predicate()
{
	delete types_;
	if (can_substitute_ != NULL)
	{
		delete[] can_substitute_;
	}
}

bool Predicate::canSubstitute(const Predicate& predicate) const
{
	if (can_substitute_ == NULL)
	{
		if (predicate.getName() != name_)
			return false;

		if (predicate.getArity() != getArity())
			return false;

		// Check if the types match up.
		for (unsigned int i = 0; i < getArity(); i++)
		{
			const Type* this_type = (*types_)[i];
			const Type* other_type = (*predicate.types_)[i];
			
			if (this_type != other_type && !this_type->isSupertypeOf(*other_type))
			{
				return false;
			}
		}
		return true;
	}
	else
	{
		return can_substitute_[predicate.getId()];
	}
}

bool Predicate::operator==(const Predicate& predicate) const
{
	if (predicate.getName() != name_)
		return false;
	
	if (predicate.getArity() != getArity())
		return false;

	// Check if the types match up.
	for (unsigned int i = 0; i < getArity(); i++)
	{
		const Type* this_type = (*types_)[i];
		const Type* other_type = (*predicate.types_)[i];
		
		if (this_type != other_type)
			return false;
	}

	return true;
}

bool Predicate::operator!=(const Predicate& predicate) const
{
	return !(predicate == *this);
}

void Predicate::initCache()
{
	bool* can_substitute_tmp = new bool[all_predicates_.size()];
	memset(can_substitute_tmp, false, sizeof(bool) * all_predicates_.size());
	
	for (unsigned int i = 0; i < all_predicates_.size(); i++)
	{
		can_substitute_tmp[i] = canSubstitute(*all_predicates_[i]);
	}
	
	can_substitute_ = can_substitute_tmp;
}

std::ostream& operator<<(std::ostream& os, const Predicate& predicate)
{
	os << "(" << predicate.name_;
	for (std::vector<const Type*>::const_iterator ci = predicate.types_->begin(); ci != predicate.types_->end(); ci++)
	{
		os << " " << (*ci)->getName();
	}
	os << ")";
	if (predicate.is_static_)
	{
		os << "[static]";
	}

	return os;
}

void Predicate::processPredicates(const VAL::pred_decl_list& predicates, const TypeManager& type_manager)
{
	std::vector<Predicate*> all_generated_predicates;
	/**
	 * Prior to calling this function, TIM analysis is done on the domain. To retrieve this information
	 * we need to cast the predicate symbol of the VAL::pred_decl instances into the TIM equivalent one.
	 * Than we can proceed with detecting its properties.
	 * A predicate symbol can contain more than a single TIM analysis as the predicate might have different
	 * behavious based on the type of its variables. Therefor we construct a separate predicate for every
	 * possible combination.
	 * Note: We can reduce this, if we know that the behaviour is equal, but we leave this for future work.
	 */
	for (VAL::pred_decl_list::const_iterator ci = predicates.begin(); ci != predicates.end(); ci++)
	{
		VAL::pred_decl* predicate_declaration = *ci;
		VAL::holding_pred_symbol* hps = HPS(predicate_declaration->getPred());
		const std::string& raw_predicate_name = hps->getName();
		std::string predicate_name(raw_predicate_name);
		std::transform(raw_predicate_name.begin(), raw_predicate_name.end(), predicate_name.begin(), (int(*)(int))std::tolower);
		assert (raw_predicate_name.size() > 0);
		assert (predicate_name.size() > 0);
		for (VAL::holding_pred_symbol::PIt i = hps->pBegin();i != hps->pEnd();++i)
		{
			const TIM::TIMpredSymbol* tps = static_cast<const TIM::TIMpredSymbol*>(*i);

			// Build a list of all types this predicate holds.
			//std::vector<const Type*>* types = new std::vector<const Type*>();
			std::vector<const Type*> types;
			for (VAL::Types::const_iterator tim_pred_ci = tps->tcBegin(); tim_pred_ci != tps->tcEnd(); tim_pred_ci++)
			{
				const VAL::pddl_typed_symbol* pts = *tim_pred_ci;
				const Type* type = type_manager.getType(pts->type->getName());
				assert(type != NULL);
				
				types.push_back(type);
			}

			// Check if this predicate is static.
			bool is_static = tps->isDefinitelyStatic();
			//Predicate* predicate = new Predicate(predicate_name, *types, is_static);
			
			// Create all the predicates which can be created from more generic types.
			unsigned int type_parents[types.size()];
			unsigned int current_type_parents[types.size()];
			for (unsigned int i = 0; i < types.size(); i++)
			{
				unsigned int type_depth = 1;
				const Type* type = types[i];
				while ((type = type->getSupertype()) != NULL)
				{
					++type_depth;
				}
				type_parents[i] = type_depth;
				current_type_parents[i] = 0;
			}
			
			bool done = false;
			while (!done)
			{
				done = true;
				std::vector<const Type*>* new_types = new std::vector<const Type*>();
				for (unsigned int i = 0; i < types.size(); i++)
				{
					const Type* type = types[i];
					for (unsigned int depth = 0; depth < current_type_parents[i]; depth++)
					{
						type = type->getSupertype();
					}
					new_types->push_back(type);
				}
				
				if (predicate_map_.find(std::make_pair(predicate_name, *new_types)) == predicate_map_.end())
				{
					Predicate* new_predicate = new Predicate(all_predicates_.size(), predicate_name, *new_types, is_static);
					predicate_map_[std::make_pair(predicate_name, *new_types)] = new_predicate;
					all_predicates_.push_back(new_predicate);
					all_generated_predicates.push_back(new_predicate);
				}
				
				for (unsigned int i = 0; i < types.size(); i++)
				{
					if (current_type_parents[i] + 1 != type_parents[i])
					{
						current_type_parents[i] = current_type_parents[i] + 1;
						done = false;
						break;
					}
					else
					{
						current_type_parents[i] = 0;
					}
				}
			}

#ifdef MYPOP_PREDICATE_COMMENTS
			std::cout << "Predicate: " << *predicate << std::endl;
#endif
		}
	}
	
	std::for_each (all_generated_predicates.begin(), all_generated_predicates.end(), std::mem_fun(&Predicate::initCache));
}

void Predicate::checkStaticPredicates(const ActionManager& action_manager)
{
	for (std::map<std::pair<std::string, std::vector<const Type*> >, Predicate*>::const_iterator ci = predicate_map_.begin(); ci != predicate_map_.end(); ci++)
	{
		Predicate* predicate = (*ci).second;

		// Check if there exists an operator who affects this predicate.
		// NOTE: We do not check if this operator can be applied in the current domain, leave that for another time :).
		bool appears_in_effects = false;
		for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); !appears_in_effects && ci != action_manager.getManagableObjects().end(); ci++)
		{
			const Action* action = *ci;

			for (std::vector<const Atom*>::const_iterator ci = action->getEffects().begin(); ci != action->getEffects().end(); ci++)
			{
				const Atom* effect = *ci;

				// Check if the effect can be linked to the predicate.
				if (effect->getPredicate().getName() != predicate->getName())
				{
					continue;
				}

				// Compare types, if the effect affects any subtype of the predicates the predicate cannot be static.
				bool types_are_compatible = true;
				for (unsigned int i = 0; i < predicate->getTypes().size(); i++)
				{
					const Type* predicate_type = predicate->getTypes()[i];
					const Type* effect_type = effect->getPredicate().getTypes()[i];

					if (!predicate_type->isEqual(*effect_type) && !effect_type->isSubtypeOf(*predicate_type) && !predicate_type->isSubtypeOf(*effect_type))
					{
						types_are_compatible = false;
						break;
					}
				}

				if (types_are_compatible)
				{
//					std::cout << "Predicate: " << *predicate << " is affected by ";
//					effect->print(std::cout);
//					std::cout << std::endl;
					appears_in_effects = true;
					break;
				}
			}
		}

		predicate->is_static_ = !appears_in_effects;
	}
}

const Predicate& Predicate::getPredicate(const TIM::Property& property, const TypeManager& type_manager)
{
	const VAL::extended_pred_symbol* extended_property = property.root();
	std::vector<const Type*> predicate_types;
	for(std::vector<VAL::pddl_typed_symbol*>::const_iterator esp_i = extended_property->tcBegin(); esp_i != extended_property->tcEnd(); ++esp_i)
	{
		const Type* type = type_manager.getType((*esp_i)->type->getName());
		assert (type != NULL);
		predicate_types.push_back(type);
	}

	return Predicate::getPredicate(extended_property->getName(), predicate_types);
}

const Predicate& Predicate::getPredicate(const std::string& name, const std::vector<const Type*>& types)
{
	assert (name.size() > 0);
	std::string lower_case_name(name);
	std::transform(name.begin(), name.end(), lower_case_name.begin(), (int(*)(int))std::tolower);
	map<std::pair<std::string, std::vector<const Type*> >, Predicate*>::const_iterator ci = predicate_map_.find(std::make_pair(lower_case_name, types));
	if (ci == predicate_map_.end())
	{
		std::cerr << "Could not find a predicate with the following characteristics: (" << name << " ";
		for (std::vector<const Type*>::const_iterator ci = types.begin(); ci != types.end(); ci++)
		{
			std::cerr << **ci << " ";
		}
		std::cerr << ")" << std::endl;
		assert (false);
		exit(1);
	}
	return *(*ci).second;
}

};

