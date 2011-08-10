#include <assert.h>
#include "VALfiles/TimSupport.h"
#include "VALfiles/TypedAnalyser.h"
#include "predicate_manager.h"
#include "action_manager.h"
#include "type_manager.h"
#include "formula.h"

///#define MYPOP_PREDICATE_COMMENTS

namespace MyPOP {

//Predicate::Predicate(const std::string& name)
Predicate::Predicate(const std::string& name, const std::vector<const Type*>& types, bool is_static)
	: name_(name), types_(&types), is_static_(is_static)
{
	
}

Predicate::~Predicate()
{
	delete types_;
}

void Predicate::makeStatic(bool make_static)
{
	if (make_static == is_static_)
		return;

	is_static_ = make_static;
//	std::cout << "Make static: " << *this << " : " << make_static << std::endl;
}

bool Predicate::canSubstitute(const Predicate& predicate) const
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

PredicateManager::PredicateManager(const TypeManager& type_manager)
	: type_manager_(&type_manager)
{

}

PredicateManager::~PredicateManager()
{
	for (std::map<std::pair<std::string, std::vector<const Type*> >, Predicate*>::iterator i = predicate_map_.begin(); i != predicate_map_.end(); i++)
	{
		delete (*i).second;
	}
}

void PredicateManager::processPredicates(const VAL::pred_decl_list& predicates)
{
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
		const std::string& predicate_name = hps->getName();

		for (VAL::holding_pred_symbol::PIt i = hps->pBegin();i != hps->pEnd();++i)
		{
			const TIM::TIMpredSymbol* tps = static_cast<const TIM::TIMpredSymbol*>(*i);
//			tps->write(std::cout);
//			std::cout << "\nIs definitely static " << tps->isDefinitelyStatic() << tps->isStatic() << std::endl;
//			std::cout << ", ";

			// Build a list of all types this predicate holds.
			std::vector<const Type*>* types = new std::vector<const Type*>();

			for (VAL::Types::const_iterator tim_pred_ci = tps->tcBegin(); tim_pred_ci != tps->tcEnd(); tim_pred_ci++)
			{
				const VAL::pddl_typed_symbol* pts = *tim_pred_ci;
				const Type* type = type_manager_->getType(pts->type->getName());
				assert(type != NULL);
				
				types->push_back(type);
			}

			// Check if this predicate is static.
			bool is_static = tps->isDefinitelyStatic();

			Predicate* predicate = new Predicate(predicate_name, *types, is_static);
	
			// Store this to our table.
			predicate_map_[std::make_pair(predicate_name, *types)] = predicate;
			addManagableObject(predicate);

#ifdef MYPOP_PREDICATE_COMMENTS
			std::cout << "Predicate: " << *predicate << std::endl;
#endif

			// Find the most generalised types.
			std::vector<const Type*>* general_types = NULL;
			std::map<std::string, std::vector<const Type*>* >::const_iterator type_ci = general_predicates_.find(predicate_name);
			if (type_ci == general_predicates_.end())
			{
				general_types = new std::vector<const Type*>();
				general_predicates_[predicate_name] = general_types;
			}
			else
			{
				general_types = (*type_ci).second;
			}

#ifdef MYPOP_PREDICATE_COMMENTS
			std::cout << "Find super types for: " << predicate_name << std::endl;
#endif


			if (general_types->size() == 0)
			{
				for (unsigned int i = 0; i < types->size(); i++)
				{
					const Type* current_type = (*types)[i];
					general_types->push_back(current_type);
				}
			}

			else
			{
				for (unsigned int i = 0; i < types->size(); i++)
				{
					const Type* current_type = (*types)[i];
#ifdef MYPOP_PREDICATE_COMMENTS
					std::cout << "Check " << i << "th type" << std::endl;
					std::cout << *current_type << std::endl;
					std::cout << " v.s. current general type: " << std::endl;
					std::cout << *(*general_types)[i] << std::endl;
#endif

					if ((*general_types)[i]->isSubtypeOf(*current_type))
					{
#ifdef MYPOP_PREDICATE_COMMENTS
						std::cout << "- " << *(*general_types)[i] << " is a subtype of " << *current_type << std::endl;
#endif
						(*general_types)[i] = current_type;
					}
					else if ((*general_types)[i] != current_type && !current_type->isSubtypeOf(*(*general_types)[i]))
					{
						// If this type is not the same nor the subtype, we must find for the supertype both are members of.
						const Type* super_type = (*general_types)[i]->getSupertype();
						
						///std::cout << "The super type of the general type " << *(*general_types)[i] << " is " << *super_type << std::endl;
						
						while (super_type != NULL && !current_type->isSubtypeOf(*super_type) && current_type != super_type)
						{
#ifdef MYPOP_PREDICATE_COMMENTS
							std::cout << "- " << "Is: " << *super_type << " a super type of " << *current_type << "?" << std::endl;
#endif
							super_type = super_type->getSupertype();
#ifdef MYPOP_PREDICATE_COMMENTS
							if (super_type != NULL)
							{
								std::cout << "- New super type: " << *super_type << std::endl;
							}
							else
							{
								std::cout << "- No supertype found!" << std::endl;
							}
#endif
						}
						assert (super_type != NULL);

#ifdef MYPOP_PREDICATE_COMMENTS
						std::cout << "- " << "Super type!!!" << *super_type << std::endl;
#endif
						(*general_types)[i] = super_type;
					}
					else
					{
#ifdef MYPOP_PREDICATE_COMMENTS
						std::cout << "- The same." << std::endl;
#endif
					}
				}
			}

#ifdef MYPOP_PREDICATE_COMMENTS
			if (getGeneralPredicate(predicate_name) != NULL)
			{
				std::cout << "Generalised types for predicate: " << *predicate << ": " << *getGeneralPredicate(predicate_name) << std::endl;
			}
#endif
		}
	}

	// Make sure all the generalised predicates have been created.
	for (std::map<std::string, std::vector<const Type*>* >::const_iterator ci = general_predicates_.begin(); ci != general_predicates_.end(); ci++)
	{
		std::string name = (*ci).first;
		if (getGeneralPredicate(name) == NULL)
		{
			assert (predicate_map_.count(std::make_pair(name, *(*ci).second)) == 0);
			Predicate* predicate = new Predicate(name, *(*ci).second, false);
			predicate_map_[std::make_pair(name, *(*ci).second)] = predicate;
			addManagableObject(predicate);
		}
	}
}

void PredicateManager::checkStaticPredicates(const ActionManager& action_manager)
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

		predicate->makeStatic(!appears_in_effects);
	}
}

const Predicate* PredicateManager::getPredicate(const std::string& name, const std::vector<const Type*>& types) const
{
//	std::cout << "Find predicate " << name << std::endl;
//	for (std::vector<const Type*>::const_iterator ci = types.begin(); ci != types.end(); ci++)
//	{
//		std::cout << "- " << **ci << std::endl;
//	}
	map<std::pair<std::string, std::vector<const Type*> >, Predicate*>::const_iterator ci = predicate_map_.find(std::make_pair(name, types));
	if (ci == predicate_map_.end())
	{
		return NULL;
		//assert (false);
	}
	return (*ci).second;
}

const Predicate* PredicateManager::getGeneralPredicate(const std::string& name) const
{
//	std::cout << "Find general predicate " << name << std::endl;
	std::map<std::string, std::vector<const Type*>* >::const_iterator type_ci = general_predicates_.find(name);

	if (type_ci == general_predicates_.end())
	{
		return NULL;
	}

	return getPredicate(name, *(*type_ci).second);
}

}
