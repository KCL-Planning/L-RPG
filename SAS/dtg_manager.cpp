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

namespace MyPOP {

namespace SAS_Plus {

/***********************
 * Bounded Atom...
 **********************/
BoundedAtom::BoundedAtom(StepID id, const Atom& atom, const Property* property)
	: id_(id), atom_(&atom), property_(property)
{

}

BoundedAtom::~BoundedAtom()
{

}

StepID BoundedAtom::getId() const
{
	return id_;
}

const Atom& BoundedAtom::getAtom() const
{
	return *atom_;
}

InvariableIndex BoundedAtom::getIndex(StepID id, const Term& term, const Bindings& bindings) const
{
	for (InvariableIndex i = 0; i < atom_->getArity(); i++)
	{
		const Term* bounded_term = atom_->getTerms()[i];
		
		if (bounded_term->isTheSameAs(id_, term, id, bindings))
		{
			return i;
		}
	}
	
	assert (false);
}

const Property* BoundedAtom::getProperty() const
{
	return property_;
}

bool BoundedAtom::isMutexWith(const BoundedAtom& other) const
{
	if (property_ != NULL)
	{
		return property_->isMutexWith(other.getProperty());
	}
	
	return false;
}

/*bool BoundedAtom::isMutexWith(StepID id, const Atom& atom, InvariableIndex invariable_index, const Bindings& bindings) const
{
	if (property_ == NULL)
	{
//		std::cout << "[BoundedAtom::isMutexWith] No property state, can't test mutexes..." << std::endl;
		return false;
	}
	
	std::cout << "[BoundedAtom::isMutexWith] ";
	print(std::cout, bindings);
	std::cout << std::endl;
	std::cout << "[BoundedAtom::isMutexWith] Test against: " << atom.getPredicate() << "[" << invariable_index << "]" << std::endl;
	
	// If the predicate is present in this bounded atom's property state it isn't mutex.
	const std::vector<Property*>& lhs_properties = property_->getPropertyState().getProperties();
	for (std::vector<Property*>::const_iterator ci = lhs_properties.begin(); ci != lhs_properties.end(); ci++)
	{
		const Property* property = *ci;
///		std::cout << "[BoundedAtom::isMutexWith] LHS property: " << property->getPredicate().getName() << "[" << property->getIndex() << "]" << std::endl;
		if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index)
		{
			return false;
		}
	}

	for (std::vector<const PropertyState*>::const_iterator ci = property_->getPropertyState().getPropertySpace().getPropertyStates().begin(); ci !=  property_->getPropertyState().getPropertySpace().getPropertyStates().end(); ci++)
	{
		const PropertyState* property_state = *ci;
		const std::vector<Property*>& properties = property_state->getProperties();
		if (property_state == &property_->getPropertyState())
		{
			continue;
		}
		
		for (std::vector<Property*>::const_iterator ci = properties.begin(); ci != properties.end(); ci++)
		{
			const Property* property = *ci;
			std::cout << "[BoundedAtom::isMutexWith] Check against: " << property->getPredicate().getName() << "[" << property->getIndex() << "]" << std::endl;
			
			std::cout << 
			std::cout << *atom.getTerms()[invariable_index] << std::endl;
			std::cout << *atom_->getTerms()[invariable_index] << std::endl;
			
			if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index &&
			    atom.getTerms()[invariable_index]->canUnify(id, *atom_->getTerms()[invariable_index], id_, bindings))
			{
				return true;
			}
		}
	}
	
	return false;
}*/

bool BoundedAtom::isMutexWith(const Atom& atom, StepID step_id, const Bindings& bindings, InvariableIndex invariable_index) const
{
	if (property_ == NULL)
	{
//		std::cout << "[BoundedAtom::isMutexWith] No property state, can't test mutexes..." << std::endl;
		return false;
	}
	
//	std::cout << "[BoundedAtom::isMutexWith] Is ";
//	print(std::cout, bindings);
//	std::cout << "[" << property_->getIndex() << "] mutex with ";
//	atom.print(std::cout, bindings, step_id);
//	std::cout << "[" << invariable_index << "]" << std::endl;

	// Make sure the invariables are in agreement.
	if (!atom.getTerms()[invariable_index]->canUnify(step_id, *atom_->getTerms()[property_->getIndex()], id_, bindings))
	{
//		std::cout << "The invariables are not the same, so they cannot be mutex by default!" << std::endl;
		return false;
	}
	
	// If the predicate is present in this bounded atom's property state it isn't mutex.
	const std::vector<Property*>& lhs_properties = property_->getPropertyState().getProperties();
	for (std::vector<Property*>::const_iterator ci = lhs_properties.begin(); ci != lhs_properties.end(); ci++)
	{
		const Property* property = *ci;
//		std::cout << "[BoundedAtom::isMutexWith] LHS property: " << property->getPredicate().getName() << "[" << property->getIndex() << "]" << std::endl;
		if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index)
		{
			return false;
		}
	}


	for (std::vector<const PropertyState*>::const_iterator ci = property_->getPropertyState().getPropertySpace().getPropertyStates().begin(); ci !=  property_->getPropertyState().getPropertySpace().getPropertyStates().end(); ci++)
	{
		const PropertyState* property_state = *ci;
		const std::vector<Property*>& properties = property_state->getProperties();
		
		// If the property states are the same they are not mutex (already tested above).
		if (property_state == &property_->getPropertyState())
		{
			continue;
		}
		
		// If the property of another property states matches with the given one we conclude it must be mutex.
		for (std::vector<Property*>::const_iterator ci = properties.begin(); ci != properties.end(); ci++)
		{
			const Property* property = *ci;
//			std::cout << "[BoundedAtom::isMutexWith] Check against: " << property->getPredicate().getName() << "[" << property->getIndex() << "]" << std::endl;
			if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index)
			{
				return true;
			}
		}
	}
	
	return false;
}

void BoundedAtom::print(std::ostream& os, const Bindings& bindings) const
{
	atom_->print(os, bindings, id_);
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

		//const Predicate& predicate = Utility::getPredicate(*type_manager_, *predicate_manager_, *property);
		const VAL::extended_pred_symbol* extended_property = property->root();
		const Predicate* predicate = predicate_manager_->getGeneralPredicate(extended_property->getName());
		assert (predicate != NULL);

		// Adding the predicate to the DTG will also create a lifted DTG node with that predicate.
		// Further refinements can be made to this DTG by splitting these nodes.
		predicates.push_back(std::make_pair(predicate, property->aPosn()));
	}
}


void DomainTransitionGraphManager::generateDomainTransitionGraphsTIM(const VAL::pddl_type_list& types, const Bindings& bindings)
{
	struct timeval start_time_tim_translation;
	gettimeofday(&start_time_tim_translation, NULL);
	
	// Store temporary DTGs in this vector, during post processing they might get split again. Only then will we add the DTGs as a managable object (see Manager class).
	std::vector<DomainTransitionGraph*> tmp_dtgs;
	
	std::vector<TIM::PropertySpace*> property_spaces;
	property_spaces.insert(property_spaces.end(), TIM::TA->pbegin(), TIM::TA->pend());
//	property_spaces.insert(property_spaces.end(), TIM::TA->abegin(), TIM::TA->aend());
//	property_spaces.insert(property_spaces.end(), TIM::TA->sbegin(), TIM::TA->send());

	// Construct the DTGs by combining all properties which appear together in either the LHS or RHS of a transition rule.
	for (std::vector<TIM::PropertySpace*>::const_iterator property_space_i = property_spaces.begin(); property_space_i != property_spaces.end(); ++property_space_i)
	{
		TIM::PropertySpace* property_space = *property_space_i;
		
		PropertySpace* dtg_property_space = new PropertySpace();
		
		std::set<std::vector<std::pair<const Predicate*, unsigned int> > > processed_expressions;
		
		//std::vector<std::vector<std::pair<const Predicate*, InvariableIndex> >* > predicates_to_add;
		///std::vector<PropertyState*> property_states;
		
		// The DTG where all predicates will be added to.
		///DomainTransitionGraph* dtg = new DomainTransitionGraph(*this, *dtg_property_space, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);
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
					
					std::cout << "!Rule: ";
					rule_a->getLHS()->write(std::cout);
					std::cout << " -> ";
					rule_a->getRHS()->write(std::cout);
					std::cout << " is a proper subset of: ";
					rule_b->getLHS()->write(std::cout);
					std::cout << " -> ";
					rule_b->getRHS()->write(std::cout);
					std::cout << std::endl;
					
					std::cout << "Generate new rule: " << std::endl;
					rule_b->getLHS()->write(std::cout);
					std::cout << " =--> ";
					rule_a->getRHS()->write(std::cout);
					std::cout << " ++ ";
					
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
						
						property->write(std::cout);
						std::cout << " ++ ";
					}
					std::cout << std::endl;
					
					if (processed_expressions.count(predicates_rhs) == 0)
					{
						//dtg->addPredicate(predicates_rhs, true);
						//predicates_to_add.insert(predicates_to_add.end(), predicates_rhs.begin(), predicates_rhs.end());
						///property_states.push_back(new PropertyState(*dtg_property_space, predicates_rhs));
						PropertyState* new_property_state = new PropertyState(*dtg_property_space, predicates_rhs);
						dtg_property_space->addPropertyState(*new_property_state);
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
				//dtg->addPredicate(predicates, true);
				//predicates_to_add.insert(predicates_to_add.end(), predicates.begin(), predicates.end());
///				property_states.push_back(new PropertyState(*dtg_property_space, predicates));
				PropertyState* new_property_state = new PropertyState(*dtg_property_space, predicates);
				dtg_property_space->addPropertyState(*new_property_state);
				processed_expressions.insert(predicates);
			}
			
			predicates.clear();
			getProperties(predicates, *rule->getRHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				//dtg->addPredicate(predicates, true);
				//predicates_to_add.insert(predicates_to_add.end(), predicates.begin(), predicates.end());
				///property_states.push_back(new PropertyState(*dtg_property_space, predicates));
				PropertyState* new_property_state = new PropertyState(*dtg_property_space, predicates);
				dtg_property_space->addPropertyState(*new_property_state);
				processed_expressions.insert(predicates);
			}
		}
		
		dtg->addBalancedSet(*dtg_property_space, true);

		std::cout << " === DTG after adding all predicates === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
		
		//addTransitions(*dtg);
		//dtg->reestablishTransitions();
		dtg->establishTransitions();

		std::cout << " === DTG after adding all transitions === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;

		dtg->addObjects();

		std::cout << " === DTG after adding all objects === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;

		addManagableObject(dtg);
	}
	struct timeval end_time_tim_translation;
	gettimeofday(&end_time_tim_translation, NULL);
	
	double time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "TIM transation took: " << time_spend << " seconds" << std::endl;

	/**
	 * After constructing the DTGs based on the TIM analysis, we now need to take it a little further. This 
	 * part is the Merge and Ground phase. Every transition in each DTG is checked, if a precondition references
	 * to another DTG whose properties link to the same set of objects (or subset thereof) than these DTGs need to
	 * be merged because they both describe (relevant) properties linked to the same object.
	 *
	 * To merge a DTG node we clone that node for every node in the DTG linked to the precondition and merge all atoms.
	 * The original node is removed and replaced by the clones and the transitions are reevaluated. The DTG we merged with
	 * will loose a subset of the objects linked to it since the property have now been taken over by the DTG it merged 
	 * with. The only objects remaining will be the difference, if this set is empty the DTG merged with will be removed.
	 *
	 * The next phase is to identify which properties need to be grounded.
	 */
	gettimeofday(&start_time_tim_translation, NULL);
	mergeDTGs();
	gettimeofday(&end_time_tim_translation, NULL);
	time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "Merging DTGs took: " << time_spend << " seconds" << std::endl;
	
	std::cout << "RESULTS AFTER MERGING" << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		std::cout << "Resulting DTG after merging: " << *dtg << std::endl;
	}
	
	/**
	 * Split phase:
	 * After merging the DTGs linked by preconditions which share the same invariable, we now tend to the
	 * variables which are not invariable. For these, we need to ground them out.
	 */
	gettimeofday(&start_time_tim_translation, NULL);
	splitDTGs();
	gettimeofday(&end_time_tim_translation, NULL);
	time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "Grounding DTGs took: " << time_spend << " seconds" << std::endl;
	
	std::cout << "RESULTS AFTER GROUNDING" << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		std::cout << "Resulting DTG after grounding: " << *dtg << std::endl;
	}
	
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
	std::set<const DomainTransitionGraph*> unsupported_predicates_dtg;
	for (std::vector<Predicate*>::const_iterator ci = predicate_manager_->getManagableObjects().begin(); ci != predicate_manager_->getManagableObjects().end(); ci++)
	{
		const Predicate* predicate = *ci;
		bool is_supported = false;
		
		std::cout << "Check if the predicate : " << *predicate << " is supported!" << std::endl;
		
		// Check if any of the DTG nodes supports the given predicate by making a dummy atom of it.
		std::vector<const Term*>* new_terms = new std::vector<const Term*>();
		for (std::vector<const Type*>::const_iterator ci = predicate->getTypes().begin(); ci != predicate->getTypes().end(); ci++)
		{
			const Type* type = *ci;
			new_terms->push_back(new Variable(*type, "test"));
		}
		Atom* possitive_atom = new Atom(*predicate, *new_terms, false);

		assert (objects_.size() > 0);
		
		// Check if this predicate is present.
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
		{
			const DomainTransitionGraph* dtg = *ci;
			
			StepID test_atom_id = dtg->getBindings().createVariableDomains(*possitive_atom);
			std::vector<const DomainTransitionGraphNode*> found_nodes;
			dtg->getNodes(found_nodes, test_atom_id, *possitive_atom, dtg->getBindings());
			
			if (found_nodes.size() > 0)
			{
				std::cout << "The predicate " << *predicate << " is supported by " << std::endl;
				for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
				{
					(*ci)->print(std::cout);
					std::cout << std::endl;
				}
				is_supported = true;
				break;
			}
		}
		
		/**
		 * Unsupported predicates come in two varieties:
		 * 1) The predicate is static, so only a single node needs to be constructed with these values.
		 * 2) The predicate is not static, but can only be made true or false. This is encoded using two
		 * nodes and all relevant transitions between the two. The other node must contain the atom negated.
		 */
		if (!is_supported)
		{
			std::cout << "The predicate: " << *predicate << " is not processed yet!" << std::endl;
			
			// 1) The predicate is static.
			///PropertySpace* property_space = new PropertySpace();
			///DomainTransitionGraph* new_dtg = new DomainTransitionGraph(*this, *property_space, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);
			DomainTransitionGraph* new_dtg = new DomainTransitionGraph(*this, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);
			unsupported_predicates_dtg.insert(new_dtg);
			std::vector<std::pair<const Predicate*, unsigned int> >* predicates_to_add = new std::vector<std::pair<const Predicate*, unsigned int> >();
			predicates_to_add->push_back(std::make_pair(predicate, NO_INVARIABLE_INDEX));
			
			DomainTransitionGraphNode* possitive_new_dtg_node = new DomainTransitionGraphNode(*new_dtg, std::numeric_limits<unsigned int>::max());
			
			StepID possitive_atom_id = new_dtg->getBindings().createVariableDomains(*possitive_atom);
			
			/// TEST
			PropertySpace* property_space = new PropertySpace();
			PropertyState* property_state = new PropertyState(*property_space, *predicates_to_add);
			possitive_new_dtg_node->addAtom(new BoundedAtom(possitive_atom_id, *possitive_atom, property_state->getProperties()[0]), NO_INVARIABLE_INDEX);
			
			///possitive_new_dtg_node->addAtom(new BoundedAtom(possitive_atom_id, *possitive_atom, NULL), NO_INVARIABLE_INDEX);
			new_dtg->addNode(*possitive_new_dtg_node);

			addManagableObject(new_dtg);
			
			// 2) The predicate is not static.
			if (!predicate->isStatic())
			{
				DomainTransitionGraphNode* negative_new_dtg_node = new DomainTransitionGraphNode(*new_dtg, std::numeric_limits<unsigned int>::max());
				Atom* negative_atom = new Atom(*predicate, *new_terms, true);
				StepID negative_atom_id = new_dtg->getBindings().createVariableDomains(*possitive_atom);
				
				///negative_new_dtg_node->addAtom(new BoundedAtom(negative_atom_id, *negative_atom, NULL), NO_INVARIABLE_INDEX);
				negative_new_dtg_node->addAtom(new BoundedAtom(negative_atom_id, *negative_atom, property_state->getProperties()[0]), NO_INVARIABLE_INDEX);
				new_dtg->addNode(*negative_new_dtg_node);
				
				std::cout << "Simple DTG : " << *new_dtg << std::endl;
				
				// Find all transitions which can make this predicate true and false and add them as transitions.
				std::vector<std::pair<const Action*, const Atom*> > achievers;
				action_manager_->getAchievingActions(achievers, *possitive_atom);
				
				for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator ci = achievers.begin(); ci != achievers.end(); ci++)
				{
					const Action* achieving_action = (*ci).first;
					
					// Create a transition between the two nodes.
					std::vector<BoundedAtom>* enablers = new std::vector<BoundedAtom>();
					///Transition::createTransition(*enablers, *achieving_action, *negative_new_dtg_node, *possitive_new_dtg_node, *initial_facts_);
					const Transition* transition = Transition::createSimpleTransition(*enablers, *achieving_action, *negative_new_dtg_node, *possitive_new_dtg_node, *initial_facts_);
					
					if (transition != NULL)
					{
						negative_new_dtg_node->addTransition(*transition, false);
					}
				}
				
				achievers.clear();
				action_manager_->getAchievingActions(achievers, *negative_atom);
				
				for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator ci = achievers.begin(); ci != achievers.end(); ci++)
				{
					const Action* achieving_action = (*ci).first;
					
					// Create a transition between the two nodes.
					std::vector<BoundedAtom>* enablers = new std::vector<BoundedAtom>();
					const Transition* transition = Transition::createSimpleTransition(*enablers, *achieving_action, *possitive_new_dtg_node, *negative_new_dtg_node, *initial_facts_);
					if (transition != NULL)
					{
						possitive_new_dtg_node->addTransition(*transition, false);
					}
				}
			}
			
			std::cout << "Resulting DTG: " << *new_dtg << std::endl;
		}
	}

	gettimeofday(&start_time_tim_translation, NULL);
	
	bool graphs_split = true;
	double total_time_identify = 0;
	double total_time_split = 0;
	double total_time_reestablish = 0;
	double total_time_remove = 0;
	struct timeval tmp_start;
	struct timeval tmp_end;
	
	std::cout << " ************** Start splitting the graphs! ******************** " << std::endl;
	
	while (graphs_split)
	{
		graphs_split = false;
	
		/**
		* After creating all the DTGs, we must check if they all form a connected graph, i.e. is every node reachable from all other nodes?
		*/
		std::map<DomainTransitionGraph*, std::vector<DomainTransitionGraph*>* > splitted_mapping;
		for (std::vector<DomainTransitionGraph*>::reverse_iterator ri = objects_.rbegin(); ri != objects_.rend(); ri++)
		{
			DomainTransitionGraph* dtg = *ri;
			
			/**
			 * DTGs who are created to encode facts which can be true or false do not need to be split.
			 */
			if (unsupported_predicates_dtg.count(dtg) != 0)
			{
				continue;
			}
			
			std::cout << "Work on: " << *dtg << "(" << dtg->getNodes().size() << ")" << std::endl;
			
			gettimeofday(&tmp_start, NULL);
			std::vector<DomainTransitionGraph*>* split_graphs = new std::vector<DomainTransitionGraph*>();
			dtg->identifySubGraphs(*split_graphs);
			gettimeofday(&tmp_end, NULL);
			total_time_identify += tmp_end.tv_sec - tmp_start.tv_sec + (tmp_end.tv_usec - tmp_start.tv_usec) / 1000000.0;
			
			/**
			 * Remove the original if it has been split. Also remove all splitted DTGs if there is no initial state which
			 * can be unified with at least one of its nodes.
			 */
			if (split_graphs->size() > 1)
			{
				for (std::vector<DomainTransitionGraph*>::reverse_iterator ri2 = split_graphs->rbegin(); ri2 != split_graphs->rend(); ri2++)
				{
					DomainTransitionGraph* splitted_graph = *ri2;
					std::cout << "Splitted DTG (before reading objects): " << *splitted_graph << std::endl;
					splitted_graph->addObjects();
					std::cout << "Splitted DTG: " << *splitted_graph << std::endl;
					
					if (splitted_graph->getObjects().size() == 0)
					{
						split_graphs->erase(ri2.base() - 1);
					}
				}
				
				splitted_mapping[dtg] = split_graphs;
				objects_.erase(ri.base() - 1);
				
				graphs_split = true;
			}
		}

		/**
		 * Add results of splitting the DTGs.
		 */
		for (std::map<DomainTransitionGraph*, std::vector<DomainTransitionGraph*>* >::const_iterator ci = splitted_mapping.begin(); ci != splitted_mapping.end(); ci++)
		{
			objects_.insert(objects_.end(), (*ci).second->begin(), (*ci).second->end());
		}
		
		/**
		 * Propagate the results of splitting.
		 */
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
		{
			DomainTransitionGraph* dtg = *ci;
			
			/**
			 * DTGs who are created to encode facts which can be true or false do not need to be split.
			 */
			if (unsupported_predicates_dtg.count(dtg) != 0)
			{
				continue;
			}
			
			gettimeofday(&tmp_start, NULL);
			dtg->splitNodes(splitted_mapping);
			gettimeofday(&tmp_end, NULL);
			total_time_split += tmp_end.tv_sec - tmp_start.tv_sec + (tmp_end.tv_usec - tmp_start.tv_usec) / 1000000.0;

			gettimeofday(&tmp_start, NULL);
			dtg->reestablishTransitions();
			gettimeofday(&tmp_end, NULL);
			
			total_time_reestablish += tmp_end.tv_sec - tmp_start.tv_sec + (tmp_end.tv_usec - tmp_start.tv_usec) / 1000000.0;
		}

		gettimeofday(&tmp_start, NULL);
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
		{
			DomainTransitionGraph* dtg = *ci;
			
			/**
			 * DTGs who are created to encode facts which can be true or false do not need to be split.
			 */
			if (unsupported_predicates_dtg.count(dtg) != 0)
			{
				continue;
			}
			
			gettimeofday(&tmp_start, NULL);
			dtg->removeUnsupportedTransitions();
			gettimeofday(&tmp_end, NULL);
			total_time_remove += tmp_end.tv_sec - tmp_start.tv_sec + (tmp_end.tv_usec - tmp_start.tv_usec) / 1000000.0;
		}
		gettimeofday(&tmp_end, NULL);
		total_time_remove += tmp_end.tv_sec - tmp_start.tv_sec + (tmp_end.tv_usec - tmp_start.tv_usec) / 1000000.0;
	}
	gettimeofday(&end_time_tim_translation, NULL);
	time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "* Identifying graphs: " << total_time_identify << " seconds" << std::endl;
	std::cerr << "* Splitting: " << total_time_split << " seconds" << std::endl;
	std::cerr << "* Reestablish transitions: " << total_time_reestablish << " seconds" << std::endl;
	std::cerr << "* Remove unsupported transitions: " << total_time_remove << " seconds" << std::endl;

	std::cout << "RESULTS AFTER SPLITTING" << std::endl;
	std::cout << " === Result === " << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}

	std::cout << " === End === " << std::endl;
	
	std::cout << "FINAL RESULTS" << std::endl;
	std::cout << " === Result === " << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
}

void DomainTransitionGraphManager::mergeDTGs()
{
//	std::cout << " *************** [DomainTransitionGraphManager::mergeDTGs] *******************" << std::endl;
	bool dtg_altered = true;
	while (dtg_altered)
	{
		dtg_altered = false;
		std::map<const DomainTransitionGraph*, std::set<const Object*>* > dtgs_to_remove;
		
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
		{
			DomainTransitionGraph* dtg = *ci;
			
			/**
			 * If the DTG has been merged with another DTG and is marked for removal we do not need to process since all
			 * properties have already been taken over by the other DTG.
			 */
			if (dtgs_to_remove.count(dtg) != 0)
			{
///				std::cout << "Skip: " << *dtg << std::endl;
				continue;
			}
//			std::cout << "Check DTG: " << *dtg << std::endl;
			
			std::vector<DomainTransitionGraphNode*> nodes_to_remove;
			std::vector<DomainTransitionGraphNode*> nodes_to_add;
			
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
			{
				DomainTransitionGraphNode* from_dtg_node = *ci;
				bool merged = false;
				
				for (std::vector<const Transition*>::const_iterator ci = from_dtg_node->getTransitions().begin(); ci != from_dtg_node->getTransitions().end(); ci++)
				{
					const Transition* transition = *ci;


//					std::cout << "Transition: from ";
//					transition->getFromNode().print(std::cout);
//					std::cout << " to ";
//					transition->getToNode().print(std::cout);
//					std::cout << "[" << transition->getStep()->getAction() << "]" << std::endl;

					const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
//					std::vector<std::pair<const Atom*, InvariableIndex> > preconditions;
//					transition->getAllPreconditions(preconditions);
					
					// Check which of the preconditions of this action refers to an external DTG.
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
					{
						const Atom* precondition = (*ci).first;
						InvariableIndex invariable = (*ci).second;

//						std::cout << "Process the precondition: ";
//						precondition->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
//						std::cout << "(" << invariable << ")" << std::endl;

						std::vector<const DomainTransitionGraphNode*> found_dtg_nodes;
						getDTGNodes(found_dtg_nodes, transition->getStep()->getStepId(), *precondition, dtg->getBindings(), invariable);
						
						// If the precondition isn't linked to an invariable we can ignore it. - we'll process it during the grounding phase.
						// Wrong, we need to merge those which are invariable in their respective DTGs.
						if (invariable == NO_INVARIABLE_INDEX)
						{
							continue;
						}
						
						for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = found_dtg_nodes.begin(); ci != found_dtg_nodes.end(); ci++)
						{
							const DomainTransitionGraphNode* precondition_dtg_node = *ci;

//							std::cout << "Candidate: ";
//							precondition_dtg_node->print(std::cout);
//							std::cout << std::endl;

							if (&precondition_dtg_node->getDTG() == &transition->getFromNode().getDTG())
							{
//								std::cout << "- No, part of same DTG!" << std::endl;
								continue;
							}
							
							// Check if the invariable of the external DTG node corresponds with the DTG we are looking at.
							const BoundedAtom* dtg_node_atom = NULL;
							BoundedAtom* variable_dtg_node_atom = NULL;
							for (std::vector<BoundedAtom*>::const_iterator ci = precondition_dtg_node->getAtoms().begin(); ci != precondition_dtg_node->getAtoms().end(); ci++)
							{
								BoundedAtom* bounded_atom = *ci;

//								std::cout << "* BoundedAtom: ";
//								bounded_atom->print(std::cout, precondition_dtg_node->getDTG().getBindings());
//								std::cout << std::endl;

								bool matches_precondition_dtg_invariable = false;
								if (precondition_dtg_node->getIndex(*bounded_atom) != invariable)
								{
									// If the invariable does not match, we check if the precondition is an invariable for the other DTG. If that's the case
									// we might need to merge it with this node.
									matches_precondition_dtg_invariable = true;
//									std::cout << "Invariable doesn't match!" << std::endl;
///									continue;
								}

								if (precondition_dtg_node->getDTG().getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition->getStep()->getStepId(), &transition->getFromNode().getDTG().getBindings()))
								{
///									std::cout << "Found node:" << std::endl;
									if (matches_precondition_dtg_invariable)
									{
										variable_dtg_node_atom = bounded_atom;
									}
									else
									{
										dtg_node_atom = bounded_atom;
										break;
									}
								}
							}
							
							if (dtg_node_atom != NULL || variable_dtg_node_atom != NULL)
							{
								
//								std::cout << "!!! Merge node matching the precondition: ";
//								precondition_dtg_node->print(std::cout);
//								std::cout << std::endl << " and the from node: ";
//								from_dtg_node->print(std::cout);
//								std::cout << std::endl;

								/**
								 * Three cases of merging need to be distincted here.
								 * Considering the transition PRECS => FROM -> TO.
								 * Given a precondition PREC \in PRECS which appears as a dtg node DTG_NODE in the dtg DTG:
								 *
								 * If there are no dtg nodes which overlap with FROM, then we merge every node \in DTG with
								 * FROM.
								 * If there is a dtg node which does overlap, there are three possibilities:
								 * 1) if the intersection with FROM and the given node is not empty, but the node is a subset
								 * then we can ignore it.
								 * 2) if it is not a proper subset, but FROM is with the given node. Then FROM is replaced by the given node.
								 * 3) if neither of these cases hold, then the node is added as a new node to the DTG.
								 *
								 * Since TIM rules out the possibility of overlapping, so we only need to make sure that there
								 * is no overlap. If there is overlap we can safely ignore it, otherwise we need to merge.
								 */
								if (dtg_node_atom != NULL)
								{
									bool do_merge = true;
									for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = precondition_dtg_node->getDTG().getNodes().begin(); ci != precondition_dtg_node->getDTG().getNodes().end(); ci++)
									{
										// Check for every node in the DTG linked to the precondition if they merge with the FROM node.
										const DomainTransitionGraphNode* dtg_node = *ci;
										for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
										{
											BoundedAtom* prec_atom = *ci;
											
											for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node->getAtoms().begin(); ci != from_dtg_node->getAtoms().end(); ci++)
											{
												BoundedAtom* from_atom = *ci;
												if (dtg_node->getDTG().getBindings().canUnify(prec_atom->getAtom(), prec_atom->getId(), from_atom->getAtom(), from_atom->getId(), &from_dtg_node->getDTG().getBindings()) &&
													dtg_node->getIndex(*prec_atom) == from_dtg_node->getIndex(*from_atom))
												{
													do_merge = false;
													break;
												}
											}

											if (!do_merge) break;
										}
										
										if (!do_merge) break;
									}
									
									if (!do_merge) continue;
								}
								
								for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = precondition_dtg_node->getDTG().getNodes().begin(); ci != precondition_dtg_node->getDTG().getNodes().end(); ci++)
								{
									const DomainTransitionGraphNode* dtg_node = *ci;
									DomainTransitionGraphNode* clone_from_dtg_node = NULL;
									if (dtg_node_atom != NULL)
									{
										clone_from_dtg_node = new DomainTransitionGraphNode(*from_dtg_node, false);

										if (clone_from_dtg_node->merge(*dtg_node))
										{
											dtg_altered = true;

//											std::cout << "Result of the merge: ";
//											clone_from_dtg_node->print(std::cout);
//											std::cout << std::endl;
										}
										else
										{
											assert (false);
										}
									}
									else
									{
///										std::cout << "Pay attention!" << std::endl;
										clone_from_dtg_node = new DomainTransitionGraphNode(*from_dtg_node, false);
										clone_from_dtg_node->addAtom(variable_dtg_node_atom, INVALID_INDEX_ID); 
									}
									nodes_to_add.push_back(clone_from_dtg_node);
								}
								merged = true;
								
								std::set<const Object*>* merged_objects = NULL;
								std::map<const DomainTransitionGraph*, std::set<const Object*>* >::iterator dtg_i = dtgs_to_remove.find(&precondition_dtg_node->getDTG());
								if (dtg_i == dtgs_to_remove.end())
								{
									merged_objects = new std::set<const Object*>();
									dtgs_to_remove[&precondition_dtg_node->getDTG()] = merged_objects;
								}
								else
								{
									merged_objects = (*dtg_i).second;
								}
								
								dtg->merge(precondition_dtg_node->getDTG());
								
								/**
								 * After merging, we mark the objects for which the properties have been taken over from
								 * the other DTG as redundant and ready for removal which will happen at the end of this phase.
								 */
								std::vector<const Object*> merged_dtg = precondition_dtg_node->getDTG().getObjects();
								std::vector<const Object*> this_dtg = dtg->getObjects();
								std::sort(merged_dtg.begin(), merged_dtg.end());
								std::sort(this_dtg.begin(), this_dtg.end());
								std::set_intersection(merged_dtg.begin(), merged_dtg.end(), this_dtg.begin(), this_dtg.end(), std::inserter(*merged_objects, merged_objects->begin()));
							}
						}
					}
				}
				
				if (merged) nodes_to_remove.push_back(from_dtg_node);
			}
			
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_to_remove.begin(); ci != nodes_to_remove.end(); ci++)
			{
				dtg->removeNode(**ci);
			}

			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_to_add.begin(); ci != nodes_to_add.end(); ci++)
			{
/*
				std::cout << "Add the node: ";
				(*ci)->print(std::cout);
				std::cout << std::endl;
*/
				dtg->addNode(**ci);
				
///				std::cout << "Result: " << *dtg << std::endl;
			}
			dtg->reestablishTransitions();
		}
		
		for (std::map<const DomainTransitionGraph*, std::set<const Object*>* >::const_iterator ci = dtgs_to_remove.begin(); ci != dtgs_to_remove.end(); ci++)
		{
			DomainTransitionGraph* dtg = const_cast<DomainTransitionGraph*>((*ci).first);
			std::set<const Object*>* objects_to_remove = (*ci).second;
/*
			std::cout << "Process DTG: " << *dtg << std::endl;
			
			std::cout << "Objects to remove: ";
			for (std::set<const Object*>::const_iterator ci = objects_to_remove->begin(); ci != objects_to_remove->end(); ci++)
			{
				std::cout << **ci << ", ";
			}
			std::cout << std::endl;
*/

			dtg->removeObjects(*objects_to_remove);
			
///			std::cout << "Result after removing objects from DTG: " << *dtg << std::endl;
			
			if (dtg->getObjects().empty())
			{
				removeDTG(*dtg);
			}
		}
	}
	
	/**
	 * Merge dependened invariable DTG nodes.
	 */
//	std::cout << "[DomainTransitionGraph::mergeDTGs] Merge depended invariable DTG nodes." << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;

//		std::cout << "Check DTG: " << *dtg << "(pointer address=" << dtg << ")" << std::endl;
		
		std::vector<DomainTransitionGraphNode*> nodes_to_remove;
		std::vector<DomainTransitionGraphNode*> nodes_to_add;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* from_dtg_node = *ci;
			
			for (std::vector<const Transition*>::const_iterator ci = from_dtg_node->getTransitions().begin(); ci != from_dtg_node->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;

//				std::cout << "Transition: from ";
//				transition->getFromNode().print(std::cout);
//				std::cout << " to ";
//				transition->getToNode().print(std::cout);
//				std::cout << "[" << transition->getStep()->getAction() << "]" << std::endl;

				const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
//				std::vector<std::pair<const Atom*, InvariableIndex> > preconditions;
//				transition->getAllPreconditions(preconditions);
				
				// Check which of the preconditions of this action refers to an external DTG.
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
				{
					const Atom* precondition = (*ci).first;
					InvariableIndex invariable = (*ci).second;

//					std::cout << "Process the precondition: ";
//					precondition->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
//					std::cout << "(" << invariable << ")" << std::endl;

					std::vector<const DomainTransitionGraphNode*> found_dtg_nodes;
					getDTGNodes(found_dtg_nodes, transition->getStep()->getStepId(), *precondition, dtg->getBindings(), invariable);
					
					/**
					 * If the precondition isn't to the invariable of this DTG node there are two scenarios:
					 * - The precondition is part of another DTG node and its invariable is linked to a node in the from_node. If this is the
					 * case then the precondition must be merged with this node.
					 * - If the precondition's invariable is not linked to this node we need to ground it.
					 */
					if (invariable == NO_INVARIABLE_INDEX)
					{
//						std::cout << " - The precondition isn't linked to the invariable. Check if the term is invariable in another DTG." << std::endl;
						// Check if the precondition is invariable in their respective DTG(s).
						std::vector<const DomainTransitionGraphNode*> matching_dtg_nodes;
						getDTGNodes(matching_dtg_nodes, transition->getStep()->getStepId(), *precondition, dtg->getBindings());
						
						///InvariableIndex precondition_invariable = NO_INVARIABLE_INDEX;
						///const Property* precondition_property = NULL;
						std::vector<std::pair<InvariableIndex, const Property*> > precondition_properties;
						bool merge_with_self = false;
						
						for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = matching_dtg_nodes.begin(); ci != matching_dtg_nodes.end(); ci++)
						{
							const DomainTransitionGraphNode* matching_dtg_node = *ci;
							
/*							if (&matching_dtg_node->getDTG() == dtg)
							{
								std::cout << "Alert! Proposing a DTG to merge with itself!!!" << std::endl;
								continue;
							}*/
							
							// Figure out what the invariable is.
							for (std::vector<BoundedAtom*>::const_iterator ci = matching_dtg_node->getAtoms().begin(); ci != matching_dtg_node->getAtoms().end(); ci++)
							{
								const BoundedAtom* bounded_atom = *ci;
								if (dtg->getBindings().canUnify(*precondition, transition->getStep()->getStepId(), bounded_atom->getAtom(), bounded_atom->getId(), &matching_dtg_node->getDTG().getBindings()))
								{
									InvariableIndex matching_invariable_index = matching_dtg_node->getIndex(*bounded_atom);
									
//									std::cout << " -= Precondition is invariable in the DTG node: ";
//									matching_dtg_node->print(std::cout);
//									std::cout << "[" << matching_invariable_index << "]" << std::endl;
									
									// TEST
									if (matching_invariable_index == NO_INVARIABLE_INDEX) continue;
									
									assert (&matching_dtg_node->getDTG() != NULL);
									
									if (dtg->containsPropertySpace(bounded_atom->getProperty()->getPropertyState().getPropertySpace()))
									{
//										std::cout << "Alert! Proposing a DTG to merge with itself!!!" << std::endl;

										merge_with_self = true;
										precondition_properties.clear();

										break;
									}
									
									precondition_properties.push_back(std::make_pair(matching_invariable_index, bounded_atom->getProperty()));
									
//									std::cout << "Candidate to bind: ";
//									bounded_atom->print(std::cout, matching_dtg_node->getDTG().getBindings());
//									std::cout << "[" << &bounded_atom->getProperty()->getPropertyState().getPropertySpace() << "]" << std::endl;
									
//									std::cout << "From DTG node: ";
//									matching_dtg_node->print(std::cout);
//									std::cout << " (pointer address=" << &matching_dtg_node->getDTG() << ")" << std::endl;
									
/**
									if (precondition_invariable == NO_INVARIABLE_INDEX)
									{
										precondition_invariable = matching_invariable_index;
										precondition_property = bounded_atom->getProperty();
									}
									else
									{
										// This is WRONG.
										assert (precondition_invariable == matching_invariable_index);
									}
*/
								}
							}
							
							if (merge_with_self)
							{
								break;
							}
						}
						
						/**
						 * Not sure what to do if the same precondition is able to get two new atoms in the DTG node...
						 */
						unsigned int counter = 0;
						
						/// if (precondition_invariable != NO_INVARIABLE_INDEX)
						for (std::vector<std::pair<InvariableIndex, const Property*> >::const_iterator ci = precondition_properties.begin(); ci != precondition_properties.end(); ci++)
						{
							
							InvariableIndex precondition_invariable = (*ci).first;
							const Property* precondition_property = (*ci).second;
							/**
							 * Check if the variable in the precondition is present in the from node. If this is not
							 * the case then the value of this variable is irrelevant.
							 */
							bool need_to_merge = false;
							bool already_exists = false;
							for (std::vector< BoundedAtom*>::const_iterator ci = from_dtg_node->getAtoms().begin(); ci != from_dtg_node->getAtoms().end(); ci++)
							{
								const BoundedAtom* bounded_atom = *ci;
								
								///assert (&bounded_atom->getProperty()->getPropertyState().getPropertySpace() != &precondition_property->getPropertyState().getPropertySpace());
								
								for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
								{
									const Term* term = *ci;
									
									if (term->isTheSameAs(bounded_atom->getId(), *precondition->getTerms()[precondition_invariable], transition->getStep()->getStepId(), dtg->getBindings()))
									{
										need_to_merge = true;
									}
									
									// TEST
									if (from_dtg_node->getDTG().getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition->getStep()->getStepId(), &dtg->getBindings()))
									{
										already_exists = true;
										break;
									}
								}
								
								// TEST
								if (already_exists) break;
							}
							
							if (need_to_merge && !already_exists)
							{
//								std::cout << "Need to merge external invariable: ";
//								precondition->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
//								std::cout << "(" << precondition_invariable << ") property space: " << &precondition_property->getPropertyState().getPropertySpace() << std::endl;
								assert (counter == 0);
								++counter;

								StepID external_invariable_id = dtg->getBindings().createVariableDomains(*precondition);
								from_dtg_node->addAtom(new BoundedAtom(external_invariable_id, *precondition, precondition_property), precondition_invariable);
							}
						}
					}
				}
			}
		}
		dtg->establishTransitions();
	}
}

void DomainTransitionGraphManager::splitDTGs()
{
	std::cout << " *********** SPLIT DTGs!!!! ************** " << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		std::vector<DomainTransitionGraphNode*> nodes_to_remove;
		std::vector<DomainTransitionGraphNode*> nodes_to_add;
		
		std::cout << "Check DTG: " << *dtg << std::endl;
		
		std::map<const DomainTransitionGraphNode*, std::set<std::pair<const Property*, InvariableIndex> >*> properties_to_ground;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* from_dtg_node = *ci;
			
			std::set<std::pair<const Property*, InvariableIndex> >* to_ground_table = new std::set<std::pair<const Property*, InvariableIndex> >();
			properties_to_ground[from_dtg_node] = to_ground_table;
		}
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* from_dtg_node = *ci;
			
//			std::set<std::pair<const Property*, InvariableIndex> >* to_ground_table = properties_to_ground[from_dtg_node];

			std::cout << "Process the dtg node: ";
			from_dtg_node->print(std::cout);
			std::cout << std::endl;
			for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node->getAtoms().begin(); ci != from_dtg_node->getAtoms().end(); ci++)
			{
				const BoundedAtom* bounded_atom = *ci;
				std::cout << " *";
				bounded_atom->print(std::cout, dtg->getBindings());
				std::cout << std::endl;
				
				for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
				{
					const Term* term = *ci;
					std::cout << " **" << &term->getDomain(bounded_atom->getId(), dtg->getBindings()) << "." << std::endl;
				}
			}

			for (std::vector<const Transition*>::const_iterator ci = from_dtg_node->getTransitions().begin(); ci != from_dtg_node->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;
				
				std::cout << *transition << std::endl;
				
/*				
				std::cout << "Transition: from ";
				transition->getFromNode().print(std::cout);
				std::cout << " to ";
				transition->getToNode().print(std::cout);
				std::cout << "[" << transition->getStep()->getAction() << "]" << std::endl;
*/

				const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
//				std::vector<std::pair<const Atom*, InvariableIndex> > preconditions;
//				transition->getAllPreconditions(preconditions);
				
				// Check which of the preconditions of this action refers to an external DTG.
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
				{
					const Atom* precondition = (*ci).first;
					InvariableIndex invariable = (*ci).second;
					
					std::cout << "- Check if the precondition is linked to this DTG: ";
					precondition->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
					std::cout << "(" << invariable << "){" << precondition << "}" << std::endl;
					
					std::vector<const DomainTransitionGraphNode*> precondition_linked_to_this_dtg;
					dtg->getNodes(precondition_linked_to_this_dtg, transition->getStep()->getStepId(), *precondition, dtg->getBindings(), invariable);
					
					/** 
					 * If the precondition is linked to this DTG, we might need to do something special, but we'll skip that for now.
					 */
					///if (precondition_linked_to_this_dtg.size() != 0)
//					{
///						std::cout << "The precondition is part of this DTG node, skip!" << std::endl;
///						continue;
//					}

					/**
					 * If the precondition is linked to this DTG and shares a property space with it we cannot ground it.
					 */
					if (invariable != NO_INVARIABLE_INDEX)
					{
						bool skip = false;
						for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = precondition_linked_to_this_dtg.begin(); ci != precondition_linked_to_this_dtg.end(); ci++)
						{
							const DomainTransitionGraphNode* node_linked_to_precondition = *ci;
							for (std::vector<BoundedAtom*>::const_iterator ci = node_linked_to_precondition->getAtoms().begin(); ci != node_linked_to_precondition->getAtoms().end(); ci++)
							{
								const BoundedAtom* bounded_atom = *ci;
								
								if (bounded_atom->getProperty() == NULL || !node_linked_to_precondition->getDTG().containsPropertySpace(bounded_atom->getProperty()->getPropertyState().getPropertySpace()))
								{
									continue;
								}

								// TODO: Make sure the invariable is linked up.
								if (dtg->getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition->getStep()->getStepId()))
								{
									std::cout << "--- The precondition is part of this DTG node, skip!" << std::endl;
									skip = true;
									break;
								}
							}
							
							if (skip)
							{
								break;
							}
						}
						
						if (skip)
						{
							continue;
						}
					}
					
					std::cout << "-- Process the precondition: ";
					precondition->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
					std::cout << "(" << invariable << "){" << precondition << "}" << std::endl;
					
					/**
					 * Check which of the variable domains of the preconditions are linked to the from node, these need to be grounded, unless they correspond
					 * with the invariable.
					 */
					for (InvariableIndex precondition_term_index = 0; precondition_term_index < precondition->getTerms().size(); precondition_term_index++)
					{
						assert (&transition->getFromNode().getDTG() == dtg);
						const Term* precondition_term = precondition->getTerms()[precondition_term_index];
						
						std::cout << "--- Precondition term: ";
						precondition_term->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
						std::cout << "(" << &precondition_term->getDomain(transition->getStep()->getStepId(), dtg->getBindings()) << ")" << std::endl;

						std::cout << "Transitions: " << transition->getPreconditions().size() << std::endl;
						
						for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getPreconditions().begin(); ci != transition->getPreconditions().end(); ci++)
						{
							const Atom* from_atom = (*ci).first;
							InvariableIndex from_atom_invariable = (*ci).second;
							
							std::cout << "---- Compare the precondition term with the terms of all preconditions linked to the from_node. From_node precondition under consideration: ";
							from_atom->print(std::cout, transition->getFromNode().getDTG().getBindings(), transition->getStep()->getStepId());
							std::cout << "(" << transition->getPreconditions().size() << ")" << std::endl;
							
							for (unsigned int from_atom_term_index = 0; from_atom_term_index < from_atom->getTerms().size(); from_atom_term_index++)
							{
								// TODO: We do not ground the invariable of this DTG (only in special cases, but we'll deal with that later (in time)).
								if (precondition_term->canUnify(transition->getStep()->getStepId(), *from_atom->getTerms()[from_atom_term_index], transition->getStep()->getStepId(), dtg->getBindings()) &&
								    from_atom_term_index == from_atom_invariable)
								{
									std::cout << "----- Term refers to the invariable of this DTG, skip!" << std::endl;
									continue;
								}
								
								const Term* dtg_term = from_atom->getTerms()[from_atom_term_index];
								
								std::cout << "----- Compare to precondition: ";
								dtg_term->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
								std::cout << "(" << &dtg_term->getDomain(transition->getStep()->getStepId(), dtg->getBindings()) << ")" << std::endl;

								// If they are the same, we need to ground it.
								if (precondition_term->isTheSameAs(transition->getStep()->getStepId(), *dtg_term, transition->getStep()->getStepId(), dtg->getBindings()))
								{
									std::vector<const SAS_Plus::DomainTransitionGraphNode*> supporting_dtg_nodes;
									getDTGNodes(supporting_dtg_nodes, transition->getStep()->getStepId(), *precondition, dtg->getBindings(), invariable);
									
									std::cout << "------ Do we need to ground the term: " << *dtg_term << "?" << std::endl;
									
									bool ground = true;
									// Check if the precondition is linked to the invariable of the other DTG, if this is the case we cannot ground otherwise we must.
									for (std::vector<const SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = supporting_dtg_nodes.begin(); ci != supporting_dtg_nodes.end(); ci++)
									{
										const DomainTransitionGraphNode* dtg_node = *ci;
										std::cout << "------ Found the dtg node representing this precondition: ";
										dtg_node->print(std::cout);
										std::cout << std::endl;

										/**
										 * If the predicate is marked as invariable in the corresponding DTG, we cannot split!
										 */
										for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
										{
											const BoundedAtom* bounded_atom = *ci;
											
											if (bounded_atom->getProperty()->getPredicate().getName() == precondition->getPredicate().getName() &&
											    bounded_atom->getProperty()->getPredicate().getArity() == precondition->getPredicate().getArity() &&
											    bounded_atom->getProperty()->getIndex() == precondition_term_index)
											{
												std::cout << "------- Index " << precondition->getPredicate() << " [" << precondition_term_index << "] is invariable in the DTG: " << dtg_node->getDTG() << std::endl;
												ground = false;
												break;
											}
										}
										
										if (!ground) break;
									}
									
									if (ground)
									{
										std::cout << "------ Ground the term: ";
										from_atom->print(std::cout, transition->getFromNode().getDTG().getBindings(), transition->getStep()->getStepId());
										std::cout << "(" << from_atom_term_index << "){" << *dtg_term << "}" << std::endl;
										
										/**
										 * Whenever we ground a variable which appears in the persistent set of a transition we must also
										 * ground the variable in the corresponding atom in the to node.
										 */
										if (transition->isPreconditionPersistent(*from_atom, from_atom_invariable))
										{
											const DomainTransitionGraphNode& to_dtg_node = transition->getToNode();
											
											for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node.getAtoms().begin(); ci != to_dtg_node.getAtoms().end(); ci++)
											{
												const BoundedAtom* bounded_atom = *ci;
												if (to_dtg_node.getIndex(*bounded_atom) == from_atom_invariable &&
												    dtg->getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), *from_atom, transition->getStep()->getStepId()))
												{
														std::set<std::pair<const Property*, InvariableIndex> >* tmp_to_ground_table = properties_to_ground[&to_dtg_node];
														
														std::cout << "------- Ground the persistent property: " << bounded_atom->getProperty()->getPredicate() << "(" << from_atom_term_index << ") +==--> ";
														to_dtg_node.print(std::cout);
														std::cout << std::endl;
														tmp_to_ground_table->insert(std::make_pair(bounded_atom->getProperty(), from_atom_term_index));
												}
											}
										}
									
										for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
										{
											DomainTransitionGraphNode* node = *ci;
											
											for (std::vector<BoundedAtom*>::const_iterator ci = node->getAtoms().begin(); ci != node->getAtoms().end(); ci++)
											{
												const BoundedAtom* bounded_atom = *ci;
										
												for (InvariableIndex i = 0; i < bounded_atom->getAtom().getTerms().size(); i++)
												{
													const Term* term = bounded_atom->getAtom().getTerms()[i];
													
													if (term->isTheSameAs(bounded_atom->getId(), *dtg_term, transition->getStep()->getStepId(), dtg->getBindings()))
													{
														std::set<std::pair<const Property*, InvariableIndex> >* tmp_to_ground_table = properties_to_ground[node];
														
														std::cout << "------- Ground the property: " << bounded_atom->getProperty()->getPredicate() << "(" << i << ") +==--> ";
														node->print(std::cout);
														std::cout << std::endl;
														tmp_to_ground_table->insert(std::make_pair(bounded_atom->getProperty(), i));
													}
												}
											}
										}
									}
								}
								else
								{
									std::cout << "FAIL! ";
									precondition_term->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
									std::cout << " is not the same as: ";
									dtg_term->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
									std::cout << std::endl;
								}
							}
						}
					}
				}
			}
		}
		
		std::cout << " =======++++======= Move to actual grounding! =======++++======= " << std::endl;
		
		/**
		 * Perform the actual splitting.
		 */
		for (std::map<const DomainTransitionGraphNode*, std::set<std::pair<const Property*, InvariableIndex> >*>::const_iterator ci = properties_to_ground.begin(); ci != properties_to_ground.end(); ci++)
		{
			const DomainTransitionGraphNode* org_node_to_split = (*ci).first;
			std::set<std::pair<const Property*, InvariableIndex> >* properties_to_ground = (*ci).second;
			
			// Ground all properties in turn.
			std::vector<const DomainTransitionGraphNode*> dtg_nodes_to_ground;
			std::vector<DomainTransitionGraphNode*> new_dtg_nodes;
			dtg_nodes_to_ground.push_back(org_node_to_split);
			
			std::cout << " ==+++--> ";
			org_node_to_split->print(std::cout);
			std::cout << " (((" << properties_to_ground->size() << ")))" << std::endl;
			
			for (std::set<std::pair<const Property*, InvariableIndex> >::const_iterator ci = properties_to_ground->begin(); ci != properties_to_ground->end(); ci++)
			{
				std::pair<const Property*, InvariableIndex> property_to_ground = *ci;
				
				std::cout << "Process the property to ground: " << property_to_ground.first->getPredicate() << "[" << property_to_ground.first->getIndex() << "] (" << property_to_ground.second << ")" << std::endl;
				
				for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes_to_ground.begin(); ci != dtg_nodes_to_ground.end(); ci++)
				{
					const DomainTransitionGraphNode* dtg_node_to_split = *ci;
					///bool split = false;
					
					for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node_to_split->getAtoms().begin(); ci != dtg_node_to_split->getAtoms().end(); ci++)
					{
						const BoundedAtom* bounded_atom = *ci;
						
						std::cout << "-- compare v.s.: " << bounded_atom->getProperty()->getPredicate() << "[" << bounded_atom->getProperty()->getIndex() << "]" << std::endl;
						
						if (property_to_ground.first == bounded_atom->getProperty())
						{
							dtg_node_to_split->groundTerm(new_dtg_nodes, *bounded_atom->getAtom().getTerms()[property_to_ground.second], bounded_atom->getId());
					///		split = true;
							break;
						}
					}
				}
				
				/**
				 * Update the DTG.
				 */
				for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes_to_ground.begin(); ci != dtg_nodes_to_ground.end(); ci++)
				{
					dtg->removeNode(**ci);
				}
				
				for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = new_dtg_nodes.begin(); ci != new_dtg_nodes.end(); ci++)
				{
					dtg->addNode(**ci);
				}

				/**
				 * After grounding the terms and getting new results, we remove the splitted node and add the resulting nodes to the DTG.
				 */
				dtg_nodes_to_ground.clear();
				dtg_nodes_to_ground.insert(dtg_nodes_to_ground.end(), new_dtg_nodes.begin(), new_dtg_nodes.end());
				new_dtg_nodes.clear();
			}
		}
		
		std::cout << " =======++++======= Done with grounding! =======++++======= " << std::endl;
		
		dtg->reestablishTransitions();
	}
}

bool DomainTransitionGraphManager::removeDTG(const DomainTransitionGraph& dtg)
{
	for (std::vector<DomainTransitionGraph*>::iterator i = objects_.begin(); i != objects_.end(); i++)
	{
		if (&dtg == *i)
		{
			objects_.erase(i);
			return true;
		}
	}
	
	return false;
}

void DomainTransitionGraphManager::getDTGs(std::vector<const DomainTransitionGraph*>& found_dtgs, StepID step_id, const Atom& atom, const Bindings& bindings, unsigned int index) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
		(*ci)->getNodes(dtg_nodes, step_id, atom, bindings, index);

		if (dtg_nodes.size() > 0)
		{
			found_dtgs.push_back(*ci);
		}
	}
}

void DomainTransitionGraphManager::getDTGNodes(std::vector<const DomainTransitionGraphNode*>& found_dtg_nodes, StepID step_id, const Atom& atom, const Bindings& bindings, unsigned int index) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
		(*ci)->getNodes(dtg_nodes, step_id, atom, bindings, index);
		found_dtg_nodes.insert(found_dtg_nodes.end(), dtg_nodes.begin(), dtg_nodes.end());
	}
}

void DomainTransitionGraphManager::getDTGNodes(std::vector<const DomainTransitionGraphNode*>& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const Bindings& bindings) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
 	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
		(*ci)->getNodes(dtg_nodes, initial_facts, bindings);
		found_dtg_nodes.insert(found_dtg_nodes.end(), dtg_nodes.begin(), dtg_nodes.end());
	}
}

bool DomainTransitionGraphManager::isSupported(unsigned int id, const MyPOP::Atom& atom, const MyPOP::Bindings& bindings) const
{
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		
		if (dtg->isSupported(id, atom, bindings))
		{
			return true;
		}
	}
	return false;
}

};

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::Transition& transition, const Bindings& bindings)
{
	printToDot(ofs, transition.getFromNode());
	ofs << " -> ";
	printToDot(ofs, transition.getToNode());
	ofs << "[ label=\"";
	transition.getStep()->getAction().print(ofs, bindings, transition.getStep()->getStepId());
	ofs << "\"]" << std::endl;
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraphNode& dtg_node)
{
	ofs << "\"[" << &dtg_node << "] ";
	for (std::vector<SAS_Plus::BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
	{
		(*ci)->print(ofs, dtg_node.getDTG().getBindings());
		
		if (ci + 1 != dtg_node.getAtoms().end())
		{
///			ofs << "\\n";
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
	}
	
	// Create the edges.
	for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = dtg.getNodes().begin(); ci != dtg.getNodes().end(); ci++)
	{
		const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
		const std::vector<const SAS_Plus::Transition*>& transitions = dtg_node->getTransitions();

		for (std::vector<const SAS_Plus::Transition*>::const_iterator transitions_ci = transitions.begin(); transitions_ci != transitions.end(); transitions_ci++)
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
/*		const std::vector<const MyPOP::SAS_Plus::Property*>& predicates = dtg.getPredicates();
		
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
		*/
}

};
