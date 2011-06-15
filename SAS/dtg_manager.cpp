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

#define MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
///#define MYPOP_SAS_PLUS_DTG_MANAGER_DEBUG


namespace MyPOP {

namespace SAS_Plus {

/***********************
 * Bounded Atom...
 **********************/

BoundedAtom& BoundedAtom::createBoundedAtom(const Atom& atom, const Property* property, Bindings& bindings)
{
	StepID new_step_id = bindings.createVariableDomains(atom);
	BoundedAtom* bounded_atom = new BoundedAtom(new_step_id, atom, property);
	return *bounded_atom;
}

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

	bool potentially_mutex = false;
	for (std::vector<const PropertyState*>::const_iterator ci = property_->getPropertyState().getPropertySpace().getPropertyStates().begin(); ci !=  property_->getPropertyState().getPropertySpace().getPropertyStates().end(); ci++)
	{
		const PropertyState* property_state = *ci;
		const std::vector<Property*>& properties = property_state->getProperties();
		
		// If the property states are the same they are not mutex (already tested above).
		if (property_state == &property_->getPropertyState())
		{
			continue;
		}
		
//		bool bounded_atom_present = false;
		
		// If the property of another property states matches with the given one we conclude it must be mutex.
		for (std::vector<Property*>::const_iterator ci = properties.begin(); ci != properties.end(); ci++)
		{
			const Property* property = *ci;
//			std::cout << "[BoundedAtom::isMutexWith] Check against: " << property->getPredicate().getName() << "[" << property->getIndex() << "]" << std::endl;
			if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index)
			{
				potentially_mutex = true;
			}
			if (property->getPredicate().getName() == property_->getPredicate().getName() && property->getIndex() == property_->getIndex())
			{
//				bounded_atom_present = true;
				potentially_mutex = false;
				break;
			}
		}
	}
	
	return potentially_mutex;
}

void BoundedAtom::print(std::ostream& os, const Bindings& bindings, bool verbal) const
{
	atom_->print(os, bindings, id_, verbal);
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

	assert (property_spaces.size() > 0);

	// Construct the DTGs by combining all properties which appear together in either the LHS or RHS of a transition rule.
	for (std::vector<TIM::PropertySpace*>::const_iterator property_space_i = property_spaces.begin(); property_space_i != property_spaces.end(); ++property_space_i)
	{
		TIM::PropertySpace* property_space = *property_space_i;
		
		PropertySpace* dtg_property_space = new PropertySpace();
		
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
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all predicates (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif
		dtg->establishTransitions();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all transitions (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif
		dtg->addObjects();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all objects (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif
		addManagableObject(dtg);
	}
	struct timeval end_time_tim_translation;
	gettimeofday(&end_time_tim_translation, NULL);
	
	double time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "TIM transation took: " << time_spend << " seconds" << std::endl;

	struct timeval start_time_apply_rules;
	gettimeofday(&start_time_apply_rules, NULL);
	
	applyRules();
	
	struct timeval end_time_apply_rules;
	gettimeofday(&end_time_apply_rules, NULL);
	
	time_spend = end_time_apply_rules.tv_sec - start_time_apply_rules.tv_sec + (end_time_apply_rules.tv_usec - start_time_apply_rules.tv_usec) / 1000000.0;
	std::cerr << "Applying the rules took: " << time_spend << " seconds" << std::endl;
	
	
	struct timeval start_time_unsupported_predicates;
	gettimeofday(&start_time_unsupported_predicates, NULL);

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
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "Check if the predicate : " << *predicate << " is supported!" << std::endl;
#endif
		
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
			std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
			dtg->getNodes(found_nodes, test_atom_id, *possitive_atom, dtg->getBindings());
			
			if (found_nodes.size() > 0)
			{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "The predicate " << *predicate << " is supported by " << std::endl;
				for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
				{
					(*ci).first->print(std::cout);
					std::cout << std::endl;
				}
#endif
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
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "The predicate: " << *predicate << " is not processed yet!" << std::endl;
#endif
			
			// 1) The predicate is static.
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
			
			new_dtg->addNode(*possitive_new_dtg_node);

			addManagableObject(new_dtg);
			
			// 2) The predicate is not static.
			if (!predicate->isStatic())
			{
				// Add all preconditions which share a term with the unsupported predicate.
				DomainTransitionGraphNode* negative_new_dtg_node = new DomainTransitionGraphNode(*new_dtg, std::numeric_limits<unsigned int>::max());
				Atom* negative_atom = new Atom(*predicate, *new_terms, true);
				StepID negative_atom_id = new_dtg->getBindings().createVariableDomains(*possitive_atom);
				
				negative_new_dtg_node->addAtom(new BoundedAtom(negative_atom_id, *negative_atom, property_state->getProperties()[0]), NO_INVARIABLE_INDEX);
				new_dtg->addNode(*negative_new_dtg_node);
				
				for (std::vector<const Term*>::const_iterator ci = negative_atom->getTerms().begin(); ci != negative_atom->getTerms().end(); ci++)
				{
					const Term* from_node_term = *ci;
					const Term* to_node_term = possitive_atom->getTerms()[std::distance(negative_atom->getTerms().begin(), ci)];
					
					from_node_term->unify(negative_atom_id, *to_node_term, possitive_atom_id, new_dtg->getBindings());
				}
				
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "Simple DTG : " << *new_dtg << std::endl;
#endif
				
				// Find all transitions which can make this predicate true and false and add them as transitions.
				std::vector<std::pair<const Action*, const Atom*> > achievers;
				action_manager_->getAchievingActions(achievers, *possitive_atom);
				
				for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator ci = achievers.begin(); ci != achievers.end(); ci++)
				{
					const Action* achieving_action = (*ci).first;
					
					// Create a transition between the two nodes.
					std::vector<BoundedAtom>* enablers = new std::vector<BoundedAtom>();
					const Transition* transition = Transition::createTransition(*enablers, *achieving_action, *negative_new_dtg_node, *possitive_new_dtg_node, *initial_facts_);
					
					std::cout << "Process the transition: " << *transition << std::endl;
					
					if (transition != NULL)
					{
						// Inspect the transition and add all preconditions which shares a term with the positive achieved fact.
						bool precondition_added = true;
						std::set<const Atom*> closed_list;
						while (precondition_added)
						{
							precondition_added = false;
							const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
							for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
							{
								const Atom* precondition = (*ci).first;
								if (closed_list.count(precondition) != 0)
								{
									continue;
								}
								
								bool precondition_added = false;
								for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
								{
									const Term* precondition_term = *ci;
									
									for (std::vector<BoundedAtom*>::const_iterator ci = negative_new_dtg_node->getAtoms().begin(); ci != negative_new_dtg_node->getAtoms().end(); ci++)
									{
										const BoundedAtom* from_node_atom = *ci;
										
										for (std::vector<const Term*>::const_iterator ci = from_node_atom->getAtom().getTerms().begin(); ci != from_node_atom->getAtom().getTerms().end(); ci++)
										{
											const Term* from_node_atom_term = *ci;

											if (precondition_term->isTheSameAs(transition->getStep()->getStepId(), *from_node_atom_term, from_node_atom->getId(), new_dtg->getBindings()))
											{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
												std::cout << "Add the precondition: ";
												precondition->print(std::cout, new_dtg->getBindings(), transition->getStep()->getStepId());
												std::cout << std::endl;
#endif
												closed_list.insert(precondition);
												precondition_added = true;
												BoundedAtom* atom_to_add = new BoundedAtom(transition->getStep()->getStepId(), *precondition, NULL);
												negative_new_dtg_node->addAtom(atom_to_add, NO_INVARIABLE_INDEX);
												break;
											}
										}
										
										if (precondition_added)
										{
											break;
										}
									}
									
									if (precondition_added)
									{
										break;
									}
								}
							}
						}
						
						negative_new_dtg_node->addTransition(*transition, false);
					}
				}
			}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Resulting DTG: " << *new_dtg << std::endl;
#endif
		}
	}
	
	struct timeval end_time_unsupported_predicates;
	gettimeofday(&end_time_unsupported_predicates, NULL);
	
	time_spend = end_time_unsupported_predicates.tv_sec - start_time_unsupported_predicates.tv_sec + (end_time_unsupported_predicates.tv_usec - start_time_unsupported_predicates.tv_usec) / 1000000.0;
	std::cerr << "Creating DTGs for unsupported predicates: " << time_spend << " seconds" << std::endl;

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "FINAL RESULTS" << std::endl;
	std::cout << " === Result === " << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
#endif
}


void DomainTransitionGraphManager::applyRules()
{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << " *************** [DomainTransitionGraphManager::applyRules] *******************" << std::endl;
#endif

	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "[DomainTransitionGraphManager::applyRules] Check DTG: " << *dtg << std::endl;
#endif

		std::vector<DomainTransitionGraphNode*> resulting_nodes;
		std::vector<DomainTransitionGraphNode*> dtg_nodes_to_remove;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			bool replace_lifted_dtg_node = false;
			
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "[DomainTransitionGraphManager::applyRules] Check DTG Node: ";
			dtg_node->print(std::cout);
			std::cout << std::endl;
#endif

			for (unsigned int i = 0; i < dtg_node->getTransitions().size(); i++)
			{
				const Transition* org_transition = dtg_node->getTransitions()[i];
				DomainTransitionGraphNode* from_dtg_node_clone = new DomainTransitionGraphNode(*dtg_node, false, false);
				DomainTransitionGraphNode* to_dtg_node_clone = new DomainTransitionGraphNode(org_transition->getToNode(), false, false);
				
				std::vector<BoundedAtom>* enablers = new std::vector<BoundedAtom>();
				
				Transition* transition = Transition::createTransition(*enablers, org_transition->getStep()->getAction(), *from_dtg_node_clone, *to_dtg_node_clone, *initial_facts_);
				
				assert (transition != NULL);
				
				std::cout << "Process the transition: " << *transition << "." << std::endl;
				
				std::vector<BoundedAtom*> atoms_to_add_to_from_node;
				std::vector<BoundedAtom*> atoms_to_add_to_to_node;
				std::vector<unsigned int> precondition_index_to_add_to_to_node;
				std::vector<std::pair<const Term*, StepID> > from_terms_to_ground;
				std::vector<std::pair<const Term*, StepID> > to_terms_to_ground;
				bool finished = false;
				while (!finished)
				{
					finished = true;
					
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
					std::cout << "[DomainTransitionGraphManager::applyRules] Process the transition: " << *transition << std::endl;
#endif
					
					/**
					 * Check which terms in the transition's preconditions correspond with those of the from node. For each of
					 * these terms we have a piecewise function:
					 *
					 * Ground from_{term}             if precondition_{term} is 'unballanced'
					 * Add precondition to from       otherwise
					 *
					 * A predicate's term is unballanced if it does not occur in any DTG node with the term being the invariable. 
					 * Another way of putting it is saying that the predicate - given the term as index - is an attribute in 
					 * TIM terms.
					 *
					 * In addition if a term is shared between a node of the from node and a term of the to node and it is unballanced
					 * it needs to be ground.
					 */
					const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
					
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator precondition_ci = preconditions.begin(); precondition_ci != preconditions.end(); precondition_ci++)
					{
						const Atom* precondition = (*precondition_ci).first;
						InvariableIndex precondition_invariable_index = (*precondition_ci).second;
						bool static_precondition = precondition->getPredicate().isStatic();
						
						// Ignore those which are already part of the DTG node.
						bool already_part = false;
						for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
						{
							const BoundedAtom* bounded_atom = *ci;
							if (dtg->getBindings().areIdentical(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition->getStep()->getStepId()))
							{
								already_part = true;
								break;
							}
						}
						
						if (already_part)
						{
							continue;
						}
						
						bool precondition_added = false;

						for (std::vector<const Term*>::const_iterator term_precondition_ci = precondition->getTerms().begin(); term_precondition_ci != precondition->getTerms().end(); term_precondition_ci++)
						{
							const Term* precondition_term = *term_precondition_ci;
							
							for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
							{
								const BoundedAtom* bounded_atom = *ci;
								
								for( std::vector<const Term*>::const_iterator bounded_atom_ci = bounded_atom->getAtom().getTerms().begin(); bounded_atom_ci != bounded_atom->getAtom().getTerms().end(); bounded_atom_ci++)
								{
									const Term* from_term = *bounded_atom_ci;
									
									if (from_term->isTheSameAs(bounded_atom->getId(), *precondition_term, transition->getStep()->getStepId(), dtg->getBindings()))
									{
										std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_matching_nodes;
										
										getDTGNodes(found_matching_nodes, bounded_atom->getId(), bounded_atom->getAtom(), dtg->getBindings(), std::distance(bounded_atom->getAtom().getTerms().begin(), bounded_atom_ci));
										bool self_ballanced = !found_matching_nodes.empty();
										
										// Check if precondition_term is unballanced in the precondition predicate.
										std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
										getDTGNodes(found_nodes, transition->getStep()->getStepId(), *precondition, dtg->getBindings(), std::distance(precondition->getTerms().begin(), term_precondition_ci));
										
										bool ground_term = false;
										bool add_predicate = false;
										if (self_ballanced && static_precondition)
										{
											add_predicate = true;
										}
										else if (found_nodes.empty())
										{
											ground_term = true;
										}
										else if (!already_part)
										{
											add_predicate = true;
										}
										
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
										std::cout << "Process the predicate: ";
										precondition->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
										std::cout << "{";
										precondition_term->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
										std::cout << " / " << std::distance(precondition->getTerms().begin(), term_precondition_ci) << "}: static[" << static_precondition << "]; self ballanced[" << self_ballanced << "]; predicate ballanced[" << !found_nodes.empty() << "]" << std::endl;
#endif
										
										if (ground_term)
										{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "Ground the term!" << std::endl;
#endif
											from_terms_to_ground.push_back(std::make_pair(precondition_term, transition->getStep()->getStepId()));
											
											/**
											 * If the term is not removed by the effects of the action and it is balanced, we must add it to the to node.
											 */
											bool precondition_is_deleted = false;
											const std::vector<std::pair<const Atom*, InvariableIndex> > effects = transition->getEffects();
											for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
											{
												const Atom* effect = (*ci).first;
												InvariableIndex effect_invariable_index = (*ci).second;
												
												if (effect->isNegative() &&
												    effect_invariable_index == precondition_invariable_index &&
												    dtg->getBindings().areIdentical(*effect, transition->getStep()->getStepId(), *precondition, transition->getStep()->getStepId()))
												{
													precondition_is_deleted = true;
													break;
												}
											}
											
											if (!precondition_is_deleted)
											{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
												std::cout << "Add the predicate to the to node!" << std::endl;
#endif
												precondition_index_to_add_to_to_node.push_back(std::distance(preconditions.begin(), precondition_ci));
											}
										}
										else if (add_predicate)
										{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "Add the predicate.";
#endif
											
											// Check if we can figure out the property linked with this precondition.
											const Property* property = NULL;
											for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
											{
												if (property == NULL)
												{
													property = (*ci).second->getProperty();
												}
												else if (property != (*ci).second->getProperty())
												{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
													std::cout << "Conflicting properties!" << std::endl;
#endif
													property = NULL;
													break;
												}
											}
											
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											if (property != NULL)
											{
												std::cout << "Found property: " << *property << std::endl;
											}
											else
											{
												std::cout << "No property found..." << std::endl;
											}
#endif
											BoundedAtom* atom_to_add = new BoundedAtom(transition->getStep()->getStepId(), *precondition, property);
											atoms_to_add_to_from_node.push_back(atom_to_add);
											finished = false;
											precondition_added = true;
											//break;
										}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
										else
										{
											std::cout << "Ignore the predicate.";
										}
#endif
										
										/**
										 * Check if this precondition's term also appears in a term of the to node. If this is the case and the term
										 * is inballanced it needs to be grounded.
										 */
										for (std::vector<const Term*>::const_iterator term_precondition_ci = precondition->getTerms().begin(); term_precondition_ci != precondition->getTerms().end(); term_precondition_ci++)
										{
											const Term* precondition_term = *term_precondition_ci;

											std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
											getDTGNodes(found_nodes, transition->getStep()->getStepId(), *precondition, dtg->getBindings(), std::distance(precondition->getTerms().begin(), term_precondition_ci));

											if (!found_nodes.empty())
											{
												continue;
											}
											
											// Check if this term is part of the to node.
											bool term_is_part_of_to_node = false;
											for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
											{
												const BoundedAtom* to_bounded_atom = *ci;
												
												for (std::vector<const Term*>::const_iterator ci = to_bounded_atom->getAtom().getTerms().begin(); ci != to_bounded_atom->getAtom().getTerms().end(); ci++)
												{
													const Term* term = *ci;
													
													// Only ground the term if it is unballanced in the to node as well.
													getDTGNodes(found_nodes, to_bounded_atom->getId(), to_bounded_atom->getAtom(), dtg->getBindings(), std::distance(to_bounded_atom->getAtom().getTerms().begin(), ci));

													if (!found_nodes.empty())
													{
														found_nodes.clear();
														continue;
													}
													
													if (precondition_term->isTheSameAs(transition->getStep()->getStepId(), *term, to_bounded_atom->getId(), dtg->getBindings()))
													{
														term_is_part_of_to_node = true;
														break;
													}
												}
												
												if (term_is_part_of_to_node)
												{
													break;
												}
											}
											
											if (!term_is_part_of_to_node)
											{
												continue;
											}
											
											from_terms_to_ground.push_back(std::make_pair(precondition_term, transition->getStep()->getStepId()));
											to_terms_to_ground.push_back(std::make_pair(precondition_term, transition->getStep()->getStepId()));
											
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "(precondition) Ground the term: ";
											precondition_term->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
											std::cout << " in the TO node." << std::endl;
#endif
										}
										
										if (add_predicate)
										{
											break;
										}
									}
								}
								
								if (precondition_added)
								{
									break;
								}
							}
							
							if (precondition_added)
							{
								break;
							}
						}
					}
					for (std::vector<BoundedAtom*>::const_iterator ci = atoms_to_add_to_from_node.begin(); ci != atoms_to_add_to_from_node.end(); ci++)
					{
						from_dtg_node_clone->addAtom(*ci, NO_INVARIABLE_INDEX);
					}
					atoms_to_add_to_from_node.clear();
				}

				/**
				 * Now that we know which terms to ground we check if any of these terms are present in the to node,
				 * if that's the case than these need to be grounded too. Failing to do so would mean that transitions
				 * cannot be made properly.
				 */
				const std::vector<std::pair<const Atom*, InvariableIndex> >& persistent_preconditions = transition->getAllPersistentPreconditions();
				
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = persistent_preconditions.begin(); ci != persistent_preconditions.end(); ci++)
				{
					const Atom* persistent_precondition = (*ci).first;
					InvariableIndex precondition_invariable = (*ci).second;
					
					// Check if the precondition shares a term with one we need to ground.
					for (std::vector<std::pair<const Term*, StepID> >::const_iterator ci = from_terms_to_ground.begin(); ci != from_terms_to_ground.end(); ci++)
					{
						const Term* precondition_term_to_ground = (*ci).first;
						StepID precondition_id = (*ci).second;
						
						for (std::vector<const Term*>::const_iterator persistent_precondition_terms_ci = persistent_precondition->getTerms().begin(); persistent_precondition_terms_ci != persistent_precondition->getTerms().end(); persistent_precondition_terms_ci++)
						{
							const Term* persistent_precondition_term = *persistent_precondition_terms_ci;
							
							if (persistent_precondition_term->isTheSameAs(transition->getStep()->getStepId(), *precondition_term_to_ground, precondition_id, dtg->getBindings()))
							{
								for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
								{
									const BoundedAtom* to_bounded_atom = *ci;
									if (to_dtg_node_clone->getIndex(*to_bounded_atom) == precondition_invariable &&
									    dtg->getBindings().canUnify(to_bounded_atom->getAtom(), to_bounded_atom->getId(), *persistent_precondition, transition->getStep()->getStepId()))
									{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
										std::cout << "Ground the term: ";
										to_bounded_atom->getAtom().getTerms()[std::distance(persistent_precondition->getTerms().begin(), persistent_precondition_terms_ci)]->print(std::cout, dtg->getBindings(), to_bounded_atom->getId());
										std::cout << " in the TO node." << std::endl;
#endif
										to_terms_to_ground.push_back(std::make_pair(to_bounded_atom->getAtom().getTerms()[std::distance(persistent_precondition->getTerms().begin(), persistent_precondition_terms_ci)], to_bounded_atom->getId()));
									}
								}
							}
						}
					}
				}

				/**
				 * In addition to grounding the terms which are persistent we should also add atoms to the to node.
				 */
				for (std::vector<BoundedAtom*>::const_iterator ci = atoms_to_add_to_to_node.begin(); ci != atoms_to_add_to_to_node.end(); ci++)
				{
					to_dtg_node_clone->addAtom(*ci, NO_INVARIABLE_INDEX);
				}

				/**
				 * Establish the transitions and print the final result.
				 */
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << " -+! Final results !+- " << std::endl;
#endif
				std::vector<DomainTransitionGraphNode*> from_grounded_nodes;
				if (from_dtg_node_clone->groundTerms(from_grounded_nodes, from_terms_to_ground))
				{
					from_dtg_node_clone->removeTransitions(true);
					
					
					std::vector<DomainTransitionGraphNode*> to_grounded_nodes;
					to_dtg_node_clone->groundTerms(to_grounded_nodes, to_terms_to_ground);
					
					std::vector<BoundedAtom>* enable_dummy = new std::vector<BoundedAtom>();
					for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = from_grounded_nodes.begin(); ci != from_grounded_nodes.end(); ci++)
					{
						DomainTransitionGraphNode* from_dtg_node = *ci;
						
//						std::cout << "Found grounded node: " << std::endl << *from_dtg_node << std::endl;
						for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = to_grounded_nodes.begin(); ci != to_grounded_nodes.end(); ci++)
						{
							DomainTransitionGraphNode* to_dtg_node = new DomainTransitionGraphNode(**ci, false, false);
							
							/**
							 * Fix the terms, if two terms are equal in the original transition they should be equal in the
							 * grounded instances.
							 */
							for (std::vector<BoundedAtom*>::const_iterator from_dtg_node_ci = from_dtg_node_clone->getAtoms().begin(); from_dtg_node_ci != from_dtg_node_clone->getAtoms().end(); from_dtg_node_ci++)
							{
								BoundedAtom* from_dtg_node_clone_bounded_atom = *from_dtg_node_ci;
								
								for (std::vector<BoundedAtom*>::const_iterator to_dtg_node_ci = to_dtg_node_clone->getAtoms().begin(); to_dtg_node_ci != to_dtg_node_clone->getAtoms().end(); to_dtg_node_ci++)
								{
									BoundedAtom* to_dtg_node_clone_bounded_atom = *to_dtg_node_ci;
									
									for (std::vector<const Term*>::const_iterator from_dtg_node_term_ci = from_dtg_node_clone_bounded_atom->getAtom().getTerms().begin(); from_dtg_node_term_ci != from_dtg_node_clone_bounded_atom->getAtom().getTerms().end(); from_dtg_node_term_ci++)
									{
										const Term* from_dtg_node_clone_term = *from_dtg_node_term_ci;
										
										for (std::vector<const Term*>::const_iterator to_dtg_node_term_ci = to_dtg_node_clone_bounded_atom->getAtom().getTerms().begin(); to_dtg_node_term_ci != to_dtg_node_clone_bounded_atom->getAtom().getTerms().end(); to_dtg_node_term_ci++)
										{
											const Term* to_dtg_node_clone_term = *to_dtg_node_term_ci;
											
											if (from_dtg_node_clone_term->isTheSameAs(from_dtg_node_clone_bounded_atom->getId(), *to_dtg_node_clone_term, to_dtg_node_clone_bounded_atom->getId(), dtg->getBindings()))
											{
												// Establish the same relationship in the grounded version.
												const BoundedAtom* equivalent_from_bounded_atom = from_dtg_node->getAtoms()[std::distance(from_dtg_node_clone->getAtoms().begin(), from_dtg_node_ci)];
												const BoundedAtom* equivalent_to_bounded_atom = to_dtg_node->getAtoms()[std::distance(to_dtg_node_clone->getAtoms().begin(), to_dtg_node_ci)];
												
												const Term* equivalent_from_term = equivalent_from_bounded_atom->getAtom().getTerms()[std::distance(from_dtg_node_clone_bounded_atom->getAtom().getTerms().begin(), from_dtg_node_term_ci)];
												const Term* equivalent_to_term = equivalent_to_bounded_atom->getAtom().getTerms()[std::distance(to_dtg_node_clone_bounded_atom->getAtom().getTerms().begin(), to_dtg_node_term_ci)];
												
												equivalent_from_term->unify(equivalent_from_bounded_atom->getId(), *equivalent_to_term, equivalent_to_bounded_atom->getId(), dtg->getBindings());
											}
										}
									}
								}
							}
							
							const Transition* new_transition = Transition::createTransition(*enable_dummy, transition->getStep()->getAction(), *from_dtg_node, *to_dtg_node, *initial_facts_);
							
							if (new_transition == NULL)
							{
								continue;
							}
							
							from_dtg_node->addTransition(*new_transition, false);
							
							for (std::vector<unsigned int>::const_iterator ci = precondition_index_to_add_to_to_node.begin(); ci != precondition_index_to_add_to_to_node.end(); ci++)
							{
								BoundedAtom* bounded_atom = new BoundedAtom(new_transition->getStep()->getStepId(), *new_transition->getAllPreconditions()[*ci].first, NULL);
								
								bool already_part_of_to_node = false;
								
								// Make sure it is not already part of the to node.
								for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node->getAtoms().begin(); ci != to_dtg_node->getAtoms().end(); ci++)
								{
									const BoundedAtom* to_bounded_atom = *ci;
									if (from_dtg_node->getDTG().getBindings().areEquivalent(to_bounded_atom->getAtom(), to_bounded_atom->getId(), bounded_atom->getAtom(), bounded_atom->getId()))
									{
										already_part_of_to_node = true;
										break;
									}
								}
								
								if (!already_part_of_to_node)
								{
									to_dtg_node->addAtom(bounded_atom, INVALID_INDEX_ID);
								}
							}
						}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
						std::cout << " NEW: " << *from_dtg_node << std::endl;
#endif
						resulting_nodes.push_back(from_dtg_node);
						replace_lifted_dtg_node = true;
					}
				}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "ORG:" << std::endl;
				from_dtg_node_clone->print(std::cout);
				std::cout << " -=- ";
				transition->getStep()->getAction().print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
				std::cout << std::endl << " -+----------+- " << std::endl;
#endif
			}
			
			if (replace_lifted_dtg_node)
			{
				dtg_nodes_to_remove.push_back(dtg_node);
			}
		}
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes_to_remove.begin(); ci != dtg_nodes_to_remove.end(); ci++)
		{
				dtg->removeNode(**ci);
		}
				
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = resulting_nodes.begin(); ci != resulting_nodes.end(); ci++)
		{
			assert (dtg->addNode(**ci));
		}
	}
	
/*
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	**
	 * Print out the result in DOT format.
	 *
	std::ofstream ofs;
	ofs.open("relaxed_dtgs.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = resulting_nodes.begin(); ci != resulting_nodes.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		Graphviz::printToDot(ofs, *dtg_node);
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			Graphviz::printToDot(ofs, *transition, dtg_node->getDTG().getBindings());
		}
	}
	
	ofs << "}" << std::endl;
	ofs.close();
#endif
*/
}

bool DomainTransitionGraphManager::isTermStatic(const Atom& atom, StepID step_id, InvariableIndex term_index, const Bindings& bindings) const
{
	std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_dtg_nodes;
	getDTGNodes(found_dtg_nodes, step_id, atom, bindings);
	
	for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_dtg_nodes.begin(); ci != found_dtg_nodes.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		const BoundedAtom* bounded_atom = (*ci).second;
		
		if (dtg_node->getIndex(*bounded_atom) == term_index)
		{
			return false;
		}
	}
	
	return true;
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
