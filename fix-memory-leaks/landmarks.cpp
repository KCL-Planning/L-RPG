#include <fstream>
#include <algorithm>
#include <vector>
#include <iterator>

#include <boost/bind.hpp>
#include <boost/lambda/lambda.hpp>
#include <boost/lambda/bind.hpp>

#include "landmarks.h"
#include "action_manager.h"
#include "type_manager.h"
#include "predicate_manager.h"
#include "plan.h"
#include "plan_flaws.h"
#include "parser_utils.h"
#include "bindings_propagator.h"
#include "plan_bindings.h"
#include "formula.h"
#include "term_manager.h"
#include "SAS/dtg_manager.h"
#include "SAS/dtg_node.h"
#include "SAS/transition.h"
//#include "SAS/reachability.h"

///#define MYPOP_LANDMARKS_COMMENTS

namespace MyPOP {

namespace LANDMARKS {

/*************************
 * The LandmarkOrderings class
 *************************/
bool LandmarkOrderings::addOrdering(const Ordering& ordering)
{

	// Check if any of the new orderings concern a step id which is greater than we currently
	// have stored.
	StepID max_step_id = (ordering.before_id() < ordering.after_id() ? ordering.after_id() : ordering.before_id());
	if (max_step_id >= orderings_.size())
	{
		// Add new bitsets for the new step(s).
		while (max_step_id >= orderings_.size())
		{
			orderings_.push_back(new boost::dynamic_bitset<>());
		}

		// Extend the existing and new bitsets.
		for (std::vector<boost::dynamic_bitset<>*>::const_iterator ci = orderings_.begin(); ci != orderings_.end(); ci++)
		{
			(*ci)->resize(max_step_id + 1, true);
		}

		biggest_step_id_ = max_step_id;
	}

#ifdef MYPOP_LANDMARKS_COMMENTS
	std::cout << "Highest index " << biggest_step_id_ << std::endl;
	std::cout << "Ordering size" << orderings_.size() << std::endl;
	std::cout << "before id " << ordering.before_id() << std::endl;
	std::cout << "after id " << ordering.after_id() << std::endl;
#endif

	// Having extended the bitset. We continue by imposing the actual ordering constraint.
	(*orderings_[ordering.after_id()])[ordering.before_id()] = false;

	// Now we have to search through the bitset for other orderings we can deduce from this
	// information. All steps ordered before before_id are also ordered before after_id and
	// all steps ordered after after_id are also ordered after before_id (Bweh!? - you're
	// still with me? ;)).
	for (StepID i = 0; i < biggest_step_id_; i++)
	{
		// Step id i cannot be ordered before after_id. So make sure it also cannot be ordered
		// before before_id.
		if (!canBeOrderedBefore(i, StepTime::dummy_step_time, ordering.after_id(), StepTime::dummy_step_time))
		{
			// If the step cannot be ordered after, we cannot impose the ordering.
			if (!canBeOrderedAfter(i, StepTime::dummy_step_time, ordering.before_id(), StepTime::dummy_step_time))
				return false;
		}

		// The other way around, step id i cannot be ordered after before_id. So make sure it also
		// cannot be ordered after after_id.
		if (!canBeOrderedAfter(i, StepTime::dummy_step_time, ordering.before_id(), StepTime::dummy_step_time))
		{
			// If the step cannot be ordered before, we cannot impose the ordering.
			if (!canBeOrderedBefore(i, StepTime::dummy_step_time, ordering.after_id(), StepTime::dummy_step_time))
				return false;
		}
	}

	// We could succesfully impose the orderings.
	return true;
}
	
/*************************
 * The LandmarkManager class
 *************************/
LandmarkManager::LandmarkManager(const ActionManager& action_manager, const TypeManager& type_manager, const TermManager& term_manager)
	: action_manager_(&action_manager), type_manager_(&type_manager), term_manager_(&term_manager), landmark_graph_(new LandmarkGraph(term_manager))
{

}

LandmarkManager::~LandmarkManager()
{
	delete landmark_graph_;
}

void LandmarkManager::findLandmarksFromGoal(const VAL::operator_list& operators, const VAL::pddl_type_list& types, Plan& initial_plan, const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const SAS_Plus::CausalGraph& causal_graph)
{
	// When looking for landmarks from the goals it may very well be that more than one action supports this
	// landmark, we must ensure that we can unify all the supporting actions before we can call the shared 
	// precondition a landmark.
	std::vector<const PreconditionLandmark*> landmarks;

	std::vector<const PreconditionLandmark*>* goal_shared_landmarks = new std::vector<const PreconditionLandmark*>();

	// Initialise the landmarks with the goals we want to achieve.
	for (std::vector<OpenConditionPtr>::const_iterator ci = initial_plan.getOpenConditions().begin(); ci != initial_plan.getOpenConditions().end(); ci++)
	{
		const Atom& goal_atom = (*ci)->getAtom();
		PreconditionLandmark* goal_landmark = new PreconditionLandmark((*ci)->getStep()->getStepId(), goal_atom, initial_plan.getBindings(), *landmark_graph_);
		goal_shared_landmarks->push_back(goal_landmark);
		goal_landmark->setSharedLandmarks(*goal_shared_landmarks);

		std::vector<StepPtr>* steps = new std::vector<StepPtr>();
		StepPtr landmark_step(new Step(goal_landmark->getStepId(), (*ci)->getStep()->getAction()));
		steps->push_back(landmark_step);
		goal_landmark->setAchievingActions(*steps);
		landmarks.push_back(goal_landmark);
	}

	// Initialise the initial facts and transform them into landmarks.
	const Action& initial_state_action = initial_plan.getSteps()[Step::INITIAL_STEP]->getAction();
	const std::vector<const Atom*>& initial_effects = initial_state_action.getEffects();
	std::vector<const Landmark*> initial_landmarks;
	for (std::vector<const Atom*>::const_iterator ci = initial_effects.begin(); ci != initial_effects.end(); ci++)
	{
		// Create a new landmark and order it before the goal landmarks.
		Landmark* initial_landmark = new Landmark(Step::INITIAL_STEP, **ci, initial_plan.getBindings(), *landmark_graph_);
		initial_landmarks.push_back(initial_landmark);

		/*for (std::vector<const PreconditionLandmark*>::const_iterator goal_landmarks_ci = landmarks.begin(); goal_landmarks_ci != landmarks.end(); goal_landmarks_ci++)
		{
			landmark_graph_->addOrdering(*initial_landmark, **goal_landmarks_ci);
		}*/
	}

	while (landmarks.size() > 0)
	{
		// The actual landmark.
		const PreconditionLandmark& landmark = *landmarks.front();
		landmarks.erase(landmarks.begin());
		
		std::cout << " === Process landmark: ";
		landmark.getAtom().print(std::cout, landmark_graph_->getBindings(), landmark.getStepId());
		std::cout << " ===" << std::endl;

		// If the landmark is bindable to the initial state than we are done and no further landmarks can be derived using this technique.
		StepPtr initial_step = initial_plan.getSteps()[0];

		if (landmark_graph_->isUnifiable(initial_step, initial_plan.getBindings(), landmark))
		{
			std::cout << "The landmark ";
			landmark.getAtom().print(std::cout);
			std::cout << " is unifiable with the initial state, moving on!" << std::endl;
			continue;
		}
		
		// Check if all possible achievers share a common precondition.
		std::vector<const PreconditionLandmark*> new_landmarks;
		getCommonPreconditions(new_landmarks, landmark, initial_plan, dtg_manager);
		
		// If no shared precondition was found, we search for the first achievers of that landmark instead.
		if (new_landmarks.size() == 0)
		{
			getFirstAchievers(new_landmarks, landmark, initial_plan, dtg_manager);
		}
	
		// We have now added the landmarks to the landmark graph and their bindings are fixed. The next step is to check if there are any intermediate
		// landmarks between the landmark we just processed and all the common preconditions we just found. We do this analysis by looking at the DTGs.
		for (std::vector<const PreconditionLandmark*>::const_iterator shared_landmark_ci = new_landmarks.begin(); shared_landmark_ci != new_landmarks.end(); shared_landmark_ci++)
		{
			const PreconditionLandmark* shared_landmark = *shared_landmark_ci;
			findClosestLandmarksInDTG(landmarks, dtg_manager, *shared_landmark, landmark);
		}

		// If no shared landmarks were found, try to find a path to the initial state.
		if (new_landmarks.size() == 0)
		{
			std::cout << "Find additional landmarks!" << std::endl;
			for (std::vector<const Landmark*>::const_iterator ci = initial_landmarks.begin(); ci != initial_landmarks.end(); ci++)
			{
				findClosestLandmarksInDTG(landmarks, dtg_manager, **ci, landmark);
			}
		}
		
		landmarks.insert(landmarks.end(), new_landmarks.begin(), new_landmarks.end());
	}

	std::cout << initial_plan << std::endl;
}

void LandmarkManager::getCommonPreconditions(std::vector<const PreconditionLandmark*>& landmarks, const PreconditionLandmark& landmark, Plan& initial_plan, const SAS_Plus::DomainTransitionGraphManager& dtg_manager) const
{
	// Check which actions can achieve the given predicate.
	std::vector<std::pair<const Action*, const Atom*> > achieving_actions;
	action_manager_->getAchievingActions(achieving_actions, landmark.getAtom());

	std::cout << "All actions who achieve this landmark: " << std::endl;

	// Create the variable domains for all operators.
	std::map<const Action*, StepID> action_step_ids;
	for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator action_ci = achieving_actions.begin(); action_ci != achieving_actions.end(); action_ci++)
	{
		const Action* action = (*action_ci).first;
		std::cout << "* " << *action << std::endl;

		// Initialise the variable domains of all the actions.
		if (action_step_ids.find(action) == action_step_ids.end())
		{
			StepID action_step_id = landmark_graph_->getBindings().createVariableDomains(*action);
			action_step_ids[action] = action_step_id;
		}
	}

	// Store the steps of all supporting actions. Both the action and the effect achieving the landmark.
	std::vector<StepPtr>* supporting_action_steps = new std::vector<StepPtr>();
	std::vector<const Atom*> supporting_action_effects;

	for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator actions_ci = achieving_actions.begin(); actions_ci != achieving_actions.end(); actions_ci++)
	{
		// Check if the action can be unified with the landmark.
		const Action* the_action = (*actions_ci).first;

		StepID action_step_id = action_step_ids[the_action];
		StepPtr new_step(new Step(action_step_id, *the_action));

		const Atom* the_effect = (*actions_ci).second;

		// The actions which can achieve the atom of the landmark might not be able to support the actual landmark. E.g. if the atom
		// is: (available ?device) but there are many different subtypes of devices and the landmark happens to be of type ?phone.
		// Then the action (make-available ?car) will not be applicable and hence we skip it.
		if (!landmark_graph_->getBindings().canUnify(landmark.getAtom(), landmark.getStepId(), *the_effect, action_step_id))
		{
			std::cout << "Cannot unify " << *the_action << " with ";
			landmark.getAtom().print(std::cout);
			std::cout << std::endl;
			continue;
		}

		std::cout << "Supporting action: ";
		the_action->print(std::cout, landmark_graph_->getBindings(), action_step_id);
		std::cout << " (Effect: ";
		the_effect->print(std::cout, landmark_graph_->getBindings(), action_step_id);
		std::cout << std::endl;
		
		// Add the discovered landmarks to the list to be processed.
		supporting_action_steps->push_back(new_step);
		supporting_action_effects.push_back(the_effect);
	}

	// If none of the actions could be unified this problem is unsolvable!
	assert (supporting_action_steps->size() > 0);
	
	StepPtr initial_step = initial_plan.getSteps()[0];
	const Action& initial_state_action = initial_plan.getSteps()[Step::INITIAL_STEP]->getAction();
	const std::vector<const Atom*>& initial_effects = initial_state_action.getEffects();

	// If all the actions could be unified: apply the actual bindings.
	for (int i = supporting_action_steps->size() - 1; i > -1; i--)
	{
		// Unify the action with the goal.
		const Action& the_action = (*supporting_action_steps)[i]->getAction();

		StepID action_step_id = action_step_ids[&the_action];
		StepPtr new_step(new Step(action_step_id, the_action));

		const Atom* the_effect = supporting_action_effects[i];

		assert (landmark_graph_->getBindings().unify(landmark.getAtom(), landmark.getStepId(), *the_effect, action_step_id));

		std::cout << "Bind together ";
		landmark.getAtom().print(std::cout, landmark_graph_->getBindings(), landmark.getStepId());
		std::cout << " and ";
		the_effect->print(std::cout, landmark_graph_->getBindings(), action_step_id);
		std::cout << " -> ";
		the_action.print(std::cout, landmark_graph_->getBindings(), action_step_id);
		std::cout << std::endl;
		
		// Try to bind all static preconditions.
		std::vector<const Atom*> preconditions;
		Utility::convertFormula(preconditions, &the_action.getPrecondition());
		
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
		{
			const Atom* precondition = *ci;
			if (!precondition->getPredicate().isStatic())
			{
				continue;
			}
			
			std::cout << "Static precondition: ";
			precondition->print(std::cout, landmark_graph_->getBindings(), action_step_id);
			std::cout << std::endl;
			
			// Store all possible assignments of the static preconditions.
			std::set<const Object*>* possible_assignments[precondition->getArity()];
			for (unsigned int i = 0; i < precondition->getArity(); i++)
			{
				possible_assignments[i] = new std::set<const Object*>();
			}
			
			for (std::vector<const Atom*>::const_iterator ci2 = initial_effects.begin(); ci2 != initial_effects.end(); ci2++)
			{
				const Atom* initial_fact = *ci2;
				
				std::cout << "Check against initial fact: ";
				initial_fact->print(std::cout, initial_plan.getBindings(), Step::INITIAL_STEP);
				std::cout << std::endl;
				
				if (landmark_graph_->getBindings().canUnify(*precondition, action_step_id, *initial_fact, Step::INITIAL_STEP, &initial_plan.getBindings()))
				{
					assert (initial_fact->getArity() == precondition->getArity());
					for (unsigned int i = 0; i < precondition->getArity(); i++)
					{
						//VariableDomain& vd = initial_plan.getBindings().getNonConstVariableDomain(Step::INITIAL_STEP, *initial_fact->getTerms()[i]->asVariable());
						//possible_assignments[i]->insert(vd.getDomain().begin(), vd.getDomain().end());
						possible_assignments[i]->insert(initial_fact->getTerms()[i]->asObject());
					}
				}
			}
			
			// Unify the operator's static preconditions with the possible assignments from the initial state. If this assignments
			// lead to an empty domain we remove the operator as a possible supporter for the landmark.
			bool do_delete = false;
			for (unsigned int i = 0; i < precondition->getArity(); i++)
			{
				std::vector<const Object*> objects;
				objects.insert(objects.begin(), possible_assignments[i]->begin(), possible_assignments[i]->end());
				
				VariableDomain& vd = landmark_graph_->getBindings().getNonConstVariableDomain(action_step_id, *precondition->getTerms()[i]->asVariable());
				vd.makeEqualTo(objects);
				
				if (vd.getDomain().size() == 0)
				{
					supporting_action_steps->erase(supporting_action_steps->begin() + i);
					do_delete = true;
					break;
				}
			}
			
			if (do_delete)
			{
				break;
			}
		}
	}

	// In case of multiple actions being applicable, check if they share a common precondition. To do so
	// we initialise the shared_precondition vector with all the preconditions of the first action and
	// eliminate those who are not shared by any of the others.
	std::vector<const Atom*> shared_preconditions;
	getSharedPreconditions(shared_preconditions, *supporting_action_steps);

	// If no shared landmarks are found we will do an extra round of pruning. This is (hopefully) the same as looking for greedy-necessary
	// landmarks when using the RPG. The goal is to look for the earliest possible achievers of the landmarks.
	// Check all the preconditions of the actions and see if they are mutex with each other. We do this by checking if they appear in the same
	// DTG in which case they can't be true at the same time. Next we remove from the DTGs the landmark we try to achieve and check which nodes
	// can be reached from the initial state. All nodes which can be reached from the initial state are the 'first achievers' and the other nodes
	// are those which can only be achieved after this landmark has been achieved at least once.
	// At least... that's the idea :).
/*	
	if (shared_preconditions.size() == 0)
	{
		std::vector<StepPtr> new_supporting_action_steps;
		std::vector<const Atom*> new_supporting_action_effects;

		// Check out if there is a precondition for one of the actions which shares a common DTG with the landmark we try to achieve.
		std::vector<const SAS_Plus::DomainTransitionGraph*> landmark_nodes;
		dtg_manager.getDTGs(landmark_nodes, landmark.getStepId(), landmark.getAtom(), landmark_graph_->getBindings());

		// Check all the DTGs of the preconditions and check if there is an overlap.
		for (unsigned int i = 0; i < supporting_action_steps->size(); i++)
		{
			const StepPtr step = (*supporting_action_steps)[i];
			const Atom* effect = supporting_action_effects[i];

			std::cout << "Check ";
			step->getAction().print(std::cout, landmark_graph_->getBindings(), step->getStepId());
			std::cout << "[";
			effect->print(std::cout, landmark_graph_->getBindings(), step->getStepId());
			std::cout << "]" << std::endl;

			std::vector<const Atom*> preconditions;
			Utility::convertFormula(preconditions, &step->getAction().getPrecondition());

			std::vector<const SAS_Plus::DomainTransitionGraph*> supporting_action_preconditions;

			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				dtg_manager.getDTGs(supporting_action_preconditions, step->getStepId(), *effect, landmark_graph_->getBindings());
			}
			std::sort(supporting_action_preconditions.begin(), supporting_action_preconditions.end());

			// Check if there is any overlap in the DTGs.
			std::vector<const SAS_Plus::DomainTransitionGraph*> intersection(supporting_action_preconditions.size() + landmark_nodes.size());
			std::vector<const SAS_Plus::DomainTransitionGraph*>::const_iterator end_intersection_ci = std::set_intersection(supporting_action_preconditions.begin(), supporting_action_preconditions.end(), landmark_nodes.begin(), landmark_nodes.end(), intersection.begin());

			// Check if there is any intersection at all, if not: move on.
			if (end_intersection_ci == intersection.begin())
			{
				continue;
			}

			// Do the DTG analysis by only allowing the common DTG to hold the value from the initial state.
			// NOTE: Not sure if multiple DTGs can actually be considered at this point.
			assert (end_intersection_ci == intersection.begin() + 1);

			const SAS_Plus::DomainTransitionGraph* landmark_dtg = *intersection.begin();
			std::cout << "Compare against: " << *landmark_dtg << std::endl;
///				std::vector<const Atom*> allowed_initial_facts;

///				for (std::vector<const Atom*>::const_iterator ci = initial_effects.begin(); ci != initial_effects.end(); ci++)
///				{
///					const Atom* initial_fact = *ci;
///					std::cout << "Initial fact: ";
///					initial_fact->print(std::cout, initial_plan.getBindings(), Step::INITIAL_STEP);
///					std::cout << std::endl;
///
///					std::vector<const SAS_Plus::DomainTransitionGraphNode*> initial_dtg_nodes;
///					landmark_dtg->getNodes(initial_dtg_nodes, Step::INITIAL_STEP, *initial_fact, initial_plan.getBindings());
///
///					// If no nodes have been found, this initial step can be added.
///					if (initial_dtg_nodes.size() == 0)
///					{
///						std::cout << ":)" << std::endl;
///						allowed_initial_facts.push_back(initial_fact);
///					}
///					else
///					{
///						// Check for each node if the predicate object is equal to that of the landmark.
///						int initial_predicate_index = landmark_dtg->getPredicateInvariableIndex(initial_fact->getPredicate());
///						int landmark_predicate_index = landmark_dtg->getPredicateInvariableIndex(landmark.getAtom().getPredicate());
///
///						if (landmark_graph_->getBindings().canUnify(*landmark.getAtom().getTerms()[landmark_predicate_index], landmark.getStepId(), *initial_fact->getTerms()[initial_predicate_index], Step::INITIAL_STEP, &initial_plan.getBindings()))
///						{
///							std::cout << ":D" << std::endl;
///							allowed_initial_facts.push_back(initial_fact);
///						}
///						else
///						{
///							std::cout << ";(" << std::endl;
///						}
///					}
///				}

			// Now check if the precondition can be reached from the initial state.
			std::cout << "Building reachability graph..." << std::endl;
			SAS_Plus::ReachabilityAnalist analyst(dtg_manager);

			std::vector<const SAS_Plus::DomainTransitionGraphNode*> landmark_nodes;
			landmark_dtg->getNodes(landmark_nodes, landmark.getStepId(), landmark.getAtom(), landmark_graph_->getBindings());

			std::for_each(landmark_nodes.begin(), landmark_nodes.end(), boost::lambda::bind(&SAS_Plus::ReachabilityAnalist::ignoreNode, &analyst, *boost::lambda::_1));
//				analyst.constructReachablilityGraph(allowed_initial_facts, initial_plan.getBindings());
			analyst.constructReachablilityGraph(initial_effects, initial_plan.getBindings());
			std::cout << "[DONE] Building reachability graph..." << std::endl;

			// Check if the action is applicable.
			bool is_reachable = true;
			std::vector<const SAS_Plus::DomainTransitionGraphNode*> precondition_dtg_nodes;
			for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				landmark_dtg->getNodes(precondition_dtg_nodes, step->getStepId(), **ci, landmark_graph_->getBindings());
			}

			for (std::vector<const SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = precondition_dtg_nodes.begin(); ci != precondition_dtg_nodes.end(); ci++)
			{
				const SAS_Plus::DomainTransitionGraphNode* precondition_node = *ci;
				std::cout << "Is " << *precondition_node << " reachable?" << std::endl;
				if (analyst.getReachableDTGNode(*precondition_node) == NULL)
				{
					is_reachable = false;
					break;
				}
			}
			if (is_reachable)
			{
				step->getAction().print(std::cout, landmark_graph_->getBindings(), step->getStepId());
				std::cout << "Is reachable!!!" << std::endl;
				new_supporting_action_steps.push_back(step);
				new_supporting_action_effects.push_back(effect);
			}
		}

		supporting_action_steps->clear();
		supporting_action_effects.clear();

		supporting_action_steps->insert(supporting_action_steps->begin(), new_supporting_action_steps.begin(), new_supporting_action_steps.end());
		supporting_action_effects.insert(supporting_action_effects.begin(), new_supporting_action_effects.begin(), new_supporting_action_effects.end());

		getSharedPreconditions(shared_preconditions, *supporting_action_steps);
	}
*/

	// We now have a vector containing all preconditions which are shared among all the achieving actions; Add these
	// as landmarks.
	std::cout << "Landmarks for " << landmark << ":" << std::endl;

	// Group all the landmarks derived from a common precondition together. These will be used to derive extra landmarks.
	for (std::vector<const Atom*>::const_iterator ci = shared_preconditions.begin(); ci != shared_preconditions.end(); ci++)
	{
		// Add the new found landmark to the list to be processed.
		const Atom* shared_landmark_atom = *ci;

		// A new StepID for each landmark needs to be created. We could use the StepID of one of the actions this landmark is
		// a precondition of. But doing so would mean that an ordering constraint on one of the preconditions would mean the same
		// order constraint on all of the shared precondition. This would mean we introduce false ordering constraints, so we
		// add each landmark with a unique ID but unify all its variable domains so a change in one will mean a change in all.
		StepID shared_landmark_atom_id = landmark_graph_->getBindings().createVariableDomains(*shared_landmark_atom);
		landmark_graph_->getBindings().unify(*shared_landmark_atom, shared_landmark_atom_id, *shared_landmark_atom, ((*supporting_action_steps)[0]->getStepId()));

		PreconditionLandmark* shared_landmark = new PreconditionLandmark(shared_landmark_atom_id, *shared_landmark_atom, landmark_graph_->getBindings(), *landmark_graph_);

		landmarks.push_back(shared_landmark);
		landmark_graph_->addOrdering(*shared_landmark, landmark);

		std::cout << "* [" << shared_landmark_atom_id << "] ";
		shared_landmark_atom->print(std::cout, landmark_graph_->getBindings(), shared_landmark_atom_id);
		initial_step->getAction().print(std::cout, initial_plan.getBindings(), initial_step->getStepId());
		std::cout << std::endl;
	}
	std::cout << std::endl;
}

void LandmarkManager::getFirstAchievers(std::vector<const PreconditionLandmark*>& landmarks, const PreconditionLandmark& landmark, Plan& initial_plan, const SAS_Plus::DomainTransitionGraphManager& dtg_manager) const
{
	std::cout << "Trying to find the first achievers of the landmark " << landmark << std::endl;
	
	SAS_Plus::ReachabilityAnalist reachability_analist(dtg_manager);
	std::vector<const Landmark*> landmarks_to_reach;
	landmarks_to_reach.push_back(&landmark);
	
	const std::vector<const Atom*>& initial_facts = initial_plan.getSteps()[Step::INITIAL_STEP]->getAction().getEffects();
	
	reachability_analist.initialiseReachablilityGraph(initial_facts, initial_plan.getBindings());
	
	// Perform the reachaiblity analisys and check which transitions can reach the landmark.
	reachability_analist.constructReachablilityGraph(landmarks_to_reach, initial_facts);
	
	std::vector<const SAS_Plus::DomainTransitionGraphNode*> landmark_nodes;
	dtg_manager.getDTGNodes(landmark_nodes, landmark.getStepId(), landmark.getAtom(), landmark.getLandmarkGraph().getBindings());
	
	std::cout << "% Get first achievers of " << landmark << "(" << landmark_nodes.size() << ")" << std::endl;
	
	for (std::vector<const SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = landmark_nodes.begin(); ci != landmark_nodes.end(); ci++)
	{
		std::cout << "Check the DTG node: ";
		(*ci)->print(std::cout);
		std::cout << std::endl;
		const SAS_Plus::ReachableDTGNode* reachable_node = reachability_analist.getReachableDTGNode(**ci);
		std::vector<const SAS_Plus::ReachableDTGNode*> reachable_nodes = reachable_node->getReachableFromNodes();
		for (std::vector<const SAS_Plus::ReachableDTGNode*>::const_iterator ci = reachable_nodes.begin(); ci != reachable_nodes.end(); ci++)
		{
			std::cout << "** Reachable from: " << (*ci)->getDTGNode() << std::endl;
		}
	}
}

void LandmarkManager::getSharedPreconditions(std::vector<const Atom*>& shared_preconditions, const std::vector<StepPtr>& action_steps) const
{
	if (action_steps.size() == 0)
		return;

	Utility::convertFormula(shared_preconditions, &action_steps[0]->getAction().getPrecondition());

	std::cout << "Initial shared preconditions: ";
	for (std::vector<const Atom*>::iterator shared_i = shared_preconditions.begin(); shared_i != shared_preconditions.end(); shared_i++)
	{
		(*shared_i)->print(std::cout);
		std::cout << ", ";
	}
	std::cout << std::endl;

	for (std::vector<const Atom*>::reverse_iterator shared_i = shared_preconditions.rbegin(); shared_i != shared_preconditions.rend(); shared_i++)
	{
		bool found = false;
		
		// Remove those atoms from the shared precondition vector which are not shared by this action.
		for (std::vector<StepPtr>::const_iterator achieving_ci = action_steps.begin() + 1; achieving_ci != action_steps.end(); achieving_ci++)
		{
			const Action& supporting_action = (*achieving_ci)->getAction();
			std::vector<const Atom*> preconditions;

			Utility::convertFormula(preconditions, &supporting_action.getPrecondition());

			for (std::vector<const Atom*>::const_iterator precondition_ci = preconditions.begin(); precondition_ci != preconditions.end(); precondition_ci++)
			{
				// TODO: Check if the atoms need to be exactly the same or if they should just be able to be unified...
				if (*shared_i == *precondition_ci)
				{
					found = true;
					break;
				}
			}

			// If the precondition isn't shared between a single action, remove it.
			if (!found)
			{
				(*(shared_i.base() - 1))->print(std::cout);
				std::cout << " is not part of the shared list! as it is not shared by action " << supporting_action << std::endl;
				shared_preconditions.erase(shared_i.base() - 1);
				break;
			}
		}
	}
}


void LandmarkManager::findClosestLandmarksInDTG(std::vector<const PreconditionLandmark*>& found_landmarks, const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const Landmark& from_landmark, const Landmark& to_landmark)
{
/*
	std::cout << "Find path between: " << from_landmark << " and " << to_landmark << std::endl;
	// First check to which DTG both landmarks are linked.
	std::vector<const SAS_Plus::DomainTransitionGraph*> from_dtg_graphs;
	dtg_manager.getDTGs(from_dtg_graphs, from_landmark.getStepId(), from_landmark.getAtom(), landmark_graph_->getBindings());
	std::vector<const SAS_Plus::DomainTransitionGraph*> to_dtg_graphs;
	dtg_manager.getDTGs(to_dtg_graphs, to_landmark.getStepId(), to_landmark.getAtom(), landmark_graph_->getBindings());

	// Check to see if there is any overlapping.
	std::sort(from_dtg_graphs.begin(), from_dtg_graphs.end());
	std::sort(to_dtg_graphs.begin(), to_dtg_graphs.end());

	std::vector<const SAS_Plus::DomainTransitionGraph*> intersection(max(from_dtg_graphs.size(), to_dtg_graphs.size()));
	std::vector<const SAS_Plus::DomainTransitionGraph*>::iterator intersection_end = std::set_intersection(from_dtg_graphs.begin(), from_dtg_graphs.end(), to_dtg_graphs.begin(), to_dtg_graphs.end(), intersection.begin());

	// For the shared DTGs check for additional landmarks.
	for (std::vector<const SAS_Plus::DomainTransitionGraph*>::const_iterator ci = intersection.begin(); ci != intersection_end; ci++)
	{
		// Find the nodes in this DTG for the two landmarks.
		const SAS_Plus::DomainTransitionGraph* dtg = *ci;
		assert (dtg != NULL);
		
		int from_index = dtg->getPredicateInvariableIndex(from_landmark.getAtom().getPredicate());
		int to_index = dtg->getPredicateInvariableIndex(to_landmark.getAtom().getPredicate());
		
		if (!landmark_graph_->getBindings().canUnify(*from_landmark.getAtom().getTerms()[from_index], from_landmark.getStepId(), *to_landmark.getAtom().getTerms()[to_index], to_landmark.getStepId()))
		{
			continue;
		}
		
		std::vector<const SAS_Plus::DomainTransitionGraphNode*> from_dtg_nodes;
		dtg->getNodes(from_dtg_nodes, from_landmark.getStepId(), from_landmark.getAtom(), landmark_graph_->getBindings());

		std::vector<const SAS_Plus::DomainTransitionGraphNode*> to_dtg_nodes;
		dtg->getNodes(to_dtg_nodes, to_landmark.getStepId(), to_landmark.getAtom(), landmark_graph_->getBindings());

		// Now we will employ the pathfinder to check for a path between the two sets of points.
		SAS_Plus::Pathfinder path_finder(*dtg);

		// Create initial path.
		std::vector<const SAS_Plus::DomainTransitionGraphNode*> path;
		bool path_found = path_finder.getPath(path, from_dtg_nodes, to_dtg_nodes);

		if (!path_found)
		{
			std::cout << "No path found!" << std::endl;
			continue;
		}
		
		for (std::vector<const SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = path.begin(); ci != path.end(); ci++)
		{
			std::cout << "* " << **ci << std::endl;
		}
		
		if  (path.size() < 3)
		{
			std::cout << "Path too short!" << std::endl;
			continue;
		}

		// For each node on the path we will dissalow that node and see if a path is still available. We start at the
		// node just before the to_node and work our way down. This is because we are searching for landmark from the
		// goal state to the initial state. So the closest landmark is the landmark closest to the to_node.
		for (unsigned int i = path.size() - 2; i > 0; i--)
		{
			path_finder.clearIgnoreList();
			path_finder.ignoreNode(*path[i]);
			std::vector<const SAS_Plus::DomainTransitionGraphNode*> tmp_path;
			
			std::cout << "Try again, ignore: " << *path[i] << std::endl;

			if (!path_finder.getPath(tmp_path, from_dtg_nodes, to_dtg_nodes))
			{
				// No path was found so the blocked node must have been the closest landmark!
				PreconditionLandmark* landmark = new PreconditionLandmark(path[i]->getId(), path[i]->getAtom(), dtg->getBindings(), *landmark_graph_);
				
				std::cout << "Found new landmark! " << *landmark << std::endl;
				
				std::vector<const PreconditionLandmark*>* shared_landmarks = new std::vector<const PreconditionLandmark*>();
				landmark->setSharedLandmarks(*shared_landmarks);
				
				// Find all actions which can achieve this landmark.
				std::vector<StepPtr>* achieving_actions = new std::vector<StepPtr>();
				landmark->setAchievingActions(*achieving_actions);
				
				path_finder.clearIgnoreList();
				tmp_path.clear();
				
				std::vector<const SAS_Plus::DomainTransitionGraphNode*> to_nodes;
				to_nodes.push_back(path[i]);
				
				while (path_finder.getPath(tmp_path, from_dtg_nodes, to_nodes))
				{
					const SAS_Plus::DomainTransitionGraphNode* node = tmp_path[tmp_path.size() - 2];
					
					// Check all transitions and pick the ones who lead to the landmark.
					for (std::vector<const SAS_Plus::Transition*>::const_iterator ci = node->getTransitions().begin(); ci != node->getTransitions().end(); ci++)
					{
						if (landmark_graph_->getBindings().canUnify(landmark->getAtom(), landmark->getStepId(), (*ci)->getToNode().getAtom(), (*ci)->getToNode().getId(), &dtg->getBindings()))
						{
							StepID transition_action_step_id = landmark_graph_->getBindings().createVariableDomains((*ci)->getStep()->getAction());
							StepPtr action_ptr(new Step(transition_action_step_id, (*ci)->getStep()->getAction()));
							achieving_actions->push_back(action_ptr);
							
							assert (landmark_graph_->getBindings().unify(landmark->getAtom(), landmark->getStepId(), (*ci)->getEffect(), transition_action_step_id));

							std::cout << "Achieving action: ";
							(*ci)->getStep()->getAction().print(std::cout, landmark_graph_->getBindings(), transition_action_step_id);
							std::cout << std::endl;
						}
					}
					
					path_finder.ignoreNode(*node);
				}				
	
				// Order this landmark before the previous landmark.
				std::cout << "Order  before (" << to_landmark.getStepId() << ")" << to_landmark << std::endl;
				landmark_graph_->addOrdering(*landmark, to_landmark);
				found_landmarks.push_back(landmark);
				break;
			}
			for (std::vector<const SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = tmp_path.begin(); ci != tmp_path.end(); ci++)
			{
				std::cout << "* " << **ci << std::endl;
			}
		}
	}
	*/
}

/*void LandmarkManager::findLandmarksInDTG(const SAS_Plus::DomainTransitionGraphManager& dtg_manager, const Landmark& from_landmark, const Landmark& to_landmark)
{
	std::cout << "Find path between: " << from_landmark << " and " << to_landmark << std::endl;
	// First check to which DTG both landmarks are linked.
	std::vector<const SAS_Plus::DomainTransitionGraph*> from_dtg_graphs;
	dtg_manager.getDTGs(from_dtg_graphs, from_landmark.getStepId(), from_landmark.getAtom(), landmark_graph_->getBindings());
	std::vector<const SAS_Plus::DomainTransitionGraph*> to_dtg_graphs;
	dtg_manager.getDTGs(to_dtg_graphs, to_landmark.getStepId(), to_landmark.getAtom(), landmark_graph_->getBindings());

	// Check to see if there is any overlapping.
	std::sort(from_dtg_graphs.begin(), from_dtg_graphs.end());
	std::sort(to_dtg_graphs.begin(), to_dtg_graphs.end());

	std::vector<const SAS_Plus::DomainTransitionGraph*> intersection(max(from_dtg_graphs.size(), to_dtg_graphs.size()));
	std::vector<const SAS_Plus::DomainTransitionGraph*>::iterator intersection_end = std::set_intersection(from_dtg_graphs.begin(), from_dtg_graphs.end(), to_dtg_graphs.begin(), to_dtg_graphs.end(), intersection.begin());

	// For the shared DTGs check for additional landmarks.
	for (std::vector<const SAS_Plus::DomainTransitionGraph*>::const_iterator ci = intersection.begin(); ci != intersection_end; ci++)
	{
		// Find the nodes in this DTG for the two landmarks.
		const SAS_Plus::DomainTransitionGraph* dtg = *ci;
		assert (dtg != NULL);
		std::vector<const SAS_Plus::DomainTransitionGraphNode*> from_dtg_nodes;
		dtg->getNodes(from_dtg_nodes, from_landmark.getStepId(), from_landmark.getAtom(), landmark_graph_->getBindings());

		std::vector<const SAS_Plus::DomainTransitionGraphNode*> to_dtg_nodes;
		dtg->getNodes(to_dtg_nodes, to_landmark.getStepId(), to_landmark.getAtom(), landmark_graph_->getBindings());

		// Now we will employ the pathfinder to check for a path between the two sets of points.
		SAS_Plus::Pathfinder path_finder(*dtg);

		// The way we will find landmarks is by successively ignoring a node in the DTG. We first find a path and we will than block
		// the first node of this path and try again:
		// * If no path can be found we know that the blocked node was a landmark.
		// * If a path can be found, we block the first node of this new path and try again.
		// * If we have to block a node for the second time we know that there is no landmark to be found on the first step. So
		// * we take the path and block the 2nd step and continue until we cannot block any nodes anymore (i.e. we reached the goal node).
		unsigned int tier = 0;
		std::set<const SAS_Plus::DomainTransitionGraphNode*> blocked_nodes;
		blocked_nodes.insert(from_dtg_nodes.begin(), from_dtg_nodes.end());
		blocked_nodes.insert(to_dtg_nodes.begin(), to_dtg_nodes.end());

		const SAS_Plus::DomainTransitionGraphNode* potential_landmark = NULL;
		const Landmark* previous_landmark = &from_landmark;

		while (true)
		{
			std::vector<const SAS_Plus::DomainTransitionGraphNode*> path;
			bool path_found = path_finder.getPath(path, from_dtg_nodes, to_dtg_nodes);
	
			if (path_found)
			{
				std::cout << "Found path: ";
				for (std::vector<const SAS_Plus::DomainTransitionGraphNode*>::const_iterator path_ci = path.begin(); path_ci != path.end(); path_ci++)
				{
					(*path_ci)->getAtom().print(std::cout, dtg->getBindings(), (*path_ci)->getId());
					std::cout << ", ";
				}
				std::cout << std::endl;

				// If the path is just 2 steps there is no way we can find a landmark since both the begin point and end point already are!
				if (path.size() < 3) break;
			}
			else
			{
				std::cout << "No path found!!!! ";

				if (potential_landmark != NULL)
				{
					potential_landmark->getAtom().print(std::cout, dtg->getBindings(), potential_landmark->getId());

					// Add the landmark to the landmark graph.
					Landmark* landmark = new Landmark(potential_landmark->getId(), potential_landmark->getAtom(), dtg->getBindings(), *landmark_graph_);

					// Order this landmark before the previous landmark.
					std::cout << "Order  before (" << previous_landmark->getStepId() << ")" << *previous_landmark << std::endl;
					landmark_graph_->addOrdering(*landmark, *previous_landmark);
					previous_landmark = landmark;
				}
				std::cout << " is a landmark!!!" << std::endl;

				if (potential_landmark != NULL)
				{
					// After adding a landmark, reset and continue.
					tier = 0;
					blocked_nodes.insert(potential_landmark);
					path_finder.clearIgnoreList();
					from_dtg_nodes.clear();
					from_dtg_nodes.push_back(potential_landmark);
					continue;
				}
			}

			// Check if we need to move to the next tier.
			if (!path_found || blocked_nodes.find(path[tier]) != blocked_nodes.end())
			{
				++tier;
			}

			// Check if we are done.
			if (tier >= path.size())
			{
				std::cout << "Break!" << std::endl;
				break;
			}

			path_finder.clearIgnoreList();
			path_finder.ignoreNode(*path[tier]);
			blocked_nodes.insert(path[tier]);

			assert (tier < path.size());
			potential_landmark = path[tier];
			assert (potential_landmark != NULL);
			std::cout << "Tier: " << tier << " - Blocked landmark: ";
			potential_landmark->getAtom().print(std::cout, dtg->getBindings(), potential_landmark->getId());
			std::cout << std::endl;
		}
	}
}*/

/*
// Not used anymore...
void LandmarkManager::findLandmarksInDTGs(const SAS_Plus::DomainTransitionGraphManager& dtg_manager, MyPOP::Plan& initial_plan)
{
	// When looking for landmarks from the goals it may very well be that more than one action supports this
	// landmark, we must ensure that we can unify all the supporting actions before we can call the shared 
	// precondition a landmark.
	std::vector<const Landmark*> landmarks;
	
	// Initialise the landmarks with the goals we want to achieve.
	for (std::vector<OpenConditionPtr>::const_iterator ci = initial_plan.getOpenConditions().begin(); ci != initial_plan.getOpenConditions().end(); ci++)
	{
		const Atom& goal_atom = (*ci)->getAtom();
		const Landmark* goal_landmark = new Landmark((*ci)->getStep()->getStepId(), goal_atom, initial_plan.getBindings(), *landmark_graph_);
		//const Landmark& goal_landmark = landmark_graph_->addLandmark(goal_atom, initial_plan.getBindings(), (*ci)->getStep()->getStepId());
		landmarks.push_back(goal_landmark);
	}
	
	// For each goal, find the DTG it is linked to.
	for (std::vector<const Landmark*>::const_iterator ci = landmarks.begin(); ci != landmarks.end(); ci++)
	{
		const Landmark* landmark = *ci;
		std::vector<const SAS_Plus::DomainTransitionGraph*> goal_dtg_graphs;
		dtg_manager.getDTGs(goal_dtg_graphs, landmark->getStepId(), landmark->getAtom(), landmark_graph_->getBindings());
		
		// If no DTG is found, it must mean that the predicate is one which can only be
		// true or false.
		// TODO: Maybe generate DTGs for these as well?
		if (goal_dtg_graphs.size() == 0)
		{
			std::cout << "No DTG fond for the landmark: ";
			landmark->getAtom().print(std::cout, initial_plan.getBindings(), landmark->getStepId());
			std::cout << std::endl;
			continue;
		}
		
		const SAS_Plus::DomainTransitionGraph* goal_dtg = NULL;
		const SAS_Plus::DomainTransitionGraphNode* goal_dtg_node = NULL;
		
		// Determine which DTG holds the goal value.
		for (std::vector<const SAS_Plus::DomainTransitionGraph*>::const_iterator goal_dtg_ci = goal_dtg_graphs.begin(); goal_dtg_ci != goal_dtg_graphs.end(); goal_dtg_ci++)
		{
			std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
			(*goal_dtg_ci)->getNodes(dtg_nodes, Step::GOAL_STEP, landmark->getAtom(), landmark_graph_->getBindings());
			if (dtg_nodes.size() > 0)
			{
				assert (dtg_nodes.size() == 1);
				// Make sure there is only a single DTG holding this fact.
				assert (goal_dtg == NULL);
				assert (goal_dtg_node == NULL);
				
				goal_dtg = *goal_dtg_ci;
				goal_dtg_node = dtg_nodes[0];
			}
		}
		
		assert (goal_dtg != NULL);
		assert (goal_dtg_node != NULL);

		std::cout << "Goal dtg: " << *goal_dtg << std::endl;
		
		// A pathfinder to do reachability tests.
		SAS_Plus::Pathfinder pathfinder(*goal_dtg);
		
		// Check for each goal node which initial fact it is linked with it.
		const SAS_Plus::DomainTransitionGraphNode* initial_dtg_node = NULL;
		
		StepPtr initial_step = initial_plan.getSteps()[Step::INITIAL_STEP];
		const Action& initial_state_action = initial_step->getAction();
		const std::vector<const Atom*>& initial_state_effects = initial_state_action.getEffects();
		for (std::vector<const Atom*>::const_iterator ci = initial_state_effects.begin(); ci != initial_state_effects.end(); ci++)
		{
			const Atom* initial_fact = *ci;

			std::cout << "Check ";
			initial_fact->print(std::cout, initial_plan.getBindings(), Step::INITIAL_STEP);
			std::cout << " v.s. ";
			landmark->getAtom().print(std::cout , initial_plan.getBindings(), Step::GOAL_STEP);
			std::cout << std::endl;

			// Check if the given initial value can be unified with any of the nodes in the DTG which contains
			// the goal.
			std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
			goal_dtg->getNodes(dtg_nodes, Step::INITIAL_STEP, *initial_fact, initial_plan.getBindings());
			if (dtg_nodes.size() > 0)
			{
				assert (dtg_nodes.size() == 1);
				const SAS_Plus::DomainTransitionGraphNode* node = dtg_nodes[0];
				// Check if the invariable variable is the same as the goal's. This check is necessary because
				// we make use of lifted DTGs. So the DTG can be the same for multiple objects of the same type
				// and we need to make sure we do not confuse these with the specific type defined by the goal.
				int goal_predicate_index = goal_dtg->getPredicateInvariableIndex(landmark->getAtom().getPredicate());
				int initial_predicate_index = goal_dtg->getPredicateInvariableIndex(initial_fact->getPredicate());

				std::cout << "Check ";
				initial_fact->print(std::cout, initial_plan.getBindings(), Step::INITIAL_STEP);
				std::cout << " [" << initial_predicate_index << "]";
				std::cout << " v.s. ";
				landmark->getAtom().print(std::cout , initial_plan.getBindings(), Step::GOAL_STEP);
				std::cout << " [" << goal_predicate_index << "]";
				std::cout << std::endl;
				
				assert (goal_predicate_index != -1);
				assert (initial_predicate_index != -1);
				
				assert (initial_fact->getTerms()[initial_predicate_index]->isObject());
				assert (landmark->getAtom().getTerms()[goal_predicate_index]->isObject());
				
				// Now check if the objects at the given indexes are equal, if not than the initial fact is not
				// related to the goal atom.
				if (initial_fact->getTerms()[initial_predicate_index] !=
				    landmark->getAtom().getTerms()[goal_predicate_index])
				{
					continue;
				}
				
				// Make sure there is only a single DTG holding this fact.
				if (initial_dtg_node != NULL && initial_dtg_node != node)
				{
					std::cout << "[Error] Both " << *initial_dtg_node << " and " << *node << " can be the initial value of ";
					landmark->getAtom().print(std::cout, initial_plan.getBindings(), Step::GOAL_STEP);
					std::cout << std::endl;
					assert (false);
				}
				initial_dtg_node = node;
			}
		}
		
		assert (initial_dtg_node != NULL);
		
		// We now have both the DTG node for the goal fact and the node corresponding to the initial state.
		std::cout << "Find a path from " << *initial_dtg_node << " to " << *goal_dtg_node << "!" << std::endl;
		
		assert (pathfinder.isReachable(*initial_dtg_node, *goal_dtg_node));

		// Next we remove a node from the DTG and check if a path from the goal to the initial state is till
		// present. If this is not the case, we have located a landmark!
		for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator dtg_node_ci = goal_dtg->getNodes().begin(); dtg_node_ci != goal_dtg->getNodes().end(); dtg_node_ci++)
		{
			const SAS_Plus::DomainTransitionGraphNode* node = *dtg_node_ci;
			// Make sure we do not remove the goal and initial dtg node.
			if (node == initial_dtg_node || node == goal_dtg_node)
			{
				continue;
			}

			// Remove the node from the DTG.
			pathfinder.ignoreNode(*node);

			// Check if the path is reachable with this node removed.
			if (!pathfinder.isReachable(*initial_dtg_node, *goal_dtg_node))
			{
				std::cout << *node << " is a landmark!!!" << std::endl;
				new Landmark(node->getId(), node->getAtom(), goal_dtg->getBindings(), *landmark_graph_);
				//landmark_graph_->addLandmark(node->getAtom(), goal_dtg->getBindings(), node->getId());
			}

			// Reset the pathfinder.
			pathfinder.clearIgnoreList();
		}
	}
}*/

/*************************
 * The Landmark class
 *************************/
Landmark::Landmark(StepID step_id, const Atom& atom, const Bindings& bindings, LandmarkGraph& landmark_graph)
	: step_id_(step_id), atom_(&atom), landmark_graph_(&landmark_graph)
{
	landmark_graph.addLandmark(*this, bindings);
}


Landmark::~Landmark()
{
}

std::ostream& operator<<(std::ostream& os, const Landmark& landmark)
{
	os << "(" << landmark.getStepId() << ") ";
	landmark.getAtom().print(os, landmark.getLandmarkGraph().getBindings(), landmark.getStepId());
	return os;
}


/*************************
 * The PreconditionLandmark class
 *************************/
PreconditionLandmark::PreconditionLandmark(StepID step_id, const Atom& atom, const Bindings& bindings, LandmarkGraph& landmark_graph)
	: Landmark(step_id, atom, bindings, landmark_graph), shared_landmarks_(NULL), achieving_actions_(NULL)
{

}

void PreconditionLandmark::setSharedLandmarks(const std::vector<const PreconditionLandmark*>& shared_landmarks)
{
	assert (shared_landmarks_ == NULL);
	shared_landmarks_ = &shared_landmarks;
}

void PreconditionLandmark::setAchievingActions(const std::vector<StepPtr>& achieving_actions)
{
	assert (achieving_actions_ == NULL);
	achieving_actions_ = &achieving_actions;
}


/*************************
 * The LandmarkGraph class
 *************************/
LandmarkGraph::LandmarkGraph(const TermManager& term_manager)
	: bindings_(new Bindings(term_manager, propagator_))
{

}

void LandmarkGraph::addLandmark(Landmark& landmark, const Bindings& atom_bindings)
{
	assert (bindings_ == &getBindings());
	// If the landmark is bound to another binding, copy this binding information.
	if (&atom_bindings != bindings_)
	{
		// Create a new step id for this landmark.
		const Atom& atom = landmark.getAtom();
		StepID new_step_id = bindings_->createVariableDomains(atom);

		// Create the variable domain for this landmark.
		std::vector<VariableDomain*> new_variable_domains;
		bindings_->getVariableDomains(new_variable_domains, new_step_id, atom);
		
		// Now make the variable domains equal to the ones the landmark is currently bounded to.
		std::vector<const VariableDomain*> org_variable_domains;
		atom_bindings.getVariableDomains(org_variable_domains, landmark.getStepId(), atom);
		
		for (unsigned int i = 0; i < org_variable_domains.size(); i++)
		{
			const VariableDomain* org_variable_domain = org_variable_domains[i];
			VariableDomain* new_variable_domain = new_variable_domains[i];
			
			new_variable_domain->makeEqualTo(org_variable_domain->getDomain());
		}

		landmark.setStepId(new_step_id);
	}

	landmarks_.push_back(&landmark);
//	std::cout << "Added landmark: ";
//	landmark.getAtom().print(std::cout, *bindings_, landmark.getStepId());
//	std::cout << "[" << landmark.getStepId() << "]" << std::endl;
}

void LandmarkGraph::addOrdering(const Landmark& from_landmark, const Landmark& to_landmark)
{
	Ordering new_ordering(from_landmark.getStepId(), StepTime::dummy_step_time, to_landmark.getStepId(), StepTime::dummy_step_time);
	assert (orderings_.addOrdering(new_ordering));
}

/*void LandmarkGraph::isUnifiableWith(std::vector<const Landmark*>& unifiable_landmarks, std::vector<const Landmark*>& initial_landmarks, const Landmark& landmark) const
{
	for (std::vector<const Landmark*>::const_iterator ci = initial_landmarks.begin(); ci != initial_landmarks.end(); ci++)
	{
		if (bindings_->canUnify(landmark.getAtom(), landmark.getStepId(), (*ci)->getAtom(), (*ci)->getStepId()))
		{
			unifiable_landmarks.push_back(*ci);
		}
	}

	return false;
}*/

bool LandmarkGraph::isUnifiable(StepPtr initial_step, const Bindings& bindings, const PreconditionLandmark& landmark) const
{	
	// If the landmark is bindable to the initial state than we are done and no further landmarks can be derived using this technique.
	std::vector<const Atom*> initial_state_effects;
	const Action& initial_state_action = initial_step->getAction();
	initial_state_action.getAchievingEffects(landmark.getAtom(), initial_state_effects);

	for (std::vector<const Atom*>::const_iterator ci = initial_state_effects.begin(); ci != initial_state_effects.end(); ci++)
	{
		const Atom* the_effect = *ci;
		//bool can_unify = true;
		
		if (bindings_->canUnify(landmark.getAtom(), landmark.getStepId(), *the_effect, initial_step->getStepId(), &bindings))
		{
			return true;
		}
		/*for(std::vector<StepPtr>::const_iterator steps_ci = landmark.getAchievingActions().begin(); steps_ci != landmark.getAchievingActions().end(); steps_ci++)
		{
			if (!bindings_->canUnify(landmark.getAtom(), (*steps_ci)->getStepId(), *the_effect, initial_step->getStepId(), &bindings))
			{
				can_unify = false;
				break;
			}
		}
		
		if (can_unify)
		{
			return true;
		}*/
	}

	return false;
}

std::ostream& operator<<(std::ostream& os, const LandmarkGraph& landmark_graph)
{
	// Print all the landmarks.
	for (std::vector<const Landmark*>::const_iterator ci = landmark_graph.getLandmarks().begin(); ci != landmark_graph.getLandmarks().end(); ci++)
	{
		const Landmark* landmark = *ci;
		os << "[" << landmark->getStepId() << "] ";
		landmark->getAtom().print(os, landmark_graph.getBindings(), landmark->getStepId());
		os << std::endl;
	}
	landmark_graph.getOrderings().print(os);
	os << std::endl;
	return os;
}

};

void Graphviz::printToDot(const LANDMARKS::LandmarkGraph& landmark_graph)
{
	std::ofstream ofs;
	ofs.open("landmarks.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;
	
	// Declare the nodes.
	for (std::vector<const LANDMARKS::Landmark*>::const_iterator ci = landmark_graph.getLandmarks().begin(); ci != landmark_graph.getLandmarks().end(); ci++)
	{
		const LANDMARKS::Landmark* landmark = *ci;
		if (landmark->getAtom().getPredicate().isStatic())
		{
			continue;
		}
		ofs << "\"[" << landmark->getStepId() << "] ";
		landmark->getAtom().print(ofs, landmark_graph.getBindings(), landmark->getStepId());
		ofs << "\"" << std::endl;
	}
	
	// Create the edges.
	for (std::vector<const LANDMARKS::Landmark*>::const_iterator from_ci = landmark_graph.getLandmarks().begin(); from_ci != landmark_graph.getLandmarks().end(); from_ci++)
	{
		const LANDMARKS::Landmark* from_node = *from_ci;
		if (from_node->getAtom().getPredicate().isStatic())
		{
			continue;
		}
		for (std::vector<const LANDMARKS::Landmark*>::const_iterator to_ci = landmark_graph.getLandmarks().begin(); to_ci != landmark_graph.getLandmarks().end(); to_ci++)
		{
			const LANDMARKS::Landmark* to_node = *to_ci;
			if (to_node->getAtom().getPredicate().isStatic())
			{
				continue;
			}
			
			if (to_node->getStepId() == from_node->getStepId())
			{
				continue;
			}
			
			if (!landmark_graph.getOrderings().canBeOrderedAfter(from_node->getStepId(), StepTime::dummy_step_time, to_node->getStepId(), StepTime::dummy_step_time) &&
			    !landmark_graph.getOrderings().canBeOrderedBefore(to_node->getStepId(), StepTime::dummy_step_time, from_node->getStepId(), StepTime::dummy_step_time))
			{
				// If the from node cannot be ordered before the to node but it can be ordered after, we will add a edge between the two.
				ofs << "\"[" << from_node->getStepId() << "] ";
				from_node->getAtom().print(ofs, landmark_graph.getBindings(), from_node->getStepId());
				ofs << "\"";
				
				ofs << " -> ";
				
				ofs << "\"[" << to_node->getStepId() << "] ";
				to_node->getAtom().print(ofs, landmark_graph.getBindings(), to_node->getStepId());
				ofs << "\"" << std::endl;
			}
		}
	}
	
	ofs << "}" << std::endl;
	ofs.close();
}


};
