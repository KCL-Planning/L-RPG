#include <cstdio>
#include <iostream>
#include <sstream>
#include <fstream>
#include <assert.h>
#include <sys/time.h>

#include "VALfiles/ptree.h"
#include "VALfiles/TIM.h"
#include "VALfiles/ToFunction.h"
#include "VALfiles/SASActions.h"
#include "VALfiles/ValidatorAPI.h"
#include "FlexLexer.h"

#include "type_manager.h"
#include "term_manager.h"
#include "action_manager.h"
#include "predicate_manager.h"
#include "formula.h"
#include "plan.h"
#include "parser_utils.h"
#include "planner.h"
#include "simple_flaw_selector.h"
#include "bindings_propagator.h"
#include "landmarks.h"
#include "relaxed_planning_graph.h"
#include "sas/causal_graph.h"
#include "heuristics/dtg_reachability.h"
#include "heuristics/equivalent_object_group.h"
#include "fc_planner.h"
#include "heuristics/fact_set.h"
#include "sas/lifted_dtg.h"
#include "heuristics/cg_heuristic.h"

///#define MYPOP_COMMENTS
#define MYPOP_KEEP_TIME

extern int yyparse();
extern int yydebug;

using std::ifstream;
using std::ofstream;

namespace VAL {

	extern parse_category* top_thing;//=NULL;

	//analysis an_analysis;
	extern analysis* current_analysis;

	extern yyFlexLexer* yfl;
};

//char * current_filename;

//using namespace VAL;
using namespace MyPOP;

int main(int argc,char * argv[])
{
	// The first line is the debug level.
	if (argc < 3)
	{
		std::cout << "Usage: mypop <domain file> <problem file>." << std::endl;
		exit(1);
	}

	struct itimerval timer = { { 1000000, 900000 }, { 1000000, 900000 } };
	setitimer ( ITIMER_PROF, &timer, NULL );

	bool use_ff = true;
	for (int i = 1; i < argc - 2; i++)
	{
		std::string command_line = std::string(argv[i]);
		if (command_line == "-cg")
		{
			use_ff = false;
		}
		else if (command_line == "-ff")
		{
			use_ff = true;
		}
		else
		{
			std::cerr << "Unknown option " << command_line << std::endl;
			exit(1);
		}
	}
/*	bool ground = false;
	// Read in commandline options.
	for (int i = 1; i < argc - 2; i++)
	{
		std::string command_line = std::string(argv[i]);
		if (command_line == "-g")
		{
			//ground = true;
			std::cerr << "Use the grounded version!" << std::endl;
		}
		else
		{
			std::cerr << "Unknown option " << command_line << std::endl;
			exit(1);
		}
	}*/
	
	std::string problem_name(argv[argc - 1]);
	std::string domain_name(argv[argc - 2]);

	TIM::performTIMAnalysis(&argv[argc - 2]);
	for_each(TA->pbegin(),TA->pend(), ptrwriter<PropertySpace>(cout,"\n"));
	for_each(TA->abegin(),TA->aend(), ptrwriter<PropertySpace>(cout,"\n"));
	
	std::size_t index = domain_name.find_last_of('/');
	std::size_t end_index = domain_name.find_last_of('.');
	std::string real_domain_name = domain_name.substr(index + 1, end_index - index - 1);
	
	std::cerr << real_domain_name << " " << argv[argc - 2] << std::endl;
	
	
	index = problem_name.find_last_of('/');
	end_index = problem_name.find_last_of('.');
	std::string real_problem_name = problem_name.substr(index + 1, end_index - index - 1);
	
	std::cerr << real_problem_name << " " << argv[argc - 1] << std::endl;

	VAL::problem* the_problem = VAL::current_analysis->the_problem;
	VAL::domain* the_domain = VAL::current_analysis->the_domain;

	assert(the_problem != NULL);
	assert(the_domain != NULL);

	// Process the types.
	TypeManager type_manager;
	type_manager.processTypes(*the_domain->types);

	// Process the objects.
	TermManager term_manager(type_manager);
	type_manager.processObjects(term_manager, *the_problem->objects);
///	term_manager.processActionVariables(*the_domain->ops);

	// Process the constants (if any).
	if (the_domain->constants != NULL)
	{
		type_manager.processObjects(term_manager, *the_domain->constants);
	}

	std::cout << term_manager << std::endl;

	// Process the predicates.
	PredicateManager predicate_manager(type_manager);
	predicate_manager.processPredicates(*the_domain->predicates);

	// Process the action schemas.
	ActionManager action_manager(type_manager, term_manager, predicate_manager);
	action_manager.processActions(*the_domain->ops);

	predicate_manager.checkStaticPredicates(action_manager);

	// Propagator.
//	SimpleBindingsPropagator* propagator = new SimpleBindingsPropagator();
	
	// Instantiate the initial plan and do the planning!
//	Plan* plan = new Plan(action_manager, term_manager, type_manager, *propagator);
	const Formula* goal = Utility::convertGoal(term_manager, predicate_manager, the_problem->the_goal, false);
	
	std::vector<const Atom*> initial_facts;
	Utility::convertEffects(term_manager, predicate_manager, *the_problem->initial_state, initial_facts);
	
//	std::vector<const Variable*>* initial_action_variables = new std::vector<const Variable*>();

	// Create the initial step, which is a custom action with the atoms of the initial state as its effects.
//	MyPOP::Action* initial_action = new MyPOP::Action("Initial action", Formula::TRUE, initial_action_variables, initial_facts);

#ifdef MYPOP_COMMENTS
	std::cout << "Print initial action" << std::endl;
	std::cout << *initial_action << std::endl;
#endif

	// Create the goal, which is a custom action with the goal atoms as preconditions.
#ifdef MYPOP_COMMENTS
	std::cout << "Create goal action" << std::endl;
#endif
//	std::vector<const Variable*>* goal_action_variables = new std::vector<const Variable*>();
//	std::vector<const Atom*>* goal_action_effects = new std::vector<const Atom*>();
//	MyPOP::Action* goal_action = new MyPOP::Action("Goal action", *goal, goal_action_variables, goal_action_effects);


#ifdef MYPOP_COMMENTS
	std::cout << "Print goal action" << std::endl;
	std::cout << *goal_action << std::endl;
#endif

//	plan->makeInitialPlan(*initial_action, *goal_action);

#ifdef MYPOP_COMMENTS
	std::cout << "Initial plan" << *plan << std::endl;
#endif

	std::vector<const Atom*> goal_facts;
	Utility::convertFormula(goal_facts, goal);

	HEURISTICS::HeuristicInterface* heuristic_interface = NULL;
	
	if (!use_ff)
	{
		std::vector<SAS_Plus::LiftedDTG*>* lifted_dtgs = new std::vector<SAS_Plus::LiftedDTG*>();
		SAS_Plus::LiftedDTG::createLiftedDTGs(*lifted_dtgs, *the_domain->types, predicate_manager, type_manager, action_manager, term_manager, initial_facts);
		Graphviz::printToDot(*lifted_dtgs);
		
		std::vector<const GroundedAtom*> grounded_goal_facts;
		for (std::vector<const Atom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ++ci)
		{
			const Atom* goal = *ci;
			const Object** variables = new const Object*[goal->getArity()];
			for (unsigned int term_index = 0; term_index < goal->getArity(); ++term_index)
			{
				variables[term_index] = static_cast<const Object*>(goal->getTerms()[term_index]);
			}
			grounded_goal_facts.push_back(&GroundedAtom::getGroundedAtom(goal->getPredicate(), variables));
		}
		
		std::vector<const GroundedAtom*> grounded_initial_facts;
		for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
		{
			const Atom* init = *ci;
			const Object** variables = new const Object*[init->getArity()];
			for (unsigned int term_index = 0; term_index < init->getArity(); ++term_index)
			{
				variables[term_index] = static_cast<const Object*>(init->getTerms()[term_index]);
			}
			grounded_initial_facts.push_back(&GroundedAtom::getGroundedAtom(init->getPredicate(), variables));
		}
		
		heuristic_interface = new HEURISTICS::LiftedCausalGraphHeuristic(*lifted_dtgs, action_manager, predicate_manager, grounded_goal_facts);
	}
	else
	{
		// Split up the actions into lifted actions.
		std::vector<const Object*> objects_part_of_property_state;
		for (std::vector<TIM::PropertySpace*>::const_iterator property_space_i = TIM::TA->pbegin(); property_space_i != TIM::TA->pend(); ++property_space_i)
		{
			TIM::PropertySpace* property_space = *property_space_i;
			for (TIM::PropertySpace::OIterator object_i = property_space->obegin(); object_i != property_space->oend(); ++object_i)
			{
				TIM::TIMobjectSymbol* tim_object = *object_i;
				
				const Object& object = term_manager.getObject(tim_object->getName());
				if (std::find(objects_part_of_property_state.begin(), objects_part_of_property_state.end(), &object) == objects_part_of_property_state.end())
				{
					objects_part_of_property_state.push_back(&object);
				}
			}
		}

		std::vector<HEURISTICS::LiftedTransition*> lifted_transitions;
		for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ++ci)
		{
			const Action* action = *ci;
			HEURISTICS::LiftedTransition::createLiftedTransitions(lifted_transitions, predicate_manager, term_manager, type_manager, *action, initial_facts, objects_part_of_property_state);
		}
		std::cerr << "Lifted transitions: " << lifted_transitions.size() << std::endl;
		HEURISTICS::LiftedTransition::mergeFactSets(lifted_transitions);

//	std::cout << "All lifted transitions:" << std::endl;
//	for (std::vector<HEURISTICS::LiftedTransition*>::const_iterator ci = lifted_transitions.begin(); ci != lifted_transitions.end(); ++ci)
//	{
//		std::cout << **ci << std::endl;
//	}
	
	// Do the domain analysis.
//#ifdef MYPOP_COMMENTS
//	std::cout << " === Creating the DTGs === " << std::endl;
//#endif
//	SAS_Plus::DomainTransitionGraphManager* dtg_manager = new SAS_Plus::DomainTransitionGraphManager(predicate_manager, type_manager, action_manager, term_manager, *initial_facts);

	// New style, working directly on the TIM structure.
/*	const SAS_Plus::DomainTransitionGraph& combined_graph = dtg_manager->generateDomainTransitionGraphsTIM(*the_domain->types, plan->getBindings());
	
	// Clean up memory by removing all the variable domains which are no longer in use!
	std::set<std::pair<StepID, const Term*> > relevant_variable_domains;
	for (std::vector<const Variable*>::const_iterator ci = initial_action_variables->begin(); ci != initial_action_variables->end(); ++ci)
	{
		relevant_variable_domains.insert(std::make_pair(Step::INITIAL_STEP, *ci));
	}
	for (std::vector<const Variable*>::const_iterator ci = goal_action_variables->begin(); ci != goal_action_variables->end(); ++ci)
	{
		relevant_variable_domains.insert(std::make_pair(Step::GOAL_STEP, *ci));
	}

	unsigned int nr_transitions = 0;
	for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = combined_graph.getNodes().begin(); ci != combined_graph.getNodes().end(); ++ci)
	{
		const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
		nr_transitions += dtg_node->getTransitions().size();
		
		for (std::vector<SAS_Plus::BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ++ci)
		{
			SAS_Plus::BoundedAtom* fact = *ci;
			for (std::vector<const Term*>::const_iterator ci = fact->getAtom().getTerms().begin(); ci != fact->getAtom().getTerms().end(); ++ci)
			{
				const Term* term = *ci;
				relevant_variable_domains.insert(std::make_pair(fact->getId(), term));
			}
		}
		
		for (std::vector<const SAS_Plus::Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ++ci)
		{
			const SAS_Plus::Transition* transition = *ci;
			
			for (std::vector<const Variable*>::const_iterator ci = transition->getAction().getVariables().begin(); ci != transition->getAction().getVariables().end(); ++ci)
			{
				relevant_variable_domains.insert(std::make_pair(transition->getStepId(), *ci));
			}
		}
	}
	
	plan->getBindings().removeAllBut(relevant_variable_domains);
*/
/*
	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = dtg_manager->getManagableObjects().begin(); ci != dtg_manager->getManagableObjects().end(); ++ci)
	{
		const SAS_Plus::DomainTransitionGraph* dtg = *ci;
		for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
			nr_transitions += dtg_node->getTransitions().size();
		}
	}
*/

//	std::cerr << "Total number of transitions: " << nr_transitions << "; Total of DTGs: " << dtg_manager->getManagableObjects().size() << "." << std::endl;


	// Do the reachability analysis.
#ifdef MYPOP_KEEP_TIME
		struct timeval start_time_prepare_reachability;
		gettimeofday(&start_time_prepare_reachability, NULL);
#endif

		heuristic_interface = new REACHABILITY::DTGReachability(lifted_transitions, term_manager, predicate_manager);
#ifdef MYPOP_KEEP_TIME
		struct timeval end_time_prepare_reachability;
		gettimeofday(&end_time_prepare_reachability, NULL);	
		
		double time_spend_preparing = end_time_prepare_reachability.tv_sec - start_time_prepare_reachability.tv_sec + (end_time_prepare_reachability.tv_usec - start_time_prepare_reachability.tv_usec) / 1000000.0;
		std::cerr << "Prepare reachability analysis: " << time_spend_preparing << " seconds" << std::endl;
#endif
	}
//	std::vector<const Atom*> goal_facts;
//	Utility::convertFormula(goal_facts, goal);
	
/*
	std::vector<const SAS_Plus::BoundedAtom*> bounded_goal_facts;
	for (std::vector<const Atom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ci++)
	{
		bounded_goal_facts.push_back(new SAS_Plus::BoundedAtom(Step::GOAL_STEP, **ci));
	}
	
	std::vector<const SAS_Plus::BoundedAtom*> bounded_initial_facts;
	for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		bounded_initial_facts.push_back(new SAS_Plus::BoundedAtom(Step::INITIAL_STEP, **ci));
	}
*/

	
	std::vector<const GroundedAction*> found_plan;
	//ForwardChainingPlanner fcp(action_manager, predicate_manager, type_manager, analyst);
	ForwardChainingPlanner fcp(action_manager, predicate_manager, type_manager, *heuristic_interface);
	std::pair<int, int> result;
	result = fcp.findPlan(found_plan, initial_facts, goal_facts, term_manager, true, false, true);
	
	// If the greedy method failed, try the non greedy method!
	if (result.first == -1)
	{
		found_plan.clear();
		GroundedAtom::removeInstantiatedGroundedAtom();
		GroundedAction::removeInstantiatedGroundedActions();
		//result = fcp.findPlan(found_plan, analyst, initial_facts, goal_facts, false, true, true);
		result = fcp.findPlan(found_plan, initial_facts, goal_facts, term_manager, false, false, false);
	}
	
	// Validate the plan!
	std::stringstream plan_stream;
	for (std::vector<const GroundedAction*>::const_iterator ci = found_plan.begin(); ci != found_plan.end(); ci++)
	{
		plan_stream << **ci << std::endl;
	}
	if (VAL::checkPlan(domain_name, problem_name, plan_stream))
	{
		std::cerr << "Valid plan!" << std::endl;
//		std::cerr << "Plan Length: " << found_plan.size() << std::endl;
		std::cerr << "States visited: " << result.first << std::endl;
		std::cerr << "Plan length: " << result.second << std::endl;
	}
	else
	{
		std::cerr << "Invalid plan!" << std::endl;
//		std::cerr << "Length: " << found_plan.size() << std::endl;
		for (std::vector<const GroundedAction*>::const_iterator ci = found_plan.begin(); ci != found_plan.end(); ci++)
		{
			std::cerr << **ci << std::endl;
		}
		std::cerr << "States visited: -1" << std::endl;
		std::cerr << "Plan length: -1" << std::endl;
	}

//	for (std::vector<HEURISTICS::LiftedTransition*>::const_iterator ci = lifted_transitions.begin(); ci != lifted_transitions.end(); ++ci)
//	{
//		delete *ci;
//	}

//	GroundedAction::removeInstantiatedGroundedActions();
//	GroundedAtom::removeInstantiatedGroundedAtom();
//	Graphviz::printToDot(dtg_manager);
//	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = dtg_manager.getManagableObjects().begin(); ci != dtg_manager.getManagableObjects().end(); ci++)
//	{
//		std::cout << " == Start DTG == " << std::endl;
//		std::cout << **ci << std::endl;
//		std::cout << " == End DTG == " << std::endl;
//	}
//	std::cout << " === DONE! Creating the DTGs === " << std::endl;
	
//	std::cout << " === Creating the CGs === " << std::endl;
//	SAS_Plus::CausalGraph cg(dtg_manager, action_manager);
//	std::cout << "Causal graph:" << std::endl;
//	std::cout << cg << std::endl;
//	Graphviz::printToDot(cg);
//	std::cout << " === DONE! Creating the CGs === " << std::endl;

//	getitimer(ITIMER_PROF, &timer);

	// Planning time.
//	double t = 1000000.9 - (timer.it_value.tv_sec + timer.it_value.tv_usec * 1e-6);
//	std::cerr << "Time: " << std::max(0, int(1000.0 * t + 0.5)) << std::endl;

	
	//	std::cout << " === Creating the Landmarks === " << std::endl;
	//LANDMARKS::LandmarkManager landmark_manager(action_manager, type_manager, term_manager);
	//landmark_manager.findLandmarksFromGoal(*the_domain->ops, *the_domain->types, *plan, dtg_manager, cg);
	//Graphviz::printToDot(landmark_manager.getLandmarkGraph());
	//std::cout << " === DONE! Creating the Landmarks === " << std::endl;


	// Start the planning process! 
//	SimpleFlawSelectionStrategy* sfss = new SimpleFlawSelectionStrategy();
//	Planner planner(*plan, action_manager, term_manager, type_manager, *sfss);
//	const Plan* solution_plan = planner.getSolution();

//	if (solution_plan == NULL)
//		std::cout << "No solution found :(" << std::endl;
//	else
//		std::cout << "Solution! " << *solution_plan << std::endl;

//	getitimer(ITIMER_PROF, &timer);

	// Planning time.
//	double t = 1000000.9 - (timer.it_value.tv_sec + timer.it_value.tv_usec * 1e-6);
//	std::cout << "Time: " << std::max(0, int(1000.0 * t + 0.5)) << std::endl;
//	std::cout << "Number of steps: " << solution_plan->getSteps().size() - 2 << std::endl;
//	std::cout << "Plans generated: " << Plan::getPlansGenerated() << std::endl;
//	std::cout << "Plans visited: " << planner.getPlansVisited() << std::endl;
//	std::cout << "Dead ends encountered: " << planner.getDeadEnds() << std::endl;
	// Don't leave any mess!
//	delete &combined_graph;
//	delete dtg_manager;
//	delete plan;
//	delete propagator;
//	delete initial_action;
//	delete goal_action;
	std::vector<REACHABILITY::ReachableFact*> no_facts;
	REACHABILITY::ReachableFact::deleteAllReachableFacts(no_facts);
	
	GroundedAtom::removeInstantiatedGroundedAtom();
	GroundedAction::removeInstantiatedGroundedActions();
	
	delete heuristic_interface;
//	delete solution_plan;
//	delete VAL::current_analysis;
//	delete MyPOP::REACHABILITY::g_reachable_fact_memory_pool;
//	MyPOP::REACHABILITY::EquivalentObjectGroup::deleteMemoryPool();
}
