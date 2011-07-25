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
#include "SAS/dtg_manager.h"
#include "SAS/causal_graph.h"
//#include "SAS/relaxed_reachability_analyst.h"
#include "relaxed_planning_graph.h"
//#include "action_graph.h"

///#define MYPOP_COMMENTS

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
	if (argc != 3)
	{
		std::cout << "Usage: mypop <domain file> <problem file>." << std::endl;
		exit(1);
	}

	struct itimerval timer = { { 1000000, 900000 }, { 1000000, 900000 } };
	setitimer ( ITIMER_PROF, &timer, NULL );

	TIM::performTIMAnalysis(&argv[1]);
	for_each(TA->pbegin(),TA->pend(), ptrwriter<PropertySpace>(cout,"\n"));
	for_each(TA->abegin(),TA->aend(), ptrwriter<PropertySpace>(cout,"\n"));

	/*//current_analysis = &an_analysis;
	ifstream* current_in_stream;

	// Parse the file.
	yydebug=0; // Set to 1 to output yacc trace 

	yfl= new yyFlexLexer;

	// Loop over given args
	for (int a = 1; a < argc; ++a)
	{
		current_filename= argv[a];
		cout << "File: " << current_filename << '\n';
		current_in_stream= new ifstream(current_filename);
		if (current_in_stream->bad())
		{
			// Output a message now.
			cout << "Failed to open\n";

			// Log an error to be reported in summary later
			line_no= 0;
			log_error(E_FATAL,"Failed to open file");
		}
		else
		{
			line_no= 1;

			// Switch the tokeniser to the current input stream
			yfl->switch_streams(current_in_stream,&cout);
			yyparse();
		}
		delete current_in_stream;
	}*/

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

//	ActionGraph action_graph(action_manager);
//	Graphviz::printToDot(action_graph);
	
	// Test grounding actions.
	/*std::cout << "All grounded actions:" << std::endl;
	for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ci++)
	{
		const Action* action = *ci;
		std::vector<const Step*> grounded_actions;
		SimpleBindingsPropagator propagator;
		Bindings binding(term_manager, propagator);
		action_manager.ground(binding, grounded_actions, *action);
		
		// Print all the grounded actions:
		for (std::vector<const Step*>::const_iterator ga_ci = grounded_actions.begin(); ga_ci != grounded_actions.end(); ga_ci++)
		{
			(*ga_ci)->getAction().print(std::cout, binding, (*ga_ci)->getStepId());
			std::cout << std::endl;
		}
	}*/

	// Propagator.
	SimpleBindingsPropagator* propagator = new SimpleBindingsPropagator();
	
	// Instantiate the initial plan and do the planning!
	Plan* plan = new Plan(action_manager, term_manager, type_manager, *propagator);
	const Formula* goal = Utility::convertGoal(term_manager, predicate_manager, the_problem->the_goal, false);
	
	std::vector<const Atom*>* initial_effects = new std::vector<const Atom*>();	
	Utility::convertEffects(term_manager, predicate_manager, *the_problem->initial_state, *initial_effects);

	std::vector<const Variable*>* initial_action_variables = new std::vector<const Variable*>();

	// Create the initial step, which is a custom action with the atoms of the initial state as its effects.
	Action* initial_action = new Action("Initial action", Formula::TRUE, initial_action_variables, initial_effects);

#ifdef MYPOP_COMMENTS
	std::cout << "Print initial action" << std::endl;
	std::cout << *initial_action << std::endl;
#endif

	// Create the goal, which is a custom action with the goal atoms as preconditions.
#ifdef MYPOP_COMMENTS
	std::cout << "Create goal action" << std::endl;
#endif
	std::vector<const Variable*>* goal_action_variables = new std::vector<const Variable*>();
	std::vector<const Atom*>* goal_action_effects = new std::vector<const Atom*>();
	Action* goal_action = new Action("Goal action", *goal, goal_action_variables, goal_action_effects);


#ifdef MYPOP_COMMENTS
	std::cout << "Print goal action" << std::endl;
	std::cout << *goal_action << std::endl;
#endif

	plan->makeInitialPlan(*initial_action, *goal_action);

#ifdef MYPOP_COMMENTS
	std::cout << "Initial plan" << *plan << std::endl;
#endif

	assert (plan->getSteps().size() == 2);

//	RPG::RelaxedPlanningGraph rpg(action_manager, *plan);
//	std::cout << rpg << std::endl;

	// Do the domain analysis.
	std::cout << " === Creating the DTGs === " << std::endl;
	SAS_Plus::DomainTransitionGraphManager dtg_manager(predicate_manager, type_manager, action_manager, term_manager, *initial_effects);
	
	// Old style, working with the lifted SAS structures.
//	dtg_manager.generateDomainTransitionGraphs(*the_domain->types, plan->getBindings());

	// New style, working directly on the TIM structure.
	dtg_manager.generateDomainTransitionGraphsTIM(*the_domain->types, plan->getBindings());
	
	Graphviz::printToDot(dtg_manager);
	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = dtg_manager.getManagableObjects().begin(); ci != dtg_manager.getManagableObjects().end(); ci++)
	{
		std::cout << " == Start DTG == " << std::endl;
		std::cout << **ci << std::endl;
		std::cout << " == End DTG == " << std::endl;
	}
	std::cout << " === DONE! Creating the DTGs === " << std::endl;
	
//	std::cout << " === Creating the CGs === " << std::endl;
//	SAS_Plus::CausalGraph cg(dtg_manager, action_manager);
//	std::cout << "Causal graph:" << std::endl;
//	std::cout << cg << std::endl;
//	Graphviz::printToDot(cg);
//	std::cout << " === DONE! Creating the CGs === " << std::endl;

	getitimer(ITIMER_PROF, &timer);

	// Based on the DTG structures, do domain analysis!
	struct timeval start_time_reachability;
	gettimeofday(&start_time_reachability, NULL);

//	SAS_Plus::RelaxedReachabilityAnalyst analyst(dtg_manager);
//	analyst.performReachabilityAnalysis(*initial_effects, plan->getBindings());

	struct timeval end_time_reachability;
	gettimeofday(&end_time_reachability, NULL);

	double time_spend = end_time_reachability.tv_sec - start_time_reachability.tv_sec + (end_time_reachability.tv_usec - start_time_reachability.tv_usec) / 1000000.0;
	std::cerr << "Reachability analysis: " << time_spend << " seconds" << std::endl;
	

	
	exit (0);

	// Planning time.
	double t = 1000000.9 - (timer.it_value.tv_sec + timer.it_value.tv_usec * 1e-6);
	std::cerr << "Time: " << std::max(0, int(1000.0 * t + 0.5)) << std::endl;

	
	/*	std::cout << " === Creating the Landmarks === " << std::endl;
	LANDMARKS::LandmarkManager landmark_manager(action_manager, type_manager, term_manager);
	landmark_manager.findLandmarksFromGoal(*the_domain->ops, *the_domain->types, *plan, dtg_manager, cg);
	Graphviz::printToDot(landmark_manager.getLandmarkGraph());
	std::cout << " === DONE! Creating the Landmarks === " << std::endl;
*/

	// Start the planning process!
	SimpleFlawSelectionStrategy* sfss = new SimpleFlawSelectionStrategy();
	Planner planner(*plan, action_manager, term_manager, type_manager, *sfss);
	const Plan* solution_plan = planner.getSolution();

	if (solution_plan == NULL)
		std::cout << "No solution found :(" << std::endl;
	else
		std::cout << "Solution! " << *solution_plan << std::endl;

	getitimer(ITIMER_PROF, &timer);

	// Planning time.
//	double t = 1000000.9 - (timer.it_value.tv_sec + timer.it_value.tv_usec * 1e-6);
//	std::cout << "Time: " << std::max(0, int(1000.0 * t + 0.5)) << std::endl;
//	std::cout << "Number of steps: " << solution_plan->getSteps().size() - 2 << std::endl;
//	std::cout << "Plans generated: " << Plan::getPlansGenerated() << std::endl;
//	std::cout << "Plans visited: " << planner.getPlansVisited() << std::endl;
//	std::cout << "Dead ends encountered: " << planner.getDeadEnds() << std::endl;

	// Don't leave any mess!
	delete propagator;
	delete sfss;
	delete initial_action;
	delete goal_action;
	delete solution_plan;
	delete VAL::current_analysis;
}
