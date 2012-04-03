#include <cstdio>
#include <iostream>
#include <sstream>
#include <fstream>
#include <assert.h>
#include <sys/time.h>

extern "C" {
#include "FF-X/ff.h"

#include "FF-X/memory.h"
#include "FF-X/output.h"

#include "FF-X/parse.h"

#include "FF-X/inst_pre.h"
#include "FF-X/inst_easy.h"
#include "FF-X/inst_hard.h"
#include "FF-X/inst_final.h"

#include "FF-X/orderings.h"

#include "FF-X/relax.h"
#include "FF-X/search.h"
};

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
#include "relaxed_planning_graph.h"
#include "sas/dtg_manager.h"
#include "sas/causal_graph.h"
#include "sas/dtg_graph.h"
#include "heuristics/dtg_reachability.h"
#include "heuristics/equivalent_object_group.h"

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

extern "C" {
void load_ops_file( char *filename );
void load_fct_file( char *filename );
};

void initialiseFF (const std::string& domain_file, const std::string& problem_file, int (*getHeuristicFunctionEHC)(State* from, State* to), int (*getHeuristicFunctionBF)(State* from, State* to))
{
  int i;
  bool found_plan;
  
  printf("Initialise FF! %s %s\n", domain_file.c_str(), problem_file.c_str());

  /* it is important for the pddl language to define the domain before 
   * reading the problem 
   */
  load_ops_file( const_cast<char*>(domain_file.c_str()) );
  
  /* problem file (facts)
   */
  load_fct_file( const_cast<char*>(problem_file.c_str()) );

  /* This is needed to get all types.
   */
  build_orig_constant_list();

  /* last step of parsing: see if it's an ADL domain!
   */
  if ( !make_adl_domain() ) {
    printf("\nff: this is not an ADL problem!");
    printf("\n    can't be handled by this version.\n\n");
    exit( 1 );
  }

  /* now instantiate operators;
   */


  /**************************
   * first do PREPROCESSING * 
   **************************/


  /* start by collecting all strings and thereby encoding 
   * the domain in integers.
   */
  encode_domain_in_integers();

  /* inertia preprocessing, first step:
   *   - collect inertia information
   *   - split initial state into
   *        _ arrays for individual predicates
   *        - arrays for all static relations
   *        - array containing non - static relations
   */
  do_inertia_preprocessing_step_1();

  /* normalize all PL1 formulae in domain description:
   * (goal, preconds and effect conditions)
   *   - simplify formula
   *   - expand quantifiers
   *   - NOTs down
   */
  normalize_all_wffs();

  /* translate negative preconds: introduce symmetric new predicate
   * NOT-p(..) (e.g., not-in(?ob) in briefcaseworld)
   */
  translate_negative_preconds();

  /* split domain in easy (disjunction of conjunctive preconds)
   * and hard (non DNF preconds) part, to apply 
   * different instantiation algorithms
   */
  split_domain();


  /***********************************************
   * PREPROCESSING FINISHED                      *
   *                                             *
   * NOW MULTIPLY PARAMETERS IN EFFECTIVE MANNER *
   ***********************************************/

  build_easy_action_templates();
  build_hard_action_templates();

  /* perform reachability analysis in terms of relaxed 
   * fixpoint
   */
  perform_reachability_analysis();

  /* collect the relevant facts and build final domain
   * and problem representations.
   */
  collect_relevant_facts();

  /* now build globally accessable connectivity graph
   */
  build_connectivity_graph();
  

  /***********************************************************
   * we are finally through with preprocessing and can worry *
   * bout finding a plan instead.                            *
   ***********************************************************/

  initialize_relax();
  do_axiom_update( &ginitial_state );
  
  /* make space in plan states info, and relax
   */
  for ( i = 0; i < MAX_PLAN_LENGTH + 1; i++ ) {
    make_state( &(gplan_states[i]), gnum_ft_conn );
    gplan_states[i].max_F = gnum_ft_conn;
  }
 
//  int ehc_states_visited = 0;
  int best_first_states_visited = 0;
//  found_plan = do_enforced_hill_climbing( &ginitial_state, &ggoal_state, getHeuristicFunctionEHC, &ehc_states_visited );
//  std::cerr << "EHC states visited: " << ehc_states_visited << std::endl;
  
// if ( !found_plan ) {
//    printf("\n\nEnforced Hill-climbing failed !");
//    printf("\nswitching to Best-first Search now.\n");
    found_plan = do_best_first_search(getHeuristicFunctionBF, &best_first_states_visited);
//  }
  
  std::cerr << std::endl << "Best-First states visited: " << best_first_states_visited << std::endl;
  if ( found_plan )
  {
		//print_plan();
		
		size_t begin_problem = problem_file.find_last_of('/') + 1;
		size_t end_problem = problem_file.find_last_of('.');
		assert (begin_problem < end_problem);
		assert (begin_problem > 0);
		assert (end_problem > 0);
		assert (end_problem < problem_file.size());
		std::string problem_name = problem_file.substr(begin_problem, problem_file.size() - begin_problem - (problem_file.size() - end_problem));
		
		size_t end_domain = domain_file.find_last_of('/');
		size_t begin_domain = domain_file.find_last_of('/', end_domain - 1) + 1;
		assert (begin_domain < end_domain);
		assert (begin_domain > 0);
		assert (end_domain > 0);
		assert (end_domain < domain_file.size());
		std::string domain_name = domain_file.substr(begin_domain, domain_file.size() - begin_domain - (domain_file.size() - end_domain));
		std::string solution_file_name("solution-" + domain_name + "-" + problem_name);
	 
		print_plan_to_file(solution_file_name.c_str());
		std::cerr << "Plan length: " << gnum_plan_ops << std::endl;
	}
	else
	{
		std::cerr << "NO PLAN FOUND!" << std::endl;
	}
  
  
  output_planner_info();
}

REACHABILITY::DTGReachability* analyst_;
Bindings* bindings_;
std::vector<const SAS_Plus::BoundedAtom*> static_facts_;
std::vector<const SAS_Plus::BoundedAtom*> bounded_goal_facts_;
PredicateManager* predicate_manager_;
TermManager* term_manager_;

const SAS_Plus::BoundedAtom& convertFactToBoundedAtom(const Fact& fact)
{
	std::string predicate_name(gpredicates[fact.predicate]);
	std::vector<const Term*>* objects = new std::vector<const Term*>();
	std::vector<const Type*> types;
	for ( int j = 0; j < garity[fact.predicate]; j++ )
	{
		const Object& object = term_manager_->getObject(std::string(gconstants[(fact.args)[j]]));
		objects->push_back(&object);
		types.push_back(object.getType());
	}
	const Predicate* predicate = predicate_manager_->getPredicate(predicate_name, types);
	if (predicate == NULL)
	{
		std::cout << "Could not find a predciate with the name: " << predicate_name << " with types: ";
		for (std::vector<const Type*>::const_iterator ci = types.begin(); ci != types.end(); ci++)
		{
			std::cout << **ci << " ";
		}
		std::cout << "." << std::endl;
		exit(0);
	}
	
	Atom* atom = new Atom(*predicate, *objects, false);
	const SAS_Plus::BoundedAtom& bounded_atom = SAS_Plus::BoundedAtom::createBoundedAtom(*atom, *bindings_);
/*
	print_Fact(const_cast<Fact*>(&fact));
	printf("%s(", gpredicates[fact.predicate]);
	for ( int j = 0; j < garity[fact.predicate]; j++ ) {
		printf("%s", gconstants[(fact.args)[j]]);
		if ( j < garity[fact.predicate] - 1 ) {
			printf(" ");
		}
	}
	printf(") -=> ");
	bounded_atom.print(std::cout, *bindings_);
	std::cout << std::endl;
*/
	return bounded_atom;
}

int calculateHeuristicForFF(State* from, State* to)
{
	// Convert both states into something we can work with!
	std::vector<const REACHABILITY::ReachableFact*> reachable_facts;
	std::vector<const SAS_Plus::BoundedAtom*> initial_facts;
	
	delete MyPOP::REACHABILITY::g_reachable_fact_memory_pool;
	MyPOP::REACHABILITY::g_reachable_fact_memory_pool = new MyPOP::UTILITY::MemoryPool(sizeof(MyPOP::REACHABILITY::ReachableFact));

//	std::cout << "******************************************************************" << std::endl;
//	std::cout << "*********************** The initial state ************************" << std::endl;
//	std::cout << "******************************************************************" << std::endl;
//	print_state(*from);
//	std::cout << std::endl;
	
//	std::cout << "From facts: " << std::endl;
//	struct timeval start_time_convert_state;
//	gettimeofday(&start_time_convert_state, NULL);
	for (int i = 0; i < from->num_F; i++)
	{
		Fact* fact = &(grelevant_facts[from->F[i]]);
		const SAS_Plus::BoundedAtom& bounded_fact = convertFactToBoundedAtom(*fact);
		initial_facts.push_back(&bounded_fact);
//		std::cout << "* ";
//		bounded_fact.print(std::cout, *bindings_);
//		std::cout << "." << std::endl;
		
//		for (unsigned int j = 0; j < bounded_fact.getAtom().getArity(); j++)
//		{
//			bounded_fact.getAtom().getTerms()[j]->getDomain(bounded_fact.getId(), *bindings_);
//		}
	}
	
	// Add all static facts, they are not listed by FF.
	unsigned int number_of_non_static_initial_facts = initial_facts.size();
	initial_facts.insert(initial_facts.end(), static_facts_.begin(), static_facts_.end());

//	struct timeval end_time_convert_state;
//	gettimeofday(&end_time_convert_state, NULL);
//	double time_spend_converting = end_time_convert_state.tv_sec - start_time_convert_state.tv_sec + (end_time_convert_state.tv_usec - start_time_convert_state.tv_usec) / 1000000.0;
//	std::cout << "Time to convert initial state: " << time_spend_converting << " seconds" << std::endl;

//	for (std::vector<const SAS_Plus::BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
//	{
//		(*ci)->print(std::cout, *bindings_);
//	}
	
//	std::cout << "Goal facts: " << std::endl;
//	for (std::vector<const SAS_Plus::BoundedAtom*>::const_iterator ci = bounded_goal_facts_.begin(); ci != bounded_goal_facts_.end(); ci++)
//	{
//		std::cout << "* ";
//		(*ci)->print(std::cout, *bindings_);
//		std::cout << "." << std::endl;
//	}
//	struct timeval start_time_analysis;
//	gettimeofday(&start_time_analysis, NULL);

	analyst_->performReachabilityAnalysis(reachable_facts, initial_facts, *bindings_);
	
//	struct timeval end_time_analysis;
//	gettimeofday(&end_time_analysis, NULL);
//	double time_spend_analysis = end_time_analysis.tv_sec - start_time_analysis.tv_sec + (end_time_analysis.tv_usec - start_time_analysis.tv_usec) / 1000000.0;
//	std::cout << "Time to do analysis: " << time_spend_analysis << " seconds" << std::endl;	
//	for (std::vector<const REACHABILITY::ReachableFact*>::const_iterator ci = reachable_facts.begin(); ci != reachable_facts.end(); ci++)
//	{
//		std::cout << "* " << **ci << std::endl;
//	}
/*
//	struct timeval start_time_heuristic;
//	gettimeofday(&start_time_heuristic, NULL);
	std::cout << "**************************************************************" << std::endl;
	std::cout << "***************** BEGIN HEURISTIC COMPARISON *****************" << std::endl;
	std::cout << "**************************************************************" << std::endl;
*/
	unsigned int heuristic_value = analyst_->getHeuristic(bounded_goal_facts_, *bindings_, *predicate_manager_);
//	struct timeval end_time_heuristic;
//	gettimeofday(&end_time_heuristic, NULL);
//	double time_spend_heuristic = end_time_heuristic.tv_sec - start_time_heuristic.tv_sec + (end_time_heuristic.tv_usec - start_time_heuristic.tv_usec) / 1000000.0;
//	std::cout << "Time to get heuristic: " << time_spend_heuristic << " seconds" << std::endl;	
//	std::cerr << "Heuristic value: " << heuristic_value << std::endl;

	// Make sure we only return 0 if it is the actual goal state!
	if (heuristic_value == 0 && get_1P(from, to) != 0)
	{
		std::cout << "We think we have reached the goal state, whereas that's not the case!" << std::endl;
		print_state(*from);
		std::cout << std::endl << "To: " << std::endl;
		print_state(*to);
		std::cout << std::endl;
		exit(1);
	}
/*
//#ifdef MYPOP_SAS_PLUS_DTG_REACHABILITY_GET_HEURISTIC_SHOW_PLAN
	std::cout << "*************************** FF *******************************" << std::endl;
	gcmd_line.display_info = 123;
	int ff_heuristic_value = get_1P(from, to);
	std::cout << std::endl << "************************ From State **************************";
	print_state(*from);
	std::cout << std::endl << "************************ End State ***************************";
	print_state(*to);
	std::cout << std::endl << "********************* Heuristic values ***********************" << std::endl;
	std::cout << "Lifted: " << heuristic_value << std::endl;
	std::cout << "FF: " << ff_heuristic_value << std::endl;
//	std::cout << "**************************************************************" << std::endl;
//	std::cout << "****************** END HEURISTIC COMPARISON ******************" << std::endl;
//	std::cout << "**************************************************************" << std::endl;
//#endif
*/
	for (unsigned int i = 0; i < number_of_non_static_initial_facts; i++)
	{
		delete initial_facts[i];
	}
	
//	std::cout << "Heuristic for FF: " << heuristic_value<< std::endl;
	return heuristic_value;
	//return get_1P_and_H(const_cast<State*>(from), const_cast<State*>(to));
}

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

	bool validate = false;
	bool calculate_heuristic = false;
	bool use_ff_heuristic = false;
	// Read in commandline options.
	for (int i = 1; i < argc - 2; i++)
	{
		std::string command_line = std::string(argv[i]);
		if (command_line == "-val")
		{
			validate = true;
			std::cerr << "Enable validation!" << std::endl;
		}
		else if (command_line == "-h")
		{
			calculate_heuristic = true;
			std::cerr << "Calculate heuristic!" << std::endl;
		}
		else if (command_line == "-ff")
		{
			use_ff_heuristic = true;
			std::cerr << "Use the FF heuristic!" << std::endl;
		}
		else
		{
			std::cerr << "Unknown option " << command_line << std::endl;
			exit(1);
		}
	}
	
	std::string problem_name(argv[argc - 1]);
	std::string domain_name(argv[argc - 2]);
	if (use_ff_heuristic)
	{
		initialiseFF(domain_name, problem_name, &get_1P_and_H, &get_1P);
		exit(0);
	}

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
	term_manager_ = &term_manager;

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
	SimpleBindingsPropagator* propagator = new SimpleBindingsPropagator();
	
	// Instantiate the initial plan and do the planning!
	Plan* plan = new Plan(action_manager, term_manager, type_manager, *propagator);
	const Formula* goal = Utility::convertGoal(term_manager, predicate_manager, the_problem->the_goal, false);
	
	std::vector<const Atom*>* initial_facts = new std::vector<const Atom*>();	
	Utility::convertEffects(term_manager, predicate_manager, *the_problem->initial_state, *initial_facts);
	
	for (std::vector<const Atom*>::const_iterator ci = initial_facts->begin(); ci != initial_facts->end(); ci++)
	{
		const Atom* initial_fact = *ci;
		if (initial_fact->getPredicate().isStatic())
		{
			static_facts_.push_back(&SAS_Plus::BoundedAtom::createBoundedAtom(*initial_fact, plan->getBindings()));
		}
	}

	std::vector<const Variable*>* initial_action_variables = new std::vector<const Variable*>();

	// Create the initial step, which is a custom action with the atoms of the initial state as its effects.
	MyPOP::Action* initial_action = new MyPOP::Action("Initial action", Formula::TRUE, initial_action_variables, initial_facts);

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
	MyPOP::Action* goal_action = new MyPOP::Action("Goal action", *goal, goal_action_variables, goal_action_effects);


#ifdef MYPOP_COMMENTS
	std::cout << "Print goal action" << std::endl;
	std::cout << *goal_action << std::endl;
#endif

	plan->makeInitialPlan(*initial_action, *goal_action);

#ifdef MYPOP_COMMENTS
	std::cout << "Initial plan" << *plan << std::endl;
#endif

	assert (plan->getSteps().size() == 2);

	// Do the domain analysis.
#ifdef MYPOP_COMMENTS
	std::cout << " === Creating the DTGs === " << std::endl;
#endif
	SAS_Plus::DomainTransitionGraphManager* dtg_manager = new SAS_Plus::DomainTransitionGraphManager(predicate_manager, type_manager, action_manager, term_manager, *initial_facts);

	// New style, working directly on the TIM structure.
	const SAS_Plus::DomainTransitionGraph& combined_graph = dtg_manager->generateDomainTransitionGraphsTIM(*the_domain->types, plan->getBindings());

	unsigned int nr_transitions = 0;
	for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = combined_graph.getNodes().begin(); ci != combined_graph.getNodes().end(); ci++)
	{
		const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
		for (std::vector<const SAS_Plus::Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			++nr_transitions;
		}
	}
	std::cerr << "Total number of transitions: " << nr_transitions << "." << std::endl;

	// Do the reachability analysis.
#ifdef MYPOP_KEEP_TIME
	struct timeval start_time_prepare_reachability;
	gettimeofday(&start_time_prepare_reachability, NULL);
#endif
//	std::vector<const REACHABILITY::ReachableFact*> lifted_reachable_facts;
	REACHABILITY::DTGReachability analyst(*dtg_manager, combined_graph, term_manager, predicate_manager);
	analyst_ = &analyst;
	bindings_ = &combined_graph.getBindings();
#ifdef MYPOP_KEEP_TIME
	struct timeval end_time_prepare_reachability;
	gettimeofday(&end_time_prepare_reachability, NULL);	
	
	double time_spend_preparing = end_time_prepare_reachability.tv_sec - start_time_prepare_reachability.tv_sec + (end_time_prepare_reachability.tv_usec - start_time_prepare_reachability.tv_usec) / 1000000.0;
	std::cerr << "Prepare reachability analysis: " << time_spend_preparing << " seconds" << std::endl;
#endif

	std::vector<const Atom*> goal_facts;
	Utility::convertFormula(goal_facts, goal);
	
	for (std::vector<const Atom*>::const_iterator ci = goal_facts.begin(); ci != goal_facts.end(); ci++)
	{
		bounded_goal_facts_.push_back(new SAS_Plus::BoundedAtom(Step::GOAL_STEP, **ci));
	}
	
	predicate_manager_ = &predicate_manager;

	initialiseFF(domain_name, problem_name, &calculateHeuristicForFF, &calculateHeuristicForFF);

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

	
	/*	std::cout << " === Creating the Landmarks === " << std::endl;
	LANDMARKS::LandmarkManager landmark_manager(action_manager, type_manager, term_manager);
	landmark_manager.findLandmarksFromGoal(*the_domain->ops, *the_domain->types, *plan, dtg_manager, cg);
	Graphviz::printToDot(landmark_manager.getLandmarkGraph());
	std::cout << " === DONE! Creating the Landmarks === " << std::endl;
*/

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
	delete &combined_graph;
	delete dtg_manager;
	delete plan;
	delete propagator;
	delete initial_action;
	delete goal_action;
//	delete solution_plan;
	delete VAL::current_analysis;
	delete MyPOP::REACHABILITY::g_reachable_fact_memory_pool;
	MyPOP::REACHABILITY::EquivalentObjectGroup::deleteMemoryPool();
}
