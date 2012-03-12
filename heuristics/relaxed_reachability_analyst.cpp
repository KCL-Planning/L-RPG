#include "relaxed_reachability_analyst.h"

#include "../formula.h"
#include "dtg_manager.h"
#include <predicate_manager.h>
#include <term_manager.h>
#include <type_manager.h>
#include <parser_utils.h>
#include "transition.h"
#include "property_space.h"

namespace MyPOP {

namespace REACHABILITY {

RelaxedReachabilityAnalyst::RelaxedReachabilityAnalyst(const DomainTransitionGraphManager& dtg_manager)
	: dtg_manager_(&dtg_manager)
{
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager.getManagableObjects().begin(); ci != dtg_manager.getManagableObjects().end(); ci++)
	{
		const DomainTransitionGraph* dtg = *ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			supported_facts_[*ci] = new std::vector<std::vector<const BoundedAtom*> *>();
		}
	}
}

void RelaxedReachabilityAnalyst::getSupportingFacts(std::vector<std::vector<const BoundedAtom*>* >& supporting_tupples, const std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >& variable_assignments, const std::vector<BoundedAtom*>& atoms_to_achieve, const Bindings& atoms_to_achieve_bindings, const std::vector<const BoundedAtom*>& initial_supporting_facts, const std::vector<const BoundedAtom*>& initial_facts, Bindings& initial_facts_bindings)
{
	assert (atoms_to_achieve.size() > initial_supporting_facts.size());
	const BoundedAtom* atom_to_process = atoms_to_achieve[initial_supporting_facts.size()];
	
//	std::cout << "[" << initial_supporting_facts.size() << "] The atom to achieve: ";
//	atom_to_process->print(std::cout, atoms_to_achieve_bindings);
//	std::cout << std::endl;

	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		StepID initial_fact_id = (*ci)->getId();
		const Atom& initial_fact = (*ci)->getAtom();
		
		if (initial_facts_bindings.canUnify(initial_fact, initial_fact_id, atom_to_process->getAtom(), atom_to_process->getId(), &atoms_to_achieve_bindings))
		{
//			std::cout << "Initial fact which can unify: ";
//			initial_fact.print(std::cout, initial_facts_bindings, initial_fact_id);
//			std::cout << std::endl;

			// Check if all terms can be supported.
			bool terms_supported = true;
			std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >* variable_assignments_clone = new std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >(variable_assignments);
			
			for (std::vector<const Term*>::const_iterator ci = atom_to_process->getAtom().getTerms().begin(); ci != atom_to_process->getAtom().getTerms().end(); ci++)
			{
				const Term* atom_term = *ci;
				unsigned int term_index = std::distance(atom_to_process->getAtom().getTerms().begin(), ci);
				
				const std::vector<const Object*>& term_domain_atom_to_process = atom_term->getDomain(atom_to_process->getId(), atoms_to_achieve_bindings);
				const std::vector<const Object*>& initial_fact_domain = initial_fact.getTerms()[term_index]->getDomain(initial_fact_id, initial_facts_bindings);

				// Find the assignments made to the term's domain.
				std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >::const_iterator found_domain = variable_assignments_clone->find(&term_domain_atom_to_process);
				
				// If no assignments have been made yet we make them equal to the initial fact's domain.
				if (found_domain == variable_assignments_clone->end())
				{
					(*variable_assignments_clone)[&term_domain_atom_to_process] = &initial_fact_domain;
//					std::cout << "Bind the " << term_index << "th term to: ";
//					for (std::vector<const Object*>::const_iterator ci = initial_fact_domain.begin(); ci != initial_fact_domain.end(); ci++)
//					{
//						std::cout << **ci;
//						if (ci + 1 != initial_fact_domain.end())
//						{
//							std::cout << ", ";
//						}
//					}
//					std::cout << "." << std::endl;
				}
				// If previous assignments have been made, we take the intersection between the previous assignments and the fact we found
				// to be unifiable with this fact.
				else
				{
					std::vector<const Object*> existing_domain = *(*variable_assignments_clone)[&term_domain_atom_to_process];
					
					// Get the intersection of the variable assignments made and the new assignment just made.
					std::vector<const Object*> initial_fact_domain_sorted_copy(initial_fact_domain);
					std::sort(initial_fact_domain_sorted_copy.begin(), initial_fact_domain_sorted_copy.end());
					std::sort(existing_domain.begin(), existing_domain.end());
					std::vector<const Object*>* intersection = new std::vector<const Object*>(std::max(initial_fact_domain_sorted_copy.size(), existing_domain.size()));
					std::vector<const Object*>::iterator intersection_end = std::set_intersection(initial_fact_domain_sorted_copy.begin(), initial_fact_domain_sorted_copy.end(), existing_domain.begin(), existing_domain.end(), intersection->begin());
					
/*					std::cout << "Bind the " << term_index << "th term to the intersection of: ";
					for (std::vector<const Object*>::const_iterator ci = initial_fact_domain_sorted_copy.begin(); ci != initial_fact_domain_sorted_copy.end(); ci++)
					{
						std::cout << **ci;
						if (ci + 1 != initial_fact_domain_sorted_copy.end())
						{
							std::cout << ", ";
						}
					}
					std::cout << " and ";
					for (std::vector<const Object*>::const_iterator ci = existing_domain.begin(); ci != existing_domain.end(); ci++)
					{
						std::cout << **ci;
						if (ci + 1 != existing_domain.end())
						{
							std::cout << ", ";
						}
					}
					std::cout << " -> ";
					for (std::vector<const Object*>::const_iterator ci = intersection->begin(); ci != intersection_end; ci++)
					{
						std::cout << **ci;
						if (ci + 1 != intersection_end)
						{
							std::cout << ", ";
						}
					}
					std::cout << "." << std::endl;
*/
					
					// If the intersection is empty we know that the term cannot be supported.
					if (intersection_end == intersection->begin())
					{
						terms_supported = false;
						break;
					}
					
					// Otherwise, we need to update the variable domain which has been modified.
					intersection->resize(std::distance(intersection->begin(), intersection_end));
					(*variable_assignments_clone)[&term_domain_atom_to_process] = intersection;
				}
			}
			
			if (!terms_supported)
			{
				continue;
			}
			
			// Construct the facts which support the preconditions.
			std::vector<const BoundedAtom*>* initial_supporting_facts_clone = new std::vector<const BoundedAtom*>(initial_supporting_facts);
			initial_supporting_facts_clone->push_back(new BoundedAtom(initial_fact_id, initial_fact));
			
			if (initial_supporting_facts_clone->size() == atoms_to_achieve.size())
			{
				std::vector<const BoundedAtom*>* finalized_supporting_facts = new std::vector<const BoundedAtom*>();
				
//				std::cout << "The following nodes support the DTG node!" << std::endl;
				for (std::vector<BoundedAtom*>::const_iterator ci = atoms_to_achieve.begin(); ci != atoms_to_achieve.end(); ci++)
				{
					const BoundedAtom* atom_to_achieve = *ci;
					const BoundedAtom& new_bounded_atom = BoundedAtom::createBoundedAtom(atom_to_achieve->getAtom(), initial_facts_bindings);
					
					finalized_supporting_facts->push_back(&new_bounded_atom);
					
//					std::cout << " * (" << atom_to_achieve->getAtom().getPredicate().getName();
					for (std::vector<const Term*>::const_iterator ci = atom_to_achieve->getAtom().getTerms().begin(); ci != atom_to_achieve->getAtom().getTerms().end(); ci++)
					{
						const Term* term_of_atom_to_achieve = *ci;
						unsigned int term_index = std::distance(atom_to_achieve->getAtom().getTerms().begin(), ci);
						const Term* new_bounded_atom_term = new_bounded_atom.getAtom().getTerms()[term_index];
						
						const std::vector<const Object*>& variable_domain_of_atom_to_achieve = term_of_atom_to_achieve->getDomain(atom_to_achieve->getId(), atoms_to_achieve_bindings);
						const std::vector<const Object*>* possible_assignments = (*variable_assignments_clone)[&variable_domain_of_atom_to_achieve];

						new_bounded_atom_term->makeDomainEqualTo(new_bounded_atom.getId(), *possible_assignments, initial_facts_bindings);
/*						std::cout << "{";
						for (std::vector<const Object*>::const_iterator ci = possible_assignments->begin(); ci != possible_assignments->end(); ci++)
						{
							std::cout << **ci;
							if (ci + 1 != possible_assignments->end())
							{
								std::cout << ", ";
							}
						}
						std::cout << "}";
*/
					}
//					std::cout << std::endl;
				}
				
//				std::cout << "The following nodes support the DTG node!" << std::endl;
//				for (std::vector<const BoundedAtom*>::const_iterator ci = finalized_supporting_facts->begin(); ci != finalized_supporting_facts->end(); ci++)
//				{
//					std::cout << " * ";
//					(*ci)->print(std::cout, initial_facts_bindings);
//					std::cout << std::endl;
//				}
				
				
/*
				for (std::vector<const BoundedAtom*>::const_iterator ci = initial_supporting_facts_clone->begin(); ci != initial_supporting_facts_clone->end(); ci++)
				{
					std::cout << " * ";
					(*ci)->print(std::cout, initial_facts_bindings);
					std::cout << "." << std::endl;
				}
*/
				supporting_tupples.push_back(finalized_supporting_facts);
			}
			else
			{
				getSupportingFacts(supporting_tupples, *variable_assignments_clone, atoms_to_achieve, atoms_to_achieve_bindings, *initial_supporting_facts_clone, initial_facts, initial_facts_bindings);
			}
		}
	}
}

void RelaxedReachabilityAnalyst::initialisePossibleAssignmentsToDTGNodes(const std::vector<const Atom*>& initial_facts, const std::vector<const BoundedAtom*>& established_facts, Bindings& initial_bindings)
{
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		const DomainTransitionGraph* dtg = *ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			
//			std::cout << " -============= Process the DTG node =============- ";
//			dtg_node->print(std::cout);
//			std::cout << std::endl;

			// Check if all atoms can unify with the initial state. For each candidate we store the invariable object. This way we can check if
			// the candidate also matches the other atoms in this node with respect to the invariable.
			//std::map<const std::vector<const Object*>*, std::vector<const Object*>*> candidates;
			//std::map<const std::vector<const Object*>*, const Object*> candidates;
			std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > candidates;
			std::vector<const BoundedAtom*> initial_supporting_facts;
			
			std::vector<std::vector<const BoundedAtom*>* >* supporting_tupples = new std::vector<std::vector<const BoundedAtom*>* >();
			
			getSupportingFacts(*supporting_tupples, candidates, dtg_node->getAtoms(), dtg->getBindings(), initial_supporting_facts, established_facts, initial_bindings);
			supported_facts_[dtg_node] = supporting_tupples;
		}
	}
}

void RelaxedReachabilityAnalyst::performReachabilityAnalysis(const std::vector<const Atom*>& initial_facts, Bindings initial_bindings)
{
	Type null_type("dummy_type", NULL);
	Object null_object(null_type, "dummy");

	std::set<const Transition*> possible_transitions;
	std::vector<const Transition*> open_list;

	/**
	 * We conjecture that the only information we need per DTG node is the list of invariables which are supported. The values of
	 * the other variables should be derived from looking at the DTGs where these are invariable.
	 * This means we only need to keep track of a single list of values per DTG node and greatly improves the runtime of the analysis.
	 */
	std::map<const DomainTransitionGraphNode*, std::vector<const Object*>* > reachable_invariables_per_dtg_node;

	/**
	 * Per DTG node, map which DTGs are reachable.
	 */
	//std::map<const DomainTransitionGraphNode*, std::vector<std::pair<const DomainTransitionGraphNode*, const Transition*> >* > reachability_graph;
	std::map<const DomainTransitionGraphNode*, std::vector<const DomainTransitionGraphNode*>* > reachability_graph;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			reachability_graph[dtg_node] = new std::vector<const DomainTransitionGraphNode*>();
		}
	}
	
	std::vector<const BoundedAtom*> established_facts;
	for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		established_facts.push_back(new BoundedAtom(Step::INITIAL_STEP, **ci));
	}
	
	for (std::vector<const BoundedAtom*>::const_iterator ci = established_facts.begin(); ci != established_facts.end(); ci++)
	{
		StepID initial_fact_id = (*ci)->getId();
		const Atom& initial_fact = (*ci)->getAtom();
		
		std::cout << "Initial fact: ";
		initial_fact.print(std::cout, initial_bindings, initial_fact_id);
		std::cout << std::endl;
	}

	
	/**
	 * The first step in the algorithm is to initialize the list of values of each DTG node with the initial state.
	 * Per atom in a DTG node we group all initial facts which can unify with it, than we take the intersection of
	 * the variable which matches with the atom's invariable and mark this set.
	 */
	initialisePossibleAssignmentsToDTGNodes(initial_facts, established_facts, initial_bindings);
	
	/**
	 * Try to achieve the preconditions of transitions.
	 */
	bool transition_achieved = true;
	std::set<const Transition*> closed_list;
	while (transition_achieved)
	{
		transition_achieved = false;
		
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = dtg_manager_->getManagableObjects().begin(); ci != dtg_manager_->getManagableObjects().end(); ci++)
		{
			DomainTransitionGraph* dtg = *ci;
			
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
			{
				DomainTransitionGraphNode* dtg_node = *ci;
				
				// Instantiate the DTG node by assigning the terms to domains we have already determined to be reachable.
				std::vector<std::vector<const BoundedAtom*>* >* assignable_atoms = supported_facts_[dtg_node];
				
				for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = assignable_atoms->begin(); ci != assignable_atoms->end(); ci++)
				{
					std::vector<const BoundedAtom*>* possible_assignment = *ci;
					
					// Map the action variable's domain to a set of objects which supports the transition. The variable domains of the
					// action variables will match the fact in the DTG nodes which allows us to find a set of facts which satisfy the
					// action's precondition and take the effects as newly established facts.
					std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > term_assignments;
					
					// Assign the predetermined assignments.
					for (std::vector<const BoundedAtom*>::iterator possible_assignment_ci = possible_assignment->begin(); possible_assignment_ci != possible_assignment->end(); possible_assignment_ci++)
					{
						const BoundedAtom* possible_atom_assignment = *possible_assignment_ci;
						const BoundedAtom* dtg_node_atom = dtg_node->getAtoms()[std::distance(possible_assignment->begin(), possible_assignment_ci)];
						
						for (std::vector<const Term*>::const_iterator ci = dtg_node_atom->getAtom().getTerms().begin(); ci != dtg_node_atom->getAtom().getTerms().end(); ci++)
						{
							const Term* dtg_node_atom_term = *ci;
							const Term* possible_atom_assignment_term = possible_atom_assignment->getAtom().getTerms()[std::distance(dtg_node_atom->getAtom().getTerms().begin(), ci)];
							
							const std::vector<const Object*>& dtg_node_atom_term_domain = dtg_node_atom_term->getDomain(dtg_node_atom->getId(), dtg->getBindings());
							const std::vector<const Object*>& possible_atom_assignment_term_domain = possible_atom_assignment_term->getDomain(possible_atom_assignment->getId(), initial_bindings);
							
							term_assignments[&dtg_node_atom_term_domain] = &possible_atom_assignment_term_domain;
						}
					}
					
					// With the bindings done check if the other preconditions - those which are not part of the DTG node - can be satisfied as well.
					for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
					{
						const Transition* transition = *ci;
//						std::cout << "Transition: ";
//						transition->getStep()->getAction().print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
//						std::cout << std::endl;
						if (closed_list.count(transition) != 0)
						{
							//continue;
						}
						const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
						
						// Convert into bounded atoms for algorithm.
						std::vector<BoundedAtom*> bounded_preconditions;
						
						for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
						{
							const Atom* precondition = (*ci).first;
							bounded_preconditions.push_back(new BoundedAtom(transition->getStep()->getStepId(), *precondition));
						}
						
						std::vector<const BoundedAtom*> initial_supporting_facts;
						std::vector<std::vector<const BoundedAtom*>* >* supporting_tupples = new std::vector<std::vector<const BoundedAtom*>* >();
						getSupportingFacts(*supporting_tupples, term_assignments, bounded_preconditions, dtg->getBindings(), initial_supporting_facts, established_facts, initial_bindings);
						
						if (!supporting_tupples->empty())
						{
							closed_list.insert(transition);
							// For each tupple of supporting facts determine the domains of each of the action parameters and use these to determine the achieved facts.
//							std::cout << "The following atoms can support the transition: " << *transition << ": " << std::endl;
							for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = supporting_tupples->begin(); ci != supporting_tupples->end(); ci++)
							{
								// Bind each term of the action to the supporting atom's term domains.
								const std::vector<const Object*>* action_parameter_domains[transition->getStep()->getAction().getVariables().size()];
								for (unsigned int i = 0; i < transition->getStep()->getAction().getVariables().size(); i++)
								{
									action_parameter_domains[i] = NULL;
								}
//								const std::vector<const Object*>* invariable_domain = NULL;
								
								const std::vector<const BoundedAtom*>* supporting_atoms = *ci;
//								std::cout << "< ";
								for (std::vector<const BoundedAtom*>::const_iterator ci = supporting_atoms->begin(); ci != supporting_atoms->end(); ci++)
								{
									const BoundedAtom* supporting_bounded_atom = *ci;
//									supporting_bounded_atom->print(std::cout, initial_bindings);
									
									unsigned int precondition_index = std::distance(supporting_atoms->begin(), ci);
									const std::pair<const Atom*, InvariableIndex>& matching_precondition = preconditions[precondition_index];
									
									for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
									{
										const Variable* action_variable = *ci;
										const std::vector<const Object*>& action_variable_domain = action_variable->getDomain(transition->getStep()->getStepId(), dtg->getBindings());
										
										unsigned int action_variable_index = std::distance(transition->getStep()->getAction().getVariables().begin(), ci);
										
										// Map the supporting domains to the variables of the action.
										for (std::vector<const Term*>::const_iterator ci = matching_precondition.first->getTerms().begin(); ci != matching_precondition.first->getTerms().end(); ci++)
										{
											const Term* precondition_term = *ci;
											const std::vector<const Object*>& term_variable_domain = precondition_term->getDomain(transition->getStep()->getStepId(), dtg->getBindings());
											unsigned int term_index = std::distance(matching_precondition.first->getTerms().begin(), ci);
/*
											if (term_index == matching_precondition.second)
											{
												if (invariable_domain != NULL)
												{
													assert (invariable_domain->size() == 1);
													assert (term_variable_domain.size() == 1);
													//if (invariable_domain != &term_variable_domain)
													if ((*invariable_domain)[0] != term_variable_domain[0])
													{
														std::cout << "Replace: { ";
														for (std::vector<const Object*>::const_iterator ci = term_variable_domain.begin(); ci != term_variable_domain.end(); ci++)
														{
															std::cout << **ci;
															if (ci + 1 != term_variable_domain.end())
															{
																std::cout << ", ";
															}
														}
														std::cout << " with ";
														for (std::vector<const Object*>::const_iterator ci = invariable_domain->begin(); ci != invariable_domain->end(); ci++)
														{
															std::cout << **ci;
															if (ci + 1 != invariable_domain->end())
															{
																std::cout << ", ";
															}
														}
														std::cout << std::endl;
														assert (false);
													}
												}
												else
												{
													invariable_domain = &term_variable_domain;
												}
											}
*/

											if (&action_variable_domain == &term_variable_domain)
											{
												const std::vector<const Object*>& supporting_atom_variable_domain = supporting_bounded_atom->getAtom().getTerms()[term_index]->getDomain(supporting_bounded_atom->getId(), initial_bindings);
												
												if (action_parameter_domains[action_variable_index] != NULL)
												{
													bool domains_are_equal = true;
													if (action_parameter_domains[action_variable_index]->size() != supporting_atom_variable_domain.size())
														domains_are_equal = false;
													else
													{
														for (unsigned int i = 0; i < supporting_atom_variable_domain.size(); i++)
														{
															if ((*action_parameter_domains[action_variable_index])[i] != supporting_atom_variable_domain[i])
															{
																domains_are_equal = false;
																break;
															}
														}
													}
													
													if (!domains_are_equal)
													{
														std::cout << "Replace: { ";
														for (std::vector<const Object*>::const_iterator ci = action_parameter_domains[action_variable_index]->begin(); ci != action_parameter_domains[action_variable_index]->end(); ci++)
														{
															assert (*ci != NULL);
															std::cout << **ci;
															if (ci + 1 != action_parameter_domains[action_variable_index]->end())
															{
																std::cout << ", ";
															}
														}
														std::cout << " with ";
														for (std::vector<const Object*>::const_iterator ci = supporting_atom_variable_domain.begin(); ci != supporting_atom_variable_domain.end(); ci++)
														{
															std::cout << **ci;
															if (ci + 1 != supporting_atom_variable_domain.end())
															{
																std::cout << ", ";
															}
														}
														std::cout << std::endl;
														assert (false);
													}
												}
												else
												{
													action_parameter_domains[action_variable_index] = &supporting_atom_variable_domain;
												}
											}
										}
									}
//									std::cout << ", ";
								}
//								std::cout << ">" << std::endl;
								
								// Add the achieved nodes to the established facts.
								const DomainTransitionGraphNode& to_node = transition->getToNode();
								for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
								{
									BoundedAtom* to_node_bounded_atom = *ci;
									std::vector<const Term*>* new_atom_terms = new std::vector<const Term*>();
									std::vector<const std::vector<const Object*>* > new_atom_domains;
									
/*									std::cout << "The action: (" << transition->getStep()->getAction().getPredicate();
									//for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
									for (unsigned int i = 0; i < transition->getStep()->getAction().getVariables().size(); i++)
//									for (std::vector<const Variable*>::const_iterator ci = transition->getStep()->getAction().getVariables().begin(); ci != transition->getStep()->getAction().getVariables().end(); ci++)
									{
										const std::vector<const Object*>* matching_variable_domain = action_parameter_domains[i];
										std::cout << "{";
										for (std::vector<const Object*>::const_iterator ci = matching_variable_domain->begin(); ci != matching_variable_domain->end(); ci++)
										{
											std::cout << **ci;
											
											if (ci + 1 != matching_variable_domain->end())
											{
												std::cout << ", ";
											}
										}
										std::cout << "}";
									}
									std::cout << ")" << std::endl;
			
//									transition->getStep()->getAction().print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
//									std::cout << std::endl;
*/
//									std::cout << "!!! Achieved the following TO Node: (" << to_node_bounded_atom->getAtom().getPredicate().getName() << " ";
									bool valid_assignments = true;
									for (std::vector<const Term*>::const_iterator ci = to_node_bounded_atom->getAtom().getTerms().begin(); ci != to_node_bounded_atom->getAtom().getTerms().end(); ci++)
									{
										const Term* to_node_term = *ci;
										new_atom_terms->push_back(to_node_term);
										const std::vector<const Object*>& to_node_term_domain = to_node_term->getDomain(to_node_bounded_atom->getId(), dtg->getBindings());
//										assert (to_node_term_domain.size() == 1);
										
										bool is_bounded = false;
										
										for (unsigned int i = 0; i < transition->getStep()->getAction().getVariables().size(); i++)
										{
											const std::vector<const Object*>& action_variable_domain = transition->getStep()->getAction().getVariables()[i]->getDomain(transition->getStep()->getStepId(), dtg->getBindings());
											if (&to_node_term_domain == &action_variable_domain)
											{
//												if (&to_node_term_domain == invariable_domain)
//												{
//													std::cout << "!%$";
//												}
												
												const std::vector<const Object*>* matching_variable_domain = action_parameter_domains[i];

												// If no matching variable domain has been found, all values are possible.
												if (matching_variable_domain == NULL)
												{
//													std::cout << "Not bound variable domain: ";
//													to_node_term->print(std::cout, dtg->getBindings(), to_node_bounded_atom->getId());
//													std::cout << "." << std::endl;
													matching_variable_domain  = &to_node_term->getDomain(to_node_bounded_atom->getId(), dtg->getBindings());
													//std::vector<const DomainTransitionGraphNode*> new_nodes
												}
												
												assert (matching_variable_domain != NULL);
												//assert (matching_variable_domain->size() == 1);
												new_atom_domains.push_back(matching_variable_domain);
//												for (std::vector<const Object*>::const_iterator ci = matching_variable_domain->begin(); ci != matching_variable_domain->end(); ci++)
//												{
//													std::cout << **ci << ", ";
//												}
												assert (matching_variable_domain->size() > 0);
												is_bounded = true;
												break;
											}
										}
										
										if (!is_bounded)
										{
//											std::cout << "The " << std::distance(to_node_bounded_atom->getAtom().getTerms().begin(), ci) << "th term is not bounded! :(((" << std::endl;
											valid_assignments = false;
											break;
										}
									}
									if (!valid_assignments)
									{
										continue;
									}
//									std::cout << "|";
									
									Atom* achieved_fact = new Atom(to_node_bounded_atom->getAtom().getPredicate(), *new_atom_terms, to_node_bounded_atom->getAtom().isNegative());
									BoundedAtom& achieved_bounded_atom = BoundedAtom::createBoundedAtom(*achieved_fact, initial_bindings);
									
									assert (achieved_fact->getArity() == achieved_fact->getPredicate().getArity());
									assert (new_atom_domains.size() == achieved_fact->getPredicate().getArity());
									assert (new_atom_terms->size() == achieved_fact->getPredicate().getArity());
									assert (achieved_fact->getTerms().size() == achieved_fact->getPredicate().getArity());
									
									// Bound the achieved fact to the supporting domains.
									for (unsigned int i = 0; i < achieved_fact->getArity(); i++)
									{
			//							std::cout << "Make ";
			//							achieved_fact->getTerms()[i]->print(std::cout, initial_bindings, achieved_bounded_atom.getId());
			//							std::cout << " equal to ";
										
//										for (std::vector<const Object*>::const_iterator ci = new_atom_domains[i]->begin(); ci != new_atom_domains[i]->end(); ci++)
//										{
//											std::cout << **ci << ", ";
//										}
//										std::cout << std::endl;
										achieved_fact->getTerms()[i]->makeDomainEqualTo(achieved_bounded_atom.getId(), *new_atom_domains[i], initial_bindings);
										assert (achieved_fact->getTerms()[i]->getDomain(achieved_bounded_atom.getId(), initial_bindings).size() > 0);
									}
									
									// Ground all the variable domains.
/*									std::vector<BoundedAtom*> grounded_achieved_bounded_atom;
									for (std::vector<const Term*>::const_iterator ci = achieved_bounded_atom.getAtom().getTerms().begin(); ci != achieved_bounded_atom.getAtom().getTerms().end(); ci++)
									{
										
									}*/
									
									bool present = false;
									for (std::vector<const BoundedAtom*>::const_iterator ci = established_facts.begin(); ci != established_facts.end(); ci++)
									{
										const BoundedAtom* bounded_atom = *ci;
										if (initial_bindings.canUnify(bounded_atom->getAtom(), bounded_atom->getId(), achieved_bounded_atom.getAtom(), achieved_bounded_atom.getId()))
										{
											bool terms_match = true;
											for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
											{
												const Term* established_fact_term = *ci;
												const Term* newly_achieved_fact_term = achieved_fact->getTerms()[std::distance(bounded_atom->getAtom().getTerms().begin(), ci)];
												
												if (!established_fact_term->isEquivalentTo(bounded_atom->getId(), *newly_achieved_fact_term, achieved_bounded_atom.getId(), initial_bindings))
												{
													terms_match = false;
													break;
												}
											}
											
											if (!terms_match)
												continue;
											
											present = true;
											
//											std::cout << "ALREADY ACHIEVED -=(";
//											achieved_bounded_atom.print(std::cout, initial_bindings);
//											std::cout << ")=-" << std::endl;
											
											break;
										}
									}
									
									if (!present)
									{
										established_facts.push_back(&achieved_bounded_atom);
										std::cout << "-=(";
										achieved_bounded_atom.print(std::cout, initial_bindings);
										std::cout << ")=-" << std::endl;
										transition_achieved = true;
									}
									//transition_achieved = true;
								}
//								std::cout << "." << std::endl;
							}
						}
					}
				}
			}
		}
		
		initialisePossibleAssignmentsToDTGNodes(initial_facts, established_facts, initial_bindings);
		
		for (std::vector<const BoundedAtom*>::const_iterator ci = established_facts.begin(); ci != established_facts.end(); ci++)
		{
			StepID initial_fact_id = (*ci)->getId();
			const Atom& initial_fact = (*ci)->getAtom();
			
			std::cout << "Initial fact: ";
			initial_fact.print(std::cout, initial_bindings, initial_fact_id);
			std::cout << std::endl;
		}
	}
}

};
	
};

