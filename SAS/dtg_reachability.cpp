#include "dtg_reachability.h"
#include "dtg_manager.h"
#include "dtg_graph.h"
#include "dtg_node.h"
#include "transition.h"
#include "../predicate_manager.h"
#include "../term_manager.h"

namespace MyPOP {
	
namespace SAS_Plus {
	
DTGReachability::DTGReachability(const DomainTransitionGraph& dtg_graph)
	: dtg_graph_(&dtg_graph)
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph.getNodes().begin(); ci != dtg_graph.getNodes().end(); ci++)
	{
		supported_facts_[*ci] = new std::vector<std::vector<const BoundedAtom*> *>();
	}
}

void DTGReachability::performReachabilityAnalsysis(const std::vector<const BoundedAtom*>& initial_facts)
{
	std::cout << "Start performing reachability analysis." << std::endl;
	
	std::vector<const Transition*> open_list;
	std::set<const Transition*> closed_list;
	
	// Keep a list of all established facts so far.
	std::vector<const BoundedAtom*> established_facts(initial_facts);
	
	std::cout << "Find initial supported DTG nodes." << std::endl;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_graph_->getNodes().begin(); ci != dtg_graph_->getNodes().end(); ci++)
	{
		// Initialise the reachability structure(s) with the values from the initial state.
		const std::vector<BoundedAtom*>& atoms_to_achieve = (*ci)->getAtoms();
		std::vector<std::vector<const BoundedAtom*>* > supporting_tupples;
		std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > variable_assignments;
		std::vector<const BoundedAtom*> initial_supporting_facts;
		getSupportingFacts(supporting_tupples, variable_assignments, atoms_to_achieve, initial_supporting_facts, established_facts);

		// Mark those transitions whose node have been 'filled' by the initial state.
		if (supporting_tupples.size() > 0)
		{
			std::cout << "Supported node: " << **ci << std::endl;
			open_list.insert(open_list.end(), (*ci)->getTransitions().begin(), (*ci)->getTransitions().end());
			
			std::vector<std::vector<const BoundedAtom*>* >* supported_facts = supported_facts_[*ci];
			supported_facts->insert(supported_facts->end(), supporting_tupples.begin(), supporting_tupples.end());
		}
	}
	
	// While there are transitions achieved:
	bool new_transition_achieved = true;
	std::set<const Transition*> new_transitions_to_add;
	while (new_transition_achieved)
	{
		new_transition_achieved = false;
		
		for (std::set<const Transition*>::const_iterator ci = new_transitions_to_add.begin(); ci != new_transitions_to_add.end(); ci++)
		{
			const Transition* new_transition = *ci;
			bool exists = false;
			for (std::vector<const Transition*>::const_iterator ci = open_list.begin(); ci != open_list.end(); ci++)
			{
				if (*ci == new_transition)
				{
					exists = true;
					break;
				}
			}
			
			if (!exists)
			{
				open_list.push_back(new_transition);
				std::cout << "New transition to considder: " << *new_transition << std::endl;
			}
		}
		new_transitions_to_add.clear();
		
		// For each transition of a marked node:
		for (std::vector<const Transition*>::reverse_iterator ri = open_list.rbegin(); ri != open_list.rend(); ri++)
		{
			/// Check if the preconditions of the transition have been satisfied.
			const Transition* transition = *ri;
			
			if (closed_list.count(transition) != 0)
				continue;
			
			std::cout << " * Work on the transition: " << *transition << "." << std::endl;
			const DomainTransitionGraphNode& from_dtg_node = transition->getFromNode();
			
			// Instantiate the DTG node by assigning the terms to domains we have already determined to be reachable.
			std::vector<std::vector<const BoundedAtom*>* >* assignable_atoms = supported_facts_[&from_dtg_node];
			
			for (std::vector<std::vector<const BoundedAtom*>* >::const_iterator ci = assignable_atoms->begin(); ci != assignable_atoms->end(); ci++)
			{
				std::vector<const BoundedAtom*>* possible_assignment = *ci;
				
				std::cout << "Possible assignments: ";
				for (std::vector<const BoundedAtom*>::const_iterator ci = possible_assignment->begin(); ci != possible_assignment->end(); ci++)
				{
					const BoundedAtom* assignment = *ci;
					assignment->print(std::cout, dtg_graph_->getBindings());
					if (ci != possible_assignment->end() - 1)
					{
						std::cout << ", ";
					}
				}
				std::cout << "." << std::endl;
				
				
				// Map the action variable's domain to a set of objects which supports the transition. The variable domains of the
				// action variables will match the fact in the DTG nodes which allows us to find a set of facts which satisfy the
				// action's precondition and take the effects as newly established facts.
				std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > term_assignments;
				
				// Assign the predetermined assignments.
				for (std::vector<const BoundedAtom*>::iterator possible_assignment_ci = possible_assignment->begin(); possible_assignment_ci != possible_assignment->end(); possible_assignment_ci++)
				{
					const BoundedAtom* possible_atom_assignment = *possible_assignment_ci;
					const BoundedAtom* dtg_node_atom = from_dtg_node.getAtoms()[std::distance(possible_assignment->begin(), possible_assignment_ci)];
					
					for (std::vector<const Term*>::const_iterator ci = dtg_node_atom->getAtom().getTerms().begin(); ci != dtg_node_atom->getAtom().getTerms().end(); ci++)
					{
						const Term* dtg_node_atom_term = *ci;
						const Term* possible_atom_assignment_term = possible_atom_assignment->getAtom().getTerms()[std::distance(dtg_node_atom->getAtom().getTerms().begin(), ci)];
						
						const std::vector<const Object*>& dtg_node_atom_term_domain = dtg_node_atom_term->getDomain(dtg_node_atom->getId(), dtg_graph_->getBindings());
						const std::vector<const Object*>& possible_atom_assignment_term_domain = possible_atom_assignment_term->getDomain(possible_atom_assignment->getId(), dtg_graph_->getBindings());
						
						term_assignments[&dtg_node_atom_term_domain] = &possible_atom_assignment_term_domain;
					}
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
				getSupportingFacts(*supporting_tupples, term_assignments, bounded_preconditions, initial_supporting_facts, established_facts);
				
				// If tupple(s) of possible assignments have been found we assign these to the action variables and extract the facts which have been achieved.
				if (!supporting_tupples->empty())
				{
					closed_list.insert(transition);
//					open_list.erase(ri.base() - 1);
					new_transitions_to_add.insert(transition->getToNode().getTransitions().begin(), transition->getToNode().getTransitions().end());
					new_transition_achieved = true;

					std::cout << " ** Found supporting tupple(s)!" << std::endl;
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
								const std::vector<const Object*>& action_variable_domain = action_variable->getDomain(transition->getStep()->getStepId(), dtg_graph_->getBindings());
								
								unsigned int action_variable_index = std::distance(transition->getStep()->getAction().getVariables().begin(), ci);
								
								// Map the supporting domains to the variables of the action.
								for (std::vector<const Term*>::const_iterator ci = matching_precondition.first->getTerms().begin(); ci != matching_precondition.first->getTerms().end(); ci++)
								{
									const Term* precondition_term = *ci;
									const std::vector<const Object*>& term_variable_domain = precondition_term->getDomain(transition->getStep()->getStepId(), dtg_graph_->getBindings());
									unsigned int term_index = std::distance(matching_precondition.first->getTerms().begin(), ci);

									if (&action_variable_domain == &term_variable_domain)
									{
										const std::vector<const Object*>& supporting_atom_variable_domain = supporting_bounded_atom->getAtom().getTerms()[term_index]->getDomain(supporting_bounded_atom->getId(), dtg_graph_->getBindings());
										
										// Debug, if we have already assigned a value to the action variable, make sure that the new one
										// is the same, otherwise something is wrong.
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
													(*ci)->print(std::cout, dtg_graph_->getBindings(), transition->getStep()->getStepId());
													if (ci + 1 != action_parameter_domains[action_variable_index]->end())
													{
														std::cout << ", ";
													}
												}
												std::cout << " with ";
												for (std::vector<const Object*>::const_iterator ci = supporting_atom_variable_domain.begin(); ci != supporting_atom_variable_domain.end(); ci++)
												{
													(*ci)->print(std::cout, dtg_graph_->getBindings(), supporting_bounded_atom->getId());
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
						std::vector<const BoundedAtom*>* to_node_achievers = new std::vector<const BoundedAtom*>();
						for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ci++)
						{
							BoundedAtom* to_node_bounded_atom = *ci;
							std::vector<const Term*>* new_atom_terms = new std::vector<const Term*>();
							std::vector<const std::vector<const Object*>* > new_atom_domains;
							
//							std::cout << "!!! Achieved the following TO Node: (" << to_node_bounded_atom->getAtom().getPredicate().getName() << " ";

							// Bind the terms of the to node to the action variables to get the achieved facts.
							bool valid_assignments = true;
							for (std::vector<const Term*>::const_iterator ci = to_node_bounded_atom->getAtom().getTerms().begin(); ci != to_node_bounded_atom->getAtom().getTerms().end(); ci++)
							{
								const Term* to_node_term = *ci;
								new_atom_terms->push_back(to_node_term);
								const std::vector<const Object*>& to_node_term_domain = to_node_term->getDomain(to_node_bounded_atom->getId(), dtg_graph_->getBindings());
//										assert (to_node_term_domain.size() == 1);
								
								bool is_bounded = false;
								
								for (unsigned int i = 0; i < transition->getStep()->getAction().getVariables().size(); i++)
								{
									const std::vector<const Object*>& action_variable_domain = transition->getStep()->getAction().getVariables()[i]->getDomain(transition->getStep()->getStepId(), dtg_graph_->getBindings());
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
//												std::cout << "Not bound variable domain: ";
//												to_node_term->print(std::cout, dtg_graph_->getBindings(), to_node_bounded_atom->getId());
//												std::cout << "." << std::endl;
											matching_variable_domain  = &to_node_term->getDomain(to_node_bounded_atom->getId(), dtg_graph_->getBindings());
											//std::vector<const DomainTransitionGraphNode*> new_nodes
										}
										
										assert (matching_variable_domain != NULL);
										//assert (matching_variable_domain->size() == 1);
										new_atom_domains.push_back(matching_variable_domain);
//										for (std::vector<const Object*>::const_iterator ci = matching_variable_domain->begin(); ci != matching_variable_domain->end(); ci++)
//										{
//											std::cout << **ci << ", ";
//										}
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
							BoundedAtom& achieved_bounded_atom = BoundedAtom::createBoundedAtom(*achieved_fact, dtg_graph_->getBindings());
							
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
								achieved_fact->getTerms()[i]->makeDomainEqualTo(achieved_bounded_atom.getId(), *new_atom_domains[i], dtg_graph_->getBindings());
								assert (achieved_fact->getTerms()[i]->getDomain(achieved_bounded_atom.getId(), dtg_graph_->getBindings()).size() > 0);
							}
							
							bool present = false;
							for (std::vector<const BoundedAtom*>::const_iterator ci = established_facts.begin(); ci != established_facts.end(); ci++)
							{
								const BoundedAtom* bounded_atom = *ci;
								if (dtg_graph_->getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), achieved_bounded_atom.getAtom(), achieved_bounded_atom.getId()))
								{
									bool terms_match = true;
									for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
									{
										const Term* established_fact_term = *ci;
										const Term* newly_achieved_fact_term = achieved_fact->getTerms()[std::distance(bounded_atom->getAtom().getTerms().begin(), ci)];
										
										if (!established_fact_term->isEquivalentTo(bounded_atom->getId(), *newly_achieved_fact_term, achieved_bounded_atom.getId(), dtg_graph_->getBindings()))
										{
											terms_match = false;
											break;
										}
									}
									
									if (!terms_match)
										continue;
									
									present = true;
									
									std::cout << "ALREADY ACHIEVED -=(";
									achieved_bounded_atom.print(std::cout, dtg_graph_->getBindings());
									std::cout << ")=-" << std::endl;
									break;
								}
							}

							if (!present)
							{
								established_facts.push_back(&achieved_bounded_atom);
								std::cout << "-=(";
								achieved_bounded_atom.print(std::cout, dtg_graph_->getBindings());
								std::cout << ")=-" << std::endl;
							}
							to_node_achievers->push_back(&achieved_bounded_atom);
						}
						
						supported_facts_[&to_node]->push_back(to_node_achievers);
//						std::cout << "." << std::endl;
					}
				}
			}
			
			
			
			/// If so mark the transition as "achieved".
			
			/// Add to the from node of that transition the to node - as it is achievable from there.
			
			/// Mark the node of the end point of the transition - but only if it contains unachieved transitions.
		}
		
		// Propagate the achievable nodes per DTG node.
	}
	
	// List all nodes which are reachable.
	
	std::cout << "List of all achievable facts: " << std::endl;
	for (std::vector<const BoundedAtom*>::const_iterator ci  = established_facts.begin(); ci != established_facts.end(); ci++)
	{
		std::cout << "- ";
		(*ci)->print(std::cout, dtg_graph_->getBindings());
		std::cout << std::endl;
	}
}


void DTGReachability::getSupportingFacts(std::vector<std::vector<const BoundedAtom*>* >& supporting_tupples, const std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >& variable_assignments, const std::vector<BoundedAtom*>& atoms_to_achieve, const std::vector<const BoundedAtom*>& initial_supporting_facts, const std::vector<const BoundedAtom*>& initial_facts)
{
	assert (atoms_to_achieve.size() > initial_supporting_facts.size());
	const BoundedAtom* atom_to_process = atoms_to_achieve[initial_supporting_facts.size()];
	
//	std::cout << "[" << initial_supporting_facts.size() << "] The atom to achieve: ";
//	atom_to_process->print(std::cout, dtg_graph_->getBindings());
//	std::cout << std::endl;

	for (std::vector<const BoundedAtom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
	{
		StepID initial_fact_id = (*ci)->getId();
		const Atom& initial_fact = (*ci)->getAtom();
		
		if (dtg_graph_->getBindings().canUnify(initial_fact, initial_fact_id, atom_to_process->getAtom(), atom_to_process->getId()))
		{
//			std::cout << "Initial fact which can unify: ";
//			initial_fact.print(std::cout, dtg_graph_->getBindings(), initial_fact_id);
//			std::cout << std::endl;

			// Check if all terms can be supported.
			bool terms_supported = true;
			std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >* variable_assignments_clone = new std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >(variable_assignments);
			
			for (std::vector<const Term*>::const_iterator ci = atom_to_process->getAtom().getTerms().begin(); ci != atom_to_process->getAtom().getTerms().end(); ci++)
			{
				const Term* atom_term = *ci;
				unsigned int term_index = std::distance(atom_to_process->getAtom().getTerms().begin(), ci);
				
				const std::vector<const Object*>& term_domain_atom_to_process = atom_term->getDomain(atom_to_process->getId(), dtg_graph_->getBindings());
				const std::vector<const Object*>& initial_fact_domain = initial_fact.getTerms()[term_index]->getDomain(initial_fact_id, dtg_graph_->getBindings());

				// Find the assignments made to the term's domain.
				std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >::const_iterator found_domain = variable_assignments_clone->find(&term_domain_atom_to_process);
				
				// If no assignments have been made yet we make them equal to the initial fact's domain.
				if (found_domain == variable_assignments_clone->end())
				{
					(*variable_assignments_clone)[&term_domain_atom_to_process] = &initial_fact_domain;
/*					std::cout << "Bind the " << term_index << "th term to: ";
					for (std::vector<const Object*>::const_iterator ci = initial_fact_domain.begin(); ci != initial_fact_domain.end(); ci++)
					{
						(*ci)->print(std::cout, dtg_graph_->getBindings(), initial_fact_id);
						if (ci + 1 != initial_fact_domain.end())
						{
							std::cout << ", ";
						}
					}
					std::cout << "." << std::endl;*/
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
					const BoundedAtom& new_bounded_atom = BoundedAtom::createBoundedAtom(atom_to_achieve->getAtom(), dtg_graph_->getBindings());
					
					finalized_supporting_facts->push_back(&new_bounded_atom);
					
//					std::cout << " * (" << atom_to_achieve->getAtom().getPredicate().getName();
					for (std::vector<const Term*>::const_iterator ci = atom_to_achieve->getAtom().getTerms().begin(); ci != atom_to_achieve->getAtom().getTerms().end(); ci++)
					{
						const Term* term_of_atom_to_achieve = *ci;
						unsigned int term_index = std::distance(atom_to_achieve->getAtom().getTerms().begin(), ci);
						const Term* new_bounded_atom_term = new_bounded_atom.getAtom().getTerms()[term_index];
						
						const std::vector<const Object*>& variable_domain_of_atom_to_achieve = term_of_atom_to_achieve->getDomain(atom_to_achieve->getId(), dtg_graph_->getBindings());
						const std::vector<const Object*>* possible_assignments = (*variable_assignments_clone)[&variable_domain_of_atom_to_achieve];

						new_bounded_atom_term->makeDomainEqualTo(new_bounded_atom.getId(), *possible_assignments, dtg_graph_->getBindings());
					}
				}
				

				supporting_tupples.push_back(finalized_supporting_facts);
			}
			else
			{
				getSupportingFacts(supporting_tupples, *variable_assignments_clone, atoms_to_achieve, *initial_supporting_facts_clone, initial_facts);
			}
		}
	}
}

};
	
};
