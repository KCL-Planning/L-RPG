


/*
 * THIS SOURCE CODE IS SUPPLIED  ``AS IS'' WITHOUT WARRANTY OF ANY KIND, 
 * AND ITS AUTHOR AND THE JOURNAL OF ARTIFICIAL INTELLIGENCE RESEARCH 
 * (JAIR) AND JAIR'S PUBLISHERS AND DISTRIBUTORS, DISCLAIM ANY AND ALL 
 * WARRANTIES, INCLUDING BUT NOT LIMITED TO ANY IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, AND
 * ANY WARRANTIES OR NON INFRINGEMENT.  THE USER ASSUMES ALL LIABILITY AND
 * RESPONSIBILITY FOR USE OF THIS SOURCE CODE, AND NEITHER THE AUTHOR NOR
 * JAIR, NOR JAIR'S PUBLISHERS AND DISTRIBUTORS, WILL BE LIABLE FOR 
 * DAMAGES OF ANY KIND RESULTING FROM ITS USE.  Without limiting the 
 * generality of the foregoing, neither the author, nor JAIR, nor JAIR's
 * publishers and distributors, warrant that the Source Code will be 
 * error-free, will operate without interruption, or will meet the needs 
 * of the user.
 */










/*********************************************************************
 *
 * File: search.h
 *
 * Description: headers of routines that search the state space
 *
 *              ADL version, Enforced Hill-climbing enhanced with
 *                           Goal-adders deletion heuristic
 *
 * Author: Joerg Hoffmann 2000
 *
 *********************************************************************/ 






#ifndef _SEARCH_H
#define _SEARCH_H

Bool do_enforced_hill_climbing( State *start, State *end, int (*getHeuristicFunction)(State* from, State* to), int* nr_states_visited);



Bool search_for_better_state( State *S, int h, State *S_, int *h_, int (*getHeuristicFunction)(State* from, State* to) );
void add_to_ehc_space( State *S, int op, EhcNode *father, int new_goal );
int expand_first_node( int h , int (*getHeuristicFunction)(State* from, State* to) );



void hash_ehc_node( EhcNode *n );
Bool ehc_state_hashed( State *S );
Bool same_state( State *S1, State *S2 ) ;
int state_sum( State *S );
void reset_ehc_hash_entrys( void );



void extract_plan_fragment( State *S );
PlanHashEntry *hash_plan_state( State *S, int step );
PlanHashEntry *plan_state_hashed( State *S );



Bool new_goal_gets_deleted( EhcNode *n );



Bool do_best_first_search( int (*getHeuristicFunction)(State* from, State* to), int* nr_states_visited );
void add_to_bfs_space( State *S, int op, BfsNode *father, int (*getHeuristicFunction)(State* from, State* to) );
void extract_plan( BfsNode *last );



void hash_bfs_node( BfsNode *n );
Bool bfs_state_hashed( State *S );



int result_to_dest( State *dest, State *source, int op );
void do_axiom_update( State *dest );
void source_to_dest( State *dest, State *source );
void copy_source_to_dest( State *dest, State *source );
void print_state( State S );



#endif /* _SEARCH_H */
