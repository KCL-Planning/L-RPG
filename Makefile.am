## Process this file with automake to produce Makefile.in
##
## Copyright (C) 2002-2004 Carnegie Mellon University
## Written by H�kan L. S. Younes.
##
## Permission is hereby granted to distribute this software for
## non-commercial research purposes, provided that this copyright
## notice is included with any such distribution.

## THIS SOFTWARE IS PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND,
## EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE
## IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
## PURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE
## SOFTWARE IS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU
## ASSUME THE COST OF ALL NECESSARY SERVICING, REPAIR OR CORRECTION.
##
## $Id: Makefile.am,v 1.6 2003/03/01 18:56:34 lorens Rel lorens $

AUTOMAKE_OPTIONS = subdir-objects

bin_PROGRAMS = mypop
mypop_SOURCES = VALfiles/DebugWriteController.cpp VALfiles/FastEnvironment.cpp \
	VALfiles/FuncAnalysis.cpp VALfiles/SASActions.cpp VALfiles/SimpleEval.cpp VALfiles/TIM.cpp \
	VALfiles/TimSupport.cpp VALfiles/ToFunction.cpp VALfiles/TypedAnalyser.cpp \
	VALfiles/instantiation.cpp VALfiles/pddl+.cpp VALfiles/ptree.cpp VALfiles/typecheck.cpp \
	sas/dtg_manager.cpp sas/dtg_node.cpp sas/transition.cpp sas/causal_graph.cpp \
	sas/dtg_graph.cpp sas/property_space.cpp sas/recursive_function.cpp \
	heuristics/dtg_reachability.cpp heuristics/equivalent_object_group.cpp heuristics/reachable_tree.cpp \
	utility/memory_pool.cpp \
	action_manager.cpp bindings_propagator.cpp formula.cpp mypop.cpp parser_utils.cpp \
	plan.cpp plan_bindings.cpp plan_flaws.cpp plan_orderings.cpp planner.cpp \
	predicate_manager.cpp relaxed_planning_graph.cpp simple_flaw_selector.cpp term_manager.cpp \
	type_manager.cpp
	

mypop_LDADD = @LIBOBJS@
mypop_CXXFLAGS = -Wall -Werror -O3 -DNDEBUG

YFLAGS = -d
noinst_HEADERS = exceptions.h flaw_selector.h manager.h planner.h \
	pointers.h predicate_manager.h relaxed_planning_graph.h
