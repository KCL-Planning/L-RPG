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
#SUBDIRS = FF-X

#bin_PROGRAMS = mypop mypopd mypopext mypopdext
bin_PROGRAMS = mypopext mypopdext
mypop_SOURCES = VALfiles/DebugWriteController.cpp VALfiles/FastEnvironment.cpp \
	VALfiles/FuncAnalysis.cpp VALfiles/SASActions.cpp VALfiles/SimpleEval.cpp VALfiles/TIM.cpp \
	VALfiles/TimSupport.cpp VALfiles/ToFunction.cpp VALfiles/TypedAnalyser.cpp \
	VALfiles/instantiation.cpp VALfiles/pddl+.cpp VALfiles/ptree.cpp VALfiles/typecheck.cpp \
	VALfiles/ValidatorAPI.cpp VALfiles/Validator.cpp VALfiles/Action.cpp VALfiles/Proposition.cpp \
	VALfiles/FuncExp.cpp VALfiles/RepairAdvice.cpp VALfiles/State.cpp \
	VALfiles/Plan.cpp VALfiles/Ownership.cpp VALfiles/Environment.cpp VALfiles/Events.cpp \
	VALfiles/Polynomial.cpp VALfiles/TrajectoryConstraints.cpp VALfiles/RobustAnalyse.cpp \
	VALfiles/PrettyPrinter.cpp VALfiles/random.cpp VALfiles/LaTeXSupport.cpp VALfiles/Utils.cpp \
	sas/lifted_dtg.cpp sas/property_space.cpp sas/causal_graph.cpp \
	heuristics/dtg_reachability.cpp heuristics/equivalent_object_group.cpp heuristics/reachable_tree.cpp \
	heuristics/fact_set.cpp heuristics/cg_heuristic.cpp heuristics/heuristic_interface.cpp \
	utility/memory_pool.cpp \
	action_manager.cpp bindings_propagator.cpp formula.cpp mypop.cpp parser_utils.cpp \
	plan.cpp plan_bindings.cpp plan_flaws.cpp plan_orderings.cpp planner.cpp \
	predicate_manager.cpp relaxed_planning_graph.cpp simple_flaw_selector.cpp term_manager.cpp \
	type_manager.cpp fc_planner.cpp
mypopd_SOURCES = ${mypop_SOURCES}
mypopext_SOURCES = ${mypop_SOURCES}
mypopdext_SOURCES = ${mypop_SOURCES}

mypop_LDADD = @LIBOBJS@
mypopd_LDADD = @LIBOBJS@
mypopext_LDADD = @LIBOBJS@
mypopdext_LDADD = @LIBOBJS@
mypop_CXXFLAGS = -Wall -Werror -O3 -DNDEBUG
mypopd_CXXFLAGS = -Wall -Werror -g
mypopext_CXXFLAGS = -Wall -Werror -O3 -DNDEBUG
mypopdext_CXXFLAGS = -Wall -Werror -g

YFLAGS = -d
noinst_HEADERS = exceptions.h flaw_selector.h manager.h planner.h \
	pointers.h predicate_manager.h relaxed_planning_graph.h
