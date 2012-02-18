cmake_minimum_required(VERSION 2.4)

project(val)

find_program(BISON_EXECUTABLE bison)

if(NOT EXISTS ${BISON_EXECUTABLE})
	message("Could not find bison executable.")
endif(NOT EXISTS ${BISON_EXECUTABLE})


FIND_PROGRAM(FLEX_EXECUTABLE flex)

if(NOT EXISTS ${FLEX_EXECUTABLE})
        message("Could not find flex executable.")
endif(NOT EXISTS ${FLEX_EXECUTABLE})

add_custom_command(
       OUTPUT
        ${CMAKE_CURRENT_BINARY_DIR}/lex.yy.cc
       COMMAND
        ${FLEX_EXECUTABLE}
       ARGS
        --outfile=${CMAKE_CURRENT_BINARY_DIR}/lex.yy.cc ${CMAKE_CURRENT_SOURCE_DIR}/pddl+.lex
       DEPENDS
        ${CMAKE_CURRENT_SOURCE_DIR}/pddl+.lex
)

add_custom_command(
       OUTPUT
        ${CMAKE_CURRENT_BINARY_DIR}/pddl+.cpp
       COMMAND
        ${BISON_EXECUTABLE}
       ARGS
        ${CMAKE_CURRENT_SOURCE_DIR}/pddl+.yacc -o ${CMAKE_CURRENT_BINARY_DIR}/pddl+.cpp
       DEPENDS
        ${CMAKE_CURRENT_SOURCE_DIR}/pddl+.yacc
       COMMAND
        ${CMAKE_CURRENT_SOURCE_DIR}/fixyywrap ${CMAKE_CURRENT_BINARY_DIR} ${CMAKE_CURRENT_SOURCE_DIR}
)

include_directories(${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_BINARY_DIR})

set(libInst_SRCS
      pddl+.cpp ptree.cpp SimpleEval.cpp
      FastEnvironment.cpp instantiation.cpp DebugWriteController.cpp
      typecheck.cpp TypedAnalyser.cpp FuncAnalysis.cpp
      TIM.cpp TimSupport.cpp TypeStripWC.cpp
)

add_library(Inst STATIC ${libInst_SRCS})

