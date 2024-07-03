###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Mathias Preiner, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

#-----------------------------------------------------------------------------#
# libcvc5parser source files

set(libcvc5parserapi_src_files
  ../api/c/cvc5_parser.cpp
  ../api/cpp/cvc5_parser.cpp
)

set(libcvc5parser_src_files
  commands.cpp
  commands.h
  command_status.cpp
  command_status.h
  input.cpp
  input.h
  lexer.cpp
  lexer.h
  parser.cpp
  parser.h
  parse_op.cpp
  parse_op.h
  parser_state.cpp
  parser_state.h
  parser_utils.cpp
  parser_utils.h
  smt2/smt2_state.cpp
  smt2/smt2_state.h
  smt2/smt2_cmd_parser.cpp
  smt2/smt2_cmd_parser.h
  smt2/smt2_lexer.cpp
  smt2/smt2_lexer.h
  smt2/smt2_cmd_parser.cpp
  smt2/smt2_cmd_parser.h
  smt2/smt2_parser.cpp
  smt2/smt2_parser.h
  smt2/smt2_term_parser.cpp
  smt2/smt2_term_parser.h
  sym_manager.cpp
  sym_manager.h
  symbol_table.cpp
  symbol_table.h
  tokens.cpp
  tokens.h
)

#-----------------------------------------------------------------------------#
# libcvc5parser configuration

add_library(cvc5parser-objs OBJECT ${libcvc5parser_src_files})
set_target_properties(cvc5parser-objs PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_compile_definitions(cvc5parser-objs PUBLIC -D__BUILDING_CVC5PARSERLIB -Dcvc5_obj_EXPORTS)

add_library(cvc5parserapi-objs OBJECT ${libcvc5parserapi_src_files})
set_target_properties(cvc5parserapi-objs PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_compile_definitions(cvc5parserapi-objs PUBLIC -D__BUILDING_CVC5LIB -Dcvc5_obj_EXPORTS)

add_dependencies(cvc5parser-objs gen-expr gen-options)
add_dependencies(cvc5parserapi-objs cvc5parser-objs gen-expr)

add_library(cvc5parser
  $<TARGET_OBJECTS:cvc5parser-objs>
  $<TARGET_OBJECTS:cvc5parserapi-objs>
)
if(BUILD_SHARED_LIBS)
  set_target_properties(cvc5parser PROPERTIES SOVERSION ${CVC5_SOVERSION})
endif()

set_target_properties(cvc5parser PROPERTIES OUTPUT_NAME cvc5parser)
target_link_libraries(cvc5parser PRIVATE cvc5)

# On Windows, CMake's default install action places
# DLLs into the runtime path (by default "bin")
install(TARGETS cvc5parser EXPORT cvc5-targets)
