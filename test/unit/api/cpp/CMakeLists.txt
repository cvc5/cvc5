###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Aina Niemetz, Andrew Reynolds
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
cvc5_add_unit_test_black(datatype_api_black api/cpp)
cvc5_add_unit_test_black(grammar_black api/cpp)
cvc5_add_unit_test_black(api_kind_black api/cpp)
cvc5_add_unit_test_black(api_proof_rule_black api/cpp)
cvc5_add_unit_test_black(api_skolem_id_black api/cpp)
cvc5_add_unit_test_black(api_sort_kind_black api/cpp)
cvc5_add_unit_test_black(api_term_manager_black api/cpp)
cvc5_add_unit_test_black(op_black api/cpp)
cvc5_add_unit_test_black(parametric_datatype_black api/cpp)
cvc5_add_unit_test_black(result_black api/cpp)
cvc5_add_unit_test_black(sort_black api/cpp)
cvc5_add_unit_test_black(term_black api/cpp)
cvc5_add_unit_test_white(op_white api/cpp)
cvc5_add_unit_test_white(solver_white api/cpp)
cvc5_add_unit_test_black(synth_result_black api/cpp)
cvc5_add_unit_test_white(term_white api/cpp)
cvc5_add_unit_test_white(api_types_black api/cpp)
cvc5_add_unit_test_black(proof_black api/cpp)
cvc5_add_unit_test_white(command_black api/cpp)
cvc5_add_unit_test_white(symbol_manager_black api/cpp)
cvc5_add_unit_test_white(input_parser_black api/cpp)
cvc5_add_unit_test_black(solver_black api/cpp)

# tests to cover deprecated functions for API coverage build in nightlies
set_source_files_properties(api_deprecated_black.cpp
  PROPERTIES COMPILE_OPTIONS
  "-Wno-deprecated-declarations;-Wno-error=deprecated-declarations")
cvc5_add_unit_test_black(api_deprecated_black api/cpp)
