###############################################################################
# Top contributors (to current version):
#   Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Generate and add unit test.
cvc5_add_unit_test_black(capi_command_black api/c)
cvc5_add_unit_test_black(capi_datatype_black api/c)
cvc5_add_unit_test_black(capi_grammar_black api/c)
cvc5_add_unit_test_black(capi_kind_black api/c)
cvc5_add_unit_test_black(capi_input_parser_black api/c)
cvc5_add_unit_test_black(capi_op_black api/c)
cvc5_add_unit_test_black(capi_parametric_datatype_black api/c)
cvc5_add_unit_test_black(capi_proof_black api/c)
cvc5_add_unit_test_black(capi_proof_rule_black api/c)
cvc5_add_unit_test_black(capi_result_black api/c)
cvc5_add_unit_test_black(capi_skolem_id_black api/c)
cvc5_add_unit_test_black(capi_solver_black api/c)
cvc5_add_unit_test_black(capi_sort_black api/c)
cvc5_add_unit_test_black(capi_sort_kind_black api/c)
cvc5_add_unit_test_black(capi_statistics_black api/c)
cvc5_add_unit_test_black(capi_symbol_manager_black api/c)
cvc5_add_unit_test_black(capi_synth_result_black api/c)
cvc5_add_unit_test_black(capi_term_black api/c)
cvc5_add_unit_test_black(capi_term_manager_black api/c)
cvc5_add_unit_test_black(capi_types_black api/c)

# suppress deprecated warnings to not error in CI
set_source_files_properties(capi_uncovered_black.cpp
  PROPERTIES COMPILE_OPTIONS
  "-Wno-deprecated-declarations;-Wno-error=deprecated-declarations")
cvc5_add_unit_test_black(capi_uncovered_black api/c)
