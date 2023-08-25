###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
cvc5_add_unit_test_black(api_sort_kind_black api/cpp)
cvc5_add_unit_test_black(op_black api/cpp)
cvc5_add_unit_test_black(parametric_datatype_black api/cpp)
cvc5_add_unit_test_black(result_black api/cpp)
cvc5_add_unit_test_black(solver_black api/cpp)
cvc5_add_unit_test_black(sort_black api/cpp)
cvc5_add_unit_test_black(term_black api/cpp)
cvc5_add_unit_test_white(op_white api/cpp)
cvc5_add_unit_test_white(solver_white api/cpp)
cvc5_add_unit_test_black(synth_result_black api/cpp)
cvc5_add_unit_test_white(term_white api/cpp)
cvc5_add_unit_test_white(types_black api/cpp)
