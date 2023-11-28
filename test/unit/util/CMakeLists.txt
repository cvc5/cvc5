###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Aina Niemetz
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

# Add unit tests.
cvc5_add_unit_test_white(array_store_all_white util)
cvc5_add_unit_test_white(assert_white util)
cvc5_add_unit_test_black(binary_heap_black util)
cvc5_add_unit_test_black(bitvector_black util)
cvc5_add_unit_test_black(boolean_simplification_black util)
cvc5_add_unit_test_black(cardinality_black util)
cvc5_add_unit_test_white(check_white util)
cvc5_add_unit_test_black(configuration_black util)
cvc5_add_unit_test_black(datatype_black util)
cvc5_add_unit_test_white(didyoumean_black util)
cvc5_add_unit_test_black(exception_black util)
cvc5_add_unit_test_black(floatingpoint_black util)
cvc5_add_unit_test_black(integer_black util)
cvc5_add_unit_test_white(integer_white util)
cvc5_add_unit_test_black(output_black util)
cvc5_add_unit_test_black(rational_black util)
cvc5_add_unit_test_white(rational_white util)
if(CVC5_USE_POLY_IMP)
cvc5_add_unit_test_black(real_algebraic_number_black util)
endif()
cvc5_add_unit_test_black(stats_black util)
