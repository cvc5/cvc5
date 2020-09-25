#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Aina Niemetz, Gereon Kremer, Andres Noetzli
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
#-----------------------------------------------------------------------------#
# Add unit tests

cvc4_add_unit_test_white(array_store_all_white util)
cvc4_add_unit_test_white(assert_white util)
cvc4_add_unit_test_black(binary_heap_black util)
cvc4_add_unit_test_black(bitvector_black util)
cvc4_add_unit_test_black(boolean_simplification_black util)
cvc4_add_unit_test_black(cardinality_public util)
cvc4_add_unit_test_white(check_white util)
cvc4_add_unit_test_black(configuration_black util)
cvc4_add_unit_test_black(datatype_black util)
cvc4_add_unit_test_black(exception_black util)
cvc4_add_unit_test_black(integer_black util)
cvc4_add_unit_test_white(integer_white util)
cvc4_add_unit_test_black(output_black util)
cvc4_add_unit_test_black(rational_black util)
cvc4_add_unit_test_white(rational_white util)
if(CVC4_USE_POLY_IMP)
cvc4_add_unit_test_black(real_algebraic_number_black util)
endif()
cvc4_add_unit_test_black(stats_black util)
