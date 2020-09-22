#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Aina Niemetz, Yoni Zohar, Alex Ozdemir
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
#-----------------------------------------------------------------------------#
# Add unit tests

cvc4_add_unit_test_black(attribute_black expr)
cvc4_add_unit_test_white(attribute_white expr)
cvc4_add_unit_test_black(expr_manager_public expr)
cvc4_add_unit_test_black(expr_public expr)
cvc4_add_unit_test_black(kind_black expr)
cvc4_add_unit_test_black(kind_map_black expr)
cvc4_add_unit_test_black(node_black expr)
cvc4_add_unit_test_black(node_algorithm_black expr)
cvc4_add_unit_test_black(node_builder_black expr)
cvc4_add_unit_test_black(node_manager_black expr)
cvc4_add_unit_test_white(node_manager_white expr)
cvc4_add_unit_test_black(node_self_iterator_black expr)
cvc4_add_unit_test_black(node_traversal_black expr)
cvc4_add_unit_test_white(node_white expr)
cvc4_add_unit_test_black(symbol_table_black expr)
cvc4_add_unit_test_black(type_cardinality_public expr)
cvc4_add_unit_test_white(type_node_white expr)
