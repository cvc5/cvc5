###############################################################################
# Top contributors (to current version):
#   Aina Niemetz
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
cvc5_add_unit_test_black(attribute_black node)
cvc5_add_unit_test_white(attribute_white node)
cvc5_add_unit_test_black(kind_black node)
cvc5_add_unit_test_black(kind_map_black node)
cvc5_add_unit_test_black(node_black node)
cvc5_add_unit_test_black(node_algorithm_black node)
cvc5_add_unit_test_black(node_algorithms_black node)
cvc5_add_unit_test_black(node_builder_black node)
cvc5_add_unit_test_black(node_manager_black node)
cvc5_add_unit_test_white(node_manager_white node)
cvc5_add_unit_test_black(node_self_iterator_black node)
cvc5_add_unit_test_black(node_traversal_black node)
cvc5_add_unit_test_white(node_white node)
cvc5_add_unit_test_black(symbol_table_black node)
cvc5_add_unit_test_black(type_cardinality_black node)
cvc5_add_unit_test_white(type_node_white node)
