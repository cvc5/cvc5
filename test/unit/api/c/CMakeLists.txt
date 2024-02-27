###############################################################################
# Top contributors (to current version):
#   Aina Niemetz
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

# Generate and add unit test.
cvc5_add_unit_test_black(capi_kind_black api/c)
cvc5_add_unit_test_black(capi_sort_kind_black api/c)
cvc5_add_unit_test_black(capi_types_black api/c)
