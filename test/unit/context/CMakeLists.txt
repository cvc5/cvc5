###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Aina Niemetz
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

# Add unit tests.
cvc5_add_unit_test_black(cdlist_black context)
cvc5_add_unit_test_black(cdhashmap_black context)
cvc5_add_unit_test_white(cdhashmap_white context)
cvc5_add_unit_test_black(cdo_black context)
cvc5_add_unit_test_black(context_black context)
cvc5_add_unit_test_black(context_mm_black context)
cvc5_add_unit_test_white(context_white context)
