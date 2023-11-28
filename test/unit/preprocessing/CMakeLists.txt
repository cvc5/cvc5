###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Aina Niemetz
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
cvc5_add_unit_test_white(pass_bv_gauss_white preprocessing)
cvc5_add_unit_test_white(pass_foreign_theory_rewrite_white preprocessing)
