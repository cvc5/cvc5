###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Andrew Reynolds, Aina Niemetz
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
cvc5_add_unit_test_black(interactive_shell_black main)
cvc5_add_unit_test_black(interactive_shell_sygus_black main)
