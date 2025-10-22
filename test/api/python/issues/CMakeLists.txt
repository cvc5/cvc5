###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
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

cvc5_add_python_api_test(issue5074 "issues")
cvc5_add_python_api_test(issue6111 "issues")
cvc5_add_python_api_test(proj-issue306 "issues")

if (NOT ENABLE_SAFE_MODE AND NOT ENABLE_STABLE_MODE)
  cvc5_add_python_api_test(issue4889 "issues")
endif()
