###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Add unit tests.
cvc5_add_unit_test_white(cnf_stream_white prop)
cvc5_add_unit_test_white(cadical_propagator_white prop)
# The propagator test includes CaDiCaL headers and constructs a CaDiCaL::Solver
# directly. The cvc5 library only exposes CaDiCaL privately, so link the CaDiCaL
# target explicitly to get its include directories and symbols.
if(TARGET cadical_propagator_white)
  target_link_libraries(cadical_propagator_white PUBLIC CaDiCaL)
endif()
