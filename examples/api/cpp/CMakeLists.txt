###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Aina Niemetz, Abdalrhman Mohamed
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

set(CVC5_EXAMPLES_API_CPP
  bags
  bitvectors
  bitvectors_and_arrays
  combination
  datatypes
  extract
  floating_point_arith
  helloworld
  linear_arith
  quickstart
  relations
  sequences
  sets
  strings
  transcendentals
  parser
  parser_sym_manager
  uf
)

foreach(example ${CVC5_EXAMPLES_API_CPP})
  cvc5_add_example(${example} "" "api/cpp")
endforeach()

if(CVC5_USE_COCOA)
  cvc5_add_example(finite_field "" "api/cpp")
endif()

set(SYGUS_EXAMPLES_API_CPP
  sygus-fun
  sygus-inv
)

foreach(example ${SYGUS_EXAMPLES_API_CPP})
  cvc5_add_example(${example} "${example}.cpp utils.h utils.cpp" "api/cpp")
endforeach()
