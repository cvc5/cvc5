###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Abdalrhman Mohamed, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

set(CVC5_EXAMPLES_API
  bitvectors
  bitvectors_and_arrays
  combination
  datatypes
  extract
  helloworld
  linear_arith
  quickstart
  sequences
  sets
  strings
  transcendentals
)

foreach(example ${CVC5_EXAMPLES_API})
  cvc5_add_example(${example} "" "api")
endforeach()

set(SYGUS_EXAMPLES_API
  sygus-fun
  sygus-grammar
  sygus-inv
)

foreach(example ${SYGUS_EXAMPLES_API})
  cvc5_add_example(${example} "${example}.cpp utils.h utils.cpp" "api")
endforeach()
