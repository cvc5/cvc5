#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Mathias Preiner, Abdalrhman Mohamed, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
set(CVC4_EXAMPLES_API
  bitvectors
  bitvectors_and_arrays
  combination
  datatypes
  extract
  helloworld
  linear_arith
  sets
  sequences
  strings
  sygus-fun
  sygus-grammar
  sygus-inv
)

foreach(example ${CVC4_EXAMPLES_API})
  cvc4_add_example(${example} "" "api")
endforeach()
