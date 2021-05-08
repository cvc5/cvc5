###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Mathias Preiner
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

set(EXAMPLES_NRA_TRANSLATE_BIN_DIR ${EXAMPLES_BIN_DIR}/nra-translate)

set(CVC5_EXAMPLES_NRA_TRANSLATE
  normalize
  smt2info
  smt2todreal
  smt2toisat
  smt2tomathematica
  smt2toqepcad
  smt2toredlog
)

foreach(example ${CVC5_EXAMPLES_NRA_TRANSLATE})
  cvc5_add_example(${example} "" "nra-translate"
    # arguments to binary (for testing)
    # input file is required by all tests
    ${CMAKE_CURRENT_SOURCE_DIR}/nra-translate-example-input.smt2
    # This is a dummy argument for smt2toredlog (argument is only printed, can
    # be anything for testing purposes). We pass this to all examples since the
    # other examples ignore additional arguments.
    "foo")
endforeach()
