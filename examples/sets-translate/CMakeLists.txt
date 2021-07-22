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

if(Boost_FOUND)
  cvc5_add_example(sets2arrays
    "sets_translate.cpp" "sets-translate"
    # argument to binary (for testing)
    ${CMAKE_CURRENT_SOURCE_DIR}/sets-translate-example-input.smt2)

  cvc5_add_example(sets2axioms
    "sets_translate.cpp" "sets-translate"
    # argument to binary (for testing)
    ${CMAKE_CURRENT_SOURCE_DIR}/sets-translate-example-input.smt2)
  target_compile_definitions(sets2axioms PRIVATE -DENABLE_AXIOMS)
endif()

