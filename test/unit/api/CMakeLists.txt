#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Aina Niemetz, Andres Noetzli, Makai Mann
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
#-----------------------------------------------------------------------------#
# Add unit tests

cvc4_add_unit_test_black(datatype_api_black api)
cvc4_add_unit_test_black(op_black api)
cvc4_add_unit_test_black(result_black api)
cvc4_add_unit_test_black(solver_black api)
cvc4_add_unit_test_black(sort_black api)
cvc4_add_unit_test_black(term_black api)
cvc4_add_unit_test_black(grammar_black api)
