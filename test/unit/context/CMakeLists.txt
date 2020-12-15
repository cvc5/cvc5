#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
#-----------------------------------------------------------------------------#
# Add unit tests

cvc4_add_unit_test_black(cdlist_black context)
cvc4_add_unit_test_black(cdmap_black context)
cvc4_add_unit_test_white(cdmap_white context)
cvc4_add_unit_test_black(cdo_black context)
cvc4_add_unit_test_black(context_black context)
cvc4_add_unit_test_black(context_mm_black context)
cvc4_add_unit_test_white(context_white context)
