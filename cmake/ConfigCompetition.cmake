#####################
## ConfigCompetition.cmake
## Top contributors (to current version):
##   Aina Niemetz, Andres Noetzli, Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
add_definitions(-DCVC4_COMPETITION_MODE)
add_check_c_cxx_flag("-funroll-all-loops")
add_check_c_cxx_flag("-fexpensive-optimizations")
add_check_c_cxx_flag("-fno-enforce-eh-specs")
# OPTLEVEL=9
set(OPTIMIZATION_LEVEL 9)
# enable_debug_symbols=no
cvc4_set_option(ENABLE_DEBUG_SYMBOLS OFF)
# enable_statistics=no
cvc4_set_option(ENABLE_STATISTICS OFF)
# enable_assertions=no
cvc4_set_option(ENABLE_ASSERTIONS OFF)
# enable_proof=no
cvc4_set_option(ENABLE_PROOFS OFF)
# enable_tracing=no
cvc4_set_option(ENABLE_TRACING OFF)
# enable_dumping=no
cvc4_set_option(ENABLE_DUMPING OFF)
# enable_muzzle=yes
cvc4_set_option(ENABLE_MUZZLE ON)
# enable_valgrind=no
# enable_shared=no
cvc4_set_option(ENABLE_SHARED OFF)
cvc4_set_option(ENABLE_UNIT_TESTING OFF)

# By default, we include all dependencies in our competition build that are
# required to achieve the best performance
set(ENABLE_GPL ON)
cvc4_set_option(USE_CADICAL ON)
cvc4_set_option(USE_CLN ON)
cvc4_set_option(USE_CRYPTOMINISAT ON)
cvc4_set_option(USE_EDITLINE OFF)
cvc4_set_option(USE_GLPK ON)
cvc4_set_option(USE_SYMFPU ON)
