#####################
## ConfigProduction.cmake
## Top contributors (to current version):
##   Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# OPTLEVEL=3
set(OPTIMIZATION_LEVEL 3)
# enable_debug_symbols=no
cvc4_set_option(ENABLE_DEBUG_SYMBOLS OFF)
# enable_statistics=yes
cvc4_set_option(ENABLE_STATISTICS ON)
# enable_assertions=no
cvc4_set_option(ENABLE_ASSERTIONS OFF)
# enable_proof=yes
cvc4_set_option(ENABLE_PROOFS ON)
# enable_tracing=no
cvc4_set_option(ENABLE_TRACING OFF)
# enable_dumping=yes
cvc4_set_option(ENABLE_DUMPING ON)
# enable_muzzle=no
cvc4_set_option(ENABLE_MUZZLE OFF)
# enable_valgrind=no
cvc4_set_option(ENABLE_UNIT_TESTING OFF)
