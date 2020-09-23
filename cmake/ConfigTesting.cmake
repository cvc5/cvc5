#####################
## ConfigTesting.cmake
## Top contributors (to current version):
##   Aina Niemetz, Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# OPTLEVEL=2
set(OPTIMIZATION_LEVEL 2)
# enable_debug_symbols=yes
cvc4_set_option(ENABLE_DEBUG_SYMBOLS ON)
# enable_statistics=yes
cvc4_set_option(ENABLE_STATISTICS ON)
# enable_assertions=yes
cvc4_set_option(ENABLE_ASSERTIONS ON)
# enable_proof=yes
cvc4_set_option(ENABLE_PROOFS ON)
# enable_tracing=yes
cvc4_set_option(ENABLE_TRACING ON)
# enable_dumping=yes
cvc4_set_option(ENABLE_DUMPING ON)
# enable_muzzle=no
cvc4_set_option(ENABLE_MUZZLE OFF)
# enable_valgrind=no
cvc4_set_option(ENABLE_UNIT_TESTING ON)
