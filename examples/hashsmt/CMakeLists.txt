#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Mathias Preiner, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
if(Boost_FOUND)
   cvc4_add_example(sha1_inversion
     "sha1_inversion.cpp word.cpp" "hashsmt"
     # arguments to binary (for testing)
     "a" "sha1_inversion.outfile")
endif()

cvc4_add_example(sha1_collision
  "sha1_collision.cpp word.cpp" "hashsmt"
  # arguments to binary (for testing)
  "1" "1" "sha1_collision.outfile")
