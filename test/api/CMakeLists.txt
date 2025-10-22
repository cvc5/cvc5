###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

add_custom_target(build-apitests)
add_dependencies(build-tests build-apitests)

add_subdirectory(c)
add_subdirectory(cpp)
if (BUILD_BINDINGS_PYTHON)
  add_subdirectory(python)
endif()
if (BUILD_BINDINGS_JAVA)
  add_subdirectory(java)
endif()

add_custom_target(apitests
  COMMAND ctest --output-on-failure -L "api" -j${CTEST_NTHREADS} $$ARGS
  DEPENDS build-apitests)