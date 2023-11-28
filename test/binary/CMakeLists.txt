###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Andrew V. Jones, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##
include_directories(.)
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

# if we've built using libedit, (--editline) then we want the interactive shell tests
if (USE_EDITLINE)

  # Check for pexpect -- zero return code is success
  execute_process(
    COMMAND ${Python_EXECUTABLE} -c "import pexpect"
    RESULT_VARIABLE PEXPECT_RC
    ERROR_QUIET
  )

  # Add the test if we have pexpect
  if(PEXPECT_RC EQUAL 0)
    add_custom_target(binarytests
      COMMAND ctest --output-on-failure -L "binary" -j${CTEST_NTHREADS} $$ARGS)
    add_test(
      NAME interactive_shell
      COMMAND
      "${Python_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/test/binary/interactive_shell.py"
      WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
    )
    set_tests_properties(interactive_shell PROPERTIES LABELS "binary")
  endif()
endif()
