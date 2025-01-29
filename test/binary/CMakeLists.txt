###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Andrew Reynolds, Daniel Larraz
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
include_directories(.)
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

# if we've built using libedit, (--editline) then we want the interactive shell tests
if (USE_EDITLINE)

  check_python_module(pexpect)

  add_custom_target(binarytests
    COMMAND ctest --output-on-failure -L "binary" -j${CTEST_NTHREADS} $$ARGS)
  add_test(
    NAME interactive_shell
    COMMAND
    "${Python_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/test/binary/interactive_shell.py"
    WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
  )
  set_tests_properties(interactive_shell PROPERTIES LABELS "binary")
  add_test(
    NAME interactive_shell_parser_inc
    COMMAND
    "${Python_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/test/binary/interactive_shell_parser_inc.py"
    WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
  )
  set_tests_properties(interactive_shell_parser_inc PROPERTIES LABELS "binary")
  # TODO (see #10414): test this regardless of the guard
  if (NOT APPLE)
    add_test(
      NAME interactive_shell_define_fun_rec_multiline
      COMMAND
      "${Python_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/test/binary/interactive_shell_define_fun_rec_multiline.py"
      WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
    )
    set_tests_properties(interactive_shell_define_fun_rec_multiline PROPERTIES LABELS "binary")
  endif()
  add_test(
    NAME issue_10258
    COMMAND
    "${Python_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/test/binary/issue_10258.py"
    WORKING_DIRECTORY "${CMAKE_BINARY_DIR}"
  )
  set_tests_properties(issue_10258 PROPERTIES LABELS "binary")
endif()
