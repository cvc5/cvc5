###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
include_directories(${PROJECT_BINARY_DIR}/src)

# Portfolio uses POSIX fork/wait. After one worker solves, siblings and their
# timeout children must be reaped before the parent exits. --use-portfolio is
# an expert option, so skip safe/stable builds.
if (UNIX AND NOT ENABLE_SAFE_MODE AND NOT ENABLE_STABLE_MODE)
  add_test(
    NAME portfolio_stop_siblings
    COMMAND
    "${Python_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/test/binary/portfolio_stop_siblings.py"
    WORKING_DIRECTORY "${PROJECT_BINARY_DIR}"
  )
  set_tests_properties(portfolio_stop_siblings PROPERTIES LABELS "binary")
endif()

# Convenience target for every test labeled "binary" (portfolio and editline).
# Keep this outside USE_EDITLINE so non-editline builds still have it.
add_custom_target(binarytests
  COMMAND ctest --output-on-failure -L "binary" -j${CTEST_NTHREADS} $$ARGS)

# if we've built using libedit, (--editline) then we want the interactive shell tests
if (USE_EDITLINE)

  check_python_module(pexpect)

  add_test(
    NAME interactive_shell
    COMMAND
    "${Python_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/test/binary/interactive_shell.py"
    WORKING_DIRECTORY "${PROJECT_BINARY_DIR}"
  )
  set_tests_properties(interactive_shell PROPERTIES LABELS "binary")
  add_test(
    NAME interactive_shell_parser_inc
    COMMAND
    "${Python_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/test/binary/interactive_shell_parser_inc.py"
    WORKING_DIRECTORY "${PROJECT_BINARY_DIR}"
  )
  set_tests_properties(interactive_shell_parser_inc PROPERTIES LABELS "binary")
  add_test(
    NAME interactive_shell_define_fun_rec_multiline
    COMMAND
    "${Python_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/test/binary/interactive_shell_define_fun_rec_multiline.py"
    WORKING_DIRECTORY "${PROJECT_BINARY_DIR}"
  )
  set_tests_properties(interactive_shell_define_fun_rec_multiline PROPERTIES LABELS "binary")
  add_test(
    NAME issue_10258
    COMMAND
    "${Python_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/test/binary/issue_10258.py"
    WORKING_DIRECTORY "${PROJECT_BINARY_DIR}"
  )
  set_tests_properties(issue_10258 PROPERTIES LABELS "binary")
  add_test(
    NAME interactive_shell_no_home
    COMMAND
    "${Python_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/test/binary/interactive_shell_no_home.py"
    WORKING_DIRECTORY "${PROJECT_BINARY_DIR}"
  )
  set_tests_properties(interactive_shell_no_home PROPERTIES LABELS "binary")
endif()
