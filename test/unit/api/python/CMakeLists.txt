#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Makai Mann
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
#-----------------------------------------------------------------------------#
# Add python bindings unit tests

# Check if the pytest Python module is installed.
execute_process(
  COMMAND
  ${PYTHON_EXECUTABLE} -c "import pytest"
  RESULT_VARIABLE
    RET_PYTEST
  ERROR_QUIET
)

if(RET_PYTEST)
    message(FATAL_ERROR
      "Could not find Python module pytest. Install via `pip install pytest'.")
endif()

#   we create test target 'unit/<output_dir>/myunittest'
#   and run it with 'ctest -R "unit/<output_dir>/myunittest"'.
add_test (NAME unit/api/python/python-tests
  COMMAND ${PYTHON_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/src/api/python
)
