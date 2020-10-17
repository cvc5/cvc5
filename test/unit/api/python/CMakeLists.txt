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

add_test (NAME python-tests
  COMMAND ${PYTHON_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}
  WORKING_DIRECTORY ${PROJECT_BINARY_DIR}/src/api/python
)
