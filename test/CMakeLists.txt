#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Aina Niemetz, Mathias Preiner, Makai Mann
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
#-----------------------------------------------------------------------------#
# Add target 'check', builds and runs
# > unit tests
# > regression tests of levels 0 and 1
# > api tests

add_custom_target(build-tests)

if (BUILD_BINDINGS_PYTHON)
  set(PYTEST_COMMAND "${CMAKE_COMMAND}" "-E" "env" "PYTHONPATH=${PROJECT_SOURCE_DIR}/build/src/api/python"
                     "${PYTHON_EXECUTABLE}" "-m" "pytest" "${PROJECT_SOURCE_DIR}/test/unit/api/python")
else()
  # No-Op if not building with Python bindings
  set(PYTEST_COMMAND ":")
endif()

message("PYTEST_COMMAND=${PYTEST_COMMAND}")

# Note: Do not add custom targets for running tests (regress, apitests,
# units) as dependencies to other run targets. This will result in executing
# tests multiple times. For example, if check would depend on regress it would
# first run the command of the regress target (i.e., run all regression tests)
# and afterwards run the command specified for the check target.
# Dependencies of check are added in the corresponding subdirectories.
add_custom_target(check
  COMMAND
    ctest --output-on-failure -LE "regress[3-4]" -j${CTEST_NTHREADS} $$ARGS
  COMMAND
     ${PYTEST_COMMAND}
  COMMAND_EXPAND_LISTS
  DEPENDS
    build-tests)

#-----------------------------------------------------------------------------#
# Add subdirectories

if (NOT BUILD_LIB_ONLY)
  add_subdirectory(regress)
endif()
add_subdirectory(api EXCLUDE_FROM_ALL)

if(ENABLE_UNIT_TESTING)
  add_subdirectory(unit EXCLUDE_FROM_ALL)

  if(BUILD_SWIG_BINDINGS_JAVA)
    add_subdirectory(java)
  endif()
endif()

if(LFSC_BINARY)
  add_subdirectory(signatures)
endif()
