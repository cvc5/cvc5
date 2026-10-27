find_program(LCOV_BINARY lcov REQUIRED)
find_program(GENHTML_BINARY NAMES genhtml REQUIRED)
find_program(FASTCOV_BINARY fastcov REQUIRED)

set(COVERAGE_COMPILER_FLAGS "-g -O0 --coverage -fprofile-arcs -ftest-coverage"
    CACHE INTERNAL "")

##
# Add compilers flags for code coverage.
##
function(append_coverage_compiler_flags)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${COVERAGE_COMPILER_FLAGS}" PARENT_SCOPE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${COVERAGE_COMPILER_FLAGS}" PARENT_SCOPE)
  message(STATUS "Appending code coverage compiler flags: ${COVERAGE_COMPILER_FLAGS}")
endfunction()

##
# Sets up code coverage targets NAME and NAME-reset
#
# NAME-reset: Reset code coverage counters to zero.
# NAME: Generate code coverage report since the last reset.
#
# Options:
#   NAME: name of the target
#   DEPENDENCIES: list of dependencies
#   PATHS: additional source code directories to include in the report
#
##
function(setup_code_coverage_fastcov)
  set(options NONE)
  set(oneValueArgs NAME PATH)
  set(multiValueArgs DEPENDENCIES EXCLUDE)
  cmake_parse_arguments(
    COVERAGE "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

  set(EXCLUDES -e /usr/include)
  foreach(DIR ${COVERAGE_EXCLUDE})
    list(APPEND EXCLUDES "${DIR}")
    message(STATUS "Exclude ${DIR} in coverage reports")
  endforeach()

  if(DEFINED ENV{FASTCOV_PARALLEL_JOBS})
    set(FASTCOV_PARALLEL_JOBS $ENV{FASTCOV_PARALLEL_JOBS})
  else()
    include(ProcessorCount)
    ProcessorCount(FASTCOV_PARALLEL_JOBS)
  endif()

  add_custom_target(${COVERAGE_NAME}-reset
    COMMAND
      ${FASTCOV_BINARY} -d ${COVERAGE_PATH} ${EXCLUDES} --zerocounters
          -j${FASTCOV_PARALLEL_JOBS}
    COMMENT
      "Resetting code coverage counters to zero."
  )

  add_custom_target(${COVERAGE_NAME}-json
    COMMAND
      ${FASTCOV_BINARY}
          -b -d ${COVERAGE_PATH} ${EXCLUDES} -o coverage.json
          -j${FASTCOV_PARALLEL_JOBS} -X
    DEPENDS
      ${COVERAGE_DEPENDENCIES}
    COMMENT
      "Generate code coverage JSON report."
  )

  add_custom_target(${COVERAGE_NAME}
    COMMAND
      ${FASTCOV_BINARY} -C coverage.json --lcov -o coverage.info
    COMMAND
      ${GENHTML_BINARY} --branch-coverage --demangle-cpp --no-prefix -o coverage coverage.info
    DEPENDS
      coverage-json
    COMMENT
      "Generate code coverage report."
  )
endfunction()
