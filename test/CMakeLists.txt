#-----------------------------------------------------------------------------#
# Add target 'check', builds and runs
# > unit tests
# > regression tests of levels 0 and 1
# > system tests

add_custom_target(build-tests)
# Since examples are also built and run for testing, we have to add examples
# to the build test dependencies.
add_dependencies(build-tests examples)

# Note: Do not add custom targets for running tests (regress, systemtests,
# units) as dependencies to other run targets. This will result in executing
# tests multiple times. For example, if check would depend on regress it would
# first run the command of the regress target (i.e., run all regression tests)
# and afterwards run the command specified for the check target.
# Dependencies of check are added in the corresponding subdirectories.
add_custom_target(check
  COMMAND
    ctest --output-on-failure -LE "regress[2-4]" -j${CTEST_NTHREADS} $(ARGS)
  DEPENDS
    build-tests)

#-----------------------------------------------------------------------------#
# Add subdirectories

add_subdirectory(regress)
add_subdirectory(system EXCLUDE_FROM_ALL)

if(ENABLE_UNIT_TESTING)
  add_subdirectory(unit EXCLUDE_FROM_ALL)

  if(BUILD_BINDINGS_JAVA)
    add_subdirectory(java)
  endif()
endif()
