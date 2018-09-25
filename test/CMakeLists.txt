#-----------------------------------------------------------------------------#
# Add subdirectories

add_subdirectory(regress)
add_subdirectory(system EXCLUDE_FROM_ALL)

if(BUILD_BINDINGS_JAVA)
  add_subdirectory(java)
endif()

if(ENABLE_UNIT_TESTING)
  add_subdirectory(unit EXCLUDE_FROM_ALL)
endif()

#-----------------------------------------------------------------------------#
# Add target 'check', builds and runs
# > unit tests
# > regression tests of levels 0 and 1
# > system tests

add_custom_target(check
  COMMAND
    ctest --output-on-failure -LE "regress[2-4]" -j${CTEST_NTHREADS} $(ARGS)
  DEPENDS regress systemtests)
if(BUILD_BINDINGS_JAVA)
  add_dependencies(check cvc4javatests)
endif()
if(ENABLE_UNIT_TESTING)
  add_dependencies(check units)
endif()
