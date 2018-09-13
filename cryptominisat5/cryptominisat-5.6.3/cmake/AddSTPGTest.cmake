# AddSTPGTest(<sourcefile> [<defines> ...])
#
# Adds a GoogleTest to the current test suite (${TESTSUITE})
# with executable name <sourcefile> with the file extension removed and
# the UNIT_TEST_EXE_SUFFIX appended.
# The executable will be linked with libstp.
# Remaining arguments to this function are interpreted as preprocessor macros
# to defines.
#
# e.g.
# AddSTPGTest(mysimpleprogram.cpp FOO=15 BAR=\"a string\")
#
function(AddSTPGTest sourcefile)
    get_filename_component(testname ${sourcefile} NAME_WE)

    # testname has suffix because lit expects this
    set(testname "${testname}${UNIT_TEST_EXE_SUFFIX}")

    add_executable(${testname} EXCLUDE_FROM_ALL ${sourcefile})

    # Add define flags requested by users
    list(LENGTH ARGN LEN_ARGN)
    if(LEN_ARGN GREATER 0)
        set_property(TARGET ${testname} APPEND PROPERTY COMPILE_DEFINITIONS ${ARGN})
        #message(STATUS "Added flags to test ${testname} ${ARGN}")
    endif()

    target_link_libraries(${testname} libstp ${GTEST_BOTH_LIBRARIES})

    # Add dependency so that building the testsuite
    # will cause this test (testname) to be built
    add_dependencies(${TESTSUITE} ${testname})
endfunction()
