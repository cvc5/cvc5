# Sets for the current directory (and below) the testsuite to use.
# This macro should be used with the AddSTPGTest function.
macro(AddGTestSuite TESTSUITENAME)
    set(TESTSUITE "${TESTSUITENAME}") # Unit test group name
    # Setup custom target
    add_custom_target(${TESTSUITE})
    add_dependencies(check ${TESTSUITE})

    if(USE_VALGRIND)
        set(LIT_EXTRA_FLAGS --vg --vg-leak)
    else()
        set(LIT_EXTRA_FLAGS "")
    endif()

    add_custom_command(TARGET ${TESTSUITE}
                       POST_BUILD
                       COMMAND ${LIT_TOOL} ${LIT_ARGS} ${LIT_EXTRA_FLAGS} ${CMAKE_CURRENT_BINARY_DIR}
                       COMMENT "Running ${TESTSUITE}"
                      )

    # Setup lit configuration
    configure_file(${CMAKE_SOURCE_DIR}/tests/lit-unit-tests-common.site.cfg.in
                   ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg
                   @ONLY@
                  )
endmacro()
