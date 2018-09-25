# Copyright (c) 2017, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.


find_program(LIT_TOOL
    lit
    DOC "Path to lit tool"
)

if(NOT LIT_TOOL)
    message(FATAL_ERROR "Could not find 'lit' tool. You need to install it by e.g. 'pip install lit' If it's already installed, set LIT_TOOL to the full path for lit")
endif()

# Checking absolute path because if(EXISTS ...) behaviour only well
# defined if path is absolute
IF(NOT IS_ABSOLUTE "${LIT_TOOL}")
    message(FATAL_ERROR "LIT_TOOL must be set to an absolute PATH")
endif()

if(NOT EXISTS "${LIT_TOOL}")
    # Can happen if users environment changes after initial configure
    message(FATAL_ERROR "LIT_TOOL is set but the path does not seem to exist. Try deleting the LIT_TOOL cache variable and reconfiguring")
endif()

set(LIT_ARGS -v CACHE STRING "Arguments to pass to lit")

# -----------------------------------------------------------------------------
# Find GTest library which will be used to drive tests
# -----------------------------------------------------------------------------
# GoogleTest devs don't recommend using a pre-built GTest library
# ( https://code.google.com/p/googletest/wiki/FAQ#Why_is_it_not_recommended_to_install_a_pre-compiled_copy_of_Goog ).
# Because of this, distros like Ubuntu don't provide a pre-built GTest library
# so ``find_package(GTest REQUIRED)`` fails.
#
# Instead it is recommended that projects build their own copy of GTest. Detecting
# the location of GTest source code is probably error prone so using a copy in the
# repository seems like the easiest thing to do. This also has the added benefit that
# everyone uses the same version of GTest.
set(GTEST_PREFIX ${PROJECT_SOURCE_DIR}/utils/gtest)
message(STATUS "NOTE: if adding the 'gtest' subdirectory fails, you need to issue 'git submodule init' and 'git submodule update'")
add_subdirectory(${GTEST_PREFIX} gtest)
set(GTEST_BOTH_LIBRARIES gtest gtest_main)

include_directories(${GTEST_PREFIX}/include)
add_definitions( -DCMS_TESTING_ENABLED )

# Add handy macros/functions
include(AddSTPGTest)
include(AddGTestSuite)

# -----------------------------------------------------------------------------
# -----------------------------------------------------------------------------

if(NOT ONLY_SIMPLE)
    # Tests that drive cryptominisat by using cnf files (e.g. smt2, smt and cvc files)
    add_subdirectory(${PROJECT_SOURCE_DIR}/tests/cnf-files)

    # Needed for fuzz-testing
    add_subdirectory(${PROJECT_SOURCE_DIR}/utils/cnf-utils cnf-utils)
    add_subdirectory(${PROJECT_SOURCE_DIR}/utils/drat-trim drat-trim)
    add_subdirectory(${PROJECT_SOURCE_DIR}/utils/sha1-sat sha1-sat)
    add_subdirectory(${PROJECT_SOURCE_DIR}/utils/minisat minisat)
endif()

add_sanitize_flags()
if (PYTHON_EXECUTABLE AND ZLIB_FOUND AND NOT STATS_NEEDED AND NOT ONLY_SIMPLE)
    add_subdirectory(${PROJECT_SOURCE_DIR}/utils/minisat_only_elim_and_subsume minisat_only_elim_and_subsume)
    add_subdirectory(simp-checks)
endif()


include_directories(
    ${PROJECT_SOURCE_DIR}
)
include_directories(
    ${PROJECT_BINARY_DIR}/cmsat5-src
)

# README test
add_executable(readme_test
    readme_test.cpp
)
target_link_libraries(readme_test
    libcryptominisat5
)
add_test (
    NAME readme_test
    COMMAND readme_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
)

# C bindings test
if (NOT SANITIZE)
    add_executable(c_test
        c_test.c
    )
    target_link_libraries(c_test
        libcryptominisat5
    )
    add_test (
        NAME c_test
        COMMAND c_test
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
endif()

# Multisol test
add_executable(multisol_test
    multisol_test.cpp
)
target_link_libraries(multisol_test
    libcryptominisat5
)
add_test (
    NAME multisol_test
    COMMAND multisol_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
)


if (IPASIR)
    add_executable(ipasir_test
        ipasir_test.cpp
    )
    target_link_libraries(ipasir_test
        ${GTEST_BOTH_LIBRARIES}
        ipasircryptominisat5
    )
    add_test (
        NAME ipasir_test
        COMMAND ipasir_test
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
endif()

#google test harness
set (MY_TESTS
#     clause_alloc_test
    basic_test
    assump_test
    heap_test
    clause_test
    stp_test
    scc_test
    vrepl_test
    clause_cleaner_test
    probe_test
    distiller_all_with_all_test
    distill_long_with_implicit_test
    subsume_impl_test
    comp_find_test
    intree_test
    xorfinder_test
    comphandler_test
    dump_test
    searcher_test
    solver_test
#    undefine_test
)

if (USE_GAUSS)
    set (MY_TESTS ${MY_TESTS}
        # gauss_test
        matrixfinder_test
    )
endif()

foreach(F ${MY_TESTS})
    add_executable(${F}
        ${F}.cpp
    )
    target_link_libraries(${F}
        ${GTEST_BOTH_LIBRARIES}
        libcryptominisat5
    )
    add_test (
        NAME ${F}
        COMMAND ${F}
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
endforeach()
