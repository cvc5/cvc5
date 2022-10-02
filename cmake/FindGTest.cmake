###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find GTest
##

include(deps-helper)

find_path(GTest_INCLUDE_DIR NAMES gtest/gtest.h)
find_library(GTest_LIBRARIES NAMES gtest)
find_library(GTest_MAIN_LIBRARIES NAMES gtest_main)

set(GTest_FOUND_SYSTEM FALSE)
if(GTest_INCLUDE_DIR AND GTest_LIBRARIES AND GTest_MAIN_LIBRARIES)
    set(GTest_FOUND_SYSTEM TRUE)
endif()

if(NOT GTest_FOUND_SYSTEM)
    check_ep_downloaded("GTest-EP")
    if(NOT GTest-EP_DOWNLOADED)
      check_auto_download("GTest" "")
    endif()

    include(ExternalProject)

    set(GTest_VERSION "1.11.0")

    ExternalProject_Add(
        GTest-EP
        ${COMMON_EP_CONFIG}
        URL https://github.com/google/googletest/archive/refs/tags/release-${GTest_VERSION}.tar.gz
        URL_HASH SHA1=7b100bb68db8df1060e178c495f3cbe941c9b058
        DOWNLOAD_NAME gtest.tar.gz
        CMAKE_ARGS
          -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
          -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
        BUILD_COMMAND ${CMAKE_COMMAND} --build .
            --config ${CMAKE_BUILD_TYPE} --target gtest
        COMMAND ${CMAKE_COMMAND} --build .
            --config ${CMAKE_BUILD_TYPE} --target gtest_main
        BUILD_BYPRODUCTS
            <INSTALL_DIR>/lib/libgtest.a
            <INSTALL_DIR>/lib/libgtest_main.a
    )

    set(GTest_INCLUDE_DIR "${DEPS_BASE}/include/")
    set(GTest_LIBRARIES "${DEPS_BASE}/lib/libgtest.a")
    set(GTest_MAIN_LIBRARIES "${DEPS_BASE}/lib/libgtest_main.a")
endif()

set(GTest_FOUND TRUE)

add_library(GTest::GTest STATIC IMPORTED GLOBAL)
set_target_properties(GTest::GTest PROPERTIES
    IMPORTED_LOCATION "${GTest_LIBRARIES}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${GTest_INCLUDE_DIR}"
)

add_library(GTest::Main STATIC IMPORTED GLOBAL)
set_target_properties(GTest::Main PROPERTIES
    IMPORTED_LOCATION "${GTest_MAIN_LIBRARIES}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${GTest_INCLUDE_DIR}"
)

find_package(Threads QUIET)
if(TARGET Threads::Threads)
    set_target_properties(GTest::GTest PROPERTIES
        INTERFACE_LINK_LIBRARIES Threads::Threads)
endif()

mark_as_advanced(GTest_FOUND)
mark_as_advanced(GTest_FOUND_SYSTEM)
mark_as_advanced(GTest_INCLUDE_DIR)
mark_as_advanced(GTest_LIBRARIES)
mark_as_advanced(GTest_MAIN_LIBRARIES)

if(GTest_FOUND_SYSTEM)
    message(STATUS "Found GTest ${GTest_VERSION}: ${GTest_LIBRARIES}")
else()
    message(STATUS "Building GTest ${GTest_VERSION}: ${GTest_LIBRARIES}")
    add_dependencies(GTest::GTest GTest-EP)
    add_dependencies(GTest::Main GTest-EP)
endif()
