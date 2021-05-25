###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Andrew V. Jones
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find ANTLR3
# ANTLR3_FOUND - should always be true
# ANTLR3 - target for the ANTLR3 runtime
# ANTLR3_COMMAND - command line to run ANTLR3
##

include(deps-helper)

find_file(ANTLR3_JAR NAMES antlr-3.4-complete.jar PATH_SUFFIXES share/java/)
find_path(ANTLR3_INCLUDE_DIR NAMES antlr3.h)
find_library(ANTLR3_RUNTIME NAMES antlr3c)

set(ANTLR3_FOUND_SYSTEM FALSE)
if(ANTLR3_JAR AND ANTLR3_INCLUDE_DIR AND ANTLR3_RUNTIME)
    set(ANTLR3_FOUND_SYSTEM TRUE)

    # Parse ANTLR3 version
    file(STRINGS "${ANTLR3_INCLUDE_DIR}/antlr3config.h" ANTLR3_VERSION REGEX "^#define VERSION \"[0-9.]+\"")
    string(REGEX MATCH "[0-9.]+" ANTLR3_VERSION "${ANTLR3_VERSION}")

    check_system_version("ANTLR3")
endif()

if(NOT ANTLR3_FOUND_SYSTEM)
    check_ep_downloaded("ANTLR3-EP-jar")
    if(NOT ANTLR3-EP-jar_DOWNLOADED)
      check_auto_download("ANTLR3" "")
    endif()

    include(ExternalProject)

    set(ANTLR3_VERSION "3.4")

    # Download antlr generator jar
    ExternalProject_Add(
        ANTLR3-EP-jar
        ${COMMON_EP_CONFIG}
        URL https://www.antlr3.org/download/antlr-${ANTLR3_VERSION}-complete.jar
        URL_HASH SHA1=5cab59d859caa6598e28131d30dd2e89806db57f
        DOWNLOAD_NO_EXTRACT ON
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy
            <SOURCE_DIR>/../antlr-3.4-complete.jar
            <INSTALL_DIR>/share/java/antlr-3.4-complete.jar
        BUILD_BYPRODUCTS <INSTALL_DIR>/share/java/antlr-3.4-complete.jar
    )

    # Download config guess
    ExternalProject_Add(
        ANTLR3-EP-config.guess
        ${COMMON_EP_CONFIG}
        URL "http://git.savannah.gnu.org/gitweb/?p=config.git\\\;a=blob_plain\\\;f=config.guess\\\;hb=HEAD"
        DOWNLOAD_NAME config.guess
        DOWNLOAD_NO_EXTRACT ON
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/../config.guess <INSTALL_DIR>/share/config.guess
        BUILD_BYPRODUCTS <INSTALL_DIR>/share/config.guess
    )

    if(CMAKE_SYSTEM_PROCESSOR MATCHES ".*64$")
        set(64bit "--enable-64bit")
    else()
        unset(64bit)
    endif()

    # Download, build and install antlr3 runtime
    ExternalProject_Add(
        ANTLR3-EP-runtime
        ${COMMON_EP_CONFIG}
        DEPENDS ANTLR3-EP-config.guess
        URL https://www.antlr3.org/download/C/libantlr3c-3.4.tar.gz
        URL_HASH SHA1=faa9ab43ab4d3774f015471c3f011cc247df6a18
        CONFIGURE_COMMAND ${CMAKE_COMMAND} -E copy 
            <SOURCE_DIR>/../config.guess <SOURCE_DIR>/config.guess
        COMMAND sed -i.orig "s/avr | avr32/avr | aarch64 | avr32/"
            <SOURCE_DIR>/config.sub
        COMMAND ${CMAKE_COMMAND} -E copy_directory <SOURCE_DIR>/include include/
        COMMAND <SOURCE_DIR>/configure
            --with-pic
            --disable-antlrdebug
            --prefix=<INSTALL_DIR>
            --srcdir=<SOURCE_DIR>
            --disable-shared
            --enable-static
            ${64bit}
            --host=${TOOLCHAIN_PREFIX}
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libantlr3c.a
    )

    set(ANTLR3_JAR "${DEPS_BASE}/share/java/antlr-3.4-complete.jar")
    set(ANTLR3_INCLUDE_DIR "${DEPS_BASE}/include/")
    set(ANTLR3_RUNTIME "${DEPS_BASE}/lib/libantlr3c.a")
endif()

find_package(Java COMPONENTS Runtime REQUIRED)

set(ANTLR3_FOUND TRUE)
# This may not be a single binary: the EP has a whole commandline
# We thus do not make this an executable target.
# Just call ${ANTLR3_COMMAND} instead.
set(ANTLR3_COMMAND ${Java_JAVA_EXECUTABLE} -cp "${ANTLR3_JAR}" org.antlr.Tool
    CACHE STRING "run ANTLR3" FORCE)

add_library(ANTLR3 STATIC IMPORTED GLOBAL)
set_target_properties(ANTLR3 PROPERTIES IMPORTED_LOCATION "${ANTLR3_RUNTIME}")
set_target_properties(ANTLR3 PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "${ANTLR3_INCLUDE_DIR}")

mark_as_advanced(ANTLR3_BINARY)
mark_as_advanced(ANTLR3_COMMAND)
mark_as_advanced(ANTLR3_FOUND)
mark_as_advanced(ANTLR3_FOUND_SYSTEM)
mark_as_advanced(ANTLR3_INCLUDE_DIR)
mark_as_advanced(ANTLR3_JAR)
mark_as_advanced(ANTLR3_RUNTIME)

if(ANTLR3_FOUND_SYSTEM)
    message(STATUS "Found ANTLR3 runtime: ${ANTLR3_RUNTIME}")
    message(STATUS "Found ANTLR3 JAR: ${ANTLR3_JAR}")
else()
    message(STATUS "Building ANTLR3 runtime: ${ANTLR3_RUNTIME}")
    message(STATUS "Downloading ANTLR3 JAR: ${ANTLR3_JAR}")
    add_dependencies(ANTLR3 ANTLR3-EP-runtime ANTLR3-EP-jar)
endif()
