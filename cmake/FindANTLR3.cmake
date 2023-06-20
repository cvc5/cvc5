###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Andres Noetzli, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
find_library(ANTLR3_LIBRARIES NAMES antlr3c)

set(ANTLR3_FOUND_SYSTEM FALSE)
if(ANTLR3_JAR AND ANTLR3_INCLUDE_DIR AND ANTLR3_LIBRARIES)
    set(ANTLR3_FOUND_SYSTEM TRUE)

    # Parse ANTLR3 version
    file(STRINGS "${ANTLR3_INCLUDE_DIR}/antlr3config.h" ANTLR3_VERSION REGEX "^#define VERSION \"[0-9.]+\"")
    string(REGEX MATCH "[0-9.]+" ANTLR3_VERSION "${ANTLR3_VERSION}")

    check_system_version("ANTLR3")
endif()

if(NOT BUILD_SHARED_LIBS AND ANTLR3_FOUND_SYSTEM)
  force_static_library()
  find_library(ANTLR3_STATIC_LIBRARIES NAMES antlr3c)
  if(NOT ANTLR3_STATIC_LIBRARIES)
    set(ANTLR3_FOUND_SYSTEM FALSE)
  endif()
  reset_force_static_library()
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
            <DOWNLOADED_FILE>
            <INSTALL_DIR>/share/java/antlr-3.4-complete.jar
        BUILD_BYPRODUCTS <INSTALL_DIR>/share/java/antlr-3.4-complete.jar
    )

    # Download config guess
    ExternalProject_Add(
        ANTLR3-EP-config.guess
        ${COMMON_EP_CONFIG}
        URL "https://git.savannah.gnu.org/cgit/config.git/plain/config.guess"
        DOWNLOAD_NAME config.guess
        DOWNLOAD_NO_EXTRACT ON
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy
          <DOWNLOADED_FILE>
          <INSTALL_DIR>/share/config.guess
        BUILD_BYPRODUCTS <INSTALL_DIR>/share/config.guess
    )

    # Download config sub
    ExternalProject_Add(
        ANTLR3-EP-config.sub
        ${COMMON_EP_CONFIG}
        URL "https://git.savannah.gnu.org/cgit/config.git/plain/config.sub"
        DOWNLOAD_NAME config.sub
        DOWNLOAD_NO_EXTRACT ON
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy
          <DOWNLOADED_FILE>
          <INSTALL_DIR>/share/config.sub
        BUILD_BYPRODUCTS <INSTALL_DIR>/share/config.sub
    )

    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
        set(64bit "--enable-64bit")
    else()
        unset(64bit)
    endif()
 
    set(compilers "")
    if (CMAKE_CROSSCOMPILING_MACOS)
      # We set the CC and CXX flags as suggested in
      # https://github.com/antlr/antlr3/blob/5c2a916a10139cdb5c7c8851ee592ed9c3b3d4ff/runtime/C/INSTALL#L133-L135.
      set(compilers
        "CC=${CMAKE_C_COMPILER} -arch ${CMAKE_OSX_ARCHITECTURES}"
        "CXX=${CMAKE_CXX_COMPILER} -arch ${CMAKE_OSX_ARCHITECTURES}")
    endif()

    # Download, build and install antlr3 runtime
    ExternalProject_Add(
        ANTLR3-EP-runtime
        ${COMMON_EP_CONFIG}
        BUILD_IN_SOURCE ON
        DEPENDS ANTLR3-EP-config.guess ANTLR3-EP-config.sub
        URL https://www.antlr3.org/download/C/libantlr3c-3.4.tar.gz
        URL_HASH SHA1=faa9ab43ab4d3774f015471c3f011cc247df6a18
        PATCH_COMMAND ${CMAKE_COMMAND} -E copy
          <INSTALL_DIR>/share/config.guess
          <SOURCE_DIR>/config.guess
        COMMAND ${CMAKE_COMMAND} -E copy
          <INSTALL_DIR>/share/config.sub
          <SOURCE_DIR>/config.sub
        CONFIGURE_COMMAND
          ${CONFIGURE_CMD_WRAPPER} ${SHELL} <SOURCE_DIR>/configure
            ${compilers}
            --with-pic
            --disable-antlrdebug
            --disable-abiflags
            --prefix=<INSTALL_DIR>
            --libdir=<INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}
            --srcdir=<SOURCE_DIR>
            --enable-shared
            --enable-static
            ${64bit}
            --host=${TOOLCHAIN_PREFIX}
        BUILD_BYPRODUCTS <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libantlr3c.a
                         <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libantlr3c${CMAKE_SHARED_LIBRARY_SUFFIX}
    )

    set(ANTLR3_JAR "${DEPS_BASE}/share/java/antlr-3.4-complete.jar")
    set(ANTLR3_INCLUDE_DIR "${DEPS_BASE}/include/")
    set(ANTLR3_LIBRARIES "${DEPS_BASE}/${CMAKE_INSTALL_LIBDIR}/libantlr3c.a")
endif()

find_package(Java COMPONENTS Runtime REQUIRED)

set(ANTLR3_FOUND TRUE)
# This may not be a single binary: the EP has a whole commandline
# We thus do not make this an executable target.
# Just call ${ANTLR3_COMMAND} instead.
set(ANTLR3_COMMAND ${Java_JAVA_EXECUTABLE} -cp "${ANTLR3_JAR}" org.antlr.Tool
    CACHE STRING "run ANTLR3" FORCE)

add_library(ANTLR3 STATIC IMPORTED GLOBAL)
set_target_properties(ANTLR3 PROPERTIES
    IMPORTED_LOCATION "${ANTLR3_LIBRARIES}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${ANTLR3_INCLUDE_DIR}"
)
if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
  set_target_properties(ANTLR3 PROPERTIES IMPORTED_IMPLIB "${ANTLR3_LIBRARIES}")
endif()

mark_as_advanced(ANTLR3_BINARY)
mark_as_advanced(ANTLR3_COMMAND)
mark_as_advanced(ANTLR3_FOUND)
mark_as_advanced(ANTLR3_FOUND_SYSTEM)
mark_as_advanced(ANTLR3_INCLUDE_DIR)
mark_as_advanced(ANTLR3_JAR)
mark_as_advanced(ANTLR3_LIBRARIES)

if(ANTLR3_FOUND_SYSTEM)
    message(STATUS "Found ANTLR3 runtime: ${ANTLR3_LIBRARIES}")
    message(STATUS "Found ANTLR3 JAR: ${ANTLR3_JAR}")
else()
    message(STATUS "Building ANTLR3 runtime: ${ANTLR3_LIBRARIES}")
    message(STATUS "Downloading ANTLR3 JAR: ${ANTLR3_JAR}")
    add_dependencies(ANTLR3 ANTLR3-EP-runtime ANTLR3-EP-jar)
endif()
