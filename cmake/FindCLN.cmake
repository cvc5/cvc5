###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Andrew V. Jones
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find CLN
# CLN_FOUND - system has CLN lib
# CLN_INCLUDE_DIR - the CLN include directory
# CLN_LIBRARIES - Libraries needed to use CLN
##

include(deps-helper)

find_path(CLN_INCLUDE_DIR NAMES cln/cln.h)
find_library(CLN_LIBRARIES NAMES cln)

set(CLN_FOUND_SYSTEM FALSE)
if(CLN_INCLUDE_DIR AND CLN_LIBRARIES)
  set(CLN_FOUND_SYSTEM TRUE)

  file(STRINGS ${CLN_INCLUDE_DIR}/cln/version.h CLN_VERSION
       REGEX "^#define[\t ]+CL_VERSION .*"
  )
  string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+" CLN_VERSION "${CLN_VERSION}")

  check_system_version("CLN")
endif()

if(NOT CLN_FOUND_SYSTEM)
  check_ep_downloaded("CLN-EP")
  if(NOT CLN-EP_DOWNLOADED)
    check_auto_download("CLN" "--no-cln")
  endif()

  include(ExternalProject)

  fail_if_cross_compiling("Windows" "" "CLN" "autoconf fails")
  fail_if_cross_compiling("" "arm" "CLN" "syntax error in configure")

  set(CLN_VERSION "1.3.6")
  string(REPLACE "." "-" CLN_TAG ${CLN_VERSION})

  find_program(AUTORECONF autoreconf)
  if(NOT AUTORECONF)
    message(SEND_ERROR "Can not build CLN, missing binary for autoreconf")
  endif()

  ExternalProject_Add(
    CLN-EP
    ${COMMON_EP_CONFIG}
    URL "https://www.ginac.de/CLN/cln.git/?p=cln.git\\\;a=snapshot\\\;h=cln_${CLN_TAG}\\\;sf=tgz"
    URL_HASH SHA1=71d02b90ef0575f06b7bafb8690f73e8064d8228
    DOWNLOAD_NAME cln.tgz
    CONFIGURE_COMMAND
      ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ./autogen.sh
    COMMAND
      ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> autoreconf -iv
    COMMAND ${SHELL} <SOURCE_DIR>/configure --prefix=<INSTALL_DIR> --enable-shared
            --enable-static --with-pic
    BUILD_BYPRODUCTS <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libcln.a
                     <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libcln${CMAKE_SHARED_LIBRARY_SUFFIX}
  )

  add_dependencies(CLN-EP GMP)

  set(CLN_INCLUDE_DIR "${DEPS_BASE}/include/")
  if(BUILD_SHARED_LIBS)
    set(CLN_LIBRARIES "${DEPS_BASE}/${CMAKE_INSTALL_LIBDIR}/libcln${CMAKE_SHARED_LIBRARY_SUFFIX}")
  else()
    set(CLN_LIBRARIES "${DEPS_BASE}/${CMAKE_INSTALL_LIBDIR}/libcln.a")
  endif()
endif()

set(CLN_FOUND TRUE)

if(BUILD_SHARED_LIBS)
  add_library(CLN SHARED IMPORTED GLOBAL)
else()
  add_library(CLN STATIC IMPORTED GLOBAL)
endif()
set_target_properties(CLN PROPERTIES
  IMPORTED_LOCATION "${CLN_LIBRARIES}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CLN_INCLUDE_DIR}"
)
target_link_libraries(CLN INTERFACE GMP)

mark_as_advanced(AUTORECONF)
mark_as_advanced(CLN_FOUND)
mark_as_advanced(CLN_FOUND_SYSTEM)
mark_as_advanced(CLN_INCLUDE_DIR)
mark_as_advanced(CLN_LIBRARIES)

if(CLN_FOUND_SYSTEM)
  message(STATUS "Found CLN ${CLN_VERSION}: ${CLN_LIBRARIES}")
else()
  message(STATUS "Building CLN ${CLN_VERSION}: ${CLN_LIBRARIES}")
  add_dependencies(CLN CLN-EP)
endif()
