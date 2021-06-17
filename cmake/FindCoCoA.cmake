###############################################################################
# Top contributors (to current version):
#   Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find CoCoA
# CoCoA_FOUND - system has CoCoA lib
# CoCoA_INCLUDE_DIR - the CoCoA include directory
# CoCoA_LIBRARIES - Libraries needed to use CoCoA
##

include(deps-helper)

find_path(CoCoA_INCLUDE_DIR NAMES CoCoA/CoCoA.h)
find_library(CoCoA_LIBRARIES NAMES CoCoA)

set(CoCoA_FOUND_SYSTEM FALSE)
if(CoCoA_INCLUDE_DIR AND CoCoA_LIBRARIES)
  set(CoCoA_FOUND_SYSTEM TRUE)

  file(STRINGS ${CoCoA_INCLUDE_DIR}/CoCoA/library.H CoCoA_VERSION
       REGEX "^COCOALIB_VERSION=.*"
  )
  string(REGEX MATCH "[0-9]+\\.[0-9]+" CoCoA_VERSION "${CoCoA_VERSION}")

  check_system_version("CoCoA")
endif()

if(NOT CoCoA_FOUND_SYSTEM)
  check_ep_downloaded("CoCoA-EP")
  if(NOT CoCoA-EP_DOWNLOADED)
    check_auto_download("CoCoA" "--no-cocoa")
  endif()

  include(ExternalProject)

  set(CoCoA_VERSION "0.99712")

  if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
    # use $(MAKE) instead of "make" to allow for parallel builds
    set(make_cmd "$(MAKE)")
  else()
    # $(MAKE) does not work with ninja
    set(make_cmd "make")
  endif()

  ExternalProject_Add(
    CoCoA-EP
    ${COMMON_EP_CONFIG}
    URL "http://cocoa.dima.unige.it/cocoalib/tgz/CoCoALib-${CoCoA_VERSION}.tgz"
    URL_HASH SHA1=873d0b60800cd3852939816ce0aa2e7f72dac4ce
    BUILD_IN_SOURCE YES
    CONFIGURE_COMMAND ./configure --prefix=<INSTALL_DIR>
    BUILD_COMMAND ${make_cmd} library
  )
  # Remove install directory before make install. CoCoA will complain otherwise
  ExternalProject_Add_Step(
    CoCoA-EP clear-install
    COMMAND ${CMAKE_COMMAND} -E remove_directory <INSTALL_DIR>/include/CoCoA-${CoCoA_VERSION}
    DEPENDEES build
    DEPENDERS install
  )

  add_dependencies(CoCoA-EP GMP)

  set(CoCoA_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(CoCoA_LIBRARIES "${DEPS_BASE}/lib/libcocoa.a")
endif()

set(CoCoA_FOUND TRUE)

add_library(CoCoA STATIC IMPORTED GLOBAL)
set_target_properties(CoCoA PROPERTIES IMPORTED_LOCATION "${CoCoA_LIBRARIES}")
set_target_properties(
  CoCoA PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "${CoCoA_INCLUDE_DIR}"
)
set_target_properties(CoCoA PROPERTIES INTERFACE_LINK_LIBRARIES GMP)

mark_as_advanced(CoCoA_FOUND)
mark_as_advanced(CoCoA_FOUND_SYSTEM)
mark_as_advanced(CoCoA_INCLUDE_DIR)
mark_as_advanced(CoCoA_LIBRARIES)

if(CoCoA_FOUND_SYSTEM)
  message(STATUS "Found CoCoA ${CoCoA_VERSION}: ${CoCoA_LIBRARIES}")
else()
  message(STATUS "Building CoCoA ${CoCoA_VERSION}: ${CoCoA_LIBRARIES}")
  add_dependencies(CoCoA CoCoA-EP)
endif()
