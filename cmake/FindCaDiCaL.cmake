###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Andres Noetzli
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find CaDiCaL
# CaDiCaL_FOUND - system has CaDiCaL lib
# CaDiCaL_INCLUDE_DIR - the CaDiCaL include directory
# CaDiCaL_LIBRARIES - Libraries needed to use CaDiCaL
##

include(deps-helper)

find_path(CaDiCaL_INCLUDE_DIR NAMES cadical.hpp)
find_library(CaDiCaL_LIBRARIES NAMES cadical)

set(CaDiCaL_FOUND_SYSTEM FALSE)
if(CaDiCaL_INCLUDE_DIR AND CaDiCaL_LIBRARIES)
  set(CaDiCaL_FOUND_SYSTEM TRUE)

  # Unfortunately it is not part of the headers
  find_program(CaDiCaL_BINARY NAMES cadical)
  if(CaDiCaL_BINARY)
    execute_process(
      COMMAND ${CaDiCaL_BINARY} --version OUTPUT_VARIABLE CaDiCaL_VERSION
    )
  else()
    set(CaDiCaL_VERSION "")
  endif()

  check_system_version("CaDiCaL")
endif()

if(NOT CaDiCaL_FOUND_SYSTEM)
  check_ep_downloaded("CaDiCaL-EP")
  if(NOT CaDiCaL-EP_DOWNLOADED)
    check_auto_download("CaDiCaL" "")
  endif()

  include(CheckSymbolExists)
  include(ExternalProject)

  set(CaDiCaL_VERSION "rel-1.5.2")
  set(CaDiCaL_CHECKSUM "8bc2c3bdf4ef3780f001b31c2fe02168f3bb34b8")

  # avoid configure script and instantiate the makefile manually the configure
  # scripts unnecessarily fails for cross compilation thus we do the bare
  # minimum from the configure script here
  set(CXXFLAGS "-fPIC -O3 -DNDEBUG -DQUIET -std=c++11")
  if(CMAKE_CROSSCOMPILING_MACOS)
    set(CXXFLAGS "${CXXFLAGS} -arch ${CMAKE_OSX_ARCHITECTURES}")
  endif()

  # check for getc_unlocked
  check_symbol_exists("getc_unlocked" "cstdio" HAVE_UNLOCKED_IO)
  if(NOT HAVE_UNLOCKED_IO)
    string(APPEND CXXFLAGS " -DNUNLOCKED")
  endif()

  # On macOS, we have to set `-isysroot` to make sure that include headers are
  # found because they are not necessarily installed at /usr/include anymore.
  if(CMAKE_OSX_SYSROOT)
    string(APPEND CXXFLAGS " ${CMAKE_CXX_SYSROOT_FLAG} ${CMAKE_OSX_SYSROOT}")
  endif()

  if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
    # use $(MAKE) instead of "make" to allow for parallel builds
    set(make_cmd "$(MAKE)")
  else()
    # $(MAKE) does not work with ninja
    set(make_cmd "make")
  endif()

  ExternalProject_Add(
    CaDiCaL-EP
    ${COMMON_EP_CONFIG}
    BUILD_IN_SOURCE ON
    URL https://github.com/arminbiere/cadical/archive/${CaDiCaL_VERSION}.tar.gz
    URL_HASH SHA1=${CaDiCaL_CHECKSUM}
    CONFIGURE_COMMAND mkdir -p <SOURCE_DIR>/build
    # avoid configure script, prepare the makefile manually
    COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/makefile.in
            <SOURCE_DIR>/build/makefile
    COMMAND
      sed -i.orig -e "s,@CXX@,${CMAKE_CXX_COMPILER}," -e
      "s,@CXXFLAGS@,${CXXFLAGS}," -e "s,@MAKEFLAGS@,,"
      <SOURCE_DIR>/build/makefile
    BUILD_COMMAND ${make_cmd} -C <SOURCE_DIR>/build libcadical.a
    INSTALL_COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/build/libcadical.a
                    <INSTALL_DIR>/lib/libcadical.a
    COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/src/cadical.hpp
            <INSTALL_DIR>/include/cadical.hpp
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libcadical.a
  )

  set(CaDiCaL_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(CaDiCaL_LIBRARIES "${DEPS_BASE}/lib/libcadical.a")
endif()

set(CaDiCaL_FOUND TRUE)

add_library(CaDiCaL STATIC IMPORTED GLOBAL)
set_target_properties(
  CaDiCaL PROPERTIES IMPORTED_LOCATION "${CaDiCaL_LIBRARIES}"
)
set_target_properties(
  CaDiCaL PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CaDiCaL_INCLUDE_DIR}"
)

if (WIN32)
  # The Windows version of CaDiCaL calls GetProcessMemoryInfo(), which is
  # defined in the Process Status API (psapi), so we declare it as a dependency
  # of the CaDiCaL library (without this, linking a static cvc5 executable
  # fails).
  set_target_properties(
    CaDiCaL PROPERTIES IMPORTED_LINK_INTERFACE_LIBRARIES psapi
  )
endif ()

mark_as_advanced(CaDiCaL_FOUND)
mark_as_advanced(CaDiCaL_FOUND_SYSTEM)
mark_as_advanced(CaDiCaL_INCLUDE_DIR)
mark_as_advanced(CaDiCaL_LIBRARIES)

if(CaDiCaL_FOUND_SYSTEM)
  message(STATUS "Found CaDiCaL ${CaDiCaL_VERSION}: ${CaDiCaL_LIBRARIES}")
else()
  message(STATUS "Building CaDiCaL ${CaDiCaL_VERSION}: ${CaDiCaL_LIBRARIES}")
  add_dependencies(CaDiCaL CaDiCaL-EP)
  install(FILES
    ${CaDiCaL_LIBRARIES}
    DESTINATION ${CMAKE_INSTALL_LIBDIR}
  )
endif()
