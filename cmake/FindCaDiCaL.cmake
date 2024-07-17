###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Andrew V. Teylu, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

  # Generate our version check file in CMAKE_BINARY_DIR
  set(CaDiCaL_version_src "${CMAKE_BINARY_DIR}/CaDiCaL_version.cpp")
  file(WRITE ${CaDiCaL_version_src}
    "
    #include <cadical.hpp>
    #include <iostream>

    int main(void)
    {
      std::cout << CaDiCaL::Solver::version() << std::endl;
      return 0;
    }
    "
  )

  # `try_run` doesn't have a way to specify a specific include dirs, so we need
  # to set (and then reset) `CMAKE_CXX_FLAGS`; our version file is a .cpp file,
  # so CXX_FLAGS are the right flags
  set(OLD_CXX_FLAGS ${CMAKE_CXX_FLAGS})

  # cvc5 doesn't support MSVC, so we're fine to hard-code `-I` as the include
  # flag
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I${CaDiCaL_INCLUDE_DIR}")

  # Try to compile and run our version file
  try_run(RUN_RESULT_VAR
    COMPILE_RESULT_VAR
    ${CMAKE_BINARY_DIR}
    ${CaDiCaL_version_src}
    LINK_LIBRARIES ${CaDiCaL_LIBRARIES}
    RUN_OUTPUT_VARIABLE CaDiCaL_VERSION
  )

  # Restore our CXX flags after checking with `try_run`
  set(CMAKE_CXX_FLAGS ${OLD_CXX_FLAGS})

  # If this failed to compile or run, we have bigger issues
  if (NOT ${RUN_RESULT_VAR} EQUAL 0 OR NOT ${COMPILE_RESULT_VAR})
    set(CaDiCaL_VERSION "")
  endif()

  # Minimum supported version
  set(CaDiCaL_FIND_VERSION "1.6.0")

  # Set FOUND_SYSTEM to true; check_system_version will unset this if the
  # version is less than the minimum required
  set(CaDiCaL_FOUND_SYSTEM TRUE)

  # Check the version against the required version
  check_system_version("CaDiCaL")
endif()

if(NOT CaDiCaL_FOUND_SYSTEM)
  check_ep_downloaded("CaDiCaL-EP")
  if(NOT CaDiCaL-EP_DOWNLOADED)
    check_auto_download("CaDiCaL" "")
  endif()

  include(CheckSymbolExists)
  include(ExternalProject)

  set(CaDiCaL_VERSION "rel-1.7.4")
  set(CaDiCaL_CHECKSUM "866c8a1332ff1ad5dc7ad403bdef3164420f3f947816b5c9509aad1d18ada7a1")

  # avoid configure script and instantiate the makefile manually the configure
  # scripts unnecessarily fails for cross compilation thus we do the bare
  # minimum from the configure script here
  set(CaDiCaL_CXXFLAGS "-fPIC -O3 -DNDEBUG -DQUIET -std=c++11")
  if(CMAKE_CROSSCOMPILING_MACOS)
    set(CaDiCaL_CXXFLAGS "${CaDiCaL_CXXFLAGS} -arch ${CMAKE_OSX_ARCHITECTURES}")
  endif()

  # check for getc_unlocked
  check_symbol_exists("getc_unlocked" "cstdio" HAVE_UNLOCKED_IO)
  if(NOT HAVE_UNLOCKED_IO)
    string(APPEND CaDiCaL_CXXFLAGS " -DNUNLOCKED")
  endif()

  # On macOS, we have to set `-isysroot` to make sure that include headers are
  # found because they are not necessarily installed at /usr/include anymore.
  if(CMAKE_OSX_SYSROOT)
    string(APPEND CaDiCaL_CXXFLAGS " ${CMAKE_CXX_SYSROOT_FLAG} ${CMAKE_OSX_SYSROOT}")
  endif()

  if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
    # use $(MAKE) instead of "make" to allow for parallel builds
    set(make_cmd "$(MAKE)")
  else()
    # $(MAKE) does not work with ninja
    set(make_cmd "make")
  endif()

  set(USE_EMAR "")
  if(NOT(WASM STREQUAL "OFF"))
    set(USE_EMAR  "-e s,ar rc,emar rc,")
  endif()

  ExternalProject_Add(
    CaDiCaL-EP
    ${COMMON_EP_CONFIG}
    BUILD_IN_SOURCE ON
    URL https://github.com/arminbiere/cadical/archive/${CaDiCaL_VERSION}.tar.gz
    URL_HASH SHA256=${CaDiCaL_CHECKSUM}
    CONFIGURE_COMMAND mkdir -p <SOURCE_DIR>/build
    # avoid configure script, prepare the makefile manually
    COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/makefile.in
            <SOURCE_DIR>/build/makefile
    COMMAND
      sed -i.orig -e "s,@CXX@,${CMAKE_CXX_COMPILER}," -e
      "s,@CXXFLAGS@,${CaDiCaL_CXXFLAGS}," -e "s,@MAKEFLAGS@,," ${USE_EMAR}
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

  # Install CaDiCaL static library only if it is a static build.
  # The CaDiCaL static library is required to compile a program that
  # uses the cvc5 static library.
  if(NOT BUILD_SHARED_LIBS)
    install(FILES ${CaDiCaL_LIBRARIES} TYPE ${LIB_BUILD_TYPE})
  endif()
endif()
