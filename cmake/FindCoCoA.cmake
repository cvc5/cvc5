###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Alex Ozdemir, Sorawee Porncharoenwase
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

find_path(CoCoA_INCLUDE_DIR NAMES CoCoA/library.H)
find_library(CoCoA_LIBRARIES NAMES cocoa)

set(CoCoA_FOUND_SYSTEM FALSE)
if(CoCoA_INCLUDE_DIR AND CoCoA_LIBRARIES)
  set(CoCoA_FOUND_SYSTEM TRUE)

  file(STRINGS ${CoCoA_INCLUDE_DIR}/CoCoA/library.H CoCoA_VERSION
       REGEX "^COCOALIB_VERSION=.*"
  )
  string(REGEX MATCH "[0-9]+\\.[0-9]+" CoCoA_VERSION "${CoCoA_VERSION}")

  check_system_version("CoCoA")

  # This test checks whether CoCoA has been patched
  try_compile(CoCoA_USABLE "${DEPS_BASE}/try_compile/CoCoA-EP"
    "${CMAKE_CURRENT_LIST_DIR}/deps-utils/cocoa-test.cpp"
    CMAKE_FLAGS
      "-DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}"
      "-DINCLUDE_DIRECTORIES=${CoCoA_INCLUDE_DIR}"
    LINK_LIBRARIES ${CoCoA_LIBRARIES} ${GMP_LIBRARIES} ${GMPXX_LIBRARIES}
  )
  if(NOT CoCoA_USABLE)
    message(STATUS "The system version of CoCoA has not been patched.")
    if(ENABLE_AUTO_DOWNLOAD)
      message(STATUS "A patched version of CoCoA will be built for you.")
    else()
      message(STATUS "Use --auto-download to let us download and build a patched version of CoCoA for you.")
    endif()
    set(CoCoA_FOUND_SYSTEM FALSE)
  endif()
endif()

if(NOT CoCoA_FOUND_SYSTEM)
  check_ep_downloaded("CoCoA-EP")
  if(NOT CoCoA-EP_DOWNLOADED)
    check_auto_download("CoCoA" "--no-cocoa")
  endif()

  include(ExternalProject)

  set(CoCoA_VERSION "0.99800")

  if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
    # use $(MAKE) instead of "make" to allow for parallel builds
    set(make_cmd "$(MAKE)")
  else()
    # $(MAKE) does not work with ninja
    set(make_cmd "make")
  endif()

  get_target_property(GMP_LIBRARY GMP IMPORTED_LOCATION)

  find_program(PATCH_BIN patch)
  if(NOT PATCH_BIN)
    message(FATAL_ERROR "Can not build CoCoA, missing binary for patch")
  endif()

  set(CoCoA_CXXFLAGS "")
  # On macOS, we have to set `-isysroot` to make sure that include headers are
  # found because they are not necessarily installed at /usr/include anymore.
  if(CMAKE_OSX_SYSROOT)
    set(CoCoA_CXXFLAGS "${CMAKE_CXX_SYSROOT_FLAG} ${CMAKE_OSX_SYSROOT}")
  endif()

  ExternalProject_Add(
    CoCoA-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/cvc5/cvc5-deps/blob/main/CoCoALib-${CoCoA_VERSION}.tgz?raw=true
    URL_HASH SHA256=f8bb227e2e1729e171cf7ac2008af71df25914607712c35db7bcb5a044a928c6
    # CoCoA requires C++14, but the check does not work with compilers that
    # default to C++17 or newer. The patch fixes the check.
    PATCH_COMMAND patch -p1 -d <SOURCE_DIR>
        -i ${CMAKE_CURRENT_LIST_DIR}/deps-utils/CoCoALib-${CoCoA_VERSION}-trace.patch
    BUILD_IN_SOURCE YES
    CONFIGURE_COMMAND ${SHELL} ./configure --prefix=<INSTALL_DIR> --with-libgmp=${GMP_LIBRARY}
        --with-cxx=${CMAKE_CXX_COMPILER} --with-cxxflags=${CoCoA_CXXFLAGS}
    BUILD_COMMAND ${make_cmd} library
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libcocoa.a
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
  CoCoA PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CoCoA_INCLUDE_DIR}"
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
  # Install static library only if it is a static build.
  if(NOT BUILD_SHARED_LIBS)
    set(CoCoA_INSTALLED_LIBRARY
      "${DEPS_BASE}/lib/libcocoa-${CoCoA_VERSION}.a"
    )
    install(FILES ${CoCoA_INSTALLED_LIBRARY} TYPE ${LIB_BUILD_TYPE}
            RENAME "libcocoa.a")
  endif()
endif()
