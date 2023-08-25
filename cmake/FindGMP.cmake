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
# Find GMP
# GMP_FOUND - should always be true
# GMP - target for the GMP library
##

include(deps-helper)

find_path(GMP_INCLUDE_DIR NAMES gmp.h)
find_path(GMPXX_INCLUDE_DIR NAMES gmpxx.h)
find_library(GMP_LIBRARIES NAMES gmp)
find_library(GMPXX_LIBRARIES NAMES gmpxx)

set(GMP_FOUND_SYSTEM FALSE)
if(GMP_INCLUDE_DIR AND GMPXX_INCLUDE_DIR AND GMP_LIBRARIES AND GMPXX_LIBRARIES)
  set(GMP_FOUND_SYSTEM TRUE)

  # Attempt to retrieve the version from gmp.h
  function(getversionpart OUTPUT FILENAME DESC)
    file(STRINGS ${FILENAME} RES REGEX "^#define __GNU_MP_${DESC}[ \\t]+.*")
    string(REGEX MATCH "[0-9]+" RES "${RES}")
    set(${OUTPUT}
        "${RES}"
        PARENT_SCOPE
    )
  endfunction()
  getversionpart(MAJOR "${GMP_INCLUDE_DIR}/gmp.h" "VERSION")
  getversionpart(MINOR "${GMP_INCLUDE_DIR}/gmp.h" "VERSION_MINOR")
  getversionpart(PATCH "${GMP_INCLUDE_DIR}/gmp.h" "VERSION_PATCHLEVEL")

  if(MAJOR AND MINOR AND PATCH)
    set(GMP_VERSION
        "${MAJOR}.${MINOR}.${PATCH}"
    )
  else()
    set(GMP_VERSION "(unknown version)")
  endif()

  # This test checks whether GMP is usable and whether the version is new
  # enough
  try_compile(GMP_USABLE "${DEPS_BASE}/try_compile/GMP-EP"
    "${CMAKE_CURRENT_LIST_DIR}/deps-utils/gmp-test.cpp"
    CMAKE_FLAGS
      "-DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}"
      "-DINCLUDE_DIRECTORIES=${GMP_INCLUDE_DIR}"
    LINK_LIBRARIES ${GMP_LIBRARIES} ${GMPXX_LIBRARIES}
  )
  if(NOT GMP_USABLE)
    message(VERBOSE "System version for GMP does not work in the selected configuration. Maybe we are cross-compiling?")
    set(GMP_FOUND_SYSTEM FALSE)
  endif()
endif()

if(NOT GMP_FOUND_SYSTEM)
  check_ep_downloaded("GMP-EP")
  if(NOT GMP-EP_DOWNLOADED)
    check_auto_download("GMP" "")
  endif()

  include(ExternalProject)

  set(GMP_VERSION "6.2.1")

  set(GMP_INCLUDE_DIR "${DEPS_BASE}/include/")
  if(BUILD_SHARED_LIBS)
    set(LINK_OPTS --enable-shared --disable-static)
    if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
      set(GMP_LIBRARIES "${DEPS_BASE}/lib/libgmp.dll.a")
    else()
      set(GMP_LIBRARIES "${DEPS_BASE}/lib/libgmp${CMAKE_SHARED_LIBRARY_SUFFIX}")
    endif()
  else()
    set(LINK_OPTS --disable-shared --enable-static)
    set(GMP_LIBRARIES "${DEPS_BASE}/lib/libgmp.a")
  endif()

  set(CONFIGURE_OPTS "")  
  # GMP yields the following message at the end of the build process.
  #     WARNING: `makeinfo' is missing on your system.

  # This is a specific issue to Github CI on linux environments:
  #     https://github.com/ps2dev/ps2toolchain/issues/64
  #     https://github.com/spack/spack/issues/34906
  #     https://github.com/periscop/candl/issues/16
  #     https://github.com/microsoft/vcpkg/issues/22671
  # Many solution attempts have been tried, but none worked.

  # Since makeinfo just builds the documentation for GMP, 
  # it is possible to get around this issue by just disabling it:
  set(CONFIGURE_ENV env "MAKEINFO=true")

  if(CMAKE_CROSSCOMPILING OR CMAKE_CROSSCOMPILING_MACOS)
    set(CONFIGURE_OPTS
      --host=${TOOLCHAIN_PREFIX}
      --build=${CMAKE_HOST_SYSTEM_PROCESSOR})

    set(CONFIGURE_ENV ${CMAKE_COMMAND} -E
      env "CC_FOR_BUILD=cc")
    if (CMAKE_CROSSCOMPILING_MACOS)
      set(CONFIGURE_ENV
        ${CONFIGURE_ENV}
        env "CFLAGS=--target=${TOOLCHAIN_PREFIX}"
        env "LDFLAGS=-arch ${CMAKE_OSX_ARCHITECTURES}")
    endif()
  endif()

  # `CC_FOR_BUILD`, `--host`, and `--build` are passed to `configure` to ensure
  # that cross-compilation works (as suggested in the GMP documentation).
  # Without the `--build` flag, `configure` may fail for cross-compilation
  # builds for Windows if Wine is installed.
  ExternalProject_Add(
    GMP-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/cvc5/cvc5-deps/blob/main/gmp-${GMP_VERSION}.tar.bz2?raw=true
    URL_HASH SHA1=2dcf34d4a432dbe6cce1475a835d20fe44f75822
    CONFIGURE_COMMAND
      ${CONFIGURE_ENV}
          ${CONFIGURE_CMD_WRAPPER} ${SHELL} <SOURCE_DIR>/configure
          ${LINK_OPTS}
          --prefix=<INSTALL_DIR>
          --with-pic
          --enable-cxx
          ${CONFIGURE_OPTS}
    BUILD_BYPRODUCTS ${GMP_LIBRARIES}
  )
endif()

set(GMP_FOUND TRUE)


if(BUILD_SHARED_LIBS)
  add_library(GMP SHARED IMPORTED GLOBAL)
  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set_target_properties(GMP PROPERTIES IMPORTED_IMPLIB "${GMP_LIBRARIES}")
  endif()
else()
  add_library(GMP STATIC IMPORTED GLOBAL)
endif()
set_target_properties(GMP PROPERTIES
  IMPORTED_LOCATION "${GMP_LIBRARIES}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${GMP_INCLUDE_DIR}"
)

mark_as_advanced(GMP_FOUND)
mark_as_advanced(GMP_FOUND_SYSTEM)
mark_as_advanced(GMP_INCLUDE_DIR)
mark_as_advanced(GMP_LIBRARIES)

if(GMP_FOUND_SYSTEM)
  message(STATUS "Found GMP ${GMP_VERSION}: ${GMP_LIBRARIES}")
else()
  message(STATUS "Building GMP ${GMP_VERSION}: ${GMP_LIBRARIES}")
  add_dependencies(GMP GMP-EP)
endif()
