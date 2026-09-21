###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find MPFR
# MPFR_FOUND - system has MPFR lib
# MPFR_INCLUDE_DIR - the MPFR include directory
# MPFR_LIBRARIES - Libraries needed to use MPFR
# MPFR - target for the MPFR library
##

include(deps-helper)

# Only consider a system version of MPFR if we also use a system version of
# GMP. A system MPFR is compiled and linked against the system GMP, so mixing
# it with a locally built GMP may result in version/ABI mismatches.
if(GMP_FOUND_SYSTEM)
  find_path(MPFR_INCLUDE_DIR NAMES mpfr.h)
  find_library(MPFR_LIBRARIES NAMES mpfr)
endif()

set(MPFR_FOUND_SYSTEM FALSE)
if(GMP_FOUND_SYSTEM AND MPFR_INCLUDE_DIR AND MPFR_LIBRARIES)
  set(MPFR_FOUND_SYSTEM TRUE)

  # Retrieve version from mpfr.h
  file(STRINGS ${MPFR_INCLUDE_DIR}/mpfr.h MPFR_VERSION_LINE
       REGEX "^#define MPFR_VERSION_STRING.*")
  if(MPFR_VERSION_LINE)
    string(REGEX MATCH "\"([0-9]+\\.[0-9]+\\.[0-9]+)\"" _match "${MPFR_VERSION_LINE}")
    if(_match)
      set(MPFR_VERSION "${CMAKE_MATCH_1}")
    endif()
  endif()

  check_system_version("MPFR")
endif()

if(NOT MPFR_FOUND_SYSTEM)
  check_ep_downloaded("MPFR-EP")
  if(NOT MPFR-EP_DOWNLOADED)
    check_auto_download("MPFR" "--no-mpfr")
  endif()

  include(ExternalProject)

  set(MPFR_VERSION "4.2.2")

  set(MPFR_INCLUDE_DIR "${DEPS_BASE}/include/")

  set(MPFR_CFLAGS "")

  if(BUILD_SHARED_LIBS)
    set(LINK_OPTS --enable-shared --disable-static)
    if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
      set(MPFR_LIBRARIES "${DEPS_BASE}/lib/libmpfr.dll.a")
    else()
      set(MPFR_LIBRARIES "${DEPS_BASE}/lib/libmpfr${CMAKE_SHARED_LIBRARY_SUFFIX}")
    endif()
  else()
    if(CMAKE_SYSTEM_NAME STREQUAL "Windows" AND GMP_FOUND_SYSTEM)
      # A MinGW system GMP advertises a DLL build in gmp.h, which makes
      # MPFR's configure reject --disable-shared. Build the shared library
      # alongside the static one to get past this check (MinGW packages MPFR
      # the same way); we only use the static library below.
      set(LINK_OPTS --enable-shared --enable-static)
    else()
      set(LINK_OPTS --disable-shared --enable-static)
    endif()
    set(MPFR_LIBRARIES "${DEPS_BASE}/lib/libmpfr.a")
  endif()

  # Make sure that MPFR is compiled and linked against the same GMP we use,
  # in particular the locally built one if GMP was not found in the system.
  get_filename_component(GMP_LIB_DIR "${GMP_LIBRARIES}" DIRECTORY)

  set(CONFIGURE_OPTS "")
  # Skip building the MPFR documentation, makeinfo may not be available
  # (see FindGMP.cmake for details).
  set(CONFIGURE_ENV env "MAKEINFO=true")

  if(CMAKE_CROSSCOMPILING OR CMAKE_CROSSCOMPILING_MACOS)
    set(CONFIGURE_OPTS
      --host=${TOOLCHAIN_PREFIX}
      --build=${CMAKE_HOST_SYSTEM_PROCESSOR})

    set(CONFIGURE_ENV ${CONFIGURE_ENV} ${CMAKE_COMMAND} -E
      env "CC_FOR_BUILD=cc")
    if (CMAKE_CROSSCOMPILING_MACOS)
      set(CONFIGURE_ENV
        ${CONFIGURE_ENV}
        env "LDFLAGS=-arch ${CMAKE_OSX_ARCHITECTURES}")
      set(MPFR_CFLAGS "${MPFR_CFLAGS} --target=${TOOLCHAIN_PREFIX}")
    endif()
  else()
    set(CONFIGURE_OPTS --build=${BUILD_TRIPLET}) # Defined in Helpers
  endif()
  set(CONFIGURE_ENV ${CONFIGURE_ENV} env "CFLAGS=${MPFR_CFLAGS}")

  ExternalProject_Add(
    MPFR-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/cvc5/cvc5-deps/blob/main/mpfr-${MPFR_VERSION}.tar.xz?raw=true
    URL_HASH SHA256=b67ba0383ef7e8a8563734e2e889ef5ec3c3b898a01d00fa0a6869ad81c6ce01
    BUILD_IN_SOURCE ON
    CONFIGURE_COMMAND
      ${CONFIGURE_ENV}
          ${CONFIGURE_CMD_WRAPPER} ${SHELL} <SOURCE_DIR>/configure
          ${LINK_OPTS}
          --prefix=<INSTALL_DIR>
          --with-pic
          --with-gmp-include=${GMP_INCLUDE_DIR}
          --with-gmp-lib=${GMP_LIB_DIR}
          # MPFR enables maintainer mode by default. Disable it, otherwise
          # make may try to regenerate the autotools files (and fail) since
          # the timestamps of the extracted sources are not in archive order.
          --disable-maintainer-mode
          ${CONFIGURE_OPTS}
    BUILD_BYPRODUCTS ${MPFR_LIBRARIES}
  )
  add_dependencies(MPFR-EP GMP)
endif()

set(MPFR_FOUND TRUE)

if(BUILD_SHARED_LIBS)
  add_library(MPFR SHARED IMPORTED GLOBAL)
  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set_target_properties(MPFR PROPERTIES IMPORTED_IMPLIB "${MPFR_LIBRARIES}")
  endif()
else()
  add_library(MPFR STATIC IMPORTED GLOBAL)
endif()
set_target_properties(MPFR PROPERTIES
  IMPORTED_LOCATION "${MPFR_LIBRARIES}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${MPFR_INCLUDE_DIR}"
)
target_link_libraries(MPFR INTERFACE GMP)

mark_as_advanced(MPFR_FOUND)
mark_as_advanced(MPFR_FOUND_SYSTEM)
mark_as_advanced(MPFR_INCLUDE_DIR)
mark_as_advanced(MPFR_LIBRARIES)

if(MPFR_FOUND_SYSTEM)
  message(STATUS "Found MPFR ${MPFR_VERSION}: ${MPFR_LIBRARIES}")
else()
  message(STATUS "Building MPFR ${MPFR_VERSION}: ${MPFR_LIBRARIES}")
  add_dependencies(MPFR MPFR-EP)
  # Static builds install the MPFR static libraries.
  # These libraries are required to compile a program that
  # uses the cvc5 static library.
  # On Windows, this installs the import libraries (LIB) and
  # the DLL libraries (BIN)
  install(
    DIRECTORY ${DEPS_BASE}/lib/
    TYPE LIB
    FILES_MATCHING PATTERN libmpfr* PATTERN mpfr*.pc
  )
  if(BUILD_SHARED_LIBS AND WIN32)
    install(
      DIRECTORY ${DEPS_BASE}/${CMAKE_INSTALL_BINDIR}/
      TYPE BIN
      FILES_MATCHING PATTERN libmpfr*
    )
  endif()
  if(NOT SKIP_SET_RPATH AND BUILD_SHARED_LIBS AND APPLE)
    install(CODE "
      file(GLOB MPFR_DYLIBS \"\${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}/libmpfr*.dylib\")
      foreach(MPFR_DYLIB \${MPFR_DYLIBS})
        execute_process(COMMAND \${CMAKE_COMMAND}
          -DRPATH=@loader_path
          -DINSTALL_NAME_TOOL=${CMAKE_INSTALL_NAME_TOOL}
          -DDYLIB_PATH=\${MPFR_DYLIB}
          -DDEPS_BASE=${DEPS_BASE}
          -P ${PROJECT_SOURCE_DIR}/cmake/update_rpath_macos.cmake)
      endforeach()
    ")
  endif()
endif()
