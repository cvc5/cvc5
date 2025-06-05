###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find GLPK-cut-log
# GLPK_FOUND - system has GLPK lib
# GLPK_INCLUDE_DIR - the GLPK include directory
# GLPK_LIBRARIES - Libraries needed to use GLPK
##


find_path(GLPK_INCLUDE_DIR NAMES glpk.h)
find_library(GLPK_LIBRARIES NAMES glpk)

set(GLPK_FOUND_SYSTEM FALSE)
if(GLPK_INCLUDE_DIR AND GLPK_LIBRARIES)
  include(CheckSymbolExists)
  set(CMAKE_REQUIRED_INCLUDES ${GLPK_INCLUDE_DIR})
  set(CMAKE_REQUIRED_LIBRARIES ${GLPK_LIBRARIES} m)
  check_symbol_exists(glp_ios_get_cut "glpk.h" HAVE_GLPK_CUT_LOG)
  if(NOT HAVE_GLPK_CUT_LOG)
    message(FATAL_ERROR "Could not link against GLPK-cut-log. "
                        "Did you forget to install GLPK-cut-log?")
  endif()
  set(GLPK_FOUND_SYSTEM TRUE)
endif()

if(NOT GLPK_FOUND_SYSTEM)
  check_ep_downloaded("GLPK-EP")
  if(NOT GLPK-EP_DOWNLOADED)
    check_auto_download("GLPK" "--no-glpk")
  endif()

  include(ExternalProject)

  set(GLPK_VERSION "4.52")

  if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
    # use $(MAKE) instead of "make" to allow for parallel builds
    set(MAKE_CMD "$(MAKE)")
  else()
    # $(MAKE) does not work with ninja
    set(MAKE_CMD "make")
  endif()

  find_package(Patch)
  if(NOT Patch_FOUND)
    message(FATAL_ERROR "Can not build GLPK, missing binary for patch")
  endif()

  find_program(LIBTOOLIZE NAMES libtoolize glibtoolize)
  if(NOT LIBTOOLIZE)
    message(FATAL_ERROR "Can not build GLPK, missing binary for libtoolize")
  endif()

  find_program(ACLOCAL aclocal)
  if(NOT ACLOCAL)
    message(FATAL_ERROR "Can not build GLPK, missing binary for aclocal")
  endif()

  find_program(AUTOHEADER autoheader)
  if(NOT AUTOHEADER)
    message(FATAL_ERROR "Can not build GLPK, missing binary for autoheader")
  endif()

  find_program(AUTOCONF autoconf)
  if(NOT AUTOCONF)
    message(FATAL_ERROR "Can not build GLPK, missing binary for autoconf")
  endif()

  find_program(AUTOMAKE automake)
  if(NOT AUTOMAKE)
    message(FATAL_ERROR "Can not build GLPK, missing binary for automake")
  endif()

  set(CONFIGURE_ENV "")
  set(CONFIGURE_OPTS "")
  if(CMAKE_CROSSCOMPILING OR CMAKE_CROSSCOMPILING_MACOS)
    set(CONFIGURE_OPTS
      --host=${TOOLCHAIN_PREFIX}
      --build=${CMAKE_HOST_SYSTEM_PROCESSOR})

    set(CONFIGURE_ENV ${CONFIGURE_ENV} ${CMAKE_COMMAND} -E
      env "CC_FOR_BUILD=cc")
    if (CMAKE_CROSSCOMPILING_MACOS)
      set(CONFIGURE_ENV
        ${CONFIGURE_ENV}
        env "CFLAGS=--target=${TOOLCHAIN_PREFIX}"
        env "LDFLAGS=-arch ${CMAKE_OSX_ARCHITECTURES}")
    endif()
  else()
    set(CONFIGURE_OPTS --build=${BUILD_TRIPLET}) # Defined in Helpers
  endif()

  ExternalProject_Add(
    GLPK-EP
    ${COMMON_EP_CONFIG}
    URL "https://ftp.gnu.org/gnu/glpk/glpk-${GLPK_VERSION}.tar.gz"
    URL_HASH SHA256=9a5dab356268b4f177c33e00ddf8164496dc2434e83bd1114147024df983a3bb
    PATCH_COMMAND ${Patch_EXECUTABLE} -p1 -d <SOURCE_DIR>
        -i ${CMAKE_CURRENT_LIST_DIR}/deps-utils/glpk-cut-log.patch
    CONFIGURE_COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${LIBTOOLIZE}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${ACLOCAL}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${AUTOHEADER}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${AUTOCONF}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${AUTOMAKE} --add-missing
    COMMAND ${CONFIGURE_ENV} ${SHELL} <SOURCE_DIR>/configure
            --prefix=<INSTALL_DIR> --disable-shared
            --enable-static --with-pic ${CONFIGURE_OPTS}
    BUILD_COMMAND ${MAKE_CMD} install
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libglpk.a
                     <INSTALL_DIR>/include/glpk.h
  )

  set(GLPK_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(GLPK_LIBRARIES "${DEPS_BASE}/lib/libglpk.a")
endif()

set(GLPK_FOUND TRUE)

add_library(GLPK STATIC IMPORTED GLOBAL)
set_target_properties(GLPK PROPERTIES
    IMPORTED_LOCATION "${GLPK_LIBRARIES}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${GLPK_INCLUDE_DIR}"
)

mark_as_advanced(PATCH)
mark_as_advanced(LIBTOOLIZE)
mark_as_advanced(ACLOCAL)
mark_as_advanced(AUTOHEADER)
mark_as_advanced(AUTOCONF)
mark_as_advanced(AUTOMAKE)
mark_as_advanced(GLPK_FOUND)
mark_as_advanced(GLPK_FOUND_SYSTEM)
mark_as_advanced(GLPK_INCLUDE_DIR)
mark_as_advanced(GLPK_LIBRARIES)

if(GLPK_FOUND_SYSTEM)
  message(STATUS "Found GLPK ${GLPK_VERSION}: ${GLPK_LIBRARIES}")
else()
  message(STATUS "Building GLPK ${GLPK_VERSION}: ${GLPK_LIBRARIES}")
  add_dependencies(GLPK GLPK-EP)
  # Install static library only if it is a static build.
  if(NOT BUILD_SHARED_LIBS)
    install(FILES ${GLPK_LIBRARIES} TYPE ${LIB_BUILD_TYPE})
  endif()
endif()
