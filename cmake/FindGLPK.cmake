###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Andrew V. Teylu
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  include(checksymbolexists)
  set(cmake_required_includes ${glpk_include_dir})
  set(cmake_required_libraries ${glpk_libraries} m)
  check_symbol_exists(glp_ios_get_cut "glpk.h" have_glpk_cut_log)
  if(not have_glpk_cut_log)
    message(fatal_error "could not link against glpk-cut-log. "
                        "did you forget to install glpk-cut-log?")
  endif()
  set(GLPK_FOUND_SYSTEM TRUE)
endif()

if(NOT GLPK_FOUND_SYSTEM)
  check_ep_downloaded("GLPK-EP")
  if(NOT GLPK-EP_DOWNLOADED)
    check_auto_download("GLPK" "--no-glpk")
  endif()

  include(ExternalProject)
  include(GNUInstallDirs)

  set(GLPK_VERSION "5.0")

  if("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
    # use $(MAKE) instead of "make" to allow for parallel builds
    set(make_cmd "$(MAKE)")
  else()
    # $(MAKE) does not work with ninja
    set(make_cmd "make")
  endif()

  find_package(Patch)
  if(NOT Patch_FOUND)
    message(SEND_ERROR "Can not build GLPK, missing binary for patch")
  endif()

  find_program(LIBTOOLIZE NAMES libtoolize glibtoolize)
  if(NOT LIBTOOLIZE)
    message(SEND_ERROR "Can not build GLPK, missing binary for libtoolize")
  endif()

  find_program(ACLOCAL aclocal)
  if(NOT ACLOCAL)
    message(SEND_ERROR "Can not build GLPK, missing binary for aclocal")
  endif()

  find_program(AUTOHEADER autoheader)
  if(NOT AUTOHEADER)
    message(SEND_ERROR "Can not build GLPK, missing binary for autoheader")
  endif()

  find_program(AUTOCONF autoconf)
  if(NOT AUTOCONF)
    message(SEND_ERROR "Can not build GLPK, missing binary for autoconf")
  endif()

  find_program(AUTOMAKE automake)
  if(NOT AUTOMAKE)
    message(SEND_ERROR "Can not build GLPK, missing binary for automake")
  endif()

  ExternalProject_Add(
    GLPK-EP
    ${COMMON_EP_CONFIG}
    URL "https://ftp.gnu.org/gnu/glpk/glpk-${GLPK_VERSION}.tar.gz"
    URL_HASH SHA256=4a1013eebb50f728fc601bdd833b0b2870333c3b3e5a816eeba921d95bec6f15
    PATCH_COMMAND ${Patch_EXECUTABLE} -p1 -d <SOURCE_DIR>
        -i ${CMAKE_CURRENT_LIST_DIR}/deps-utils/glpk-cut-log.patch
    CONFIGURE_COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${LIBTOOLIZE}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${ACLOCAL}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${AUTOHEADER}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${AUTOCONF}
    COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR> ${AUTOMAKE} --add-missing
    COMMAND ${SHELL} <SOURCE_DIR>/configure --prefix=<INSTALL_DIR> --enable-shared
            --enable-static --with-pic
    BUILD_COMMAND ${make_cmd} install
    BUILD_BYPRODUCTS <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libglpk.a
                     <INSTALL_DIR>/include/glpk.h
  )

  set(GLPK_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(GLPK_LIBRARIES "${DEPS_BASE}/${CMAKE_INSTALL_LIBDIR}/libglpk.a")
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
endif()
