###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Gereon Kremer, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

if (NOT BUILD_CLN)
  find_path(CLN_INCLUDE_DIR NAMES cln/cln.h)
  find_library(CLN_LIBRARIES NAMES cln)
endif()

set(CLN_FOUND_SYSTEM FALSE)
if(CLN_INCLUDE_DIR AND CLN_LIBRARIES)
  set(CLN_FOUND_SYSTEM TRUE)

  file(STRINGS ${CLN_INCLUDE_DIR}/cln/version.h CLN_VERSION
       REGEX "^#define[\t ]+CL_VERSION.*"
  )
  if(CLN_VERSION MATCHES
     "MAJOR ([0-9]+).*MINOR ([0-9]+).*PATCHLEVEL ([0-9]+)")
    string(CONCAT CLN_VERSION ${CMAKE_MATCH_1} "." ${CMAKE_MATCH_2} "." ${CMAKE_MATCH_3})
  else()
    string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+" CLN_VERSION "${CLN_VERSION}")
  endif()

  check_system_version("CLN")
endif()

if(NOT CLN_FOUND_SYSTEM)
  check_ep_downloaded("CLN-EP")
  if(NOT CLN-EP_DOWNLOADED)
    check_auto_download("CLN" "--no-cln")
  endif()

  include(ExternalProject)

  fail_if_cross_compiling("Windows" "" "CLN" "autoconf fails")

  if("${CMAKE_GENERATOR}" STREQUAL "MSYS Makefiles")
    message(FATAL_ERROR
      "Compilation of CLN in the MSYS2 environment is not supported."
    )
  endif()

  set(CLN_VERSION "1.3.7")
  set(CLN_SO_MAJOR_VER "6")
  set(CLN_SO_MINOR_VER "0")
  set(CLN_SO_PATCH_VER "7")
  set(CLN_SO_VERSION
    "${CLN_SO_MAJOR_VER}.${CLN_SO_MINOR_VER}.${CLN_SO_PATCH_VER}"
  )

  find_program(AUTORECONF autoreconf)
  if(NOT AUTORECONF)
    message(FATAL_ERROR "Can not build CLN, missing binary for autoreconf")
  endif()

  set(CLN_INCLUDE_DIR "${DEPS_BASE}/include/")
  if(BUILD_SHARED_LIBS)
    set(LINK_OPTS --enable-shared --disable-static)
    set(CLN_LIBRARIES "${DEPS_BASE}/lib/libcln${CMAKE_SHARED_LIBRARY_SUFFIX}")
    if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
      set(CLN_BYPRODUCTS
        <INSTALL_DIR>/lib/libcln${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libcln.${CLN_SO_MAJOR_VER}${CMAKE_SHARED_LIBRARY_SUFFIX}
      )
    else()
      set(CLN_BYPRODUCTS
        <INSTALL_DIR>/lib/libcln${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libcln${CMAKE_SHARED_LIBRARY_SUFFIX}.${CLN_SO_MAJOR_VER}
        <INSTALL_DIR>/lib/libcln${CMAKE_SHARED_LIBRARY_SUFFIX}.${CLN_SO_VERSION}
      )
    endif()
  else()
    set(LINK_OPTS --enable-static --disable-shared)
    set(CLN_LIBRARIES "${DEPS_BASE}/lib/libcln${CMAKE_STATIC_LIBRARY_SUFFIX}")
    set(CLN_BYPRODUCTS <INSTALL_DIR>/lib/libcln${CMAKE_STATIC_LIBRARY_SUFFIX})
  endif()

  set(CONFIGURE_OPTS "")
  # CLN yields the following message at the end of the build process.
  #     WARNING: `makeinfo' is missing on your system.
  # This is a specific issue to Github CI on linux environments.
  # Since makeinfo just builds the documentation for CLN,
  # it is possible to get around this issue by just disabling it:
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
        env "CFLAGS=--target=${TOOLCHAIN_PREFIX}"
        env "LDFLAGS=-arch ${CMAKE_OSX_ARCHITECTURES}")
    endif()
  endif()

  set(CLN_WITH_GMP)
  if(NOT GMP_FOUND_SYSTEM)
    set(CLN_WITH_GMP "--with-gmp=<INSTALL_DIR>")
  endif()

  ExternalProject_Add(
    CLN-EP
    ${COMMON_EP_CONFIG}
    URL "https://www.ginac.de/CLN/cln-${CLN_VERSION}.tar.bz2"
    URL_HASH SHA256=7c7ed8474958337e4df5bb57ea5176ad0365004cbb98b621765bc4606a10d86b
    DOWNLOAD_NAME cln.tar.bz2
    CONFIGURE_COMMAND
      ${CONFIGURE_ENV} ${SHELL} <SOURCE_DIR>/configure
        --prefix=<INSTALL_DIR> ${LINK_OPTS} --with-pic ${CLN_WITH_GMP}
        ${CONFIGURE_OPTS}
    BUILD_BYPRODUCTS ${CLN_BYPRODUCTS}
  )

  add_dependencies(CLN-EP GMP)

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

  ExternalProject_Get_Property(CLN-EP BUILD_BYPRODUCTS INSTALL_DIR)
  string(REPLACE "<INSTALL_DIR>" "${INSTALL_DIR}" BUILD_BYPRODUCTS "${BUILD_BYPRODUCTS}")

  # Static builds install the CLN static libraries.
  # These libraries are required to compile a program that
  # uses the cvc5 static library.
  install(FILES ${BUILD_BYPRODUCTS} TYPE ${LIB_BUILD_TYPE})

  if(NOT SKIP_SET_RPATH AND BUILD_SHARED_LIBS AND APPLE)
    foreach(CLN_DYLIB ${BUILD_BYPRODUCTS})
      get_filename_component(CLN_DYLIB_NAME ${CLN_DYLIB} NAME)
      update_rpath_macos(${CLN_DYLIB_NAME})
    endforeach()
  endif()
endif()
