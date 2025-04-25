###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find CryptoMiniSat
# CryptoMiniSat_FOUND - system has CryptoMiniSat lib
# CryptoMiniSat_INCLUDE_DIR - the CryptoMiniSat include directory
# CryptoMiniSat_LIBRARIES - Libraries needed to use CryptoMiniSat
##

include(deps-helper)

find_package(cryptominisat5 ${CryptoMiniSat_FIND_VERSION} QUIET)

set(CryptoMiniSat_FOUND_SYSTEM FALSE)
if(cryptominisat5_FOUND)
  set(CryptoMiniSat_VERSION ${cryptominisat5_VERSION})
  set(CryptoMiniSat_FOUND_SYSTEM TRUE)
  add_library(CryptoMiniSat INTERFACE IMPORTED GLOBAL)
  target_link_libraries(CryptoMiniSat INTERFACE cryptominisat5)
endif()

if(NOT CryptoMiniSat_FOUND_SYSTEM)
  set(CryptoMiniSat_VERSION "5.11.21")

  check_ep_downloaded("CryptoMiniSat-EP")
  if(NOT CryptoMiniSat-EP_DOWNLOADED)
    check_auto_download("CryptoMiniSat" "--no-cryptominisat")
  endif()

  include(ExternalProject)

  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(LIBFILENAME "libcryptominisat5win")
  else()
    set(LIBFILENAME "libcryptominisat5")
  endif()

  ExternalProject_Add(
    CryptoMiniSat-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/msoos/cryptominisat/archive/refs/tags/${CryptoMiniSat_VERSION}.tar.gz
    URL_HASH SHA256=288fd53d801909af797c72023361a75af3229d1806dbc87a0fcda18f5e03763b
    CMAKE_ARGS -DCMAKE_BUILD_TYPE=Release
               # make sure not to register with cmake
               -DCMAKE_EXPORT_NO_PACKAGE_REGISTRY=ON
               -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
               -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
               -DENABLE_ASSERTIONS=OFF
               -DENABLE_PYTHON_INTERFACE=OFF
               # disable what is not needed
               -DNOBREAKID=ON
               -DNOM4RI=ON
               -DNOSQLITE=ON
               -DNOZLIB=ON
               -DONLY_SIMPLE=ON
               -DSTATICCOMPILE=ON
    BUILD_BYPRODUCTS <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libcryptominisat5.a
  )
  # remove unused stuff to keep folder small
  ExternalProject_Add_Step(
    CryptoMiniSat-EP cleanup
    DEPENDEES install
    COMMAND ${CMAKE_COMMAND} -E remove <BINARY_DIR>/cryptominisat5_simple
    COMMAND ${CMAKE_COMMAND} -E remove <INSTALL_DIR>/bin/cryptominisat5_simple
  )

  set(CryptoMiniSat_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(CryptoMiniSat_LIBRARIES "${DEPS_BASE}/${CMAKE_INSTALL_LIBDIR}/${LIBFILENAME}.a")

  add_library(CryptoMiniSat STATIC IMPORTED GLOBAL)
  set_target_properties(
    CryptoMiniSat PROPERTIES IMPORTED_LOCATION "${CryptoMiniSat_LIBRARIES}"
  )
endif()

set(CryptoMiniSat_FOUND TRUE)

mark_as_advanced(CryptoMiniSat_FOUND)
mark_as_advanced(CryptoMiniSat_FOUND_SYSTEM)
mark_as_advanced(CryptoMiniSat_INCLUDE_DIR)
mark_as_advanced(CryptoMiniSat_LIBRARIES)

if(CryptoMiniSat_FOUND_SYSTEM)
  message(
    STATUS
      "Found CryptoMiniSat ${CryptoMiniSat_VERSION}: ${CryptoMiniSat_LIBRARIES}"
  )
else()
  message(
    STATUS
      "Building CryptoMiniSat ${CryptoMiniSat_VERSION}: ${CryptoMiniSat_LIBRARIES}"
  )
  add_dependencies(CryptoMiniSat CryptoMiniSat-EP)
  # Install static library only if it is a static build.
  if(NOT BUILD_SHARED_LIBS)
    install(FILES ${CryptoMiniSat_LIBRARIES} TYPE ${LIB_BUILD_TYPE})
  endif()
endif()
