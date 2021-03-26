#####################
## FindCryptoMiniSat.cmake
## Top contributors (to current version):
##   Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find CryptoMiniSat
# CryptoMiniSat_FOUND - system has CryptoMiniSat lib
# CryptoMiniSat_INCLUDE_DIR - the CryptoMiniSat include directory
# CryptoMiniSat_LIBRARIES - Libraries needed to use CryptoMiniSat

include(deps-helper)

find_path(CryptoMiniSat_INCLUDE_DIR NAMES cryptominisat5/cryptominisat.h)
find_library(CryptoMiniSat_LIBRARIES NAMES cryptominisat5)

set(CryptoMiniSat_FOUND_SYSTEM FALSE)
if(CryptoMiniSat_INCLUDE_DIR AND CryptoMiniSat_LIBRARIES)
    set(CryptoMiniSat_FOUND_SYSTEM TRUE)

    function(GetVersionPart OUTPUT FILENAME DESC)
      file(STRINGS ${FILENAME} RES REGEX "^#define CRYPTOMINISAT_VERSION_${DESC}[ \\t]+.*")
      string(REGEX MATCH "[0-9]+" RES "${RES}")
      set(${OUTPUT} "${RES}" PARENT_SCOPE)
    endfunction()
    GetVersionPart(MAJOR "${CryptoMiniSat_INCLUDE_DIR}/cryptominisat5/cryptominisat.h" "MAJOR")
    GetVersionPart(MINOR "${CryptoMiniSat_INCLUDE_DIR}/cryptominisat5/cryptominisat.h" "MINOR")
    GetVersionPart(PATCH "${CryptoMiniSat_INCLUDE_DIR}/cryptominisat5/cryptominisat.h" "PATCH")
    set(CryptoMiniSat_VERSION "${MAJOR}.${MINOR}.${PATCH}")

    check_system_version("CryptoMiniSat")
endif()

if(NOT CryptoMiniSat_FOUND_SYSTEM)
    include(ExternalProject)

    set(CryptoMiniSat_VERSION "5.8.0")

    ExternalProject_Add(
        CryptoMiniSat-EP
        PREFIX ${DEPS_PREFIX}
        URL https://github.com/msoos/cryptominisat/archive/refs/tags/${CryptoMiniSat_VERSION}.tar.gz
        URL_HASH SHA1=f79dfa1ffc6c9c75b3a33f76d3a89a3df2b3f4c2
        PATCH_COMMAND patch <SOURCE_DIR>/src/packedmatrix.h ${CMAKE_CURRENT_LIST_DIR}/deps-utils/CryptoMiniSat-patch-ba6f76e3.patch
        CMAKE_ARGS
          -DCMAKE_BUILD_TYPE=Release
          -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
          -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
          -DENABLE_PYTHON_INTERFACE=OFF
          -DSTATICCOMPILE=ON
          -DNOBREAKID=ON
          -DNOM4RI=ON
          -DNOSQLITE=ON
          -DONLY_SIMPLE=ON
    )

    set(CryptoMiniSat_INCLUDE_DIR "${DEPS_BASE}/include/")
    set(CryptoMiniSat_LIBRARIES "${DEPS_BASE}/lib/libcryptominisat5.a")
endif()

set(CryptoMiniSat_FOUND TRUE)

add_library(CryptoMiniSat STATIC IMPORTED GLOBAL)
set_target_properties(CryptoMiniSat PROPERTIES IMPORTED_LOCATION "${CryptoMiniSat_LIBRARIES}")
set_target_properties(CryptoMiniSat PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "${CryptoMiniSat_INCLUDE_DIR}")

mark_as_advanced(CryptoMiniSat_FOUND)
mark_as_advanced(CryptoMiniSat_FOUND_SYSTEM)
mark_as_advanced(CryptoMiniSat_INCLUDE_DIR)
mark_as_advanced(CryptoMiniSat_LIBRARIES)

if(CryptoMiniSat_FOUND_SYSTEM)
    message(STATUS "Found CryptoMiniSat ${CryptoMiniSat_VERSION}: ${CryptoMiniSat_LIBRARIES}")
else()
    message(STATUS "Building CryptoMiniSat ${CryptoMiniSat_VERSION}: ${CryptoMiniSat_LIBRARIES}")
    add_dependencies(CryptoMiniSat CryptoMiniSat-EP)
endif()
