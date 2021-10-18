###############################################################################
# Top contributors (to current version):
#   Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find LibPoly
# Poly_FOUND - should always be true
# Poly - target for the libpoly library
# Polyxx - target for the C++ interface of libpoly, also links Poly
##

include(deps-helper)

find_path(Poly_INCLUDE_DIR NAMES poly/poly.h)
find_library(Poly_LIBRARIES NAMES poly)
find_library(PolyXX_LIBRARIES NAMES polyxx)

set(Poly_FOUND_SYSTEM FALSE)
if(Poly_INCLUDE_DIR
   AND Poly_LIBRARIES
   AND PolyXX_LIBRARIES
)
  set(Poly_FOUND_SYSTEM TRUE)

  file(STRINGS ${Poly_INCLUDE_DIR}/poly/version.h Poly_VERSION
       REGEX "^#define[\t ]+LIBPOLY_VERSION [0-9+]+"
  )
  string(REGEX MATCH "[0-9.]+" Poly_VERSION "${Poly_VERSION}")

  check_system_version("Poly")
endif()

if(ENABLE_STATIC_LIBRARY AND Poly_FOUND_SYSTEM)
  force_static_library()
  find_library(Poly_STATIC_LIBRARIES NAMES poly)
  find_library(PolyXX_STATIC_LIBRARIES NAMES polyxx)
  if(NOT Poly_STATIC_LIBRARIES OR NOT PolyXX_STATIC_LIBRARIES)
    set(Poly_FOUND_SYSTEM FALSE)
  endif()
  reset_force_static_library()
endif()

if(NOT Poly_FOUND_SYSTEM)
  check_ep_downloaded("Poly-EP")
  if(NOT Poly-EP_DOWNLOADED)
    check_auto_download("Poly" "--no-poly")
  endif()

  include(ExternalProject)

  set(Poly_VERSION "f543721215ec17a724dc86820a0430233931a637")

  check_if_cross_compiling(CCWIN "Windows" "")
  if(CCWIN)
    # Roughly following https://stackoverflow.com/a/44383330/2375725
    set(patchcmd
        # Avoid %z and %llu format specifiers
        COMMAND find <SOURCE_DIR>/ -type f ! -name "*.orig" -exec
                sed -i.orig "s/%z[diu]/%\\\" PRIu64 \\\"/g" {} +
        COMMAND find <SOURCE_DIR>/ -type f ! -name "*.orig" -exec
                sed -i.orig "s/%ll[du]/%\\\" PRIu64 \\\"/g" {} +
        # Make sure the new macros are available
        COMMAND find <SOURCE_DIR>/ -type f ! -name "*.orig" -exec
                sed -i.orig "s/#include <stdio.h>/#include <stdio.h>\\\\n#include <inttypes.h>/" {} +
        COMMAND find <SOURCE_DIR>/ -type f ! -name "*.orig" -exec
                sed -i.orig "s/#include <cstdio>/#include <cstdio>\\\\n#include <inttypes.h>/" {} +
        # Help with finding GMP
        COMMAND sed -i.orig "s/find_library(GMP_LIBRARY gmp)/find_library(GMP_LIBRARY gmp gmp-10)/"
                <SOURCE_DIR>/CMakeLists.txt
    )
  else()
    unset(patchcmd)
  endif()

  get_target_property(GMP_INCLUDE_DIR GMP_STATIC INTERFACE_INCLUDE_DIRECTORIES)
  get_target_property(GMP_LIBRARY GMP_STATIC IMPORTED_LOCATION)
  get_filename_component(GMP_LIB_PATH "${GMP_LIBRARY}" DIRECTORY)

  ExternalProject_Add(
    Poly-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/SRI-CSL/libpoly/archive/${Poly_VERSION}.tar.gz
    URL_HASH SHA1=3fad3b310727fa0fb2fdff5a8857709d12f72e04
    PATCH_COMMAND
      sed -i.orig
      "s,add_subdirectory(test/polyxx),add_subdirectory(test/polyxx EXCLUDE_FROM_ALL),g"
      <SOURCE_DIR>/CMakeLists.txt ${patchcmd}
    CMAKE_ARGS -DCMAKE_BUILD_TYPE=Release
               -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
               -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
               -DLIBPOLY_BUILD_PYTHON_API=OFF
               -DLIBPOLY_BUILD_STATIC=ON
               -DLIBPOLY_BUILD_STATIC_PIC=ON
               -DCMAKE_INCLUDE_PATH=${GMP_INCLUDE_DIR}
               -DCMAKE_LIBRARY_PATH=${GMP_LIB_PATH}
    BUILD_COMMAND ${CMAKE_MAKE_PROGRAM} static_pic_poly static_pic_polyxx
    INSTALL_COMMAND ${CMAKE_MAKE_PROGRAM} install
    COMMAND ${CMAKE_COMMAND} -E copy src/libpicpoly.a
            <INSTALL_DIR>/lib/libpicpoly.a
    COMMAND ${CMAKE_COMMAND} -E copy src/libpicpolyxx.a
            <INSTALL_DIR>/lib/libpicpolyxx.a
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libpicpoly.a
                     <INSTALL_DIR>/lib/libpicpolyxx.a
                     <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
                     <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
  )
  ExternalProject_Add_Step(
    Poly-EP cleanup
    DEPENDEES install
    COMMAND ls -al <INSTALL_DIR>/lib/
    COMMAND ${CMAKE_COMMAND} -E remove_directory <BINARY_DIR>/test/
  )
  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    ExternalProject_Add_Step(
      Poly-EP cleanup-macos
      DEPENDEES cleanup
      COMMAND rm
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
      COMMAND ${CMAKE_COMMAND} -E copy
        <INSTALL_DIR>/lib/libpoly.0.1.9${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
      COMMAND ${CMAKE_COMMAND} -E copy
        <INSTALL_DIR>/lib/libpolyxx.0.1.9${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
      COMMAND rm
        <INSTALL_DIR>/lib/libpoly.0${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpoly.0.1.9${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx.0${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx.0.1.9${CMAKE_SHARED_LIBRARY_SUFFIX}
      COMMAND ls -al <INSTALL_DIR>/lib/
    )
  else()
    ExternalProject_Add_Step(
      Poly-EP cleanup-linux
      DEPENDEES cleanup
      COMMAND rm
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
      COMMAND ${CMAKE_COMMAND} -E copy
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.9
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
      COMMAND ${CMAKE_COMMAND} -E copy
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.9
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
      COMMAND rm
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}.0
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.9
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}.0
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.9
      COMMAND echo "Checking <INSTALL_DIR>/lib"
      COMMAND ls -al <INSTALL_DIR>/lib/
    )
  endif()

  add_dependencies(Poly-EP GMP_SHARED GMP_STATIC)

  set(Poly_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(Poly_LIBRARIES "${DEPS_BASE}/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}")
  set(PolyXX_LIBRARIES "${DEPS_BASE}/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}")
  set(Poly_STATIC_LIBRARIES "${DEPS_BASE}/lib/libpicpoly.a")
  set(PolyXX_STATIC_LIBRARIES "${DEPS_BASE}/lib/libpicpolyxx.a")

  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(Poly_LIBRARIES "${DEPS_BASE}/bin/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}")
    set(PolyXX_LIBRARIES "${DEPS_BASE}/bin/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}")
  endif()
endif()

set(Poly_FOUND TRUE)

add_library(Poly_SHARED SHARED IMPORTED GLOBAL)
set_target_properties(Poly_SHARED PROPERTIES
  IMPORTED_LOCATION "${Poly_LIBRARIES}"
  INTERFACE_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
)
if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
  set_target_properties(Poly_SHARED PROPERTIES IMPORTED_IMPLIB "${Poly_LIBRARIES}")
endif()
target_link_libraries(Poly_SHARED INTERFACE GMP_SHARED)

add_library(Polyxx_SHARED SHARED IMPORTED GLOBAL)
set_target_properties(Polyxx_SHARED PROPERTIES
  IMPORTED_LOCATION "${PolyXX_LIBRARIES}"
  INTERFACE_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
  INTERFACE_LINK_LIBRARIES Poly_SHARED
)
if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
  set_target_properties(Polyxx_SHARED PROPERTIES IMPORTED_IMPLIB "${PolyXX_LIBRARIES}")
endif()

if(ENABLE_STATIC_LIBRARY)
  add_library(Poly_STATIC STATIC IMPORTED GLOBAL)
  set_target_properties(Poly_STATIC PROPERTIES
    IMPORTED_LOCATION "${Poly_STATIC_LIBRARIES}"
    INTERFACE_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
  )
  target_link_libraries(Poly_STATIC INTERFACE GMP_STATIC)

  add_library(Polyxx_STATIC STATIC IMPORTED GLOBAL)
  set_target_properties(Polyxx_STATIC PROPERTIES
    IMPORTED_LOCATION "${PolyXX_STATIC_LIBRARIES}"
    INTERFACE_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
    INTERFACE_LINK_LIBRARIES Poly_STATIC
  )
endif()

mark_as_advanced(Poly_FOUND)
mark_as_advanced(Poly_FOUND_SYSTEM)
mark_as_advanced(Poly_INCLUDE_DIR)
mark_as_advanced(Poly_LIBRARIES)
mark_as_advanced(PolyXX_LIBRARIES)

if(Poly_FOUND_SYSTEM)
  message(STATUS "Found Poly ${Poly_VERSION}: ${Poly_LIBRARIES}")
else()
  message(STATUS "Building Poly ${Poly_VERSION}: ${Poly_LIBRARIES}")
  add_dependencies(Poly_SHARED Poly-EP)
  add_dependencies(Polyxx_SHARED Poly-EP)

  install(FILES
    $<TARGET_LINKER_FILE:Poly_SHARED>
    $<TARGET_LINKER_FILE:Polyxx_SHARED>
    DESTINATION ${CMAKE_INSTALL_LIBDIR}
  )

  if(ENABLE_STATIC_LIBRARY)
    add_dependencies(Poly_STATIC Poly-EP)
    add_dependencies(Polyxx_STATIC Poly-EP)
  endif()
endif()
