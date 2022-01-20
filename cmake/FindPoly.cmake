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

if(NOT Poly_FOUND_SYSTEM)
  check_ep_downloaded("Poly-EP")
  if(NOT Poly-EP_DOWNLOADED)
    check_auto_download("Poly" "--no-poly")
  endif()

  include(ExternalProject)

  set(Poly_VERSION "1383809f2aa5005ef20110fec84b66959518f697")

  check_if_cross_compiling(CCWIN "Windows" "")
  if(CCWIN)
    set(patchcmd COMMAND
      ${CMAKE_SOURCE_DIR}/cmake/deps-utils/Poly-windows-patch.sh <SOURCE_DIR>
    )
  else()
    unset(patchcmd)
  endif()

  get_target_property(GMP_INCLUDE_DIR GMP INTERFACE_INCLUDE_DIRECTORIES)
  get_target_property(GMP_LIBRARY GMP IMPORTED_LOCATION)
  get_filename_component(GMP_LIB_PATH "${GMP_LIBRARY}" DIRECTORY)

  set(POLY_BYPRODUCTS
    <INSTALL_DIR>/lib/libpicpoly.a
    <INSTALL_DIR>/lib/libpicpolyxx.a
    <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
    <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
  )
  if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    list(APPEND POLY_BYPRODUCTS
      <INSTALL_DIR>/lib/libpoly.0${CMAKE_SHARED_LIBRARY_SUFFIX}
      <INSTALL_DIR>/lib/libpoly.0.1.11${CMAKE_SHARED_LIBRARY_SUFFIX}
      <INSTALL_DIR>/lib/libpolyxx.0${CMAKE_SHARED_LIBRARY_SUFFIX}
      <INSTALL_DIR>/lib/libpolyxx.0.1.11${CMAKE_SHARED_LIBRARY_SUFFIX}
    )
  elseif(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    list(APPEND POLY_BYPRODUCTS
      <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}.0
      <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.11
      <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}.0
      <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.11
    )
  endif()

  ExternalProject_Add(
    Poly-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/SRI-CSL/libpoly/archive/${Poly_VERSION}.tar.gz
    URL_HASH SHA1=e3da80491b378a4d874073d201406eb011f47c19
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
    BUILD_COMMAND ${CMAKE_MAKE_PROGRAM}
    COMMAND ${CMAKE_MAKE_PROGRAM} static_pic_poly static_pic_polyxx
    INSTALL_COMMAND ${CMAKE_MAKE_PROGRAM} install
    COMMAND ${CMAKE_COMMAND} -E copy src/libpicpoly.a
            <INSTALL_DIR>/lib/libpicpoly.a
    COMMAND ${CMAKE_COMMAND} -E copy src/libpicpolyxx.a
            <INSTALL_DIR>/lib/libpicpolyxx.a
    BUILD_BYPRODUCTS ${POLY_BYPRODUCTS}
  )
  ExternalProject_Add_Step(
    Poly-EP cleanup
    DEPENDEES install
    COMMAND ${CMAKE_COMMAND} -E remove_directory <BINARY_DIR>/test/
  )
  add_dependencies(Poly-EP GMP)

  set(Poly_INCLUDE_DIR "${DEPS_BASE}/include/")
  if(BUILD_SHARED_LIBS)
    set(Poly_LIBRARIES "${DEPS_BASE}/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}")
    set(PolyXX_LIBRARIES "${DEPS_BASE}/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}")
  else()
    set(Poly_LIBRARIES "${DEPS_BASE}/lib/libpicpoly.a")
    set(PolyXX_LIBRARIES "${DEPS_BASE}/lib/libpicpolyxx.a")
  endif()
endif()

set(Poly_FOUND TRUE)


if(BUILD_SHARED_LIBS)
  add_library(Poly SHARED IMPORTED GLOBAL)
  add_library(Polyxx SHARED IMPORTED GLOBAL)
  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set_target_properties(Poly PROPERTIES IMPORTED_IMPLIB "${Poly_LIBRARIES}")
    set_target_properties(Polyxx PROPERTIES IMPORTED_IMPLIB "${PolyXX_LIBRARIES}")
  endif()
else()
  add_library(Poly STATIC IMPORTED GLOBAL)
  add_library(Polyxx STATIC IMPORTED GLOBAL)
endif()

set_target_properties(Poly PROPERTIES
  IMPORTED_LOCATION "${Poly_LIBRARIES}"
  INTERFACE_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
)
target_link_libraries(Poly INTERFACE GMP)
set_target_properties(Polyxx PROPERTIES
  IMPORTED_LOCATION "${PolyXX_LIBRARIES}"
  INTERFACE_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
  INTERFACE_LINK_LIBRARIES Poly
)

mark_as_advanced(Poly_FOUND)
mark_as_advanced(Poly_FOUND_SYSTEM)
mark_as_advanced(Poly_INCLUDE_DIR)
mark_as_advanced(Poly_LIBRARIES)
mark_as_advanced(PolyXX_LIBRARIES)

if(Poly_FOUND_SYSTEM)
  message(STATUS "Found Poly ${Poly_VERSION}: ${Poly_LIBRARIES}")
else()
  message(STATUS "Building Poly ${Poly_VERSION}: ${Poly_LIBRARIES}")
  add_dependencies(Poly Poly-EP)
  add_dependencies(Polyxx Poly-EP)

  ExternalProject_Get_Property(Poly-EP BUILD_BYPRODUCTS INSTALL_DIR)
  string(REPLACE "<INSTALL_DIR>" "${INSTALL_DIR}" BUILD_BYPRODUCTS "${BUILD_BYPRODUCTS}")
  install(FILES
    ${BUILD_BYPRODUCTS}
    DESTINATION ${CMAKE_INSTALL_LIBDIR}
  )
endif()
