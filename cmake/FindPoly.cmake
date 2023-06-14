###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Andres Noetzli, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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

  set(Poly_VERSION "126147f1ceae9f771a68bad9cbc199cf96daec46")

  check_if_cross_compiling(CCWIN "Windows" "")
  if(CCWIN)
    set(POLY_PATCH_CMD COMMAND
      ${CMAKE_SOURCE_DIR}/cmake/deps-utils/Poly-windows-patch.sh <SOURCE_DIR>
    )
  else()
    unset(POLY_PATCH_CMD)
  endif()

  # On Windows, CMake's default install action places DLLs into the runtime
  # path (/bin) after doing the build with 'ExternalProject_Add'
  if(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(BINARY_LIBRARY_DEST "bin")
  else()
    set(BINARY_LIBRARY_DEST "lib")
  endif()

  get_target_property(GMP_INCLUDE_DIR GMP INTERFACE_SYSTEM_INCLUDE_DIRECTORIES)
  get_target_property(GMP_LIBRARY GMP IMPORTED_LOCATION)
  get_filename_component(GMP_LIB_PATH "${GMP_LIBRARY}" DIRECTORY)

  set(Poly_INCLUDE_DIR "${DEPS_BASE}/include/")

  if(BUILD_SHARED_LIBS)
    set(POLY_BUILD_STATIC OFF)
    set(POLY_TARGETS poly polyxx)
    set(POLY_INSTALL_CMD
      INSTALL_COMMAND 
        ${CMAKE_MAKE_PROGRAM} install ${POLY_TARGETS}
    )

    if(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
      set(POLY_BYPRODUCTS
        <INSTALL_DIR>/lib/libpoly.0${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpoly.0.1.11${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx.0${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx.0.1.11${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
      )
      set(Poly_LIBRARIES "${DEPS_BASE}/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}")
      set(PolyXX_LIBRARIES "${DEPS_BASE}/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}")
    elseif(CMAKE_SYSTEM_NAME STREQUAL "Windows")
      # For Windows builds, LibPoly installs the .dlls to the bin directory
      set(POLY_BYPRODUCTS
        <INSTALL_DIR>/bin/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/bin/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
      )
      set(Poly_LIBRARIES "${DEPS_BASE}/bin/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}")
      set(PolyXX_LIBRARIES "${DEPS_BASE}/bin/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}")
    else()
      set(POLY_BYPRODUCTS
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}.0
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.11
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}.0
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}.0.1.11
        <INSTALL_DIR>/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}
        <INSTALL_DIR>/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}
      )
      set(Poly_LIBRARIES "${DEPS_BASE}/lib/libpoly${CMAKE_SHARED_LIBRARY_SUFFIX}")
      set(PolyXX_LIBRARIES "${DEPS_BASE}/lib/libpolyxx${CMAKE_SHARED_LIBRARY_SUFFIX}")
    endif()
  else()
    # For static builds, we only build and install the `static_pic_poly` and
    # `static_pic_polyxx` targets. We pass the full path of GMP to LibPoly
    # below. If we are building a static version of cvc5, it is the static
    # version of GMP, which does not work for building a shared version of
    # LibPoly.
    set(POLY_BUILD_STATIC ON)
    set(POLY_TARGETS static_pic_poly static_pic_polyxx)
    set(POLY_INSTALL_CMD
      INSTALL_COMMAND 
        ${CMAKE_MAKE_PROGRAM} install ${POLY_TARGETS}
      COMMAND
        ${CMAKE_COMMAND} -E copy
          src/libpicpoly${CMAKE_STATIC_LIBRARY_SUFFIX}
          <INSTALL_DIR>/lib/libpicpoly${CMAKE_STATIC_LIBRARY_SUFFIX}
      COMMAND
        ${CMAKE_COMMAND} -E copy
          src/libpicpolyxx${CMAKE_STATIC_LIBRARY_SUFFIX}
          <INSTALL_DIR>/lib/libpicpolyxx${CMAKE_STATIC_LIBRARY_SUFFIX}
    )

    # We only want to install the headers and the position-independent version
    # of the static libraries, so remove the installation targets for the other
    # versions of LibPoly
    set(POLY_PATCH_CMD ${POLY_PATCH_CMD}
      COMMAND
        sed -ri.orig
          "/TARGETS (poly|polyxx|static_poly|static_polyxx) /d"
          <SOURCE_DIR>/src/CMakeLists.txt
    )

    set(POLY_BYPRODUCTS
      <INSTALL_DIR>/lib/libpicpoly${CMAKE_STATIC_LIBRARY_SUFFIX}
      <INSTALL_DIR>/lib/libpicpolyxx${CMAKE_STATIC_LIBRARY_SUFFIX}
    )
    set(Poly_LIBRARIES
      "${DEPS_BASE}/lib/libpicpoly${CMAKE_STATIC_LIBRARY_SUFFIX}")
    set(PolyXX_LIBRARIES
      "${DEPS_BASE}/lib/libpicpolyxx${CMAKE_STATIC_LIBRARY_SUFFIX}")
  endif()

  # We pass the full path of GMP to LibPoly, s.t. we can ensure that LibPoly is
  # able to find the correct version of GMP if we built it locally. This is
  # primarily important for cross-compiling cvc5, because LibPoly's search
  # paths make it impossible to find the locally built GMP library otherwise.
  ExternalProject_Add(
    Poly-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/SRI-CSL/libpoly/archive/${Poly_VERSION}.tar.gz
    URL_HASH SHA1=5ebbd00c8dc8b731b5382701a23c60607bcb2804
    PATCH_COMMAND
      sed -i.orig
      "s,add_subdirectory(test/polyxx),add_subdirectory(test/polyxx EXCLUDE_FROM_ALL),g"
      <SOURCE_DIR>/CMakeLists.txt
    COMMAND
      # LibPoly declares a variable `enabled_count` whose value is only written
      # and never read. Newer versions of Clang throw a warning for this, which
      # aborts the compilation when -Wall is enabled.
      sed -i.orig
      "/enabled_count/d"
      <SOURCE_DIR>/src/upolynomial/factorization.c
      ${POLY_PATCH_CMD}
    CMAKE_ARGS -DCMAKE_BUILD_TYPE=Release
               -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
               -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
               -DLIBPOLY_BUILD_PYTHON_API=OFF
               -DLIBPOLY_BUILD_STATIC=${POLY_BUILD_STATIC}
               -DLIBPOLY_BUILD_STATIC_PIC=${POLY_BUILD_STATIC}
               -DGMP_INCLUDE_DIR=${GMP_INCLUDE_DIR}
               -DGMP_LIBRARY=${GMP_LIBRARIES}
               -DCMAKE_SKIP_INSTALL_ALL_DEPENDENCY=TRUE
    BUILD_COMMAND ${CMAKE_MAKE_PROGRAM} ${POLY_TARGETS}
    ${POLY_INSTALL_CMD}
    BUILD_BYPRODUCTS ${POLY_BYPRODUCTS}
  )
  ExternalProject_Add_Step(
    Poly-EP cleanup
    DEPENDEES install
    COMMAND ${CMAKE_COMMAND} -E remove_directory <BINARY_DIR>/test/
  )
  add_dependencies(Poly-EP GMP)
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
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
)
target_link_libraries(Poly INTERFACE GMP)
set_target_properties(Polyxx PROPERTIES
  IMPORTED_LOCATION "${PolyXX_LIBRARIES}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Poly_INCLUDE_DIR}"
)

mark_as_advanced(Poly_FOUND)
mark_as_advanced(Poly_FOUND_SYSTEM)
mark_as_advanced(Poly_INCLUDE_DIR)
mark_as_advanced(Poly_LIBRARIES)
mark_as_advanced(PolyXX_LIBRARIES)

if(Poly_FOUND_SYSTEM)
  message(STATUS "Found Poly ${Poly_VERSION}: ${Poly_LIBRARIES}, ${PolyXX_LIBRARIES}")
else()
  message(STATUS "Building Poly ${Poly_VERSION}: ${Poly_LIBRARIES}, ${PolyXX_LIBRARIES}")
  add_dependencies(Poly Poly-EP)
  add_dependencies(Polyxx Poly-EP)

  ExternalProject_Get_Property(Poly-EP BUILD_BYPRODUCTS INSTALL_DIR)
  string(REPLACE "<INSTALL_DIR>" "${INSTALL_DIR}" BUILD_BYPRODUCTS "${BUILD_BYPRODUCTS}")
  install(FILES
    ${BUILD_BYPRODUCTS}
    DESTINATION ${CMAKE_INSTALL_LIBDIR}
  )
endif()
