###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Aina Niemetz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Kissat
# Kissat_FOUND - found Kissat lib
# Kissat_INCLUDE_DIR - the Kissat include directory
# Kissat_LIBRARIES - Libraries needed to use Kissat
##

include(deps-helper)

find_path(Kissat_INCLUDE_DIR NAMES kissat/kissat.h)
find_library(Kissat_LIBRARIES NAMES kissat)

set(Kissat_FOUND_SYSTEM FALSE)
if(Kissat_INCLUDE_DIR AND Kissat_LIBRARIES)
  set(Kissat_FOUND_SYSTEM TRUE)

  # Unfortunately it is not part of the headers
  find_library(Kissat_BINARY NAMES kissat)
  if(Kissat_BINARY)
    execute_process(
      COMMAND ${Kissat_BINARY} --version OUTPUT_VARIALE Kissat_VERSION
    )
  else()
    set(Kissat_VERSION "")
  endif()

  check_system_version("Kissat")
endif()

if(NOT Kissat_FOUND_SYSTEM)
  check_ep_downloaded("Kissat-EP")
  if(NOT Kissat-EP_DOWNLOADED)
    check_auto_download("Kissat" "--no-kissat")
  endif()

  include(ExternalProject)

  fail_if_include_missing("sys/resource.h" "Kissat")

  set(Kissat_VERSION "sc2021")
  set(Kissat_CHECKSUM "ad1945cc6980cc6d8b7049cf0a298f9f806ac3c9ca1ccb51f1bc533253d285cc")

  ExternalProject_Add(
    Kissat-EP
    ${COMMON_EP_CONFIG}
    BUILD_IN_SOURCE ON
    URL https://github.com/arminbiere/kissat/archive/${Kissat_VERSION}.tar.gz
    URL_HASH SHA256=${Kissat_CHECKSUM}
    CONFIGURE_COMMAND <SOURCE_DIR>/configure -fPIC --quiet
                      CC=${CMAKE_C_COMPILER}
    INSTALL_COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/build/libkissat.a
                    <INSTALL_DIR>/lib/libkissat.a
    COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/src/kissat.h
            <INSTALL_DIR>/include/kissat/kissat.h
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libkissat.a
  )

  set(Kissat_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(Kissat_LIBRARIES "${DEPS_BASE}/lib/libkissat.a")
endif()

set(Kissat_FOUND TRUE)

add_library(Kissat STATIC IMPORTED GLOBAL)
set_target_properties(Kissat PROPERTIES IMPORTED_LOCATION "${Kissat_LIBRARIES}")
set_target_properties(
  Kissat PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Kissat_INCLUDE_DIR}"
)

mark_as_advanced(Kissat_FOUND)
mark_as_advanced(Kissat_FOUND_SYSTEM)
mark_as_advanced(Kissat_INCLUDE_DIR)
mark_as_advanced(Kissat_LIBRARIES)

if(Kissat_FOUND_SYSTEM)
  message(STATUS "Found Kissat ${Kissat_VERSION}: ${Kissat_LIBRARIES}")
else()
  message(STATUS "Building Kissat ${Kissat_VERSION}: ${Kissat_LIBRARIES}")
  add_dependencies(Kissat Kissat-EP)
  # Install static library only if it is a static build.
  if(NOT BUILD_SHARED_LIBS)
    install(FILES ${Kissat_LIBRARIES} TYPE ${LIB_BUILD_TYPE})
  endif()
endif()
