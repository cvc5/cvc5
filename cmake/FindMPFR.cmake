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

find_path(MPFR_INCLUDE_DIR NAMES mpfr.h)
find_library(MPFR_LIBRARIES NAMES mpfr)

set(MPFR_FOUND_SYSTEM FALSE)
if(MPFR_INCLUDE_DIR AND MPFR_LIBRARIES)
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
  message(FATAL_ERROR
    "Could not find MPFR. Install libmpfr-dev (Debian/Ubuntu), "
    "mpfr-devel (Fedora), or mpfr (brew/macports)."
  )
endif()

set(MPFR_FOUND TRUE)

if(NOT TARGET MPFR)
  if(BUILD_SHARED_LIBS)
    add_library(MPFR SHARED IMPORTED GLOBAL)
  else()
    add_library(MPFR STATIC IMPORTED GLOBAL)
  endif()
  set_target_properties(MPFR PROPERTIES
    IMPORTED_LOCATION "${MPFR_LIBRARIES}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${MPFR_INCLUDE_DIR}"
  )
  target_link_libraries(MPFR INTERFACE GMP)
endif()

mark_as_advanced(MPFR_FOUND)
mark_as_advanced(MPFR_FOUND_SYSTEM)
mark_as_advanced(MPFR_INCLUDE_DIR)
mark_as_advanced(MPFR_LIBRARIES)

message(STATUS "Found MPFR ${MPFR_VERSION}: ${MPFR_LIBRARIES}")
