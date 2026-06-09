###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Editline
# Editline_FOUND - found Editline lib
# Editline_INCLUDE_DIRS - the Editline include directory
# Editline_LIBRARIES - Libraries needed to use Editline
##

# When finding libedit, use pkg-config to ensure we find all the required
# linking flags for libedit
find_package(PkgConfig REQUIRED)
pkg_check_modules(Editline REQUIRED libedit)

if(Editline_INCLUDE_DIRS)
  if(NOT CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    find_library(BSD_LIBRARIES NAMES bsd)
    if (BSD_LIBRARIES)
      set(Editline_LIBRARIES ${Editline_LIBRARIES} bsd)
    endif()
    set(Editline_LIBRARIES ${Editline_LIBRARIES} tinfo)
  endif()
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Editline
  DEFAULT_MSG Editline_INCLUDE_DIRS Editline_LIBRARIES)
mark_as_advanced(
  Editline_INCLUDE_DIRS
  Editline_LIBRARIES
)
if(Editline_LIBRARIES)
  message(STATUS "Editline library: ${Editline_LIBRARIES}")
endif()
