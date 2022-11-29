###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Andres Noetzli
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find LFSC
# LFSC_FOUND - system has LFSC lib
# LFSC_INCLUDE_DIR - the LFSC include directory
# LFSC_LIBRARIES - Libraries needed to use LFSC
##

find_program(LFSC_BINARY
    NAMES lfscc
    PATHS ${CMAKE_SOURCE_DIR}/deps/bin
)
find_path(LFSC_INCLUDE_DIR
    NAMES lfscc.h
    PATHS ${CMAKE_SOURCE_DIR}/deps/include
)
find_library(LFSC_LIBRARIES
    NAMES lfscc
    PATHS ${CMAKE_SOURCE_DIR}/deps/lib
)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LFSC
    QUIET
    LFSC_BINARY LFSC_INCLUDE_DIR LFSC_LIBRARIES)

mark_as_advanced(LFSC_BINARY LFSC_INCLUDE_DIR LFSC_LIBRARIES)
if(LFSC_FOUND)
  message(STATUS "Found LFSC: ${LFSC_BINARY}")
endif()
