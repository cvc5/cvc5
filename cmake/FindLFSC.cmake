#####################
## FindLFSC.cmake
## Top contributors (to current version):
##   Mathias Preiner, Andres Noetzli
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find LFSC
# LFSC_FOUND - system has LFSC lib
# LFSC_INCLUDE_DIR - the LFSC include directory
# LFSC_LIBRARIES - Libraries needed to use LFSC

find_program(LFSC_BINARY NAMES lfscc)
find_path(LFSC_INCLUDE_DIR NAMES lfscc.h)
find_library(LFSC_LIBRARIES NAMES lfscc)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LFSC
  DEFAULT_MSG
  LFSC_BINARY LFSC_INCLUDE_DIR LFSC_LIBRARIES)

mark_as_advanced(LFSC_BINARY LFSC_INCLUDE_DIR LFSC_LIBRARIES)
if(LFSC_FOUND)
  message(STATUS "Found LFSC include dir: ${LFSC_INCLUDE_DIR}")
  message(STATUS "Found LFSC libs: ${LFSC_LIBRARIES}")
endif()
