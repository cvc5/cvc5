#####################
## FindANTLR.cmake
## Top contributors (to current version):
##   Mathias Preiner, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find ANTLR
# ANTLR_FOUND - system has ANTLR lib
# ANTLR_BINARY - the ANTLR binary
# ANTLR_INCLUDE_DIR - the ANTLR include directory
# ANTLR_LIBRARIES - Libraries needed to use ANTLR

find_program(ANTLR_BINARY NAMES antlr3)
find_path(ANTLR_INCLUDE_DIR NAMES antlr3.h)
find_library(ANTLR_LIBRARIES NAMES antlr3c antlr3c-static)

# Check if antlr3FileStreamNew is available. If not we have to
# define CVC4_ANTLR3_OLD_INPUT_STREAM (src/parser/CMakeLists.txt).
if(ANTLR_INCLUDE_DIR)
  include(CheckSymbolExists)
  set(CMAKE_REQUIRED_INCLUDES ${ANTLR_INCLUDE_DIR})
  set(CMAKE_REQUIRED_LIBRARIES ${ANTLR_LIBRARIES})
  check_symbol_exists(
    antlr3FileStreamNew "antlr3defs.h" HAVE_ANTLR3_FILE_STREAM_NEW)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  ANTLR DEFAULT_MSG ANTLR_BINARY ANTLR_INCLUDE_DIR ANTLR_LIBRARIES)

mark_as_advanced(ANTLR_BINARY ANTLR_INCLUDE_DIR ANTLR_LIBRARIES
                 HAVE_ANTLR3_FILE_STREAM_NEW)
if(ANTLR_LIBRARIES)
  message(STATUS "Found ANTLR libs: ${ANTLR_LIBRARIES}")
endif()
