#####################
## FindCaDiCaL.cmake
## Top contributors (to current version):
##   Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find CaDiCaL
# CaDiCaL_FOUND - system has CaDiCaL lib
# CaDiCaL_INCLUDE_DIR - the CaDiCaL include directory
# CaDiCaL_LIBRARIES - Libraries needed to use CaDiCaL

find_path(CaDiCaL_INCLUDE_DIR NAMES cadical.hpp)
find_library(CaDiCaL_LIBRARIES NAMES cadical)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CaDiCaL
  DEFAULT_MSG
  CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)

mark_as_advanced(CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)
if(CaDiCaL_LIBRARIES)
  message(STATUS "Found CaDiCaL libs: ${CaDiCaL_LIBRARIES}")
endif()
