#####################
## FindPoly.cmake
## Top contributors (to current version):
##   Gereon Kremer
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find LibPoly
# POLY_FOUND - system has LibPoly
# POLY_INCLUDE_DIR - the LibPoly include directory
# POLY_LIBRARIES - Libraries needed to use LibPoly

# Note: contrib/get-poly copies header files to deps/install/include/poly.
# However, includes in LibPoly headers are not prefixed with "poly/" and therefore
# we have to look for headers in include/poly instead of include/.
find_path(POLY_INCLUDE_DIR NAMES poly/poly.h PATH_SUFFIXES poly)
find_library(POLY_LIB NAMES poly)
find_library(POLY_LIBXX NAMES polyxx)
set(POLY_LIBRARIES "${POLY_LIBXX};${POLY_LIB}")
unset(POLY_LIB CACHE)
unset(POLY_LIBXX CACHE)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Poly
  DEFAULT_MSG
  POLY_INCLUDE_DIR POLY_LIBRARIES)

mark_as_advanced(POLY_INCLUDE_DIR POLY_LIBRARIES)
if(POLY_LIBRARIES)
  message(STATUS "Found LibPoly: ${POLY_LIBRARIES}")
endif()
