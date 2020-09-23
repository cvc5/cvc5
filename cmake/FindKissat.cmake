#####################
## FindKissat.cmake
## Top contributors (to current version):
##   Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find Kissat
# Kissat_FOUND - found Kissat lib
# Kissat_INCLUDE_DIR - the Kissat include directory
# Kissat_LIBRARIES - Libraries needed to use Kissat

find_path(Kissat_INCLUDE_DIR NAMES kissat/kissat.h)
find_library(Kissat_LIBRARIES NAMES kissat)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Kissat
  DEFAULT_MSG Kissat_INCLUDE_DIR Kissat_LIBRARIES)

mark_as_advanced(Kissat_INCLUDE_DIR Kissat_LIBRARIES)
if(Kissat_LIBRARIES)
  message(STATUS "Found Kissat library: ${Kissat_LIBRARIES}")
endif()

