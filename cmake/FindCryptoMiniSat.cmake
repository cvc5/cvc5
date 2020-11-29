#####################
## FindCryptoMiniSat.cmake
## Top contributors (to current version):
##   Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find CryptoMiniSat
# CryptoMiniSat_FOUND - system has CryptoMiniSat lib
# CryptoMiniSat_INCLUDE_DIR - the CryptoMiniSat include directory
# CryptoMiniSat_LIBRARIES - Libraries needed to use CryptoMiniSat


find_path(CryptoMiniSat_INCLUDE_DIR NAMES cryptominisat5/cryptominisat.h)
find_library(CryptoMiniSat_LIBRARIES NAMES cryptominisat5)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CryptoMiniSat
  DEFAULT_MSG
  CryptoMiniSat_INCLUDE_DIR CryptoMiniSat_LIBRARIES)

mark_as_advanced(CryptoMiniSat_INCLUDE_DIR CryptoMiniSat_LIBRARIES)
if(CryptoMiniSat_LIBRARIES)
  message(STATUS "Found CryptoMiniSat libs: ${CryptoMiniSat_LIBRARIES}")
endif()
