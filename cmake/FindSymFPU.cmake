#####################
## FindSymFPU.cmake
## Top contributors (to current version):
##   Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find SymFPU
# SymFPU_FOUND - system has SymFPU lib
# SymFPU_INCLUDE_DIR - the SymFPU include directory

find_path(SymFPU_INCLUDE_DIR NAMES symfpu/core/unpackedFloat.h)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(SymFPU DEFAULT_MSG SymFPU_INCLUDE_DIR)

mark_as_advanced(SymFPU_INCLUDE_DIR)
