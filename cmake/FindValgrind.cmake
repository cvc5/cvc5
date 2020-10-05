#####################
## FindValgrind.cmake
## Top contributors (to current version):
##   Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
# Find Valgrind
# Valgrind_FOUND - system has Valgrind lib
# Valgrind_INCLUDE_DIR - the Valgrind include directory
#
# Note: We only require the valgrind/memcheck.h header, so we don't check if
# the valgrind executable is installed.

find_path(Valgrind_INCLUDE_DIR NAMES valgrind/memcheck.h)

find_package_handle_standard_args(Valgrind REQUIRED_VARS Valgrind_INCLUDE_DIR)
mark_as_advanced(Valgrind_INCLUDE_DIR)
