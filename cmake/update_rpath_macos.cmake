###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Update the RPATH of a macOS dynamic library to make it relocatable
#
# This script updates RPATH if not already set, replaces ${DEPS_BASE}/lib with 
# @rpath in the install name and in the paths of all library dependencies to
# ensure the dynamic library is relocatable.
#
# Input variables:
# RPATH - The rpath to use in the dynamic library
# INSTALL_NAME_TOOL - Path to the install_name tool
# DYLIB_PATH - Path to the dynamic library
# DEPS_BASE - Path to the cvc5 dependencies directory
##
# If RPATH is provided, add it unless it already exists
if(RPATH)
   # otool -l output is in the format:
   #      cmd LC_RPATH
   # cmdsize XX
   #      path <path> (offset YY)
  execute_process(
    COMMAND otool -l "${DYLIB_PATH}"
    COMMAND grep LC_RPATH -A2
    OUTPUT_VARIABLE RPATH_OUTPUT
  )
  if(NOT "${RPATH_OUTPUT}" MATCHES "${RPATH}")
    execute_process(
      COMMAND ${INSTALL_NAME_TOOL} -add_rpath ${RPATH} ${DYLIB_PATH}
    )
  endif()
endif()

# Get install name
execute_process(
  COMMAND otool -D "${DYLIB_PATH}"
  OUTPUT_VARIABLE INSTALL_NAME_OUTPUT
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
# otool -D output is in the format:
# libname.dylib:
#   /full/path/to/libname.n.dylib
# Extract the second line which contains the actual install name
string(REPLACE "\n" ";" INSTALL_NAME_LIST "${INSTALL_NAME_OUTPUT}")
list(GET INSTALL_NAME_LIST 1 INSTALL_NAME)

if("${INSTALL_NAME}" MATCHES "${DEPS_BASE}/lib")
  # Replace ${DEPS_BASE}/lib with @rpath
  string(REPLACE "${DEPS_BASE}/lib" "@rpath" NEW_INSTALL_NAME "${INSTALL_NAME}")
  execute_process(
    COMMAND ${INSTALL_NAME_TOOL} -id ${NEW_INSTALL_NAME} ${DYLIB_PATH}
  )
endif()

# Get all dependencies and replace ${DEPS_BASE}/lib with @rpath
execute_process(
  COMMAND otool -L ${DYLIB_PATH}
  OUTPUT_VARIABLE OTOOL_OUTPUT
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
string(REPLACE "\n" ";" OTOOL_LINES "${OTOOL_OUTPUT}")
# Discard the first line which is the path to ${DYLIB_PATH}
list(REMOVE_AT OTOOL_LINES 0)
foreach(LINE ${OTOOL_LINES})
  if(LINE MATCHES "${DEPS_BASE}/lib/")
    string(REGEX REPLACE "^[ \t]*([^ \t]+).*" "\\1" LIB_PATH "${LINE}")
    string(REPLACE "${DEPS_BASE}/lib" "@rpath" LIB_RPATH "${LIB_PATH}")
    execute_process(
      COMMAND ${INSTALL_NAME_TOOL} -change ${LIB_PATH} ${LIB_RPATH} ${DYLIB_PATH}
    )
  endif()
endforeach()