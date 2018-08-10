# Find ANTLR
# ANTLR_FOUND - system has ANTLR lib
# ANTLR_BINARY - the ANTLR binary
# ANTLR_INCLUDE_DIR - the ANTLR include directory
# ANTLR_LIBRARIES - Libraries needed to use ANTLR

find_program(ANTLR_BINARY
  NAMES antlr3
  PATHS "${PROJECT_SOURCE_DIR}/antlr-3.4/bin"
  )

find_path(ANTLR_INCLUDE_DIR
  NAMES antlr3.h
  PATHS "${PROJECT_SOURCE_DIR}/antlr-3.4/include"
  )

find_library(ANTLR_LIBRARIES
  NAMES antlr3c libantlr3c
  PATHS "${PROJECT_SOURCE_DIR}/antlr-3.4/lib"
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  ANTLR DEFAULT_MSG ANTLR_BINARY ANTLR_INCLUDE_DIR ANTLR_LIBRARIES)

mark_as_advanced(ANTLR_BINARY ANTLR_INCLUDE_DIR ANTLR_LIBRARIES)
