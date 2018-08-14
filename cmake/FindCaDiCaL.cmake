# Find CaDiCaL
# CaDiCaL_FOUND - system has CaDiCaL lib
# CaDiCaL_INCLUDE_DIR - the CaDiCaL include directory
# CaDiCaL_LIBRARIES - Libraries needed to use CaDiCaL

find_path(CaDiCaL_INCLUDE_DIR
          NAMES cadical.hpp
          PATHS "${PROJECT_SOURCE_DIR}/cadical/src")
find_library(CaDiCaL_LIBRARIES
             NAMES cadical
             PATHS "${PROJECT_SOURCE_DIR}/cadical/build")

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CaDiCaL
  DEFAULT_MSG
  CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)

mark_as_advanced(CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)
