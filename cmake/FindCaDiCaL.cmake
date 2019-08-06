# Find CaDiCaL
# CaDiCaL_FOUND - system has CaDiCaL lib
# CaDiCaL_INCLUDE_DIR - the CaDiCaL include directory
# CaDiCaL_LIBRARIES - Libraries needed to use CaDiCaL


# Check default location of CaDiCaL built with contrib/get-cadical.
# If the user provides a directory we will not search the default paths and
# fail if CaDiCaL was not found in the specified directory.
if(NOT CaDiCaL_HOME)
  set(CaDiCaL_HOME ${PROJECT_SOURCE_DIR}/cadical)
  set(CHECK_SYSTEM_VERSION TRUE)
endif()

find_path(CaDiCaL_INCLUDE_DIR
          NAMES cadical.hpp
          PATHS ${CaDiCaL_HOME}/src
          NO_DEFAULT_PATH)
find_library(CaDiCaL_LIBRARIES
             NAMES cadical
             PATHS ${CaDiCaL_HOME}/build
             NO_DEFAULT_PATH)

if(CHECK_SYSTEM_VERSION)
  find_path(CaDiCaL_INCLUDE_DIR NAMES cadical.hpp)
  find_library(CaDiCaL_LIBRARIES NAMES cadical)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CaDiCaL
  DEFAULT_MSG
  CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)

mark_as_advanced(CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)
if(CaDiCaL_LIBRARIES)
  message(STATUS "Found CaDiCaL libs: ${CaDiCaL_LIBRARIES}")
endif()
