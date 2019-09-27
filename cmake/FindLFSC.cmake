# Find LFSC
# LFSC_FOUND - system has LFSC lib
# LFSC_INCLUDE_DIR - the LFSC include directory
# LFSC_LIBRARIES - Libraries needed to use LFSC


# Check default location of LFSC built with contrib/get-lfsc.
# If the user provides a directory we will not search the default paths and
# fail if LFSC was not found in the specified directory.
if(NOT LFSC_HOME)
  set(LFSC_HOME ${PROJECT_SOURCE_DIR}/lfsc-checker/install)
  set(CHECK_SYSTEM_VERSION TRUE)
endif()

find_path(LFSC_INCLUDE_DIR
          NAMES lfscc.h
          PATHS ${LFSC_HOME}/include
          NO_DEFAULT_PATH)
find_library(LFSC_LIBRARIES
             NAMES lfscc
             PATHS ${LFSC_HOME}/lib
             NO_DEFAULT_PATH)

if(CHECK_SYSTEM_VERSION)
  find_path(LFSC_INCLUDE_DIR NAMES lfscc.h)
  find_library(LFSC_LIBRARIES NAMES lfscc)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LFSC
  DEFAULT_MSG
  LFSC_INCLUDE_DIR LFSC_LIBRARIES)

mark_as_advanced(LFSC_INCLUDE_DIR LFSC_LIBRARIES)
if(LFSC_LIBRARIES)
  message(STATUS "Found LFSC libs: ${LFSC_LIBRARIES}")
endif()
