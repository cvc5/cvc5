# Find LFSC
# LFSC_FOUND - system has LFSC lib
# LFSC_INCLUDE_DIR - the LFSC include directory
# LFSC_LIBRARIES - Libraries needed to use LFSC

find_path(LFSC_INCLUDE_DIR NAMES lfscc.h)
find_library(LFSC_LIBRARIES NAMES lfscc)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LFSC
  DEFAULT_MSG
  LFSC_INCLUDE_DIR LFSC_LIBRARIES)

mark_as_advanced(LFSC_INCLUDE_DIR LFSC_LIBRARIES)
if(LFSC_LIBRARIES)
  message(STATUS "Found LFSC libs: ${LFSC_LIBRARIES}")
endif()
