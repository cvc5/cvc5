# Find drat2er
# Drat2Er_FOUND - system has Drat2Er lib
# Drat2Er_INCLUDE_DIR - the Drat2Er include directory
# Drat2Er_LIBRARIES - Libraries needed to use Drat2Er

find_path(Drat2Er_INCLUDE_DIR NAMES drat2er.h)
find_library(Drat2Er_LIBRARIES NAMES libdrat2er.a)
find_library(DratTrim_LIBRARIES NAMES libdrat-trim.a)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Drat2Er
  DEFAULT_MSG
  Drat2Er_INCLUDE_DIR Drat2Er_LIBRARIES DratTrim_LIBRARIES)

mark_as_advanced(Drat2Er_INCLUDE_DIR Drat2Er_LIBRARIES DratTrim_LIBRARIES)
if(Drat2Er_LIBRARIES)
  message(STATUS "Found Drat2Er libs: ${Drat2Er_LIBRARIES}")
endif()
if(DratTrim_LIBRARIES)
  message(STATUS "Found DratTrim libs: ${DratTrim_LIBRARIES}")
  list(APPEND Drat2Er_LIBRARIES ${DratTrim_LIBRARIES})
endif()
