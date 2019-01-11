# Find drat2er
# Drat2Er_FOUND - system has Drat2Er lib
# Drat2Er_INCLUDE_DIR - the Drat2Er include directory
# Drat2Er_LIBRARIES - Libraries needed to use Drat2Er


# Check default location of Drat2Er built with contrib/get-drat2er.
# If the user provides a directory we will not search the default paths and
# fail if Drat2Er was not found in the specified directory.
if(NOT Drat2Er_HOME)
  set(Drat2Er_HOME ${PROJECT_SOURCE_DIR}/drat2er/build/install)
endif()

find_path(Drat2Er_INCLUDE_DIR
          NAMES drat2er.h
          PATHS ${Drat2Er_HOME}/include
          NO_DEFAULT_PATH)
find_library(Drat2Er_LIBRARIES
             NAMES libdrat2er.a
             PATHS ${Drat2Er_HOME}/lib
             NO_DEFAULT_PATH)
find_library(DratTrim_LIBRARIES
             NAMES libdrat-trim.a
             PATHS ${Drat2Er_HOME}/lib
             NO_DEFAULT_PATH)

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
