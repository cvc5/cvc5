# Find GMP
# GMP_FOUND - system has GMP lib
# GMP_INCLUDE_DIR - the GMP include directory
# GMP_LIBRARIES - Libraries needed to use GMP


# Check default location of GMP built with contrib/get-gmp.
# If the user provides a directory we will not search the default paths and
# fail if GMP was not found in the specified directory.
if(NOT GMP_HOME)
  set(GMP_HOME ${PROJECT_SOURCE_DIR}/gmp-6.1.2)
  set(CHECK_SYSTEM_VERSION TRUE)
endif()

find_path(GMP_INCLUDE_DIR
          NAMES gmp.h gmpxx.h
          PATHS ${GMP_HOME}/include
          NO_DEFAULT_PATH)
find_library(GMP_LIBRARIES
             NAMES gmp
             PATHS ${GMP_HOME}/lib
             NO_DEFAULT_PATH)

if(CHECK_SYSTEM_VERSION)
  find_path(GMP_INCLUDE_DIR NAMES gmp.h gmpxx.h)
  find_library(GMP_LIBRARIES NAMES gmp)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP DEFAULT_MSG GMP_INCLUDE_DIR GMP_LIBRARIES)

mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARIES)
if(GMP_LIBRARIES)
  message(STATUS "Found GMP libs: ${GMP_LIBRARIES}")
endif()
