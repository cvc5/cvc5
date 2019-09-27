# Find CryptoMiniSat
# CryptoMiniSat_FOUND - system has CryptoMiniSat lib
# CryptoMiniSat_INCLUDE_DIR - the CryptoMiniSat include directory
# CryptoMiniSat_LIBRARIES - Libraries needed to use CryptoMiniSat


# Check default location of CryptoMiniSat built with contrib/get-cryptominisat.
# If the user provides a directory we will not search the default paths and
# fail if CryptoMiniSat was not found in the specified directory.
if(NOT CryptoMiniSat_HOME)
  set(CryptoMiniSat_HOME ${PROJECT_SOURCE_DIR}/cryptominisat5/build)
  set(CHECK_SYSTEM_VERSION TRUE)
endif()

find_path(CryptoMiniSat_INCLUDE_DIR
          NAMES cryptominisat5/cryptominisat.h
          PATHS ${CryptoMiniSat_HOME}/include ${CryptoMiniSat_HOME}/cmsat5-src
          NO_DEFAULT_PATH)
find_library(CryptoMiniSat_LIBRARIES
             NAMES cryptominisat5
             PATHS ${CryptoMiniSat_HOME}/lib
             NO_DEFAULT_PATH)

if(CHECK_SYSTEM_VERSION)
  find_path(CryptoMiniSat_INCLUDE_DIR NAMES cryptominisat5/cryptominisat.h)
  find_library(CryptoMiniSat_LIBRARIES NAMES cryptominisat5)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CryptoMiniSat
  DEFAULT_MSG
  CryptoMiniSat_INCLUDE_DIR CryptoMiniSat_LIBRARIES)

mark_as_advanced(CryptoMiniSat_INCLUDE_DIR CryptoMiniSat_LIBRARIES)
if(CryptoMiniSat_LIBRARIES)
  message(STATUS "Found CryptoMiniSat libs: ${CryptoMiniSat_LIBRARIES}")
endif()
