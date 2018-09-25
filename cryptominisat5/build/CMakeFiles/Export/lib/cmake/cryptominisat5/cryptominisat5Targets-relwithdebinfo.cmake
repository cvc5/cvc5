#----------------------------------------------------------------
# Generated CMake target import file for configuration "RelWithDebInfo".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "libcryptominisat5" for configuration "RelWithDebInfo"
set_property(TARGET libcryptominisat5 APPEND PROPERTY IMPORTED_CONFIGURATIONS RELWITHDEBINFO)
set_target_properties(libcryptominisat5 PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_RELWITHDEBINFO "CXX"
  IMPORTED_LOCATION_RELWITHDEBINFO "${_IMPORT_PREFIX}/lib/libcryptominisat5.a"
  )

list(APPEND _IMPORT_CHECK_TARGETS libcryptominisat5 )
list(APPEND _IMPORT_CHECK_FILES_FOR_libcryptominisat5 "${_IMPORT_PREFIX}/lib/libcryptominisat5.a" )

# Import target "cryptominisat5_simple" for configuration "RelWithDebInfo"
set_property(TARGET cryptominisat5_simple APPEND PROPERTY IMPORTED_CONFIGURATIONS RELWITHDEBINFO)
set_target_properties(cryptominisat5_simple PROPERTIES
  IMPORTED_LOCATION_RELWITHDEBINFO "${_IMPORT_PREFIX}/bin/cryptominisat5_simple"
  )

list(APPEND _IMPORT_CHECK_TARGETS cryptominisat5_simple )
list(APPEND _IMPORT_CHECK_FILES_FOR_cryptominisat5_simple "${_IMPORT_PREFIX}/bin/cryptominisat5_simple" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
