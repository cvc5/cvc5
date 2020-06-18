# Find libpoly
# POLY_FOUND - system has libpoly
# POLY_INCLUDE_DIR - the libpoly include directory
# POLY_LIBRARIES - Libraries needed to use libpoly
# POLY_ARCH_FLAGS - Platform specific compile flags

# Note: contrib/get-poly copies header files to deps/install/include/poly.
# However, includes in libpoly headers are not prefixed with "poly/" and therefore
# we have to look for headers in include/poly instead of include/.
find_path(POLY_INCLUDE_DIR NAMES poly/poly.h PATH_SUFFIXES poly)
find_library(POLY_LIB NAMES poly)
find_library(POLY_LIBXX NAMES polyxx)
set(POLY_LIBRARIES "${POLY_LIBXX};${POLY_LIB}")
unset(POLY_LIB)
unset(POLY_LIBXX)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Poly
  DEFAULT_MSG
  POLY_INCLUDE_DIR POLY_LIBRARIES)

mark_as_advanced(POLY_INCLUDE_DIR POLY_LIBRARIES)
if(POLY_LIBRARIES)
  message(STATUS "Found polylib: ${POLY_LIBRARIES}")
endif()
