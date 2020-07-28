# Find Editline
# Editline_FOUND - found Editline lib
# Editline_INCLUDE_DIR - the Editline include directory
# Editline_LIBRARIES - Libraries needed to use Editline
# Editline_COMPENTRY_FUNC_RETURNS_CHARPTR - Indicates if compentry function
#                                           returns a (char *)

find_path(Editline_INCLUDE_DIR NAMES histedit.h)
find_library(Editline_LIBRARIES NAMES edit libedit)

if(Editline_INCLUDE_DIR)
  # Check which standard of editline is installed on the system.
  # https://github.com/CVC4/CVC4/issues/702
  include(CheckCXXSourceCompiles)
  set(CMAKE_REQUIRED_QUIET TRUE)
  set(CMAKE_REQUIRED_LIBRARIES ${Editline_LIBRARIES})
  set(CMAKE_REQUIRED_INCLUDES ${Editline_INCLUDE_DIR})
  check_cxx_source_compiles(
    "#include <stdio.h>
     #include <editline/readline.h>
     char* foo(const char*, int) { return (char*)0; }
     int main() { rl_completion_entry_function = foo; return 0; }"
     Editline_COMPENTRY_FUNC_RETURNS_CHARPTR
  )
  unset(CMAKE_REQUIRED_QUIET)
  unset(CMAKE_REQUIRED_LIBRARIES)
  unset(CMAKE_REQUIRED_INCLUDES)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Editline
  DEFAULT_MSG Editline_INCLUDE_DIR Editline_LIBRARIES)
mark_as_advanced(
  Editline_INCLUDE_DIR
  Editline_LIBRARIES
  Editline_COMPENTRY_FUNC_RETURNS_CHARPTR
)
if(Editline_LIBRARIES)
  message(STATUS "Editline library: ${Editline_LIBRARIES}")
endif()
