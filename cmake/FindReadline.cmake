# Find Readline
# Readline_FOUND - system has Readline lib
# Readline_INCLUDE_DIR - the Readline include directory
# Readline_LIBRARIES - Libraries needed to use Readline

find_path(Readline_INCLUDE_DIR NAMES readline/readline.h)
find_library(Readline_LIBRARIES NAMES readline)

# Check which standard of readline is installed on the system.
# https://github.com/CVC4/CVC4/issues/702
if(Readline_INCLUDE_DIR)
  include(CheckCXXSourceCompiles)
  set(CMAKE_REQUIRED_QUIET TRUE)
  set(CMAKE_REQUIRED_LIBRARIES readline)
  check_cxx_source_compiles(
    "#include <stdio.h>
     #include <readline/readline.h>
     char* foo(const char*, int) { return (char*)0; }
     int main() { rl_completion_entry_function = foo; return 0; }"
     Readline_COMPENTRY_FUNC_RETURNS_CHARPTR
  )
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Readline
  DEFAULT_MSG Readline_INCLUDE_DIR Readline_LIBRARIES)
mark_as_advanced(
  Readline_INCLUDE_DIR
  Readline_LIBRARIES
  Readline_COMPENTRY_FUNC_RETURNS_CHARPTR
)
