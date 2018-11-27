# Find Readline
# Readline_FOUND - system has Readline lib
# Readline_INCLUDE_DIR - the Readline include directory
# Readline_LIBRARIES - Libraries needed to use Readline
# Readline_COMPENTRY_FUNC_RETURNS_CHARPTR - Indicates if compentry function
#                                           returns a (char *)

find_path(Readline_INCLUDE_DIR NAMES readline/readline.h)
find_library(Readline_LIBRARIES NAMES readline)

# Try to compile and link a simple program against readline. 'libs' can be
# used to specify additional required libraries.
function(try_compile_readline libs _result)
  set(CMAKE_REQUIRED_QUIET TRUE)
  set(CMAKE_REQUIRED_LIBRARIES ${Readline_LIBRARIES} ${libs})
  check_cxx_source_compiles(
    "
    #include <stdio.h>
    #include <readline/readline.h>
    int main() { readline(\"\"); return 0; }
    "
    ${_result}
  )
  set(${_result} ${${_result}} PARENT_SCOPE)
endfunction()

if(Readline_INCLUDE_DIR)
  # We only need to figure out readline's additional libraries dependencies if
  # we compile static.
  # Note: It might be the case that we need to check for more/other libraries
  # depending on what the installed version of readline is linked against
  # (e.g., termcap, ncurses, ...).
    find_library(TINFO_LIBRARY tinfo)
    try_compile_readline(${TINFO_LIBRARY} OK)
    if(OK)
      list(APPEND Readline_LIBRARIES ${TINFO_LIBRARY})
    else()
      message(FATAL_ERROR
              "Could not link against readline. "
              "Check CMakeError.log for more details")
    endif()

  # Check which standard of readline is installed on the system.
  # https://github.com/CVC4/CVC4/issues/702
  include(CheckCXXSourceCompiles)
  set(CMAKE_REQUIRED_QUIET TRUE)
  set(CMAKE_REQUIRED_LIBRARIES ${Readline_LIBRARIES})
  check_cxx_source_compiles(
    "#include <stdio.h>
     #include <readline/readline.h>
     char* foo(const char*, int) { return (char*)0; }
     int main() { rl_completion_entry_function = foo; return 0; }"
     Readline_COMPENTRY_FUNC_RETURNS_CHARPTR
  )
  unset(CMAKE_REQUIRED_QUIET)
  unset(CMAKE_REQUIRED_LIBRARIES)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Readline
  DEFAULT_MSG Readline_INCLUDE_DIR Readline_LIBRARIES)
mark_as_advanced(
  Readline_INCLUDE_DIR
  Readline_LIBRARIES
  Readline_COMPENTRY_FUNC_RETURNS_CHARPTR
)
if(Readline_LIBRARIES)
  message(STATUS "Found Readline libs: ${Readline_LIBRARIES}")
endif()
