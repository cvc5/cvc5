include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

if(NOT WIN32)
  string(ASCII 27 Esc)
  set(Yellow "${Esc}[33m")
  set(ResetColor "${Esc}[m")
endif()

# Add a C flag to the global list of C flags.
macro(add_c_flag flag)
  if(CMAKE_C_FLAGS)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${flag}")
  else()
    set(CMAKE_C_FLAGS "${flag}")
  endif()
  message(STATUS "Configuring with C flag '${flag}'")
endmacro()

# Add a CXX flag to the global list of CXX flags.
macro(add_cxx_flag flag)
  if(CMAKE_CXX_FLAGS)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
  else()
    set(CMAKE_CXX_FLAGS "${flag}")
  endif()
  message(STATUS "Configuring with CXX flag '${flag}'")
endmacro()

# Add a C and CXX flag to the global list of C/CXX flags.
macro(add_c_cxx_flag flag)
  add_c_flag(${flag})
  add_cxx_flag(${flag})
endmacro()

# Check if C flag is supported and add to global list of C flags.
macro(add_check_c_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_c_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if(HAVE_FLAG${flagname})
    add_c_flag(${flag})
  endif()
endmacro()

# Check if CXX flag is supported and add to global list of CXX flags.
macro(add_check_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if(HAVE_FLAG${flagname})
    add_cxx_flag(${flag})
  endif()
endmacro()

# Check if C/CXX flag is supported and add to global list of C/CXX flags.
macro(add_check_c_cxx_flag flag)
  add_check_c_flag(${flag})
  add_check_cxx_flag(${flag})
endmacro()

# Add required CXX flag. Configuration fails if the CXX flag is not supported
# by the compiler.
macro(add_required_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagnamename ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if (NOT HAVE_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_cxx_flag(${flag})
endmacro()

# Add required C flag. Configuration fails if the C flag is not supported by
# the compiler.
macro(add_required_c_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_c_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if (NOT HAVE_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_c_flag(${flag})
endmacro()

# Add requied C/CXX flag. Configuration fails if the C/CXX flag is not
# supported by the compiler.
macro(add_required_c_cxx_flag flag)
  add_required_c_flag(${flag})
  add_required_cxx_flag(${flag})
endmacro()

# CVC4 Boolean options are three-valued to detect if an option was set by the
# user. The available values are: IGNORE (default), ON, OFF
# Default options do not override options that were set by the user, i.e.,
# cvc4_set_option only sets an option if it's value is still IGNORE.
# This e.g., allows the user to disable proofs for debug builds (where proofs
# are enabled by default).
macro(cvc4_option var description)
  set(${var} IGNORE CACHE STRING "${description}")
  # Provide drop down menu options in cmake-gui
  set_property(CACHE ${var} PROPERTY STRINGS IGNORE ON OFF)
endmacro()

# Only set option if the user did not set an option.
macro(cvc4_set_option var value)
  if(${var} STREQUAL "IGNORE")
    set(${var} ${value})
  endif()
endmacro()

# Prepend 'prepand_value' to each element of the list 'in_list'. The result
# is stored in 'out_list'.
function(list_prepend in_list prepand_value out_list)
  foreach(_elem ${${in_list}})
    list(APPEND ${out_list} "${prepand_value}${_elem}")
  endforeach()
  set(${out_list} ${${out_list}} PARENT_SCOPE)
endfunction()

# Helper to print the configuration of a 2-valued or 3-valued option 'var'
# with prefix 'str'.
macro(print_config str var)
  if(${var} STREQUAL "ON")
    set(OPT_VAL_STR "on")
  else()
    set(OPT_VAL_STR "off")
  endif()
  message("${str} ${OPT_VAL_STR}")
endmacro()


# Collect all source files that are required to build libcvc4 in LIBCVC4_SRCS
# or LIBCVC4_GEN_SRCS. If GENERATED is the first argument the sources are
# added to LIBCVC4_GEN_SRCS. All sources are prepended with the absolute
# current path path. CMAKE_CURRENT_BINARY_DIR is prepended
# to generated source files.
macro(libcvc4_add_sources)
  set(_sources ${ARGV})

  # Check if the first argument is GENERATED.
  list(GET _sources 0 _generated)
  if(${_generated} STREQUAL "GENERATED")
    list(REMOVE_AT _sources 0)
    set(_cur_path ${CMAKE_CURRENT_BINARY_DIR})
    set(_append_to LIBCVC4_GEN_SRCS)
  else()
    set(_cur_path ${CMAKE_CURRENT_SOURCE_DIR})
    set(_append_to LIBCVC4_SRCS)
  endif()

  # Prepend source files with current path.
  foreach(_src ${_sources})
    list(APPEND ${_append_to} "${_cur_path}/${_src}")
  endforeach()

  file(RELATIVE_PATH
       _rel_path "${PROJECT_SOURCE_DIR}/src" "${CMAKE_CURRENT_SOURCE_DIR}")

  # Make changes to list ${_append_to} visible to the parent scope if not
  # called from src/.
  # Note: ${_append_to} refers to the variable name whereas ${${_append_to}}
  # refers to the contents of the variable.
  if(_rel_path)
    set(${_append_to} ${${_append_to}} PARENT_SCOPE)
  endif()
endmacro()
