###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Aina Niemetz, Andrew V. Jones
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

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
  check_c_compiler_flag("${flag}" HAVE_C_FLAG${flagname})
  if(HAVE_C_FLAG${flagname})
    add_c_flag(${flag})
  endif()
endmacro()

# Check if CXX flag is supported and add to global list of CXX flags.
macro(add_check_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_CXX_FLAG${flagname})
  if(HAVE_CXX_FLAG${flagname})
    add_cxx_flag(${flag})
  endif()
endmacro()

# Check if C/CXX flag is supported and add to global list of C/CXX flags.
macro(add_check_c_cxx_flag flag)
  add_check_c_flag(${flag})
  add_check_cxx_flag(${flag})
endmacro()

# Check if C warning suppression flag is supported and add to global list of C
# flags.
macro(add_check_c_supression_flag supression_flag)
  # Obtain the non-supression warning flag name
  string(REGEX REPLACE "^-Wno-" "-W" warning_flag ${supression_flag})
  string(REGEX REPLACE "[-=]" "_" warning_flagname ${warning_flag})
  # Check if we have the warning flag
  check_c_compiler_flag("${warning_flag}" HAVE_C_FLAG${warning_flagname})
  # Only add the supression flag if we have the warning flag
  if(HAVE_C_FLAG${warning_flagname})
    add_c_flag(${supression_flag})
  endif()
endmacro()

# Check if CXX warning suppression flag is supported and add to global list of
# CXX flags.
macro(add_check_cxx_supression_flag supression_flag)
  # Obtain the non-supression warning flag name
  string(REGEX REPLACE "^-Wno-" "-W" warning_flag ${supression_flag})
  string(REGEX REPLACE "[-=]" "_" warning_flagname ${warning_flag})
  # Check if we have the warning flag
  check_cxx_compiler_flag("${warning_flag}" HAVE_CXX_FLAG${warning_flagname})
  # Only add the supression flag if we have the warning flag
  if(HAVE_CXX_FLAG${warning_flagname})
    add_cxx_flag(${supression_flag})
  endif()
endmacro()

# Check if C/CXX warning supression flag is supported and add to global list of
# C/CXX flags.
macro(add_check_c_cxx_supression_flag supression_flag)
  add_check_c_supression_flag(${supression_flag})
  add_check_cxx_supression_flag(${supression_flag})
endmacro()

# Add required CXX flag. Configuration fails if the CXX flag is not supported
# by the compiler.
macro(add_required_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagnamename ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_C_FLAG${flagname})
  if (NOT HAVE_C_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_cxx_flag(${flag})
endmacro()

# Add required C flag. Configuration fails if the C flag is not supported by
# the compiler.
macro(add_required_c_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_c_compiler_flag("${flag}" HAVE_CXX_FLAG${flagname})
  if (NOT HAVE_CXX_FLAG${flagname})
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

# cvc5 Boolean options are three-valued to detect if an option was set by the
# user. The available values are: IGNORE (default), ON, OFF
# Default options do not override options that were set by the user, i.e.,
# cvc5_set_option only sets an option if it's value is still IGNORE.
# This e.g., allows the user to disable proofs for debug builds (where proofs
# are enabled by default).
macro(cvc5_option var description)
  set(${var} IGNORE CACHE STRING "${description}")
  # Provide drop down menu options in cmake-gui
  set_property(CACHE ${var} PROPERTY STRINGS IGNORE ON OFF)
endmacro()

# Only set option if the user did not set an option.
macro(cvc5_set_option var value)
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

macro(print_info msg)
  message("${Blue}${msg}${ResetColor}")
endmacro()

# Helper to print the configuration of a 2-valued or 3-valued option 'var' with
# prefix 'str'. Optionally takes a `FOUND_SYSTEM` argument that is used to
# indicate when a given dependency is built as part of the cvc5 build.
function(print_config str var)
  set(options)
  set(oneValueArgs FOUND_SYSTEM)
  set(multiValueArgs)
  cmake_parse_arguments(ARGS "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

  if("${var}" STREQUAL "ON")
    set(OPT_VAL_STR "on")
  elseif("${var}" STREQUAL "OFF" OR "${var}" STREQUAL "IGNORE")
    set(OPT_VAL_STR "off")
  else()
    set(OPT_VAL_STR "${var}")
  endif()

  if("${ARGS_FOUND_SYSTEM}" STREQUAL "TRUE")
    set(OPT_FOUND_SYSTEM_STR " (system)")
  elseif("${ARGS_FOUND_SYSTEM}" STREQUAL "FALSE")
    set(OPT_FOUND_SYSTEM_STR " (local)")
  else()
    set(OPT_FOUND_SYSTEM_STR "")
  endif()

  message("${Blue}${str}: ${Green}${OPT_VAL_STR}${OPT_FOUND_SYSTEM_STR}${ResetColor}")
endfunction()


# Collect all source files that are required to build libcvc5 in LIBCVC5_SRCS
# or LIBCVC5_GEN_SRCS. If GENERATED is the first argument the sources are
# added to LIBCVC5_GEN_SRCS. All sources are prepended with the absolute
# current path path. CMAKE_CURRENT_BINARY_DIR is prepended
# to generated source files.
macro(libcvc5_add_sources)
  set(_sources ${ARGV})

  # Check if the first argument is GENERATED.
  list(GET _sources 0 _generated)
  if(${_generated} STREQUAL "GENERATED")
    list(REMOVE_AT _sources 0)
    set(_cur_path ${CMAKE_CURRENT_BINARY_DIR})
    set(_append_to LIBCVC5_GEN_SRCS)
  else()
    set(_cur_path ${CMAKE_CURRENT_SOURCE_DIR})
    set(_append_to LIBCVC5_SRCS)
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

# Check if given Python module is installed and raises a FATAL_ERROR error
# if the module cannot be found.
function(check_python_module module)
  execute_process(
    COMMAND
    ${Python_EXECUTABLE} -c "import ${module}"
    RESULT_VARIABLE
      RET_MODULE_TEST
    ERROR_QUIET
  )
  set(module_name ${ARGN})
  if(NOT module_name)
    set(module_name ${module})
  endif()

  if(RET_MODULE_TEST)
    message(FATAL_ERROR
        "Could not find module ${module_name} for Python "
        "version ${Python_VERSION_MAJOR}.${Python_VERSION_MINOR}. "
        "Make sure to install ${module_name} for this Python version "
        "via \n`${Python_EXECUTABLE} -m pip install ${module_name}'.\n"
        "Note: You need to have pip installed for this Python version.")
  endif()
endfunction()

macro(find_supported_python_version)
  find_package(Python COMPONENTS Interpreter REQUIRED)
endmacro()
