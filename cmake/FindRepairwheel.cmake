###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Repairwheel
# Repairwheel_FOUND - system has the repairwheel executable
# Repairwheel_EXECUTABLE - path to the repairwheel executable
# Repairwheel_VERSION - repairwheel version
##

set(Python_SCRIPTS_Paths "")

macro(add_scripts_path python_bin scheme)
  execute_process(
    COMMAND "${python_bin}" -c 
      "import sysconfig; print(sysconfig.get_paths('${scheme}')['scripts'])"
    RESULT_VARIABLE Python_SCRIPTS_RESULT
    OUTPUT_VARIABLE Python_SCRIPTS
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  if (NOT Python_SCRIPTS_RESULT AND Python_SCRIPTS)
    list(APPEND Python_SCRIPTS_Paths ${Python_SCRIPTS})
  endif()
endmacro()

# Look for repairwheel executable in Python "Scripts" directories
add_scripts_path("${Python_EXECUTABLE}" "posix_prefix")
add_scripts_path("${Python_BASE_EXECUTABLE}" "posix_user")
add_scripts_path("${Python_BASE_EXECUTABLE}" "posix_prefix")
if(WIN32)
  add_scripts_path("${Python_EXECUTABLE}" "nt")
  add_scripts_path("${Python_BASE_EXECUTABLE}" "nt_user")
  add_scripts_path("${Python_BASE_EXECUTABLE}" "nt")
endif()

if (Repairwheel_FIND_REQUIRED)
  set(Repairwheel_FIND_MODE FATAL_ERROR)
else()
  set(Repairwheel_FIND_MODE STATUS)
endif()

macro(find_repairwheel)
  find_program(Repairwheel_EXECUTABLE repairwheel ${Python_SCRIPTS_Paths})
  if(Repairwheel_EXECUTABLE)
    execute_process(
      COMMAND "${Repairwheel_EXECUTABLE}" --version
      RESULT_VARIABLE Repairwheel_VERSION_CHECK_RESULT
      OUTPUT_VARIABLE Repairwheel_VERSION
    )
    # Check we can run repairwheel successfully.
    # Otherwise, reset path to executable.
    if(NOT(Repairwheel_VERSION_CHECK_RESULT EQUAL 0))
      set(Repairwheel_EXECUTABLE "")
    endif()
  endif()
endmacro()

find_repairwheel()

if(NOT Repairwheel_EXECUTABLE AND ENABLE_AUTO_DOWNLOAD)
  message(STATUS "Installing repairwheel")
  execute_process(
    COMMAND ${Python_EXECUTABLE} -m pip install repairwheel
  )
  find_repairwheel()
endif()

if(Repairwheel_EXECUTABLE)
  set(Repairwheel_FOUND TRUE)
  message(STATUS "Found repairwheel: ${Repairwheel_EXECUTABLE}")
else()
  set(Repairwheel_FOUND FALSE)
  message(${Repairwheel_FIND_MODE} "Could NOT find repairwheel executable")
endif()
