###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

include(python-scripts-paths)
# Defines the Python_SCRIPTS_Paths variable with
# a list of Python "Scripts" directories
collect_python_scripts_paths()

if (Repairwheel_FIND_REQUIRED)
  set(Repairwheel_FIND_MODE FATAL_ERROR)
else()
  set(Repairwheel_FIND_MODE STATUS)
endif()

macro(get_repairwheel_version)
  find_program(Repairwheel_EXECUTABLE repairwheel ${Python_SCRIPTS_Paths})
  if(Repairwheel_EXECUTABLE)
    execute_process(
      COMMAND "${Repairwheel_EXECUTABLE}" --version
      RESULT_VARIABLE Repairwheel_VERSION_CHECK_RESULT
      OUTPUT_VARIABLE Repairwheel_VERSION
      ERROR_QUIET
    )
  else()
    set(Repairwheel_VERSION_CHECK_RESULT 127) # Not-found exit code
  endif()
endmacro()

set(INSTALL_REPAIRWHEEL FALSE)

get_repairwheel_version()

if (Repairwheel_VERSION_CHECK_RESULT EQUAL 0)
  set(Repairwheel_FOUND TRUE)
  message(STATUS "Found repairwheel version: ${Repairwheel_VERSION}")
  if (DEFINED Repairwheel_FIND_VERSION)
    if (Repairwheel_FIND_VERSION_EXACT)
      if (NOT (Repairwheel_VERSION VERSION_EQUAL ${Repairwheel_FIND_VERSION}))
        set(INSTALL_REPAIRWHEEL TRUE)
        set(INSTALL_REPAIRWHEEL_OPTION "==${Repairwheel_FIND_VERSION}")
        set(INSTALL_REPAIRWHEEL_MESSAGE "==${Repairwheel_FIND_VERSION}")
      endif()
    else()
      if (Repairwheel_VERSION VERSION_LESS ${Repairwheel_FIND_VERSION})
        set(INSTALL_REPAIRWHEEL TRUE)
        set(INSTALL_REPAIRWHEEL_OPTION ";-U")
        set(INSTALL_REPAIRWHEEL_MESSAGE ">=${Repairwheel_FIND_VERSION}")
      endif()
    endif()
    if (INSTALL_REPAIRWHEEL AND NOT ENABLE_AUTO_DOWNLOAD)
      set(INSTALL_REPAIRWHEEL FALSE)
      message(${Repairwheel_FIND_MODE}
        "Repairwheel version${INSTALL_REPAIRWHEEL_MESSAGE} is required, "
        "but found version ${Repairwheel_VERSION}.\n"
        "Use --auto-download to let us install it for you."
      )
    endif()
  endif()
else()
  set(Repairwheel_FOUND FALSE)
  if (NOT ENABLE_AUTO_DOWNLOAD)
    message(${Repairwheel_FIND_MODE}
      "Could NOT find repairwheel executable. "
      "Use --auto-download to let us install it for you.")
  else()
    set(INSTALL_REPAIRWHEEL TRUE)
    set(INSTALL_REPAIRWHEEL_OPTION ";-U")
    set(INSTALL_REPAIRWHEEL_MESSAGE "")
  endif()
endif()

if(INSTALL_REPAIRWHEEL)
  message(STATUS "Installing repairwheel${INSTALL_REPAIRWHEEL_MESSAGE}")
  execute_process(
    COMMAND
    ${Python_EXECUTABLE} -m pip install repairwheel${INSTALL_REPAIRWHEEL_OPTION}
    RESULT_VARIABLE REPAIRWHEEL_INSTALL_CMD_EXIT_CODE
  )
  if(REPAIRWHEEL_INSTALL_CMD_EXIT_CODE)
    message(${Repairwheel_FIND_MODE}
      "Could NOT install repairwheel${INSTALL_REPAIRWHEEL_MESSAGE}"
    )
  else()
    set(Repairwheel_FOUND TRUE)
    get_repairwheel_version()
  endif()
endif()
