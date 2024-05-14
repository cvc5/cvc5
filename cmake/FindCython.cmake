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
# Find Cython
# Cython_FOUND - found Cython Python module
##

macro(get_cython_version)
  execute_process(
      COMMAND "${Python_EXECUTABLE}" -c "import Cython; print(Cython.__version__)"
      RESULT_VARIABLE Cython_VERSION_CHECK_RESULT
      OUTPUT_VARIABLE Cython_VERSION
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE
  )
endmacro()

get_cython_version()

if (Cython_FIND_REQUIRED)
  set(Cython_FIND_MODE FATAL_ERROR)
else()
  set(Cython_FIND_MODE STATUS)
endif()

if (Cython_VERSION_CHECK_RESULT EQUAL 0)
    set(Cython_FOUND TRUE)
    message(STATUS "Found Cython version: ${Cython_VERSION}")
    if (DEFINED Cython_FIND_VERSION)
        if(Cython_FIND_VERSION_EXACT)
            if (NOT (Cython_VERSION VERSION_EQUAL ${Cython_FIND_VERSION}))
              if(ENABLE_AUTO_DOWNLOAD)
                message(STATUS
                  "Installing module Cython==${Cython_FIND_VERSION}"
                )
                execute_process(
                  COMMAND
                  ${Python_EXECUTABLE} -m pip install Cython==${Cython_FIND_VERSION}
                  RESULT_VARIABLE CYTHON_INSTALL_CMD_EXIT_CODE
                )
                if(CYTHON_INSTALL_CMD_EXIT_CODE)
                  message(${Cython_FIND_MODE}
                    "Could not install Cython==${Cython_FIND_VERSION}")
                else()
                  get_cython_version()
                endif()
              else()
                message(${Cython_FIND_MODE}
                  "Cython version == ${Cython_FIND_VERSION} is required, "
                  "but found version ${Cython_VERSION}")
              endif()
            endif()
        else()
            if (Cython_VERSION VERSION_LESS ${Cython_FIND_VERSION})
              if(ENABLE_AUTO_DOWNLOAD)
                message(STATUS "Upgrading module Cython")
                execute_process(COMMAND
                  ${Python_EXECUTABLE} -m pip install Cython -U
                  RESULT_VARIABLE CYTHON_INSTALL_CMD_EXIT_CODE
                )
                if(CYTHON_INSTALL_CMD_EXIT_CODE)
                  message(${Cython_FIND_MODE}
                    "Could not install Cython >= ${Cython_FIND_VERSION}")
                else()
                  get_cython_version()
                endif()
              else()
                message(${Cython_FIND_MODE}
                  "Cython version >= ${Cython_FIND_VERSION} is required, "
                  "but found version ${Cython_VERSION}")
              endif()
            endif()
        endif()
    endif()
else()
  set(Cython_FOUND FALSE)
  if(ENABLE_AUTO_DOWNLOAD)
    message(STATUS "Installing module Cython")
    execute_process(
      COMMAND ${Python_EXECUTABLE} -m pip install Cython
      RESULT_VARIABLE CYTHON_INSTALL_CMD_EXIT_CODE)
    if(CYTHON_INSTALL_CMD_EXIT_CODE)
      message(${Cython_FIND_MODE} "Could not install module Cython")
    else()
      set(Cython_FOUND TRUE)
      get_cython_version()
    endif()
  else()
    message(${Cython_FIND_MODE}
        "Could not find module Cython for Python "
        "version ${Python_VERSION_MAJOR}.${Python_VERSION_MINOR}. "
        "Make sure to install Cython for this Python version "
        "via \n`${Python_EXECUTABLE} -m pip install Cython'.\n"
        "or use --auto-download to let us install it for you.\n"
        "Note: You need to have pip installed for this Python version.")
  endif()
endif()
