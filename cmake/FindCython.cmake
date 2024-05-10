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

execute_process(
    COMMAND "${Python_EXECUTABLE}" -c "import Cython; print(Cython.__version__)"
    RESULT_VARIABLE Cython_VERSION_CHECK_RESULT
    OUTPUT_VARIABLE Cython_VERSION
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE
)

set(Cython_FOUND FALSE)

if (Cython_VERSION_CHECK_RESULT EQUAL 0)
    message(STATUS "Found Cython version: ${Cython_VERSION}")
    if (DEFINED Cython_FIND_VERSION)
        if(Cython_FIND_VERSION_EXACT)
            if (NOT (Cython_VERSION VERSION_EQUAL ${Cython_FIND_VERSION}))
              message(STATUS
                "Installing module Cython==${Cython_FIND_VERSION} in Python venv"
              )
              execute_process(
                COMMAND
                ${Python_EXECUTABLE} -m pip install Cython==${Cython_FIND_VERSION}
              )
            endif()
        else()
            if (Cython_VERSION VERSION_LESS ${Cython_FIND_VERSION})
              message(STATUS "Upgrading module Cython in Python venv")
              execute_process(COMMAND
                ${Python_EXECUTABLE} -m pip install Cython -U
              )
            endif()
        endif()
    endif()
else()
    message(STATUS "Installing module Cython in Python venv")
    execute_process(COMMAND ${Python_EXECUTABLE} -m pip install Cython)
endif()

set(Cython_FOUND TRUE)
