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
# Build, repair, and install a cvc5 Python wheel
#
# This script first removes any existing wheel build directories,
# builds an initial Python wheel, repairs the wheel to include
# all required shared library dependencies, and finally prepares
# an installation command to install the repaired wheel.
#
# Input variables:
# Python_EXECUTABLE - Path to the Python executable
# Repairwheel_EXECUTABLE - Path to the repairwheel tool
# BUILD_DIR - Path to the cvc5 build directory 
# DEPS_BASE - Path to the cvc5 dependencies directory
# INSTALL_CMD - Command to install the wheel
##
set(UNREPAIRED_WHEEL_DIR ${BUILD_DIR}/unrepaired-wheel)
set(REPAIRED_WHEEL_DIR ${BUILD_DIR}/repaired-wheel)

execute_process(COMMAND
  ${CMAKE_COMMAND} -E remove_directory ${UNREPAIRED_WHEEL_DIR} ${REPAIRED_WHEEL_DIR})

execute_process(COMMAND 
    ${Python_EXECUTABLE} -m pip wheel ${BUILD_DIR}/src/api/python
    --wheel-dir=${BUILD_DIR}/unrepaired-wheel)

file(GLOB WHL_FILE ${UNREPAIRED_WHEEL_DIR}/cvc5*.whl)

execute_process(COMMAND
    ${Repairwheel_EXECUTABLE} -o ${BUILD_DIR}/repaired-wheel
    -l ${BUILD_DIR}/src -l ${BUILD_DIR}/src/parser
    -l ${DEPS_BASE}/bin ${WHL_FILE})

file(GLOB WHL_FILE ${REPAIRED_WHEEL_DIR}/cvc5*.whl)

set(INSTALL_CMD "${INSTALL_CMD} ${WHL_FILE}")
string(REPLACE "\"" "" INSTALL_CMD "${INSTALL_CMD}")
if(WIN32)
  string(REPLACE "/" "\\" INSTALL_CMD "${INSTALL_CMD}")
endif()
separate_arguments(INSTALL_CMD)

execute_process(COMMAND ${INSTALL_CMD})
