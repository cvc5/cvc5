#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Makai Mann
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
if(POLICY CMP0057)
  # For cmake >= 3.3 this policy changed the behavior of IN_LIST
  # if the policy exists, we use the NEW behavior
  cmake_policy(SET CMP0057 NEW)
endif()

find_package(PythonExtensions REQUIRED)
find_package(Cython 0.29 REQUIRED)

include_directories(${PYTHON_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_LIST_DIR})         # cvc4kinds.pxd
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_CURRENT_BINARY_DIR})
# TEMP: Only needed while expr/kind.h is public in the C++ api
include_directories("${CMAKE_BINARY_DIR}/src/")

# Generate cvc4kinds.{pxd,pyx}
add_custom_target(
  gen-pycvc4-kinds
  ALL
  COMMAND
    "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_LIST_DIR}/genkinds.py"
    --kinds-header "${PROJECT_SOURCE_DIR}/src/api/cvc4cppkind.h"
    --kinds-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/cvc4kinds"
  DEPENDS
    genkinds.py
  COMMENT
    "Generate cvc4kinds.{pxd,pyx}"
)

add_cython_target(pycvc4 CXX)

add_library(pycvc4
            MODULE
            ${pycvc4})

target_link_libraries(pycvc4 cvc4 ${PYTHON_LIBRARIES})

python_extension_module(pycvc4)

# Make sure that gen-pycvc4-kinds target is run before building the bindings
# doesn't always work correctly with ALL since there are multiple targets
add_dependencies(pycvc4 gen-pycvc4-kinds)

# Installation based on https://bloerg.net/2012/11/10/cmake-and-distutils.html
configure_file(setup.py.in setup.py)

if (SKBUILD)
  # if building a wheel with scikit-build, then just put the files in the right place
  install(TARGETS pycvc4 LIBRARY DESTINATION src/api/pycvc4)
  install(FILES __init__.py DESTINATION src/api/pycvc4)
else()
  # otherwise install the python module
  # figure out if we're in a virtualenv
  execute_process(OUTPUT_VARIABLE IN_VIRTUALENV
    COMMAND
    "${PYTHON_EXECUTABLE}"
    -c
    "from __future__ import print_function; import os;
  print('YES' if 'VIRTUAL_ENV' in os.environ else 'NO', end='')")

  set(INSTALL_CMD "${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_BINARY_DIR}/setup.py install")
  # if we're in a virtualenv, we install it in the virtualenv lib location
  if ("${IN_VIRTUALENV}" STREQUAL "NO")
    set(INSTALL_CMD "${INSTALL_CMD} --prefix=${CMAKE_INSTALL_PREFIX}")
  endif()

  TODO: fix the installation option and use setuptools
  message("Python bindings install command: ${INSTALL_CMD}")
  install(CODE "execute_process(COMMAND ${INSTALL_CMD})"  FILE_PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ)
endif()

