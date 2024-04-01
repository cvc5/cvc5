###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Mathias Preiner, Andres Noetzli
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

find_package(Python ${BUILD_BINDINGS_PYTHON_VERSION} EXACT COMPONENTS Development)

if(NOT ONLY_PYTHON_EXT_SRC)
  # Python modules for building and installing
  check_python_module("setuptools")
  find_package(Cython 3.0.0 REQUIRED)
endif()

configure_file(genenums.py.in genenums.py)

# Generate cvc5kinds.{pxd,pxi}
set(GENERATED_KINDS_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5kinds.pxd"
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5kinds.pxi"
)
add_custom_command(
  OUTPUT
    ${GENERATED_KINDS_FILES}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_kind.h"
    --enums-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/cvc5kinds"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_kind.h"
)
add_custom_target(cvc5kinds DEPENDS ${GENERATED_KINDS_FILES})

# Generate cvc5proofrules.{pxd,pxi}
set(GENERATED_PROOF_RULES_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5proofrules.pxd"
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5proofrules.pxi"
)
add_custom_command(
  OUTPUT
    ${GENERATED_PROOF_RULES_FILES}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_proof_rule.h"
    --enums-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/cvc5proofrules"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_proof_rule.h"
)
add_custom_target(cvc5proofrules DEPENDS ${GENERATED_PROOF_RULES_FILES})

# Generate cvc5skolemids.{pxd,pxi}
set(GENERATED_SKOLEM_ID_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5skolemids.pxd"
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5skolemids.pxi"
)
add_custom_command(
  OUTPUT
    ${GENERATED_SKOLEM_ID_FILES}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_skolem_id.h"
    --enums-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/cvc5skolemids"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_skolem_id.h"
)
add_custom_target(cvc5skolemids DEPENDS ${GENERATED_SKOLEM_ID_FILES})

set(GENERATED_TYPES_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5types.pxd"
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5types.pxi"
)
add_custom_command(
  OUTPUT
    ${GENERATED_TYPES_FILES}
  COMMAND
    "${Python_EXECUTABLE}"
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    --enums-header "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_types.h"
    --enums-file-prefix "${CMAKE_CURRENT_BINARY_DIR}/cvc5types"
  DEPENDS
    "${CMAKE_CURRENT_BINARY_DIR}/genenums.py"
    "${PROJECT_SOURCE_DIR}/src/api/parseenums.py"
    "${PROJECT_SOURCE_DIR}/include/cvc5/cvc5_types.h"
)
add_custom_target(cvc5types DEPENDS ${GENERATED_TYPES_FILES})

copy_file_from_src(cvc5.pxi)
copy_file_from_src(cvc5.pxd)
copy_file_from_src(cvc5_python_base.pyx)
copy_file_from_src(pyproject.toml)

# Set include_dirs and library_dirs variables that are used in setup.cfg.in
if (WIN32)
  set(PYTHON_EXT "pyd")
  set(SETUP_INCLUDE_DIRS "${PROJECT_SOURCE_DIR}/include;${CMAKE_BINARY_DIR}/include")
  set(SETUP_LIBRARY_DIRS "${CMAKE_BINARY_DIR}/src;${CMAKE_BINARY_DIR}/src/parser")
else()
  set(PYTHON_EXT "so")
  set(SETUP_INCLUDE_DIRS "${PROJECT_SOURCE_DIR}/include:${CMAKE_BINARY_DIR}/include")
  set(SETUP_LIBRARY_DIRS "${CMAKE_BINARY_DIR}/src:${CMAKE_BINARY_DIR}/src/parser")
  # On Linux and macOS, set rpath variable too
  set(SETUP_RPATH "rpath=${CMAKE_BINARY_DIR}/src:${CMAKE_BINARY_DIR}/src/parser")
endif()

# Set MACOS_ARCH variable that is used in setup.py.in
if (CMAKE_CROSSCOMPILING_MACOS)
  set(MACOS_ARCH "arm64")
endif()

configure_file(setup.py.in setup.py)
configure_file(setup.cfg.in setup.cfg)
configure_file(__init__.py.in cvc5/__init__.py)

set(PYTHON_EXT_SRC_FILES
  cvc5kinds cvc5types cvc5proofrules cvc5skolemids
  ${CMAKE_CURRENT_BINARY_DIR}/cvc5.pxi
  ${CMAKE_CURRENT_BINARY_DIR}/cvc5.pxd
  ${CMAKE_CURRENT_BINARY_DIR}/cvc5_python_base.pyx
  ${CMAKE_CURRENT_BINARY_DIR}/pyproject.toml
  ${CMAKE_CURRENT_BINARY_DIR}/setup.cfg
  ${CMAKE_CURRENT_BINARY_DIR}/setup.py
)

if(NOT ONLY_PYTHON_EXT_SRC)
  set(CVC5_PYTHON_BASE_LIB
    "${CMAKE_CURRENT_BINARY_DIR}/cvc5/cvc5_python_base.${PYTHON_EXT}")

  add_custom_command(
    OUTPUT
      ${CVC5_PYTHON_BASE_LIB}
    COMMAND
      # Force a new build if any dependency has changed
      ${CMAKE_COMMAND} -E remove cvc5_python_base.cpp cvc5/cvc5_python_base.${PYTHON_EXT}
    COMMAND
      "${Python_EXECUTABLE}" setup.py build_ext --inplace
    DEPENDS
      cvc5 cvc5parser
      ${PYTHON_EXT_SRC_FILES}
    COMMENT "Generating cvc5_python_base.${PYTHON_EXT}"
  )
endif()

# Copy the pythonic API to the right place. It does not come with its own
# installation routine and consists only of a few files that need to go to
# the right place.
find_package(CVC5PythonicAPI)

set(LICENSE_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/COPYING"
  "${CMAKE_CURRENT_BINARY_DIR}/licenses/lgpl-3.0.txt"
  "${CMAKE_CURRENT_BINARY_DIR}/licenses/pythonic-LICENSE"
)

add_custom_command(
  OUTPUT
    ${LICENSE_FILES}
  COMMAND
    ${CMAKE_COMMAND} -E copy
    "${PROJECT_SOURCE_DIR}/COPYING"
    "${CMAKE_CURRENT_BINARY_DIR}/COPYING"
  COMMAND
    ${CMAKE_COMMAND} -E copy_directory
    "${PROJECT_SOURCE_DIR}/licenses"
    "${CMAKE_CURRENT_BINARY_DIR}/licenses"
  COMMAND
    ${CMAKE_COMMAND} -E copy
    "${CVC5PythonicAPI_BASEDIR}/cvc5_pythonic_api/LICENSE.txt"
    "${CMAKE_CURRENT_BINARY_DIR}/licenses/pythonic-LICENSE"
  DEPENDS CVC5PythonicAPI
)

set(COPIED_PYTHONIC_FILES
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5/pythonic/__init__.py"
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5/pythonic/cvc5_pythonic.py"
  "${CMAKE_CURRENT_BINARY_DIR}/cvc5/pythonic/cvc5_pythonic_printer.py"
)

add_custom_command(
  OUTPUT
    ${COPIED_PYTHONIC_FILES}
  COMMAND
    ${CMAKE_COMMAND} -E copy_directory
    "${CVC5PythonicAPI_BASEDIR}/cvc5_pythonic_api"
    "${CMAKE_CURRENT_BINARY_DIR}/cvc5/pythonic"
  # Remove the license of the Pythonic API from the package's source files.
  # The license file is included in the package's dist-info dir by setup()
  COMMAND
    ${CMAKE_COMMAND} -E remove
    "${CMAKE_CURRENT_BINARY_DIR}/cvc5/pythonic/LICENSE.txt"
  DEPENDS CVC5PythonicAPI
)

if(ONLY_PYTHON_EXT_SRC)

  add_custom_target(
    cvc5_python_api ALL DEPENDS
      ${PYTHON_EXT_SRC_FILES}
      ${COPIED_PYTHONIC_FILES}
      ${LICENSE_FILES}
  )

else()

  add_custom_target(
    cvc5_python_api ALL DEPENDS
      ${CVC5_PYTHON_BASE_LIB}
      ${COPIED_PYTHONIC_FILES}
      ${LICENSE_FILES}
  )

  # figure out if we're in a virtualenv
  execute_process(OUTPUT_VARIABLE IN_VIRTUALENV
    COMMAND
    "${Python_EXECUTABLE}"
    -c
    "import os; print('YES' if 'VIRTUAL_ENV' in os.environ else 'NO', end='')")

  set(INSTALL_CMD
      "${Python_EXECUTABLE} -m pip install ${CMAKE_CURRENT_BINARY_DIR}")
  # if we're in a virtualenv, we install it in the virtualenv lib location
  # otherwise install in prefix
  if ("${IN_VIRTUALENV}" STREQUAL "NO")
    set(INSTALL_CMD "${INSTALL_CMD} --prefix ${CMAKE_INSTALL_PREFIX}")
  endif()

  message("Python bindings install command: ${INSTALL_CMD}")

  install(CODE "execute_process(COMMAND ${INSTALL_CMD})"
          FILE_PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ)

endif()
