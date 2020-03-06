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

# Installation based on https://bloerg.net/2012/11/10/cmake-and-distutils.html
# Create a wrapper python directory and generate a distutils setup.py file
set(SETUP_PY_IN "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in")
set(SETUP_PY    "${CMAKE_CURRENT_BINARY_DIR}/setup.py")
configure_file(${SETUP_PY_IN} ${SETUP_PY})
set(PYCVC4_MODULE "${CMAKE_CURRENT_BINARY_DIR}/pycvc4")
file(MAKE_DIRECTORY "${PYCVC4_MODULE}")
file(WRITE ${PYCVC4_MODULE}/__init__.py "from .pycvc4 import *")
set(PYCVC4_LOC "${PYCVC4_MODULE}/$<TARGET_FILE_NAME:pycvc4>")
add_custom_command(TARGET pycvc4 POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E rename $<TARGET_FILE:pycvc4> ${PYCVC4_LOC}
)

install(CODE "execute_process(COMMAND ${PYTHON_EXECUTABLE} ${SETUP_PY} install)")
