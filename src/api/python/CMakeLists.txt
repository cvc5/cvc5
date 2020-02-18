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
    --kinds-file-prefix "cvc4kinds"
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
install(TARGETS pycvc4 DESTINATION lib)
