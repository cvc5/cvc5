find_package(PythonExtensions REQUIRED)
find_package(Cython REQUIRED)

include_directories(${PYTHON_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_LIST_DIR})         # cvc4kinds.pxd
include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

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
