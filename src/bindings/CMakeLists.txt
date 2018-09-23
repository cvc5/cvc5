if(NOT ENABLE_SHARED)
  message(FATAL_ERROR "Can't build language bindings for static CVC4 build.")
endif()

find_package(SWIG 3.0.0 REQUIRED)
include(${SWIG_USE_FILE})

set(CVC4_SWIG_INTERFACE ${PROJECT_SOURCE_DIR}/src/cvc4.i)

set_property(SOURCE ${CVC4_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

include_directories(
    ${PROJECT_SOURCE_DIR}/src
    ${PROJECT_SOURCE_DIR}/src/include
    ${CMAKE_BINARY_DIR}/src)

if(BUILD_BINDINGS_JAVA)
  add_subdirectory(java)
endif()
if(BUILD_BINDINGS_PYTHON)
  add_subdirectory(python)
endif()
