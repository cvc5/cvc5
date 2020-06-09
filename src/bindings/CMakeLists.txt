if(NOT ENABLE_SHARED)
  message(FATAL_ERROR "Can't build language bindings for static CVC4 build.")
endif()

find_package(SWIG 3.0.0 REQUIRED)
if(POLICY CMP0078)
  cmake_policy(SET CMP0078 OLD)
endif()
if(POLICY CMP0086)
  cmake_policy(SET CMP0086 OLD)
endif()

if(USE_PYTHON3 AND (SWIG_VERSION VERSION_EQUAL 3.0.8))
  message(FATAL_ERROR
    "\nSWIG ${SWIG_VERSION} is not supported for python3 bindings because of the following bug: https://github.com/swig/swig/issues/588
Please downgrade to 3.0.0-3.0.7 or upgrade.")
endif()

include(${SWIG_USE_FILE})

set(CVC4_SWIG_INTERFACE ${PROJECT_SOURCE_DIR}/src/cvc4.i)

set_property(SOURCE ${CVC4_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

include_directories(
    ${PROJECT_SOURCE_DIR}/src
    ${PROJECT_SOURCE_DIR}/src/include
    ${CMAKE_BINARY_DIR}/src)

if(BUILD_SWIG_BINDINGS_JAVA)
  add_subdirectory(java)
endif()
if(BUILD_SWIG_BINDINGS_PYTHON)
  add_subdirectory(python)
endif()
