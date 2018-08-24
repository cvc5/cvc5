find_package(PythonLibs REQUIRED)
include_directories(${PYTHON_INCLUDE_DIRS})

set(SWIG_MODULE_CVC4_EXTRA_DEPS cvc4 cvc4parser)
set_property(SOURCE ${CVC4_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)

# Suppress -Wsuggest-override warnings for generated code
set_property(
  SOURCE ${CMAKE_CURRENT_BINARY_DIR}/cvc4PYTHON_wrap.cxx
  PROPERTY COMPILE_OPTIONS -Wno-suggest-override)

# The generated module should have the name _CVC4.so, hence we use CVC4 as
# target name.
if(${CMAKE_VERSION} VERSION_LESS "3.8.0")
  swig_add_module(CVC4 Python ${CVC4_SWIG_INTERFACE})
else()
  swig_add_library(CVC4 LANGUAGE Python SOURCES ${CVC4_SWIG_INTERFACE})
endif()
swig_link_libraries(CVC4 cvc4 cvc4parser ${PYTHON_LIBRARIES})
