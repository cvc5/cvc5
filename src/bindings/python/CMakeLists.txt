# Make sure that interpreter and libraries have a compatible version.
# Note: We use the Python interpreter to determine the install path for Python
# modules.  If the interpreter and library have different versions, the module
# will be installed for the wrong Python version. Hence, we require the library
# version to match the Python interpreter's version.
find_package(PythonLibs
             ${PYTHON_VERSION_MAJOR}.${PYTHON_VERSION_MINOR} REQUIRED)
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


# Install Python bindings to the corresponding python-*/site-packages
# directory.  Lookup Python module directory and store path in
# PYTHON_MODULE_PATH.
execute_process(COMMAND
                  ${PYTHON_EXECUTABLE} -c
                    "from distutils.sysconfig import get_python_lib;\
                     print(get_python_lib(plat_specific=True,\
                             prefix='${CMAKE_INSTALL_PREFIX}'))"
                OUTPUT_VARIABLE PYTHON_MODULE_PATH
                OUTPUT_STRIP_TRAILING_WHITESPACE)

# Copy _CVC4.so and CVC4.py to PYTHON_MODULE_PATH
install(TARGETS ${SWIG_MODULE_CVC4_REAL_NAME}
        DESTINATION ${PYTHON_MODULE_PATH})
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/CVC4.py
        DESTINATION ${PYTHON_MODULE_PATH})
