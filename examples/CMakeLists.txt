include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

# Some of the examples require boost. Enable these examples if boost is
# installed.
find_package(Boost)

set(EXAMPLES_BIN_DIR ${CMAKE_BINARY_DIR}/bin/examples)

# Create target examples. Add a dependency for each examples you add.
add_custom_target(examples)

add_executable(simple_vc_cxx EXCLUDE_FROM_ALL simple_vc_cxx.cpp)
target_link_libraries(simple_vc_cxx cvc4 cvc4parser)
add_dependencies(examples simple_vc_cxx)

add_executable(simple_vc_quant_cxx EXCLUDE_FROM_ALL simple_vc_quant_cxx.cpp)
target_link_libraries(simple_vc_quant_cxx cvc4 cvc4parser)
add_dependencies(examples simple_vc_quant_cxx)

add_executable(translator EXCLUDE_FROM_ALL translator.cpp)
target_link_libraries(translator cvc4 cvc4parser)
add_dependencies(examples translator)

set_target_properties(simple_vc_cxx simple_vc_quant_cxx translator
  PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_BIN_DIR})

if(BUILD_BINDINGS_JAVA)
  find_package(Java REQUIRED)
  set(EXAMPLES_JAVA_CLASSPATH "${CMAKE_BINARY_DIR}/src/bindings/java/CVC4.jar")
  add_custom_target(SimpleVCjava
    COMMAND
      ${Java_JAVAC_EXECUTABLE}
        -cp ${EXAMPLES_JAVA_CLASSPATH} ${CMAKE_CURRENT_SOURCE_DIR}/SimpleVC.java
        -d ${CMAKE_BINARY_DIR}/bin/examples
    DEPENDS cvc4jar)
  add_dependencies(examples SimpleVCjava)
endif()

add_subdirectory(api)
add_subdirectory(hashsmt)
add_subdirectory(nra-translate)
add_subdirectory(sets-translate)

