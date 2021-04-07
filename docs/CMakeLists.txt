find_package(Doxygen REQUIRED)
find_package(Sphinx REQUIRED)
check_python_module(breathe)

set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
set(DOXYFILE_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

set(DOXYGEN_INPUT_DIR ${PROJECT_SOURCE_DIR}/src/api/cpp)
set(DOXYGEN_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/doxygen)
set(DOXYGEN_INPUT
  "${DOXYGEN_INPUT_DIR}/cvc5.h ${DOXYGEN_INPUT_DIR}/cvc5_kind.h")
set(DOXYGEN_INDEX_FILE ${DOXYGEN_OUTPUT_DIR}/xml/index.xml)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in
               ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile @ONLY)

file(MAKE_DIRECTORY ${DOXYGEN_OUTPUT_DIR})

add_custom_command(OUTPUT ${DOXYGEN_INDEX_FILE}
                   DEPENDS ${PROJECT_SOURCE_DIR}/src/api/cpp/cvc5.h
                   COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYFILE_OUT}
                   WORKING_DIRECTORY ${DOXYGEN_BIN_DIR}
                   MAIN_DEPENDENCY ${DOXYFILE_OUT} ${DOXYFILE_IN}
                   COMMENT "Generating doxygen API docs")

add_custom_target(docs-doxygen ALL DEPENDS ${DOXYGEN_INDEX_FILE})

set(SPHINX_INPUT_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(SPHINX_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx)

add_custom_target(docs ALL
                  DEPENDS docs-doxygen
                  COMMAND
                  ${SPHINX_EXECUTABLE} -b html
                  # Tell Breathe where to find the Doxygen output
                  -Dbreathe_projects.cvc5=${DOXYGEN_OUTPUT_DIR}/xml
                  ${SPHINX_INPUT_DIR} ${SPHINX_OUTPUT_DIR}
                  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                  COMMENT "Generating Sphinx Api docs")
