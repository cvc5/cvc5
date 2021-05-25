###############################################################################
# Top contributors (to current version):
#   Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##
find_package(Sphinx REQUIRED)
check_python_module(breathe)
check_python_module(sphinxcontrib.bibtex sphinxcontrib-bibtex)
check_python_module(sphinx_tabs.tabs sphinx-tabs)

add_subdirectory(cpp)
add_subdirectory(python)

set(SPHINX_INPUT_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(SPHINX_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx)

configure_file(conf.py.in ${CMAKE_CURRENT_BINARY_DIR}/conf.py)

add_custom_target(docs ALL
                  DEPENDS docs-cpp docs-python gen-options
                  COMMAND
                    ${SPHINX_EXECUTABLE} -b html
                    -c ${CMAKE_CURRENT_BINARY_DIR}
                    # Tell Breathe where to find the Doxygen output
                    -Dbreathe_projects.cvc5=${CPP_DOXYGEN_XML_FOLDER}
                    -Dbreathe_projects.std=${CPP_DOXYGEN_XML_FOLDER}
                    ${SPHINX_INPUT_DIR} ${SPHINX_OUTPUT_DIR}
                  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
                  COMMENT "Generating Sphinx Api docs")

set(SPHINX_GH_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx-gh)
add_custom_target(docs-gh ALL
                  DEPENDS docs
                  COMMAND ${CMAKE_COMMAND} -E remove_directory
                    ${SPHINX_GH_OUTPUT_DIR}
                  COMMAND ${CMAKE_COMMAND} -E copy_directory
                    ${SPHINX_OUTPUT_DIR} ${SPHINX_GH_OUTPUT_DIR}
                  COMMAND ${CMAKE_COMMAND} -E remove_directory
                    ${SPHINX_GH_OUTPUT_DIR}/_sources
                  COMMAND ${CMAKE_COMMAND} -E remove
                    ${SPHINX_GH_OUTPUT_DIR}/objects.inv
                  COMMAND ${CMAKE_COMMAND} -E rename
                    ${SPHINX_GH_OUTPUT_DIR}/_static
                    ${SPHINX_GH_OUTPUT_DIR}/static
                  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -type f |
                    xargs sed -i'orig' 's/_static/static/'
                  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -name '*orig' -delete
                  COMMENT "Generating GitHub Api docs")

