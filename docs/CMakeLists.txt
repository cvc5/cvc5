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
check_python_module(sphinxcontrib.programoutput sphinxcontrib.programoutput)
check_python_module(sphinx_rtd_theme sphinx-rtd-theme)

add_subdirectory(api)

set(SPHINX_INPUT_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(SPHINX_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx)

configure_file(conf.py.in ${CMAKE_CURRENT_BINARY_DIR}/conf.py)

add_custom_target(
  docs
  DEPENDS docs-cpp docs-java docs-python gen-options cvc5-bin
  COMMAND
    ${SPHINX_EXECUTABLE} -v -b html -c ${CMAKE_CURRENT_BINARY_DIR}
    # Tell Breathe where to find the Doxygen output
    -Dbreathe_projects.cvc5=${CPP_DOXYGEN_XML_DIR}
    -Dbreathe_projects.std=${CPP_DOXYGEN_XML_DIR} ${SPHINX_INPUT_DIR}
    ${SPHINX_OUTPUT_DIR}
  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
  COMMENT "Generating Sphinx Api docs"
)

add_custom_command(
  TARGET docs
  POST_BUILD
  COMMAND
    ${CMAKE_COMMAND} -E cmake_echo_color --cyan "Preview docs in browser: file://localhost${SPHINX_OUTPUT_DIR}/index.html"
)

set(SPHINX_GH_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx-gh)
add_custom_target(
  docs-gh
  DEPENDS docs
  # remove existing sphinx-gh/ directory
  COMMAND ${CMAKE_COMMAND} -E remove_directory ${SPHINX_GH_OUTPUT_DIR}
  # copy sphinx/ to sphinx-gh/
  COMMAND ${CMAKE_COMMAND} -E copy_directory ${SPHINX_OUTPUT_DIR}
          ${SPHINX_GH_OUTPUT_DIR}
  # remove leftovers from the build
  COMMAND ${CMAKE_COMMAND} -E remove_directory ${SPHINX_GH_OUTPUT_DIR}/.doctrees
          ${SPHINX_GH_OUTPUT_DIR}/_sources ${SPHINX_GH_OUTPUT_DIR}/_static/fonts
  COMMAND ${CMAKE_COMMAND} -E remove ${SPHINX_GH_OUTPUT_DIR}/objects.inv
  # rename _static/ to static/ (as jekyll ignores _*/ dirs)
  COMMAND ${CMAKE_COMMAND} -E rename ${SPHINX_GH_OUTPUT_DIR}/_static
          ${SPHINX_GH_OUTPUT_DIR}/static
  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -type f | xargs sed -i'orig'
          's/_static/static/'
  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -name '*orig' -delete
  # done
  COMMENT "Generating GitHub Api docs"
)
