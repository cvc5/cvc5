###############################################################################
# Top contributors (to current version):
#   Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
# Provides cmake target target-graphs with generates (png) dependency graphs
# to visualize the interdependencies of all cmake targets.
##

get_target_property(APITESTS build-apitests MANUALLY_ADDED_DEPENDENCIES)
string(REPLACE ";" " " APITESTS "${APITESTS}")

configure_file(
    cmake/CMakeGraphVizOptions.cmake.in 
    ${CMAKE_BINARY_DIR}/CMakeGraphVizOptions.cmake
    @ONLY
)

add_custom_target(target-graphs
    COMMAND
        ${CMAKE_COMMAND} --graphviz=target-graphs/graph.dot ${CMAKE_SOURCE_DIR}
    COMMAND
        find target-graphs/ -iname "graph.dot*" -and \! -iname "*.png"
        -exec dot -Tpng -O {} +
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)
