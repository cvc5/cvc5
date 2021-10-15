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
