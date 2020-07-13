#-----------------------------------------------------------------------------#
# Extract info from Git for git_versioninfo.cpp
# Note: GitInfo.cmake generates git_versioninfo.cpp.

find_package(Git)
configure_file(GitInfo.cmake.in GitInfo.cmake @ONLY)
add_custom_target(gen-gitinfo
  BYPRODUCTS ${CMAKE_CURRENT_BINARY_DIR}/git_versioninfo.cpp
  COMMAND ${CMAKE_COMMAND} -DGIT_FOUND=${GIT_FOUND} -P GitInfo.cmake)

#-----------------------------------------------------------------------------#

libcvc4_add_sources(
  check.cpp
  check.h
  configuration.cpp
  configuration.h
  configuration_private.h
  exception.cpp
  exception.h
  listener.cpp
  listener.h
  modal_exception.h
  output.cpp
  output.h
)

libcvc4_add_sources(GENERATED git_versioninfo.cpp)

#-----------------------------------------------------------------------------#
# Generate code for debug/trace tags

set(gentmptags_script ${CMAKE_CURRENT_LIST_DIR}/gentmptags.sh)
set(gentags_script ${CMAKE_CURRENT_LIST_DIR}/gentags.sh)
set(genheader_script ${CMAKE_CURRENT_LIST_DIR}/genheader.sh)

file(GLOB_RECURSE source_files
     ${PROJECT_SOURCE_DIR}/src/*.cpp
     ${PROJECT_SOURCE_DIR}/src/*.cc
     ${PROJECT_SOURCE_DIR}/src/*.h
     ${PROJECT_SOURCE_DIR}/src/*.g)
string(REPLACE ";" " " source_files_list "${source_files}")

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
  COMMAND
    ${gentmptags_script} ${CMAKE_CURRENT_LIST_DIR} Debug ${source_files_list}
  DEPENDS mktags ${gentmptags_script} ${source_files}
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
  COMMAND
    ${gentmptags_script} ${CMAKE_CURRENT_LIST_DIR} Trace ${source_files_list}
  DEPENDS mktags ${gentmptags_script} ${source_files}
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
  COMMAND ${gentags_script} Debug
  DEPENDS ${gentags_script} ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
  COMMAND ${gentags_script} Trace
  DEPENDS ${gentags_script} ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
  COMMAND ${genheader_script} ${CMAKE_CURRENT_LIST_DIR} Debug
  DEPENDS mktagheaders ${genheader_script} ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
  COMMAND ${genheader_script} ${CMAKE_CURRENT_LIST_DIR} Trace
  DEPENDS mktagheaders ${genheader_script} ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
)

add_custom_target(gen-tags
  DEPENDS
    ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
)

set_source_files_properties(
  ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
  ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
  PROPERTIES GENERATED TRUE
)
