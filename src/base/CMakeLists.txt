#-----------------------------------------------------------------------------#
# Extract info from Git for git_versioninfo.cpp
# Note: GitInfo.cmake generates git_versioninfo.cpp.

find_package(Git)
configure_file(GitInfo.cmake.in GitInfo.cmake @ONLY)
add_custom_target(gen-gitinfo
  COMMAND ${CMAKE_COMMAND} -DGIT_FOUND=${GIT_FOUND} -P GitInfo.cmake)

#-----------------------------------------------------------------------------#

libcvc4_add_sources(
  configuration.cpp
  configuration.h
  configuration_private.h
  cvc4_assert.cpp
  cvc4_assert.h
  cvc4_check.cpp
  cvc4_check.h
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

# Note: gen-tags-{debug,trace} are targets since we always want to generate
# the temporary tag files {Debug,Trace}_tags.tmp in order to check if tags
# were added/modified/deleted.
add_custom_target(
  gen-tags-debug
  COMMAND
    ${gentmptags_script} ${CMAKE_CURRENT_LIST_DIR} Debug ${source_files_list}
  DEPENDS mktags
  BYPRODUCTS ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
)

add_custom_target(
  gen-tags-trace
  COMMAND
    ${gentmptags_script} ${CMAKE_CURRENT_LIST_DIR} Trace ${source_files_list}
  DEPENDS mktags
  BYPRODUCTS ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
  COMMAND ${gentags_script} Debug
  DEPENDS gen-tags-debug ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
  COMMAND ${gentags_script} Trace
  DEPENDS gen-tags-trace ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
  COMMAND ${genheader_script} ${CMAKE_CURRENT_LIST_DIR} Debug
  DEPENDS mktagheaders ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
  COMMAND ${genheader_script} ${CMAKE_CURRENT_LIST_DIR} Trace
  DEPENDS mktagheaders ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
)

add_custom_target(gen-tags
  DEPENDS
    ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
)
