#-----------------------------------------------------------------------------#
# Extract info from Git for git_versioninfo.cpp

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
git_local_changes(GIT_IS_DIRTY)
if(${GIT_IS_DIRTY} STREQUAL "DIRTY")
  set(GIT_IS_DIRTY "true")
else()
  set(GIT_IS_DIRTY "false")
endif()
execute_process(
  COMMAND "${GIT_EXECUTABLE}" rev-parse --abbrev-ref HEAD
  OUTPUT_VARIABLE GIT_BRANCH
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

#-----------------------------------------------------------------------------#
# Generate git_versioninfo.cpp

configure_file(git_versioninfo.cpp.in git_versioninfo.cpp)

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

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
  COMMAND
    ${gentmptags_script} ${CMAKE_CURRENT_LIST_DIR} Debug ${source_files_list}
  DEPENDS mktags
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
  COMMAND
    ${gentmptags_script} ${CMAKE_CURRENT_LIST_DIR} Trace ${source_files_list}
  DEPENDS mktags
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
  COMMAND ${gentags_script} Debug
  DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
  COMMAND ${gentags_script} Trace
  DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
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
