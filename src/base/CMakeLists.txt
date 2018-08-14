set(base_src_files
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

add_library(base SHARED ${base_src_files})
set_target_properties(base PROPERTIES COMPILE_DEFINITIONS __BUILDING_CVC4LIB)
add_dependencies(base tags_headers)

#
# Generate code for debug/trace tags
#
set(mktags_script ${CMAKE_CURRENT_LIST_DIR}/mktags)
set(mktagheaders_script ${CMAKE_CURRENT_LIST_DIR}/mktagheaders)
file(GLOB_RECURSE source_files ${PROJECT_SOURCE_DIR}/src/*.cpp ${PROJECT_SOURCE_DIR}/src/*.cc ${PROJECT_SOURCE_DIR}/src/*.h ${PROJECT_SOURCE_DIR}/src/*.g)
string(REPLACE ";" " " source_files_list "${source_files}")

add_custom_command(
  OUTPUT Debug_tags.tmp
  COMMAND
    ${mktags_script}
    "Debug"
    ${source_files_list}
    > ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
  DEPENDS mktags
)

add_custom_command(
  OUTPUT Trace_tags.tmp
  COMMAND
    ${mktags_script}
    "Trace"
    ${source_files_list}
    > ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
  DEPENDS mktags
)

add_custom_command(
  OUTPUT Debug_tags
  COMMAND
    diff -q
    ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
    ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
    &> /dev/null
    || mv
    ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
    ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
    || true
  DEPENDS Debug_tags.tmp
)

add_custom_command(
  OUTPUT Trace_tags
  COMMAND
    diff -q
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
    &> /dev/null
    || mv
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
    || true
  DEPENDS Trace_tags.tmp
)

add_custom_command(
  OUTPUT Debug_tags.h
  COMMAND
    ${mktagheaders_script}
    "Debug_tags"
    ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
    > ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
  DEPENDS Debug_tags
)

add_custom_command(
  OUTPUT Trace_tags.h
  COMMAND
    ${mktagheaders_script}
    "Trace_tags"
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
    > ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
  DEPENDS Trace_tags
)

add_custom_target(
  tags_headers
  DEPENDS Debug_tags.h Trace_tags.h
)
