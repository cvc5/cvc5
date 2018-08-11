set(mktags_script ${CMAKE_CURRENT_LIST_DIR}/mktags)
set(mktagheaders_script ${CMAKE_CURRENT_LIST_DIR}/mktagheaders)
file(GLOB_RECURSE source_files ${PROJECT_SOURCE_DIR}/src/*.cpp ${PROJECT_SOURCE_DIR}/src/*.cc ${PROJECT_SOURCE_DIR}/src/*.h ${PROJECT_SOURCE_DIR}/src/*.g)
string(REPLACE ";" " " source_files_list "${source_files}")

add_custom_target(
    debug_tags_tmp
    COMMAND
      ${mktags_script}
      "Debug"
      ${source_files_list}
      > ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp
    DEPENDS mktags
)

add_custom_target(
    trace_tags_tmp
    COMMAND
      ${mktags_script}
      "Trace"
      ${source_files_list}
      > ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp
    DEPENDS mktags
)

add_custom_target(
    debug_tags
    COMMAND
      diff -q
      ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp 
      ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
      &> /dev/null
      || mv
      ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.tmp 
      ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
      || true
      DEPENDS debug_tags_tmp
)

add_custom_target(
    trace_tags
    COMMAND
      diff -q
      ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp 
      ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
      &> /dev/null
      || mv
      ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.tmp 
      ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
      || true
      DEPENDS trace_tags_tmp
)

add_custom_target(
    debug_tags.h
    COMMAND
      ${mktagheaders_script}
      "Debug_tags"
      ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags
      > ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
      DEPENDS debug_tags
)

add_custom_target(
    trace_tags.h
    COMMAND
      ${mktagheaders_script}
      "Trace_tags"
      ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags
      > ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
      DEPENDS trace_tags
)
