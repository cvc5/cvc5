#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Mathias Preiner, Andrew V. Jones, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
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

set(collect_tags_script ${CMAKE_CURRENT_LIST_DIR}/collect_tags.py)

file(GLOB_RECURSE source_files
     ${PROJECT_SOURCE_DIR}/src/*.cpp
     ${PROJECT_SOURCE_DIR}/src/*.cc
     ${PROJECT_SOURCE_DIR}/src/*.h
     ${PROJECT_SOURCE_DIR}/src/*.g)
string(REPLACE ";" " " source_files_list "${source_files}")

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Debug_tags.h
  COMMAND ${PYTHON_EXECUTABLE} ${collect_tags_script} ${CMAKE_CURRENT_BINARY_DIR}/ Debug ${PROJECT_SOURCE_DIR}/src
  DEPENDS ${collect_tags_script} ${source_files}
)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
  COMMAND ${PYTHON_EXECUTABLE} ${collect_tags_script} ${CMAKE_CURRENT_BINARY_DIR}/ Trace ${PROJECT_SOURCE_DIR}/src
  DEPENDS ${collect_tags_script} ${source_files}
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
