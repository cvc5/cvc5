###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Andrew V. Jones
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Generate cvc5config.h header
configure_file(cvc5config.h.in cvc5config.h)

#-----------------------------------------------------------------------------#

set(LIBBASE_SOURCES
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
  ${CMAKE_CURRENT_BINARY_DIR}/versioninfo.cpp
)
set_source_files_properties(
  ${CMAKE_CURRENT_BINARY_DIR}/versioninfo.cpp
  PROPERTIES GENERATED TRUE
)

#-----------------------------------------------------------------------------#
# Generate code for debug/trace tags

set(collect_tags_script ${CMAKE_CURRENT_LIST_DIR}/collect_tags.py)

file(GLOB_RECURSE source_files
     ${PROJECT_SOURCE_DIR}/src/*.cpp
     ${PROJECT_SOURCE_DIR}/src/*.cc
     ${PROJECT_SOURCE_DIR}/src/*.h
     ${PROJECT_SOURCE_DIR}/src/*.g)

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
  COMMAND ${Python_EXECUTABLE} ${collect_tags_script} ${CMAKE_CURRENT_BINARY_DIR}/ ${PROJECT_SOURCE_DIR}/src
  DEPENDS ${collect_tags_script} ${source_files}
)

add_custom_target(gen-tags
  DEPENDS
    ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
)

set_source_files_properties(
  ${CMAKE_CURRENT_BINARY_DIR}/Trace_tags.h
  PROPERTIES GENERATED TRUE
)

add_library(cvc5base OBJECT ${LIBBASE_SOURCES})
set_target_properties(cvc5base PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_compile_definitions(cvc5base PRIVATE -D__BUILDING_CVC5LIB -Dcvc5_obj_EXPORTS)
add_dependencies(cvc5base gen-versioninfo gen-tags)
