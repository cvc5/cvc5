###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Aina Niemetz
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

# libmain source files
set(libmain_src_files
  command_executor.cpp
  interactive_shell.cpp
  interactive_shell.h
  main.h
  options.h
  portfolio_driver.cpp
  portfolio_driver.h
  signal_handlers.cpp
  signal_handlers.h
  time_limit.cpp
  time_limit.h
)
set(libmain_gen_src_files
  ${CMAKE_CURRENT_BINARY_DIR}/options.cpp
)
set_source_files_properties(${libmain_gen_src_files} PROPERTIES GENERATED TRUE)

#-----------------------------------------------------------------------------#
# Build object library since we will use the object files for cvc5-bin and
# main-test library.

add_library(main OBJECT ${libmain_src_files} ${libmain_gen_src_files})
target_compile_definitions(main PRIVATE -D__BUILDING_CVC5DRIVER -Dcvc5_obj_EXPORTS)
set_target_properties(main PROPERTIES POSITION_INDEPENDENT_CODE ON)

add_dependencies(main gen-tokens cvc5-obj)

# main-test library is only used for linking against api and unit tests so
# that we don't have to include all object files of main into each api/unit
# test. Do not link against main-test in any other case.
add_library(main-test driver_unified.cpp $<TARGET_OBJECTS:main>)
target_compile_definitions(main-test PRIVATE -D__BUILDING_CVC5DRIVER)
target_link_libraries(main-test PUBLIC cvc5 cvc5parser)
if(USE_CLN)
  target_link_libraries(main-test PUBLIC CLN)
endif()
if(USE_POLY)
  target_link_libraries(main-test PUBLIC Polyxx)
endif()

#-----------------------------------------------------------------------------#
# cvc5 binary configuration

add_executable(cvc5-bin driver_unified.cpp main.cpp $<TARGET_OBJECTS:main>)
target_compile_definitions(cvc5-bin PRIVATE -D__BUILDING_CVC5DRIVER -Dcvc5_obj_EXPORTS)
set_target_properties(cvc5-bin
  PROPERTIES
    OUTPUT_NAME cvc5
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
if(PROGRAM_PREFIX)
  install(PROGRAMS
    $<TARGET_FILE:cvc5-bin>
    DESTINATION ${CMAKE_INSTALL_BINDIR}
    RENAME ${PROGRAM_PREFIX}cvc5)
else()
  install(TARGETS cvc5-bin
    DESTINATION ${CMAKE_INSTALL_BINDIR})
endif()

# In order to get a fully static executable we have to make sure that we also
# use the static system libraries.
#   https://cmake.org/cmake/help/v3.0/prop_tgt/LINK_SEARCH_START_STATIC.html
#   https://cmake.org/cmake/help/v3.0/prop_tgt/LINK_SEARCH_END_STATIC.html
if(NOT BUILD_SHARED_LIBS)
  if(STATIC_BINARY)
    set_target_properties(cvc5-bin PROPERTIES LINK_FLAGS -static)
    set_target_properties(cvc5-bin PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties(cvc5-bin PROPERTIES LINK_SEARCH_END_STATIC ON)
  endif()
  set_target_properties(cvc5-bin PROPERTIES INSTALL_RPATH "")
endif()
target_link_libraries(cvc5-bin PUBLIC cvc5 cvc5parser)

if(USE_EDITLINE)
  target_link_libraries(cvc5-bin PUBLIC ${Editline_LIBRARIES})
  target_link_libraries(main-test PUBLIC ${Editline_LIBRARIES})
  target_include_directories(main PUBLIC ${Editline_INCLUDE_DIRS})
endif()

#-----------------------------------------------------------------------------#
# Generate language tokens header files.

add_custom_command(
  OUTPUT smt2_tokens.h
  COMMAND
    sh ${CMAKE_CURRENT_LIST_DIR}/gen-token-header.sh
        ${CMAKE_CURRENT_LIST_DIR}/../parser/smt2/smt2_cmd_parser.cpp
        smt2_tokens.h
  DEPENDS ../parser/smt2/smt2_cmd_parser.cpp
)

# Create target used as a dependency for libmain.
add_custom_target(gen-tokens
  DEPENDS
    smt2_tokens.h
)

