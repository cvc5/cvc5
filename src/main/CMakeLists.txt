###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
target_compile_definitions(main PRIVATE -D__BUILDING_CVC5DRIVER)
if(ENABLE_SHARED)
  set_target_properties(main PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()

# We can't use target_link_libraries(main ...) here since this is only
# supported for cmake version >= 3.12. Hence, we have to manually add the
# library dependencies for main. As a consequence, include directories from
# dependencies are not propagated and we need to manually add the include
# directories of libcvc5 to main.
add_dependencies(main cvc5 cvc5parser gen-tokens)

# Note: This should not be required anymore as soon as we get rid of the
#       smt_engine.h include in src/main. smt_engine.h has transitive includes
#       of GMP and CLN via sexpr.h and therefore needs GMP/CLN headers.
if(USE_CLN)
  get_target_property(CLN_INCLUDES CLN INTERFACE_INCLUDE_DIRECTORIES)
  target_include_directories(main PRIVATE ${CLN_INCLUDES})
endif()
get_target_property(GMP_INCLUDES GMP INTERFACE_INCLUDE_DIRECTORIES)
target_include_directories(main PRIVATE ${GMP_INCLUDES})

# main-test library is only used for linking against api and unit tests so
# that we don't have to include all object files of main into each api/unit
# test. Do not link against main-test in any other case.
add_library(main-test driver_unified.cpp $<TARGET_OBJECTS:main>)
target_compile_definitions(main-test PRIVATE -D__BUILDING_CVC5DRIVER)
target_link_libraries(main-test PUBLIC cvc5 cvc5parser)
if(USE_CLN)
  target_link_libraries(main-test PUBLIC CLN)
endif()
target_link_libraries(main-test PUBLIC GMP)

#-----------------------------------------------------------------------------#
# cvc5 binary configuration

add_executable(cvc5-bin driver_unified.cpp main.cpp $<TARGET_OBJECTS:main>)
target_compile_definitions(cvc5-bin PRIVATE -D__BUILDING_CVC5DRIVER)
set_target_properties(cvc5-bin
  PROPERTIES
    OUTPUT_NAME cvc5
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
target_link_libraries(cvc5-bin PUBLIC cvc5 cvc5parser)
if(USE_CLN)
  target_link_libraries(cvc5-bin PUBLIC CLN)
endif()
target_link_libraries(cvc5-bin PUBLIC GMP)

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
if(ENABLE_STATIC_BINARY)
  set_target_properties(cvc5-bin PROPERTIES LINK_FLAGS -static)
  set_target_properties(cvc5-bin PROPERTIES LINK_SEARCH_START_STATIC ON)
  set_target_properties(cvc5-bin PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()

if(USE_EDITLINE)
  target_link_libraries(cvc5-bin PUBLIC ${Editline_LIBRARIES})
  target_link_libraries(main-test PUBLIC ${Editline_LIBRARIES})
  target_include_directories(main PUBLIC ${Editline_INCLUDE_DIRS})
endif()

#-----------------------------------------------------------------------------#
# Generate language tokens header files.

foreach(lang Cvc Smt2 Tptp)
  string(TOLOWER ${lang} lang_lc)
  add_custom_command(
    OUTPUT ${lang_lc}_tokens.h
    COMMAND
      sh ${CMAKE_CURRENT_LIST_DIR}/gen-token-header.sh
          ${CMAKE_CURRENT_LIST_DIR}/../parser/${lang_lc}/${lang}.g
          ${CMAKE_CURRENT_BINARY_DIR}/${lang_lc}_tokens.h
    DEPENDS ../parser/${lang_lc}/${lang}.g
  )
endforeach()

# Create target used as a dependency for libmain.
add_custom_target(gen-tokens
  DEPENDS
    cvc_tokens.h
    smt2_tokens.h
    tptp_tokens.h
)

