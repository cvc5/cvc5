#-----------------------------------------------------------------------------#
# libmain source files

set(libmain_src_files
  command_executor.cpp
  interactive_shell.cpp
  interactive_shell.h
  main.h
  util.cpp
)

#-----------------------------------------------------------------------------#
# Build object library since we will use the object files for cvc4-bin,
# pcvc4-bin, and main-test library.

add_library(main OBJECT ${libmain_src_files})
target_compile_definitions(main PRIVATE -D__BUILDING_CVC4DRIVER)
if(ENABLE_SHARED)
  set_target_properties(main PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()

# We can't use target_link_libraries(...) here since this is only supported for
# cmake version >= 3.12. Hence, we have to manually add the library
# dependencies for main. As a consequence, include directories from
# dependencies are not propagated and we need to manually add the include
# directories of libcvc4 to main.
add_dependencies(main cvc4 cvc4parser gen-tokens)
get_target_property(LIBCVC4_INCLUDES cvc4 INCLUDE_DIRECTORIES)
target_include_directories(main PRIVATE ${LIBCVC4_INCLUDES})

# main-test library is only used for linking against system and unit tests so
# that we don't have to include all object files of main into each unit/system
# test. Do not link against main-test in any other case.
add_library(main-test driver_unified.cpp $<TARGET_OBJECTS:main>)
target_compile_definitions(main-test PRIVATE -D__BUILDING_CVC4DRIVER)
target_link_libraries(main-test cvc4 cvc4parser)

#-----------------------------------------------------------------------------#
# cvc4 binary configuration

add_executable(cvc4-bin driver_unified.cpp main.cpp $<TARGET_OBJECTS:main>)
target_compile_definitions(cvc4-bin PRIVATE -D__BUILDING_CVC4DRIVER)
set_target_properties(cvc4-bin
  PROPERTIES
    OUTPUT_NAME cvc4
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
target_link_libraries(cvc4-bin cvc4 cvc4parser)
if(PROGRAM_PREFIX)
  install(PROGRAMS
    $<TARGET_FILE:cvc4-bin> DESTINATION bin RENAME ${PROGRAM_PREFIX}cvc4)
else()
  install(TARGETS cvc4-bin DESTINATION bin)
endif()

# In order to get a fully static executable we have to make sure that we also
# use the static system libraries.
#   https://cmake.org/cmake/help/v3.0/prop_tgt/LINK_SEARCH_START_STATIC.html
#   https://cmake.org/cmake/help/v3.0/prop_tgt/LINK_SEARCH_END_STATIC.html
if(ENABLE_STATIC_BINARY)
  set_target_properties(cvc4-bin PROPERTIES LINK_FLAGS -static)
  set_target_properties(cvc4-bin PROPERTIES LINK_SEARCH_START_STATIC ON)
  set_target_properties(cvc4-bin PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()

if(USE_READLINE)
  target_link_libraries(cvc4-bin ${Readline_LIBRARIES})
  target_link_libraries(main-test ${Readline_LIBRARIES})
  target_include_directories(main PRIVATE ${Readline_INCLUDE_DIR})
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

