set(ANTLR_HOME ${ANTLR_DIR})
find_package(ANTLR REQUIRED)

# Java runtime is required for ANTLR
find_package(Java COMPONENTS Runtime REQUIRED)

set(cvc4parser_src_files
  antlr_input.cpp
  antlr_input.h
  antlr_input_imports.cpp
  antlr_line_buffered_input.cpp
  antlr_line_buffered_input.h
  antlr_tracing.h
  antlr_undefines.h
  bounded_token_buffer.cpp
  bounded_token_buffer.h
  bounded_token_factory.cpp
  bounded_token_factory.h
  cvc/cvc_input.cpp
  cvc/cvc_input.h
  input.cpp
  input.h
  line_buffer.cpp
  line_buffer.h
  memory_mapped_input_buffer.cpp
  memory_mapped_input_buffer.h
  parser.cpp
  parser.h
  parser_builder.cpp
  parser_builder.h
  parser_exception.h
  smt1/smt1.cpp
  smt1/smt1.h
  smt1/smt1_input.cpp
  smt1/smt1_input.h
  smt2/smt2.cpp
  smt2/smt2.h
  smt2/smt2_input.cpp
  smt2/smt2_input.h
  smt2/sygus_input.cpp
  smt2/sygus_input.h
  tptp/TptpLexer.c
  tptp/TptpParser.c
  tptp/tptp.cpp
  tptp/tptp.h
  tptp/tptp_input.cpp
  tptp/tptp_input.h
)

# Generate parsers for all supported languages
foreach(lang Cvc Smt1 Smt2 Tptp)
  string(TOLOWER ${lang} lang_dir)
  file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir})
  add_custom_command(
    OUTPUT
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Lexer.c
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Lexer.h
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Parser.c
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Parser.h
      ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}.tokens
    COMMAND
      ${ANTLR_BINARY}
        ${CMAKE_CURRENT_SOURCE_DIR}/${lang_dir}/${lang}.g
        -fo ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}
    DEPENDS
      ${lang_dir}/${lang}.g
  )
  set(gen_src_files
    ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Lexer.c
    ${CMAKE_CURRENT_BINARY_DIR}/${lang_dir}/${lang}Parser.c)

  # Tell cmake that generated source files are actually c++ files
  set_source_files_properties(${gen_src_files} PROPERTIES LANGUAGE CXX)
  set_source_files_properties(${gen_src_files} PROPERTIES GENERATED TRUE)

  # Add generated source files to the parser source files
  list(APPEND cvc4parser_src_files ${gen_src_files})
endforeach()

add_library(cvc4parser ${cvc4parser_src_files})
set_target_properties(cvc4parser PROPERTIES SOVERSION ${CVC4_SOVERSION})
target_compile_definitions(cvc4parser PRIVATE -D__BUILDING_CVC4PARSERLIB)
target_link_libraries(cvc4parser cvc4 ${ANTLR_LIBRARIES})
target_include_directories(cvc4parser PRIVATE ${ANTLR_INCLUDE_DIR})
install(TARGETS cvc4parser DESTINATION lib)
