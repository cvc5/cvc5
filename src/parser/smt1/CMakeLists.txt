set(parser_smt1_src_files
  smt1.cpp
  smt1.h
  smt1_input.cpp
  smt1_input.h
)

set(parser_smt1_gen_src_files
  Smt1Lexer.c
  Smt1Parser.c
)

add_custom_command(
  OUTPUT ${parser_smt1_gen_src_files} Smt1Lexer.h Smt1Parser.h Smt1.tokens
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Smt1.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS
    Smt1.g
)

add_library(parsersmt1 ${parser_smt1_src_files} ${parser_smt1_gen_src_files})
target_compile_definitions(parsersmt1 PRIVATE -D__BUILDING_CVC4PARSERLIB)
set_source_files_properties(${parser_smt1_gen_src_files} PROPERTIES LANGUAGE CXX)
target_link_libraries(parsersmt1 expr)
