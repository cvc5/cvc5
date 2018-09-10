set(parser_smt2_src_files
  smt2.cpp
  smt2.h
  smt2_input.cpp
  smt2_input.h
  sygus_input.cpp
  sygus_input.h
)

set(parser_smt2_gen_src_files
  Smt2Lexer.c
  Smt2Parser.c
)

add_custom_command(
  OUTPUT ${parser_smt2_gen_src_files} Smt2Lexer.h Smt2Parser.h Smt2.tokens
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Smt2.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS
    Smt2.g
)

add_library(parsersmt2 ${parser_smt2_src_files} ${parser_smt2_gen_src_files})
target_compile_definitions(parsersmt2 PRIVATE -D__BUILDING_CVC4PARSERLIB)
set_source_files_properties(${parser_smt2_gen_src_files} PROPERTIES LANGUAGE CXX)
target_link_libraries(parsersmt2 expr)
