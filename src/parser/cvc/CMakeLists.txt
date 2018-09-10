set(parser_cvc_src_files
  cvc_input.cpp
  cvc_input.h
)

set(parser_cvc_gen_src_files
  CvcLexer.c
  CvcParser.c
)

add_custom_command(
  OUTPUT ${parser_cvc_gen_src_files} CvcLexer.h CvcParser.h Cvc.tokens
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Cvc.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS
    Cvc.g
)

add_library(parsercvc ${parser_cvc_src_files} ${parser_cvc_gen_src_files})
target_compile_definitions(parsercvc PRIVATE -D__BUILDING_CVC4PARSERLIB)
set_source_files_properties(${parser_cvc_gen_src_files} PROPERTIES LANGUAGE CXX)
target_link_libraries(parsercvc expr)
