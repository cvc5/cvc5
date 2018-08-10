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
      2> /dev/null # Ignore Antlr3 warnings
  DEPENDS
    Cvc.g
)

add_library(parsercvc SHARED ${parser_cvc_src_files} ${parser_cvc_gen_src_files})
set_target_properties(parsercvc PROPERTIES COMPILE_DEFINITIONS __BUILDING_CVC4PARSERLIB)
set_source_files_properties(${parser_cvc_gen_src_files} PROPERTIES LANGUAGE CXX)
add_dependencies(parsercvc expr)
