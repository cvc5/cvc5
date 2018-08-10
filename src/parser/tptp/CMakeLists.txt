set(parser_tptp_src_files
  tptp.cpp
  tptp.h
  tptp_input.cpp
  tptp_input.h
)

set(parser_tptp_gen_src_files
  TptpLexer.c
  TptpParser.c
)

add_custom_command(
  OUTPUT ${parser_tptp_gen_src_files} TptpLexer.h TptpParser.h Tptp.tokens
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Tptp.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
      2> /dev/null # Ignore Antlr3 warnings
  DEPENDS
    Tptp.g
)

add_library(parsertptp SHARED ${parser_tptp_src_files} ${parser_tptp_gen_src_files})
set_target_properties(parsertptp PROPERTIES COMPILE_DEFINITIONS __BUILDING_CVC4PARSERLIB)
set_source_files_properties(${parser_tptp_gen_src_files} PROPERTIES LANGUAGE CXX)
add_dependencies(parsertptp expr)
