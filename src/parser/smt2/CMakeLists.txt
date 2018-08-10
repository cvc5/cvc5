add_custom_target(AntlrSmt2
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Smt2.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS
    Smt2.g
)
#add_dependencies(... AntlrSmt2)
