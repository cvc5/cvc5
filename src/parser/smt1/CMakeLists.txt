add_custom_target(AntlrSmt1
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Smt1.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS
    Smt1.g
)
#add_dependencies(... AntlrSmt1)
