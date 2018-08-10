add_custom_target(AntlrTptp
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Tptp.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS
    Tptp.g
)
#add_dependencies(... AntlrTptp)
