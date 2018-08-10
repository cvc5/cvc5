add_custom_target(AntlrCvc
  COMMAND
    ${ANTLR_BINARY}
      ${CMAKE_CURRENT_SOURCE_DIR}/Cvc.g
      -fo ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS
    Cvc.g
)
#add_dependencies(... AntlrCvc)
