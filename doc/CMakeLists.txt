#-----------------------------------------------------------------------------#
# Set variables required for the documentation *.in files

string(TIMESTAMP MAN_DATE "%Y-%m-%d")
set(VERSION CVC4_RELEASE_STRING)

#-----------------------------------------------------------------------------#
# Generate files

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/SmtEngine.3cvc_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/SmtEngine.3cvc_template)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/cvc4.1_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/cvc4.1_template)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/cvc4.5.in
  ${CMAKE_CURRENT_BINARY_DIR}/cvc4.5)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/libcvc4.3.in
  ${CMAKE_CURRENT_BINARY_DIR}/libcvc4.3)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/libcvc4parser.3.in
  ${CMAKE_CURRENT_BINARY_DIR}/libcvc4parser.3)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/options.3cvc_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/options.3cvc_template)

#-----------------------------------------------------------------------------#
# Install man pages

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/cvc4.1 DESTINATION share/man/man1)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/cvc4.5 DESTINATION share/man/man5)
install(FILES
        ${CMAKE_CURRENT_BINARY_DIR}/libcvc4.3
        ${CMAKE_CURRENT_BINARY_DIR}/libcvc4parser.3
        ${CMAKE_CURRENT_BINARY_DIR}/options.3cvc
        ${CMAKE_CURRENT_BINARY_DIR}/SmtEngine.3cvc
        DESTINATION share/man/man3)
