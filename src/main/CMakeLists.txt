set(libmain_src_files
  interactive_shell.cpp
  interactive_shell.h
  main.h
  util.cpp
)

add_library(main ${libmain_src_files})
target_compile_definitions(main PRIVATE -D__BUILDING_CVC4DRIVER)
target_link_libraries(main cvc4 cvc4parser)

set(cvc4main_src_files
  command_executor.cpp
  driver_unified.cpp
  main.cpp
)

add_executable(cvc4-main ${cvc4main_src_files})
target_compile_definitions(cvc4-main PRIVATE -D__BUILDING_CVC4DRIVER)
set_target_properties(cvc4-main PROPERTIES OUTPUT_NAME cvc4)
target_link_libraries(cvc4-main main)
add_dependencies(cvc4-main token-headers)

#set(pcvc4_src_files
#  main.cpp
#  portfolio.cpp
#  portfolio.h
#  portfolio_util.cpp
#  portfolio_util.h
#  command_executor.cpp
#  command_executor_portfolio.cpp
#  command_executor.h
#  command_executor_portfolio.h
#  driver_unified.cpp
#)

add_custom_command(
  OUTPUT cvc_tokens.h
  COMMAND
    sh ${CMAKE_CURRENT_LIST_DIR}/gen-token-header.sh
        ${CMAKE_CURRENT_LIST_DIR}/../parser/cvc/Cvc.g
        ${CMAKE_CURRENT_BINARY_DIR}/cvc_tokens.h
  DEPENDS ../parser/cvc/Cvc.g
)

add_custom_command(
  OUTPUT smt1_tokens.h
  COMMAND
    sh ${CMAKE_CURRENT_LIST_DIR}/gen-token-header.sh
        ${CMAKE_CURRENT_LIST_DIR}/../parser/smt1/Smt1.g
        ${CMAKE_CURRENT_BINARY_DIR}/smt1_tokens.h
  DEPENDS ../parser/smt1/Smt1.g
)

add_custom_command(
  OUTPUT smt2_tokens.h
  COMMAND
    sh ${CMAKE_CURRENT_LIST_DIR}/gen-token-header.sh
        ${CMAKE_CURRENT_LIST_DIR}/../parser/smt2/Smt2.g
        ${CMAKE_CURRENT_BINARY_DIR}/smt2_tokens.h
  DEPENDS ../parser/smt2/Smt2.g
)

add_custom_command(
  OUTPUT tptp_tokens.h
  COMMAND
    sh ${CMAKE_CURRENT_LIST_DIR}/gen-token-header.sh
        ${CMAKE_CURRENT_LIST_DIR}/../parser/tptp/Tptp.g
        ${CMAKE_CURRENT_BINARY_DIR}/tptp_tokens.h
  DEPENDS ../parser/tptp/Tptp.g
)

add_custom_target(
  token-headers
  DEPENDS cvc_tokens.h smt1_tokens.h smt2_tokens.h tptp_tokens.h
)
