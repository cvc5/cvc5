set(libmain_src_files
  interactive_shell.cpp
  interactive_shell.h
  main.h
  util.cpp
)

add_library(main SHARED ${libmain_src_files})
set_target_properties(main PROPERTIES COMPILE_DEFINITIONS __BUILDING_CVC4DRIVER)
target_link_libraries(main cvc4 cvc4parser)

set(cvc4main_src_files
  command_executor.cpp
  driver_unified.cpp
  main.cpp
)

add_executable(cvc4-main ${cvc4main_src_files})
set_target_properties(cvc4-main
  PROPERTIES
    OUTPUT_NAME cvc4
    COMPILE_DEFINITIONS __BUILDING_CVC4DRIVER)
target_link_libraries(cvc4-main main) #cvc4 cvc4parser replacements)

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
