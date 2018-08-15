set(compat_src_files
  cvc3_compat.cpp
  cvc3_compat.h
)

add_library(cvc4compat ${compat_src_files})
target_compile_definitions(cvc4compat PRIVATE -D__BUILDING_CVC4COMPATLIB)
target_link_libraries(cvc4compat cvc4)
