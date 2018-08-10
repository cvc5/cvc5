set(compat_src_files
  cvc3_compat.cpp
  cvc3_compat.h
)

add_library(cvc4compat SHARED ${compat_src_files})
set_target_properties(cvc4compat
  PROPERTIES COMPILE_DEFINITIONS __BUILDING_CVC4COMPATLIB)
target_link_libraries(cvc4compat cvc4)
