set(replacements_src_files
  clock_gettime.c
  clock_gettime.h
  ffs.c
  ffs.h
  replacements.h
  strtok_r.c
  strtok_r.h
)

add_library(replacements SHARED ${replacements_src_files})
set_target_properties(replacements PROPERTIES COMPILE_DEFINITIONS __BUILDING_CVC4LIB)
