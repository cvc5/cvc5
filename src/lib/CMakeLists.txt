set(replacements_src_files
  clock_gettime.c
  clock_gettime.h
  ffs.c
  ffs.h
  replacements.h
  strtok_r.c
  strtok_r.h
)

add_library(replacements ${replacements_src_files})
target_compile_definitions(replacements PRIVATE -D__BUILDING_CVC4LIB)
