macro(prepend_path)
  foreach(SOURCE_FILE ${ARGN})
    set(PREPEND_PATH_SOURCES
      ${PREPEND_PATH_SOURCES}
      ${CMAKE_CURRENT_LIST_DIR}/${SOURCE_FILE})
  endforeach()
  set(PREPEND_PATH_SOURCES ${PREPEND_PATH_SOURCES} PARENT_SCOPE)
endmacro()

set(options_toml_files
  arith_options.toml
  arrays_options.toml
  base_options.toml
  booleans_options.toml
  builtin_options.toml
  bv_options.toml
  datatypes_options.toml
  decision_options.toml
  expr_options.toml
  fp_options.toml
  idl_options.toml
  main_options.toml
  parser_options.toml
  printer_options.toml
  proof_options.toml
  prop_options.toml
  quantifiers_options.toml
  sep_options.toml
  sets_options.toml
  smt_options.toml
  strings_options.toml
  theory_options.toml
  uf_options.toml
)

string(REPLACE "toml" "cpp;" options_cpp_files ${options_toml_files})
string(REPLACE "toml" "h;"   options_h_files ${options_toml_files})

prepend_path(${options_toml_files})

add_custom_command(
    COMMAND
      ${PYTHON_EXECUTABLE}
      ${CMAKE_CURRENT_LIST_DIR}/mkoptions.py
      ${CMAKE_CURRENT_LIST_DIR}
      ${CMAKE_CURRENT_BINARY_DIR}/../../doc
      ${CMAKE_CURRENT_BINARY_DIR}
      ${PREPEND_PATH_SOURCES}
    DEPENDS mkoptions.py ${options_toml_files}
    OUTPUT ${options_cpp_files} ${options_h_files}
    COMMENT "Generating code for options."
)

#add_library(options STATIC ${options_cpp_files})
