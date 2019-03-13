libcvc4_add_sources(
  argument_extender.h
  argument_extender_implementation.cpp
  argument_extender_implementation.h
  arith_heuristic_pivot_rule.cpp
  arith_heuristic_pivot_rule.h
  arith_propagation_mode.cpp
  arith_propagation_mode.h
  arith_unate_lemma_mode.cpp
  arith_unate_lemma_mode.h
  base_handlers.h
  bool_to_bv_mode.cpp
  bool_to_bv_mode.h
  bv_bitblast_mode.cpp
  bv_bitblast_mode.h
  datatypes_modes.h
  decision_mode.cpp
  decision_mode.h
  decision_weight.h
  didyoumean.cpp
  didyoumean.h
  language.cpp
  language.h
  open_ostream.cpp
  open_ostream.h
  option_exception.cpp
  option_exception.h
  options.h
  options_handler.cpp
  options_handler.h
  options_public_functions.cpp
  printer_modes.cpp
  printer_modes.h
  quantifiers_modes.cpp
  quantifiers_modes.h
  set_language.cpp
  set_language.h
  smt_modes.cpp
  smt_modes.h
  strings_process_loop_mode.cpp
  strings_process_loop_mode.h
  sygus_out_mode.h
  theoryof_mode.cpp
  theoryof_mode.h
  ufss_mode.h
)

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

string(REPLACE "toml" "cpp;" options_gen_cpp_files ${options_toml_files})
string(REPLACE "toml" "h;"   options_gen_h_files ${options_toml_files})

libcvc4_add_sources(GENERATED options.cpp ${options_gen_cpp_files})

list_prepend(options_toml_files "${CMAKE_CURRENT_LIST_DIR}/" abs_toml_files)

add_custom_command(
    OUTPUT
      options.cpp options_holder.h
      ${options_gen_cpp_files} ${options_gen_h_files}
    COMMAND
      ${PYTHON_EXECUTABLE}
      ${CMAKE_CURRENT_LIST_DIR}/mkoptions.py
      ${CMAKE_CURRENT_LIST_DIR}
      ${CMAKE_CURRENT_BINARY_DIR}/../../doc
      ${CMAKE_CURRENT_BINARY_DIR}
      ${abs_toml_files}
    DEPENDS
      mkoptions.py
      ${options_toml_files}
      module_template.h
      module_template.cpp
      options_holder_template.h
      options_template.cpp
      ${CMAKE_CURRENT_BINARY_DIR}/../../doc/cvc4.1_template
      ${CMAKE_CURRENT_BINARY_DIR}/../../doc/SmtEngine.3cvc_template
      ${CMAKE_CURRENT_BINARY_DIR}/../../doc/options.3cvc_template
)

add_custom_target(gen-options
  DEPENDS
    options.cpp
    options_holder.h
    ${options_gen_cpp_files}
    ${options_gen_h_files}
)
