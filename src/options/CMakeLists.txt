###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Check if the toml Python module is installed.
check_python_module("toml")

libcvc5_add_sources(
  base_handlers.h
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
  options_listener.h
  options_public_functions.cpp
  printer_modes.cpp
  printer_modes.h
  set_language.cpp
  set_language.h
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
  main_options.toml
  parser_options.toml
  printer_options.toml
  proof_options.toml
  prop_options.toml
  quantifiers_options.toml
  resource_manager_options.toml
  sep_options.toml
  sets_options.toml
  smt_options.toml
  strings_options.toml
  theory_options.toml
  uf_options.toml
)

string(REPLACE "toml" "cpp;" options_gen_cpp_files ${options_toml_files})
string(REPLACE "toml" "h;"   options_gen_h_files ${options_toml_files})

libcvc5_add_sources(GENERATED options.cpp ${options_gen_cpp_files})

list_prepend(options_toml_files "${CMAKE_CURRENT_LIST_DIR}/" abs_toml_files)

add_custom_command(
    OUTPUT
      options.cpp options_holder.h
      ${options_gen_cpp_files} ${options_gen_h_files}
    COMMAND
      ${PYTHON_EXECUTABLE}
      ${CMAKE_CURRENT_LIST_DIR}/mkoptions.py
      ${CMAKE_CURRENT_LIST_DIR}
      ${CMAKE_CURRENT_BINARY_DIR}
      ${abs_toml_files}
    DEPENDS
      mkoptions.py
      ${options_toml_files}
      module_template.h
      module_template.cpp
      options_holder_template.h
      options_template.cpp
)

add_custom_target(gen-options
  DEPENDS
    options.cpp
    options_holder.h
    ${options_gen_cpp_files}
    ${options_gen_h_files}
)
