###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Leni Aniva, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Check if the pyparsing Python module is installed.
check_python_module("pyparsing")

libcvc5_add_sources(
  basic_rewrite_rcons.cpp
  basic_rewrite_rcons.h
  rewrite_db.cpp
  rewrite_db.h
  rewrite_db_proof_cons.cpp
  rewrite_db_proof_cons.h
  rewrite_db_term_process.cpp
  rewrite_db_term_process.h
  rewrite_proof_rule.cpp
  rewrite_proof_rule.h
)

set(mkrewrites_script ${CMAKE_CURRENT_LIST_DIR}/mkrewrites.py)

set(REWRITE_OUTPUT_FILES
  rewrites.cpp
  rewrites.h
)
foreach(rewrite_in IN LISTS REWRITES_FILES)
  # NOTE: In CMake 3.20+, the `cmake_path` command can be used instead

  get_filename_component(rewrite_parent ${rewrite_in} DIRECTORY)
  get_filename_component(rewrite_name ${rewrite_in} NAME)
  get_filename_component(rewrite_dir ${rewrite_parent} NAME)
  list(APPEND REWRITE_OUTPUT_FILES "rewrites-${rewrite_dir}-${rewrite_name}.cpp")
endforeach()

libcvc5_add_sources(GENERATED
  ${REWRITE_OUTPUT_FILES}
)

add_custom_command(
    OUTPUT
      ${REWRITE_OUTPUT_FILES}
    COMMAND
      ${Python_EXECUTABLE}
      ${mkrewrites_script}
      rewrite-db
      ${CMAKE_CURRENT_LIST_DIR}
      ${REWRITES_FILES}
    DEPENDS
      ${mkrewrites_script}
      ${REWRITES_FILES}
      ${CMAKE_CURRENT_LIST_DIR}/theory_rewrites_template.cpp
      ${CMAKE_CURRENT_LIST_DIR}/rewrites_template.cpp
      ${CMAKE_CURRENT_LIST_DIR}/rewrites_template.h
    COMMENT
      "Generating rewrites.{h,cpp}"
)

add_custom_target(gen-rewrites
  DEPENDS
    ${REWRITE_OUTPUT_FILES}
)
