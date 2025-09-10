###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Leni Aniva, Abdalrhman Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  rewrite_proof_status.cpp
  rewrite_proof_status.h
  rewrites.h
)

set(mkrewrites_script ${CMAKE_CURRENT_LIST_DIR}/mkrewrites.py)

set(REWRITE_OUTPUT_FILES
  rewrites.cpp
)
foreach(rewrite_in IN LISTS REWRITES_FILES REWRITES_FILES_EXPERT)
  # NOTE: In CMake 3.20+, the `cmake_path` command can be used instead

  get_filename_component(rewrite_parent ${rewrite_in} DIRECTORY)
  get_filename_component(rewrite_name ${rewrite_in} NAME)
  get_filename_component(rewrite_dir ${rewrite_parent} NAME)
  list(APPEND REWRITE_OUTPUT_FILES "rewrites-${rewrite_dir}-${rewrite_name}.cpp")
endforeach()

libcvc5_add_sources(GENERATED
  ${REWRITE_OUTPUT_FILES}
)

list(APPEND REWRITE_OUTPUT_FILES
  ${CMAKE_BINARY_DIR}/src/api/cpp/cvc5_proof_rule.cpp
  ${CMAKE_BINARY_DIR}/include/cvc5/cvc5_proof_rule.h
)

# If the generated header differs from the source header, it should be copied to
# the source directory manually for compilation to succeed.
list(APPEND LIBCVC5_GEN_SRCS
  ${CMAKE_BINARY_DIR}/src/api/cpp/cvc5_proof_rule.cpp
)

set(LIBCVC5_GEN_SRCS ${LIBCVC5_GEN_SRCS} PARENT_SCOPE)

add_custom_command(
    OUTPUT
      ${REWRITE_OUTPUT_FILES}
    COMMAND
      ${Python_EXECUTABLE}
      ${mkrewrites_script}
      rewrite-db
      --src ${CMAKE_SOURCE_DIR}
      --bin ${CMAKE_BINARY_DIR}
      --rewrites_files ${REWRITES_FILES}
      --rewrites_files_expert ${REWRITES_FILES_EXPERT}
    DEPENDS
      ${mkrewrites_script}
      ${REWRITES_FILES}
      ${REWRITES_FILES_EXPERT}
      ${CMAKE_CURRENT_LIST_DIR}/theory_rewrites_template.cpp
      ${CMAKE_CURRENT_LIST_DIR}/rewrites_template.cpp
      ${CMAKE_SOURCE_DIR}/src/api/cpp/cvc5_proof_rule_template.cpp
      ${CMAKE_SOURCE_DIR}/include/cvc5/cvc5_proof_rule.h
    COMMENT
      "Generating rewrites.{h,cpp}"
)

add_custom_target(gen-rewrites
  DEPENDS
    ${REWRITE_OUTPUT_FILES}
)
