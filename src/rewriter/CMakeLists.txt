###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Check if the pyparsing Python module is installed.
check_python_module("pyparsing")

libcvc5_add_sources(GENERATED
  rewrites.cpp
  rewrites.h
)
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

add_custom_command(
    OUTPUT
      rewrites.cpp
      rewrites.h
    COMMAND
      ${Python_EXECUTABLE}
      ${mkrewrites_script}
      rewrite-db
      ${CMAKE_CURRENT_LIST_DIR}
      ${REWRITES_FILES}
    DEPENDS
      ${mkrewrites_script}
      ${REWRITES_FILES}
      ${CMAKE_CURRENT_LIST_DIR}/rewrites_template.cpp
      ${CMAKE_CURRENT_LIST_DIR}/rewrites_template.h
    COMMENT
      "Generating rewrites.{h,cpp}"
)

add_custom_target(gen-rewrites
  DEPENDS
    rewrites.cpp
    rewrites.h
)
