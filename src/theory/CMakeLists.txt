###############################################################################
# Top contributors (to current version):
#   José Neto, Aina Niemetz, Mathias Preiner
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

libcvc5_add_sources(GENERATED
  rewriter_tables.h
  theory_traits.h
  type_enumerator.cpp
)

set(mktheorytraits_script ${CMAKE_CURRENT_LIST_DIR}/mktheorytraits.py)
set(mkrewriter_script ${CMAKE_CURRENT_LIST_DIR}/mkrewriter.py)

add_custom_command(
  OUTPUT rewriter_tables.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mkrewriter_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/rewriter_tables_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/rewriter_tables.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkrewriter.py rewriter_tables_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT theory_traits.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mktheorytraits_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/theory_traits_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/theory_traits.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mktheorytraits.py theory_traits_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT type_enumerator.cpp
  COMMAND
    ${Python_EXECUTABLE}
    ${mktheorytraits_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/type_enumerator_template.cpp
    --output ${CMAKE_CURRENT_BINARY_DIR}/type_enumerator.cpp
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mktheorytraits.py type_enumerator_template.cpp ${KINDS_TOML_FILES}
)

add_custom_target(gen-theory
  DEPENDS
    type_enumerator.cpp
    theory_traits.h
    rewriter_tables.h
)
