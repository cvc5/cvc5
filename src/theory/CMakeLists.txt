#####################
## CMakeLists.txt
## Top contributors (to current version):
##   Aina Niemetz, Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
libcvc4_add_sources(GENERATED
  rewriter_tables.h
  theory_traits.h
  type_enumerator.cpp
)

set(mktheorytraits_script ${CMAKE_CURRENT_LIST_DIR}/mktheorytraits)
set(mkrewriter_script ${CMAKE_CURRENT_LIST_DIR}/mkrewriter)

add_custom_command(
  OUTPUT rewriter_tables.h
  COMMAND
    ${mkrewriter_script}
    ${CMAKE_CURRENT_LIST_DIR}/rewriter_tables_template.h
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/rewriter_tables.h
  DEPENDS mkrewriter rewriter_tables_template.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT theory_traits.h
  COMMAND
    ${mktheorytraits_script}
    ${CMAKE_CURRENT_LIST_DIR}/theory_traits_template.h
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/theory_traits.h
  DEPENDS mktheorytraits theory_traits_template.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT type_enumerator.cpp
  COMMAND
    ${mktheorytraits_script}
    ${CMAKE_CURRENT_LIST_DIR}/type_enumerator_template.cpp
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/type_enumerator.cpp
  DEPENDS mktheorytraits type_enumerator_template.cpp ${KINDS_FILES}
)

add_custom_target(gen-theory
  DEPENDS
    type_enumerator.cpp
    theory_traits.h
    rewriter_tables.h
)
