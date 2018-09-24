libcvc4_add_sources(GENERATED
  rewriter_tables.h
  theory_traits.h
  type_enumerator.cpp
)

# IMPORTANT: The order of the theories is important. It affects the order in
# which theory solvers are called/initialized internally. For example, strings
# depends on arith, quantifiers needs to come as the very last.
# See issue https://github.com/CVC4/CVC4/issues/2517 for more details.
set(kinds_files
  ${PROJECT_SOURCE_DIR}/src/theory/builtin/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/booleans/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/uf/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/arith/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/bv/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/fp/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/arrays/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/datatypes/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/sep/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/sets/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/strings/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/quantifiers/kinds
  ${PROJECT_SOURCE_DIR}/src/theory/idl/kinds)

set(mktheorytraits_script ${CMAKE_CURRENT_LIST_DIR}/mktheorytraits)
set(mkrewriter_script ${CMAKE_CURRENT_LIST_DIR}/mkrewriter)

add_custom_command(
  OUTPUT rewriter_tables.h
  COMMAND
    ${mkrewriter_script}
    ${CMAKE_CURRENT_LIST_DIR}/rewriter_tables_template.h
    ${kinds_files}
    > ${CMAKE_CURRENT_BINARY_DIR}/rewriter_tables.h
  DEPENDS mkrewriter rewriter_tables_template.h
)

add_custom_command(
  OUTPUT theory_traits.h
  COMMAND
    ${mktheorytraits_script}
    ${CMAKE_CURRENT_LIST_DIR}/theory_traits_template.h
    ${kinds_files}
    > ${CMAKE_CURRENT_BINARY_DIR}/theory_traits.h
  DEPENDS mktheorytraits theory_traits_template.h
)

add_custom_command(
  OUTPUT type_enumerator.cpp
  COMMAND
    ${mktheorytraits_script}
    ${CMAKE_CURRENT_LIST_DIR}/type_enumerator_template.cpp
    ${kinds_files}
    > ${CMAKE_CURRENT_BINARY_DIR}/type_enumerator.cpp
  DEPENDS mktheorytraits type_enumerator_template.cpp
)

add_custom_target(gen-theory
  DEPENDS
    type_enumerator.cpp
    theory_traits.h
    rewriter_tables.h
)
