libcvc4_add_sources(GENERATED
  rewriter_tables.h
  theory_traits.h
  type_enumerator.cpp
)

file(GLOB kinds_files ${PROJECT_SOURCE_DIR}/src/theory/*/kinds)

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
