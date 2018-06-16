file(GLOB kinds_files ${PROJECT_SOURCE_DIR}/src/theory/*/kinds)

set(mktheorytraits_script ${CMAKE_CURRENT_LIST_DIR}/mktheorytraits)
set(mkrewriter_script ${CMAKE_CURRENT_LIST_DIR}/mkrewriter)

add_custom_command(
    COMMAND
      ${mkrewriter_script}
      ${CMAKE_CURRENT_LIST_DIR}/rewriter_tables_template.h
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/rewriter_tables.h
    DEPENDS mkrewriter rewriter_tables_template.h
    OUTPUT rewriter_tables.h
      COMMENT "Generating rewriter_tables.h."
)

add_custom_command(
    COMMAND
      ${mktheorytraits_script}
      ${CMAKE_CURRENT_LIST_DIR}/theory_traits_template.h
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/theory_traits.h
    DEPENDS mktheorytraits theory_traits_template.h
    OUTPUT theory_traits.h
    COMMENT "Generating theory_traits.h."
)

add_custom_command(
    COMMAND
      ${mktheorytraits_script}
      ${CMAKE_CURRENT_LIST_DIR}/type_enumerator_template.cpp
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/type_enumerator.cpp
    DEPENDS mktheorytraits type_enumerator_template.cpp
    OUTPUT type_enumerator.cpp
    COMMENT "Generating type_enumerator.cpp."
)
