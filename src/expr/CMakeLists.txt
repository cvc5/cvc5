file(GLOB kinds_files ${PROJECT_SOURCE_DIR}/src/theory/*/kinds)

set(mkkind_script ${CMAKE_CURRENT_LIST_DIR}/mkkind)
set(mkmetakind_script ${CMAKE_CURRENT_LIST_DIR}/mkmetakind)
set(mkexpr_script ${CMAKE_CURRENT_LIST_DIR}/mkexpr)

add_custom_command(
    COMMAND
      ${mkkind_script}
      ${CMAKE_CURRENT_LIST_DIR}/kind_template.h
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/kind.h
    DEPENDS mkkind kind_template.h
    OUTPUT kind.h
    COMMENT "Generating kind.h."
)

add_custom_command(
    COMMAND
      ${mkkind_script}
      ${CMAKE_CURRENT_LIST_DIR}/kind_template.cpp
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/kind.cpp
    DEPENDS mkkind kind_template.cpp kind.h
    OUTPUT kind.cpp
    COMMENT "Generating kind.cpp."
)

add_custom_command(
    COMMAND
      ${mkkind_script}
      ${CMAKE_CURRENT_LIST_DIR}/type_properties_template.h
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/type_properties.h
    DEPENDS mkkind type_properties_template.h
    OUTPUT type_properties.h
    COMMENT "Generating type_properties.h."
)

add_custom_command(
    COMMAND
      ${mkmetakind_script}
      ${CMAKE_CURRENT_LIST_DIR}/metakind_template.h
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/metakind.h
    DEPENDS mkmetakind metakind_template.h
    OUTPUT metakind.h
    COMMENT "Generating metakind.h."
)

add_custom_command(
    COMMAND
      ${mkmetakind_script}
      ${CMAKE_CURRENT_LIST_DIR}/metakind_template.cpp
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/metakind.cpp
    DEPENDS mkmetakind metakind_template.cpp metakind.h
    OUTPUT metakind.cpp
    COMMENT "Generating metakind.cpp."
)

add_custom_command(
    COMMAND
      ${mkexpr_script}
      ${CMAKE_CURRENT_LIST_DIR}/expr_template.h
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/expr.h
    DEPENDS mkexpr expr_template.h kind.h
    OUTPUT expr.h
    COMMENT "Generating expr.h."
)

add_custom_command(
    COMMAND
      ${mkexpr_script}
      ${CMAKE_CURRENT_LIST_DIR}/expr_template.cpp
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/expr.cpp
    DEPENDS mkexpr expr_template.cpp expr.h
    OUTPUT expr.cpp
    COMMENT "Generating expr.cpp."
)

add_custom_command(
    COMMAND
      ${mkexpr_script}
      ${CMAKE_CURRENT_LIST_DIR}/expr_manager_template.h
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/expr_manager.h
    DEPENDS mkexpr expr_manager_template.h expr.h
    OUTPUT expr_manager.h
    COMMENT "Generating expr_manager.h."
)

add_custom_command(
    COMMAND
      ${mkexpr_script}
      ${CMAKE_CURRENT_LIST_DIR}/expr_manager_template.cpp
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/expr_manager.cpp
    DEPENDS mkexpr expr_manager_template.cpp expr_manager.h
    OUTPUT expr_manager.cpp
    COMMENT "Generating expr_manager.cpp."
)

add_custom_command(
    COMMAND
      ${mkexpr_script}
      ${CMAKE_CURRENT_LIST_DIR}/type_checker_template.cpp
      ${kinds_files}
      > ${CMAKE_CURRENT_BINARY_DIR}/type_checker.cpp
    DEPENDS mkexpr type_checker_template.cpp
    OUTPUT type_checker.cpp
    COMMENT "Generating type_checker.cpp."
)
