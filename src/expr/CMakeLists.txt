libcvc4_add_sources(
  array.h
  array_store_all.cpp
  array_store_all.h
  ascription_type.h
  attribute.h
  attribute.cpp
  attribute_internals.h
  attribute_unique_id.h
  emptyset.cpp
  emptyset.h
  expr_iomanip.cpp
  expr_iomanip.h
  expr_manager_scope.h
  expr_sequence.cpp
  expr_sequence.h
  kind_map.h
  lazy_proof.cpp
  lazy_proof.h
  match_trie.cpp
  match_trie.h
  node.cpp
  node.h
  node_algorithm.cpp
  node_algorithm.h
  node_builder.h
  node_manager.cpp
  node_manager.h
  node_manager_attributes.h
  node_manager_listeners.cpp
  node_manager_listeners.h
  node_self_iterator.h
  node_trie.cpp
  node_trie.h
  node_traversal.cpp
  node_traversal.h
  node_value.cpp
  node_value.h
  sequence.cpp
  sequence.h
  node_visitor.h
  proof.cpp
  proof.h
  proof_checker.cpp
  proof_checker.h
  proof_generator.cpp
  proof_generator.h
  proof_node.cpp
  proof_node.h
  proof_node_to_sexpr.cpp
  proof_node_to_sexpr.h
  proof_node_manager.cpp
  proof_node_manager.h
  proof_rule.cpp
  proof_rule.h
  proof_step_buffer.cpp
  proof_step_buffer.h
  skolem_manager.cpp
  skolem_manager.h
  symbol_table.cpp
  symbol_table.h
  term_canonize.cpp
  term_canonize.h
  type.cpp
  type.h
  type_checker.h
  type_matcher.cpp
  type_matcher.h
  type_node.cpp
  type_node.h
  variable_type_map.h
  datatype.h
  datatype.cpp
  dtype.h
  dtype.cpp
  dtype_cons.h
  dtype_cons.cpp
  dtype_selector.h
  dtype_selector.cpp
  record.cpp
  record.h
  sequence.cpp
  sequence.h
  sygus_datatype.cpp
  sygus_datatype.h
  uninterpreted_constant.cpp
  uninterpreted_constant.h
)

libcvc4_add_sources(GENERATED
  kind.cpp
  kind.h
  metakind.cpp
  metakind.h
  expr.cpp
  expr.h
  expr_manager.cpp
  expr_manager.h
  type_checker.cpp
  type_properties.h
)

#
# Generate code for kinds.
#

set(mkkind_script ${CMAKE_CURRENT_LIST_DIR}/mkkind)
set(mkmetakind_script ${CMAKE_CURRENT_LIST_DIR}/mkmetakind)
set(mkexpr_script ${CMAKE_CURRENT_LIST_DIR}/mkexpr)

add_custom_command(
  OUTPUT kind.h
  COMMAND
    ${mkkind_script}
    ${CMAKE_CURRENT_LIST_DIR}/kind_template.h
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/kind.h
  DEPENDS mkkind kind_template.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT kind.cpp
  COMMAND
    ${mkkind_script}
    ${CMAKE_CURRENT_LIST_DIR}/kind_template.cpp
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/kind.cpp
  DEPENDS mkkind kind_template.cpp kind.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT type_properties.h
  COMMAND
    ${mkkind_script}
    ${CMAKE_CURRENT_LIST_DIR}/type_properties_template.h
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/type_properties.h
  DEPENDS mkkind type_properties_template.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT metakind.h
  COMMAND
    ${mkmetakind_script}
    ${CMAKE_CURRENT_LIST_DIR}/metakind_template.h
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/metakind.h
  DEPENDS mkmetakind metakind_template.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT metakind.cpp
  COMMAND
    ${mkmetakind_script}
    ${CMAKE_CURRENT_LIST_DIR}/metakind_template.cpp
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/metakind.cpp
  DEPENDS mkmetakind metakind_template.cpp metakind.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT expr.h
  COMMAND
    ${mkexpr_script}
    ${CMAKE_CURRENT_LIST_DIR}/expr_template.h
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/expr.h
  DEPENDS mkexpr expr_template.h kind.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT expr.cpp
  COMMAND
    ${mkexpr_script}
    ${CMAKE_CURRENT_LIST_DIR}/expr_template.cpp
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/expr.cpp
  DEPENDS mkexpr expr_template.cpp expr.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT expr_manager.h
  COMMAND
    ${mkexpr_script}
    ${CMAKE_CURRENT_LIST_DIR}/expr_manager_template.h
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/expr_manager.h
  DEPENDS mkexpr expr_manager_template.h expr.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT expr_manager.cpp
  COMMAND
    ${mkexpr_script}
    ${CMAKE_CURRENT_LIST_DIR}/expr_manager_template.cpp
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/expr_manager.cpp
  DEPENDS mkexpr expr_manager_template.cpp expr_manager.h ${KINDS_FILES}
)

add_custom_command(
  OUTPUT type_checker.cpp
  COMMAND
    ${mkexpr_script}
    ${CMAKE_CURRENT_LIST_DIR}/type_checker_template.cpp
    ${KINDS_FILES}
    > ${CMAKE_CURRENT_BINARY_DIR}/type_checker.cpp
  DEPENDS mkexpr type_checker_template.cpp ${KINDS_FILES}
)

add_custom_target(gen-expr
  DEPENDS
    kind.cpp
    kind.h
    metakind.cpp
    metakind.h
    expr.cpp
    expr.h
    expr_manager.cpp
    expr_manager.h
    type_checker.cpp
    type_properties.h
)
