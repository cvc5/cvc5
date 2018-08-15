set(smtutil_src_files
  boolean_simplification.cpp
  boolean_simplification.h
  lemma_channels.cpp
  lemma_channels.h
  lemma_input_channel.h
  lemma_output_channel.h
  nary_builder.cpp
  nary_builder.h
  node_visitor.h
)

add_library(smtutil ${smtutil_src_files})
target_compile_definitions(smtutil PRIVATE -D__BUILDING_CVC4LIB)
target_link_libraries(smtutil expr)
