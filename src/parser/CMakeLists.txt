set(cvc4parser_src_files
  antlr_input.cpp
  antlr_input.h
  antlr_input_imports.cpp
  antlr_line_buffered_input.cpp
  antlr_line_buffered_input.h
  antlr_tracing.h
  antlr_undefines.h
  bounded_token_buffer.cpp
  bounded_token_buffer.h
  bounded_token_factory.cpp
  bounded_token_factory.h
  input.cpp
  input.h
  line_buffer.cpp
  line_buffer.h
  memory_mapped_input_buffer.cpp
  memory_mapped_input_buffer.h
  parser.cpp
  parser.h
  parser_builder.cpp
  parser_builder.h
  parser_exception.h
)

add_library(cvc4parser ${cvc4parser_src_files})

set_target_properties(cvc4parser
  PROPERTIES
    VERSION ${CVC4_VERSION}
    SOVERSION ${CVC4_SOVERSION}
)

target_compile_definitions(cvc4parser PRIVATE -D__BUILDING_CVC4PARSERLIB)
target_link_libraries(cvc4parser parsercvc parsersmt1 parsersmt2 parsertptp cvc4)
target_link_libraries(cvc4parser ${ANTLR_LIBRARIES})

# ANTLR includes required for all subdirectories
include_directories(${ANTLR_INCLUDE_DIR})
add_subdirectory(cvc)
add_subdirectory(smt1)
add_subdirectory(smt2)
add_subdirectory(tptp)
