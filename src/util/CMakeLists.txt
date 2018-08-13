configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/floatingpoint.h.in
  ${CMAKE_CURRENT_BINARY_DIR}/floatingpoint.h)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/rational.h.in
  ${CMAKE_CURRENT_BINARY_DIR}/rational.h)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/integer.h.in
  ${CMAKE_CURRENT_BINARY_DIR}/integer.h)

set(util_src_files
  abstract_value.cpp
  abstract_value.h
  bin_heap.h
  bitvector.cpp
  bitvector.h
  bool.h
  cardinality.cpp
  cardinality.h
  channel.h
  debug.h
  dense_map.h
  divisible.cpp
  divisible.h
  dynamic_array.h
  floatingpoint.cpp
  gmp_util.h
  hash.h
  index.cpp
  index.h
  maybe.h
  ntuple.h
  ostream_util.cpp
  ostream_util.h
  proof.h
  random.cpp
  random.h
  regexp.cpp
  regexp.h
  resource_manager.cpp
  resource_manager.h
  result.cpp
  result.h
  safe_print.cpp
  safe_print.h
  sampler.cpp
  sampler.h
  sexpr.cpp
  sexpr.h
  smt2_quote_string.cpp
  smt2_quote_string.h
  statistics.cpp
  statistics.h
  statistics_registry.cpp
  statistics_registry.h
  tuple.h
  unsafe_interrupt_exception.h
  utility.h
)

if(CVC4_USE_CLN_IMP)
  list(APPEND util_src_files rational_cln_imp.cpp integer_cln_imp.cpp)
endif()

if(CVC4_USE_GMP_IMP)
  list(APPEND util_src_files rational_gmp_imp.cpp integer_gmp_imp.cpp)
endif()

add_library(util SHARED ${util_src_files})
set_target_properties(util PROPERTIES COMPILE_DEFINITIONS __BUILDING_CVC4LIB)
add_dependencies(util options)
