configure_file(floatingpoint.h.in floatingpoint.h)
configure_file(rational.h.in rational.h)
configure_file(integer.h.in integer.h)

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
  floatingpoint.cpp
  gmp_util.h
  hash.h
  index.cpp
  index.h
  maybe.h
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

set(GMP_HOME ${GMP_DIR})
find_package(GMP REQUIRED)

add_library(util ${util_src_files})
target_compile_definitions(util PRIVATE -D__BUILDING_CVC4LIB)
target_link_libraries(util options ${GMP_LIBRARIES})
target_include_directories(util PUBLIC ${GMP_INCLUDE_DIR})
