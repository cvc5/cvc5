include_directories(${PROJECT_SOURCE_DIR}/src)
include_directories(${PROJECT_SOURCE_DIR}/src/include)
include_directories(${CMAKE_BINARY_DIR}/src)

set(CVC4_EXAMPLES
  simple_vc_cxx
  simple_vc_quant_cxx
  translator
)
set(CVC4_EXAMPLES_API
  bitvectors
  bitvectors-new
  bitvectors_and_arrays
  bitvectors_and_arrays-new
  combination
  combination-new
  datatypes
  datatypes-new
  extract
  extract-new
  helloworld
  helloworld-new
  linear_arith
  linear_arith-new
  sets
  sets-new
  strings
  strings-new
)
set(CVC4_EXAMPLES_HASHSMT
  sha1_collision
  sha1_inversion
)
set(CVC4_EXAMPLES_NRA_TRANSLATE
  normalize
  smt2info
  smt2todreal
  smt2toisat
  smt2tomathematica
  smt2toqepcad
  smt2toredlog
)
set(CVC4_EXAMPLES_SETS_TRANSLATE
  sets2arrays
  sets2axioms
)

add_subdirectory(api)
add_subdirectory(hashsmt)
add_subdirectory(nra-translate)
add_subdirectory(sets-translate)

add_executable(simple_vc_cxx EXCLUDE_FROM_ALL simple_vc_cxx.cpp)
target_link_libraries(simple_vc_cxx cvc4 cvc4parser)

add_executable(simple_vc_quant_cxx EXCLUDE_FROM_ALL simple_vc_quant_cxx.cpp)
target_link_libraries(simple_vc_quant_cxx cvc4 cvc4parser)

add_executable(translator EXCLUDE_FROM_ALL translator.cpp)
target_link_libraries(translator cvc4 cvc4parser)

add_custom_target(examples
  DEPENDS
  ${CVC4_EXAMPLES}
  ${CVC4_EXAMPLES_API}
  ${CVC4_EXAMPLES_HASHSMT}
  ${CVC4_EXAMPLES_NRA_TRANSLATE}
  ${CVC4_EXAMPLES_SETS_TRANSLATE}
)

