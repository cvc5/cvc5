include_directories(.)

set(EXAMPLES_HASHSMT_BIN_DIR ${EXAMPLES_BIN_DIR}/hashsmt) 

add_executable(sha1_inversion EXCLUDE_FROM_ALL sha1_inversion.cpp word.cpp)
target_link_libraries(sha1_inversion cvc4)

add_executable(sha1_collision EXCLUDE_FROM_ALL sha1_collision.cpp word.cpp)
target_link_libraries(sha1_collision cvc4)

set_target_properties(sha1_inversion sha1_collision
  PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${EXAMPLES_HASHSMT_BIN_DIR})
