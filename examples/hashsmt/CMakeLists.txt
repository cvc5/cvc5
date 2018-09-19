include_directories(.)

set(EXAMPLES_HASHSMT_LINK_LIBS cvc4)

if(Boost_FOUND)
   cvc4_add_example(sha1_inversion
     "sha1_inversion.cpp word.cpp" "${EXAMPLES_HASHSMT_LINK_LIBS}" "hashsmt"
     "a" "sha1_inversion.outfile")  # arguments to binary (for testing)
endif()

cvc4_add_example(sha1_collision
  "sha1_collision.cpp word.cpp" "${EXAMPLES_HASHSMT_LINK_LIBS}" "hashsmt"
  "1" "1" "sha1_collision.outfile")  # arguments to binary (for testing)
