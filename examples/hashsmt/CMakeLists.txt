if(Boost_FOUND)
   cvc4_add_example(sha1_inversion
     "sha1_inversion.cpp word.cpp" "hashsmt"
     # arguments to binary (for testing)
     "a" "sha1_inversion.outfile")
endif()

cvc4_add_example(sha1_collision
  "sha1_collision.cpp word.cpp" "hashsmt"
  # arguments to binary (for testing)
  "1" "1" "sha1_collision.outfile")
