set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/examples/hashsmt)

include_directories(.)

add_executable(sha1_inversion EXCLUDE_FROM_ALL sha1_inversion.cpp word.cpp)
target_link_libraries(sha1_inversion cvc4)

add_executable(sha1_collision EXCLUDE_FROM_ALL sha1_collision.cpp word.cpp)
target_link_libraries(sha1_collision cvc4)
