cmake_minimum_required (VERSION 2.8.9)

macro(add_cxx_flag flag)
  message(STATUS "Configure with flag '${flag}'")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endmacro()

project (cvc4)

set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

# TODO: cln
find_package(GMP REQUIRED)
set(LIBRARIES ${LIBRARIES} ${GMP_LIBRARIES})
include_directories(${GMP_INCLUDE_DIR})

add_subdirectory(src)
add_subdirectory(test)
#TODO only if with-lfsc
#add_subdirectory(proofs/signatures)

#TODO make dist (subdir: examples)

