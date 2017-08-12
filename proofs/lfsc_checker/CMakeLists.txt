cmake_minimum_required (VERSION 2.8.9)

macro(add_cxx_flag flag)
  message(STATUS "Configure with flag '${flag}'")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endmacro()

project (lfsc_checker)

set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

find_package(GMP REQUIRED)
set(LIBRARIES ${LIBRARIES} ${GMP_LIBRARIES})
include_directories(${GMP_INCLUDE_DIR})

if(NOT CMAKE_BUILD_TYPE)
  message(STATUS "Defaulting to release build.")
  set(CMAKE_BUILD_TYPE Release CACHE STRING "" FORCE)
endif()

add_cxx_flag("-Wall")
add_cxx_flag("-Wno-deprecated")

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  add_cxx_flag("-g")
  message(STATUS "Configured debug build.")
elseif(CMAKE_BUILD_TYPE STREQUAL "Release")
  message(STATUS "Configured release build.")
else()
  message(FATAL_ERROR "Invalid build type '${CMAKE_BUILD_TYPE}'")
endif()

include_directories(src)
add_subdirectory(src)

