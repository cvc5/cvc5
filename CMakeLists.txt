cmake_minimum_required (VERSION 3.0.1)

#-----------------------------------------------------------------------------#

project (cvc4)

#-----------------------------------------------------------------------------#

set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 11)

#-----------------------------------------------------------------------------#

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

macro(add_c_flag flag)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${flag}")
endmacro()

macro(add_check_c_flag flag)
  check_c_compiler_flag("${flag}" HAVE_FLAG_${flag})
  if(HAVE_FLAG_${flag})
    add_c_flag(${flag})
  endif()
endmacro()

macro(add_cxx_flag flag)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endmacro()

macro(add_check_cxx_flag flag)
  check_cxx_compiler_flag("${flag}" HAVE_FLAG_${flag})
  if(HAVE_FLAG_${flag})
    add_cxx_flag(${flag})
  endif()
endmacro()

macro(add_c_cxx_flag flag)
  add_c_flag(${flag})
  add_cxx_flag(${flag})
  message(STATUS "Configure with flag '${flag}'")
endmacro()

macro(add_check_c_cxx_flag flag)
  add_check_c_flag(${flag})
  add_check_cxx_flag(${flag})
  message(STATUS "Configure with flag '${flag}'")
endmacro()

#-----------------------------------------------------------------------------#

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
message(STATUS "LIB directory is '${CMAKE_BINARY_DIR}/lib'")
message(STATUS "BIN directory is '${CMAKE_BINARY_DIR}/bin'")

#-----------------------------------------------------------------------------#

set(build_types Debug Production)
if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "No build type set, options are: ${build_types}")
    set(CMAKE_BUILD_TYPE Production CACHE STRING "Options are: ${build_types}" FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Building ${CMAKE_BUILD_TYPE} build")

#-----------------------------------------------------------------------------#

find_package(PythonInterp REQUIRED)

find_package(GMP REQUIRED)
message(STATUS "Found GMP headers: ${GMP_INCLUDE_DIR}")
set(LIBRARIES ${LIBRARIES} ${GMP_LIBRARIES})
include_directories(${GMP_INCLUDE_DIR})

find_package(ANTLR REQUIRED)
message(STATUS "Found ANTLR headers: ${ANTLR_INCLUDE_DIR}")
set(LIBRARIES ${LIBRARIES} ${ANTLR_LIBRARIES})
include_directories(${ANTLR_INCLUDE_DIR})

#-----------------------------------------------------------------------------#

add_check_c_flag("-fexceptions")
add_check_c_cxx_flag("-Wno-deprecated")

#-----------------------------------------------------------------------------#

set(VERSION "1.6.0-prerelease")
string(TIMESTAMP MAN_DATE "%Y-%m-%d")

#-----------------------------------------------------------------------------#

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
git_local_changes(GIT_IS_DIRTY)
if(${GIT_IS_DIRTY} STREQUAL "DIRTY")
  set(GIT_IS_DIRTY "true")
else()
  set(GIT_IS_DIRTY "false")
endif()

execute_process(
  COMMAND "${GIT_EXECUTABLE}" rev-parse --abbrev-ref HEAD
  OUTPUT_VARIABLE GIT_BRANCH
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

#-----------------------------------------------------------------------------#

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/src/git_versioninfo.cpp.in
  ${CMAKE_CURRENT_BINARY_DIR}/src/git_versioninfo.cpp)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/doc/SmtEngine.3cvc_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/doc/SmtEngine.3cvc_template)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/doc/cvc4.1_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/doc/cvc4.1_template)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/doc/cvc4.5.in
  ${CMAKE_CURRENT_BINARY_DIR}/doc/cvc4.5)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/doc/libcvc4.3.in
  ${CMAKE_CURRENT_BINARY_DIR}/doc/libcvc4.3)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/doc/libcvc4compat.3.in
  ${CMAKE_CURRENT_BINARY_DIR}/doc/libcvc4compat.3)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/doc/libcvc4parser.3.in
  ${CMAKE_CURRENT_BINARY_DIR}/doc/libcvc4parser.3)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/doc/options.3cvc_template.in
  ${CMAKE_CURRENT_BINARY_DIR}/doc/options.3cvc_template)

#-----------------------------------------------------------------------------#

add_subdirectory(src/base)
add_subdirectory(src/expr)
add_subdirectory(src/options)
add_subdirectory(src/parser)
add_subdirectory(src/theory)
add_subdirectory(proofs/signatures)
include_directories(src ${CMAKE_CURRENT_BINARY_DIR}/src)
