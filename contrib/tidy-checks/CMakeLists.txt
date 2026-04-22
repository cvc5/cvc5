###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A CMake configuration for building clang-tidy checks for cvc5.
##

cmake_minimum_required(VERSION 3.16)
project(Cvc5TidyChecks LANGUAGES C CXX)

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

include_directories(${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

add_library(Cvc5TidyChecks MODULE
    Cvc5TidyModule.cpp
    NodeIdDeterminismCheck.cpp
)

set_target_properties(Cvc5TidyChecks PROPERTIES
    CXX_STANDARD 17
    PREFIX "")

target_link_libraries(Cvc5TidyChecks PRIVATE
    clangTidy
    clangTidyUtils
    clangTooling
    clangAST
    clangBasic
)
