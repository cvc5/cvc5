###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

set(CVC5_EXAMPLES_API_C
  bags
  bitvectors
  bitvectors_and_arrays
  combination
  datatypes
  extract
  floating_point_arith
  helloworld
  linear_arith
  quickstart
  relations
  sequences
  sets
  strings
  transcendentals
  parser
  parser_sym_manager
  uf
)

# Add example target and create test to run example with ctest.
#
# > name: The name of the example
# > src_files: The list of source files passed as string "src1 src2 ..."
#              (alternative: "src1;src2;...").  If empty, <name>.c is assumed.
# > ARGN: Any additional arguments passed to the macro are interpreted as
#         as arguments to the test executable.
macro(cvc5_add_c_example name src_files)
  # The build target is created without the path prefix (not supported),
  # e.g., for '<output_dir>/myexample.c'
  #   we create build target 'myexample'
  #   and build it with 'make myexample'.
  # As a consequence, all build target names must be globally unique.
  if("${src_files}" STREQUAL "")
    set(src_files_list ${name}.c)
  else()
    string(REPLACE " " ";" src_files_list "${src_files}")
  endif()
  set(test_name c_${name})
  add_executable(${test_name} ${src_files_list})
  target_link_libraries(${test_name} cvc5::cvc5 cvc5::cvc5parser)

  # The test target is prefixed with the path,
  # e.g., for '<output_dir>/myexample.cpp'
  #   we create test target '<output_dir>/myexample'
  #   and run it with 'ctest -R "<output_dir>/myexample"'.
  set(example_bin_dir ${EXAMPLES_BIN_DIR}/api/c)
  set_target_properties(${test_name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${example_bin_dir})
  add_test(${example_test} ${example_bin_dir}/${test_name} ${ARGN})
endmacro()

foreach(example ${CVC5_EXAMPLES_API_C})
  cvc5_add_c_example(${example} "")
endforeach()

if(CVC5_USE_COCOA)
  cvc5_add_c_example(finite_field "")
endif()

set(SYGUS_EXAMPLES_API_C
  sygus-fun
  sygus-inv
)

foreach(example ${SYGUS_EXAMPLES_API_C})
  cvc5_add_c_example(${example} "${example}.c utils.h utils.c")
endforeach()
