###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

configure_file(rational.h.in rational.h)
configure_file(integer.h.in integer.h)
configure_file(real_algebraic_number.h.in real_algebraic_number.h)

libcvc5_add_sources(
  bin_heap.h
  bitvector.cpp
  bitvector.h
  cocoa_globals.cpp
  cocoa_globals.h
  bool.h
  cardinality.cpp
  cardinality.h
  cardinality_class.cpp
  cardinality_class.h
  cocoa_globals.cpp
  cocoa_globals.h
  dense_map.h
  didyoumean.cpp
  didyoumean.h
  divisible.cpp
  divisible.h
  finite_field_value.cpp
  finite_field_value.h
  floatingpoint.cpp
  floatingpoint.h
  floatingpoint_size.cpp
  floatingpoint_size.h
  floatingpoint_literal_symfpu.cpp
  floatingpoint_literal_symfpu_traits.cpp
  gmp_util.h
  hash.h
  iand.h
  index.cpp
  index.h
  ostream_util.cpp
  ostream_util.h
  poly_util.cpp
  poly_util.h
  random.cpp
  random.h
  resource_manager.cpp
  resource_manager.h
  result.cpp
  result.h
  real_algebraic_number_poly_imp.cpp
  real_algebraic_number_poly_imp.h
  regexp.cpp
  regexp.h
  roundingmode.cpp
  roundingmode.h
  safe_print.cpp
  safe_print.h
  sampler.cpp
  sampler.h
  sexpr.cpp
  sexpr.h
  smt2_quote_string.cpp
  smt2_quote_string.h
  statistics_public.cpp
  statistics_public.h
  statistics_registry.cpp
  statistics_registry.h
  statistics_stats.cpp
  statistics_stats.h
  statistics_value.cpp
  statistics_value.h
  string.cpp
  string.h
  synth_result.cpp
  synth_result.h
  uninterpreted_sort_value.cpp
  uninterpreted_sort_value.h
  utility.cpp
  utility.h
)

if(CVC5_USE_CLN_IMP)
  libcvc5_add_sources(rational_cln_imp.cpp integer_cln_imp.cpp)
endif()

if(CVC5_USE_GMP_IMP)
  libcvc5_add_sources(rational_gmp_imp.cpp integer_gmp_imp.cpp)
endif()
