###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Gereon Kremer, Alex Ozdemir
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

# Add unit tests.
cvc5_add_unit_test_black(theory_uf_ho_black theory)
cvc5_add_unit_test_black(regexp_operation_black theory)
cvc5_add_unit_test_black(theory_black theory)
cvc5_add_unit_test_white(evaluator_white theory)
cvc5_add_unit_test_white(logic_info_white theory)
cvc5_add_unit_test_white(sequences_rewriter_white theory)
cvc5_add_unit_test_white(strings_rewriter_white theory)
cvc5_add_unit_test_white(theory_arith_pow2_white theory)
cvc5_add_unit_test_white(theory_arith_white theory)
cvc5_add_unit_test_white(theory_arith_coverings_white theory)
cvc5_add_unit_test_black(theory_arith_rewriter_black theory)
cvc5_add_unit_test_white(theory_bags_normal_form_white theory)
cvc5_add_unit_test_white(theory_bags_rewriter_white theory)
cvc5_add_unit_test_white(theory_bags_type_rules_white theory)
cvc5_add_unit_test_black(theory_bv_black theory)
cvc5_add_unit_test_white(theory_bv_opt_white theory)
cvc5_add_unit_test_white(theory_bv_int_blaster_white theory)
cvc5_add_unit_test_white(theory_engine_white theory)
cvc5_add_unit_test_black(theory_ff_multi_roots_black theory)
cvc5_add_unit_test_black(theory_ff_uni_roots_black theory)
cvc5_add_unit_test_black(theory_ff_core_black theory)
cvc5_add_unit_test_white(theory_int_opt_white theory)
cvc5_add_unit_test_white(theory_opt_multigoal_white theory)
cvc5_add_unit_test_white(theory_quantifiers_bv_instantiator_white theory)
cvc5_add_unit_test_white(theory_quantifiers_bv_inverter_white theory)
cvc5_add_unit_test_white(theory_sets_rewriter_white theory)
cvc5_add_unit_test_white(theory_sets_type_enumerator_white theory)
cvc5_add_unit_test_white(theory_sets_type_rules_white theory)
cvc5_add_unit_test_white(theory_strings_skolem_cache_black theory)
cvc5_add_unit_test_white(theory_strings_utils_white theory)
cvc5_add_unit_test_white(theory_strings_word_white theory)
cvc5_add_unit_test_white(theory_white theory)
cvc5_add_unit_test_white(type_enumerator_white theory)
cvc5_add_unit_test_white(arith_poly_white theory)
