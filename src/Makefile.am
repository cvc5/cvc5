# LIBCVC4_VERSION (-version-info) is in the form current:revision:age
#
# current -
#   increment if interfaces have been added, removed or changed
# revision -
#   increment if source code has changed
#   set to zero if current is incremented
# age -
#   increment if interfaces have been added
#   set to zero if interfaces have been removed
#   or changed
#
LIBCVC4_VERSION = @CVC4_LIBRARY_VERSION@

AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-D __STDC_LIMIT_MACROS \
	-D __STDC_FORMAT_MACROS \
	-I@builddir@ -I@srcdir@/include -I@srcdir@
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas -Wno-parentheses $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = lib base options util expr smt_util prop/minisat prop/bvminisat . parser compat bindings main
# The THEORIES list has been moved to Makefile.theories
include @top_srcdir@/src/Makefile.theories

lib_LTLIBRARIES = libcvc4.la

libcvc4_la_LDFLAGS = \
	-no-undefined \
	-version-info $(LIBCVC4_VERSION)

# This "tricks" automake into linking us as a C++ library (rather than
# as a C library, which messes up exception handling support)
nodist_EXTRA_libcvc4_la_SOURCES = dummy.cpp
libcvc4_la_SOURCES = \
	git_versioninfo.cpp \
	svn_versioninfo.cpp \
	context/backtrackable.h \
	context/cddense_set.h \
	context/cdhashmap.h \
	context/cdhashmap_forward.h \
	context/cdhashset.h \
	context/cdhashset_forward.h \
	context/cdinsert_hashmap.h \
	context/cdinsert_hashmap_forward.h \
	context/cdlist.h \
	context/cdlist_forward.h \
	context/cdmaybe.h \
	context/cdo.h \
	context/cdqueue.h \
	context/cdtrail_hashmap.h \
	context/cdtrail_hashmap_forward.h \
	context/cdtrail_queue.h \
	context/cdvector.h \
	context/context.cpp \
	context/context.h \
	context/context_mm.cpp \
	context/context_mm.h \
	decision/decision_attributes.h \
	decision/decision_engine.cpp \
	decision/decision_engine.h \
	decision/decision_strategy.h \
	decision/justification_heuristic.cpp \
	decision/justification_heuristic.h \
	preprocessing/preprocessing_pass.cpp \
	preprocessing/preprocessing_pass.h \
	preprocessing/preprocessing_pass_context.cpp \
	preprocessing/preprocessing_pass_context.h \
	preprocessing/preprocessing_pass_registry.cpp \
	preprocessing/preprocessing_pass_registry.h \
	printer/dagification_visitor.cpp \
	printer/dagification_visitor.h \
	printer/printer.cpp \
	printer/printer.h \
	printer/sygus_print_callback.cpp \
	printer/sygus_print_callback.h \
	printer/ast/ast_printer.cpp \
	printer/ast/ast_printer.h \
	printer/cvc/cvc_printer.cpp \
	printer/cvc/cvc_printer.h \
	printer/smt1/smt1_printer.cpp \
	printer/smt1/smt1_printer.h \
	printer/smt2/smt2_printer.cpp \
	printer/smt2/smt2_printer.h \
	printer/tptp/tptp_printer.cpp \
	printer/tptp/tptp_printer.h \
	proof/arith_proof.cpp \
	proof/arith_proof.h \
	proof/array_proof.cpp \
	proof/array_proof.h \
	proof/bitvector_proof.cpp \
	proof/bitvector_proof.h \
	proof/clause_id.h \
	proof/cnf_proof.cpp \
	proof/cnf_proof.h \
	proof/lemma_proof.cpp \
	proof/lemma_proof.h \
	proof/proof.h \
	proof/proof_manager.cpp \
	proof/proof_manager.h \
	proof/proof_output_channel.cpp \
	proof/proof_output_channel.h \
	proof/proof_utils.cpp \
	proof/proof_utils.h \
	proof/sat_proof.h \
	proof/sat_proof_implementation.h \
	proof/simplify_boolean_node.cpp \
	proof/simplify_boolean_node.h \
	proof/skolemization_manager.cpp \
	proof/skolemization_manager.h \
	proof/theory_proof.cpp \
	proof/theory_proof.h \
	proof/uf_proof.cpp \
	proof/uf_proof.h \
	proof/unsat_core.cpp \
	proof/unsat_core.h \
	prop/cnf_stream.cpp \
	prop/cnf_stream.h \
	prop/cryptominisat.cpp \
	prop/cryptominisat.h \
	prop/prop_engine.cpp \
	prop/prop_engine.h \
	prop/registrar.h \
	prop/sat_solver.h \
	prop/sat_solver_factory.cpp \
	prop/sat_solver_factory.h \
	prop/sat_solver_types.h \
	prop/theory_proxy.cpp \
	prop/theory_proxy.h \
	smt/command.cpp \
	smt/command.h \
	smt/command_list.cpp \
	smt/command_list.h \
	smt/dump.cpp \
	smt/dump.h \
	smt/logic_exception.h \
	smt/logic_request.cpp \
	smt/logic_request.h \
	smt/managed_ostreams.cpp \
	smt/managed_ostreams.h \
	smt/model.cpp \
	smt/model.h \
	smt/smt_engine.cpp \
	smt/smt_engine.h \
	smt/smt_engine_check_proof.cpp \
	smt/smt_engine_scope.cpp \
	smt/smt_engine_scope.h \
	smt/smt_statistics_registry.cpp \
	smt/smt_statistics_registry.h \
	smt/term_formula_removal.cpp \
	smt/term_formula_removal.h \
	smt/update_ostream.h \
	theory/assertion.cpp \
	theory/assertion.h \
	theory/atom_requests.cpp \
	theory/atom_requests.h \
	theory/care_graph.h \
	theory/interrupted.h \
	theory/ite_utilities.cpp \
	theory/ite_utilities.h \
	theory/logic_info.cpp \
	theory/logic_info.h \
	theory/output_channel.h \
	theory/quantifiers_engine.cpp \
	theory/quantifiers_engine.h \
	theory/rep_set.cpp \
	theory/rep_set.h \
	theory/rewriter.cpp \
	theory/rewriter.h \
	theory/rewriter_attributes.h \
	theory/shared_terms_database.cpp \
	theory/shared_terms_database.h \
	theory/sort_inference.cpp \
	theory/sort_inference.h \
	theory/substitutions.cpp \
	theory/substitutions.h \
	theory/term_registration_visitor.cpp \
	theory/term_registration_visitor.h \
	theory/theory.cpp \
	theory/theory.h \
	theory/theory_engine.cpp \
	theory/theory_engine.h \
	theory/theory_model.cpp \
	theory/theory_model.h \
	theory/theory_model_builder.cpp \
	theory/theory_model_builder.h \
	theory/theory_registrar.h \
	theory/theory_test_utils.h \
	theory/type_enumerator.h \
	theory/type_set.cpp \
	theory/type_set.h \
	theory/unconstrained_simplifier.cpp \
	theory/unconstrained_simplifier.h \
	theory/valuation.cpp \
	theory/valuation.h \
	theory/arith/approx_simplex.cpp \
	theory/arith/approx_simplex.h \
	theory/arith/arith_ite_utils.cpp \
	theory/arith/arith_ite_utils.h \
	theory/arith/arith_msum.cpp \
	theory/arith/arith_msum.h \
	theory/arith/arith_rewriter.cpp \
	theory/arith/arith_rewriter.h \
	theory/arith/arith_static_learner.cpp \
	theory/arith/arith_static_learner.h \
	theory/arith/arith_utilities.h \
	theory/arith/arithvar.cpp \
	theory/arith/arithvar.h \
	theory/arith/attempt_solution_simplex.cpp \
	theory/arith/attempt_solution_simplex.h \
	theory/arith/bound_counts.h \
	theory/arith/callbacks.cpp \
	theory/arith/callbacks.h \
	theory/arith/congruence_manager.cpp \
	theory/arith/congruence_manager.h \
	theory/arith/constraint.cpp \
	theory/arith/constraint.h \
	theory/arith/constraint_forward.h \
	theory/arith/cut_log.cpp \
	theory/arith/cut_log.h \
	theory/arith/delta_rational.cpp \
	theory/arith/delta_rational.h \
	theory/arith/dio_solver.cpp \
	theory/arith/dio_solver.h \
	theory/arith/dual_simplex.cpp \
	theory/arith/dual_simplex.h \
	theory/arith/error_set.cpp \
	theory/arith/error_set.h \
	theory/arith/fc_simplex.cpp \
	theory/arith/fc_simplex.h \
	theory/arith/infer_bounds.cpp \
	theory/arith/infer_bounds.h \
	theory/arith/linear_equality.cpp \
	theory/arith/linear_equality.h \
	theory/arith/matrix.cpp \
	theory/arith/matrix.h \
	theory/arith/nonlinear_extension.h \
	theory/arith/nonlinear_extension.cpp \
	theory/arith/normal_form.cpp \
	theory/arith/normal_form.h\
	theory/arith/partial_model.cpp \
	theory/arith/partial_model.h \
	theory/arith/pseudoboolean_proc.cpp \
	theory/arith/pseudoboolean_proc.h \
	theory/arith/simplex.cpp \
	theory/arith/simplex.h \
	theory/arith/simplex_update.cpp \
	theory/arith/simplex_update.h \
	theory/arith/soi_simplex.cpp \
	theory/arith/soi_simplex.h \
	theory/arith/tableau.cpp \
	theory/arith/tableau.h \
	theory/arith/tableau_sizes.cpp \
	theory/arith/tableau_sizes.h \
	theory/arith/theory_arith.cpp \
	theory/arith/theory_arith.h \
	theory/arith/theory_arith_private.cpp \
	theory/arith/theory_arith_private.h \
	theory/arith/theory_arith_private_forward.h \
	theory/arith/theory_arith_type_rules.h \
	theory/arith/type_enumerator.h \
	theory/arrays/array_info.cpp \
	theory/arrays/array_info.h \
	theory/arrays/array_proof_reconstruction.cpp \
	theory/arrays/array_proof_reconstruction.h \
	theory/arrays/static_fact_manager.cpp \
	theory/arrays/static_fact_manager.h \
	theory/arrays/theory_arrays.cpp \
	theory/arrays/theory_arrays.h \
	theory/arrays/theory_arrays_rewriter.cpp \
	theory/arrays/theory_arrays_rewriter.h \
	theory/arrays/theory_arrays_type_rules.h \
	theory/arrays/type_enumerator.h \
	theory/arrays/union_find.cpp \
	theory/arrays/union_find.h \
	theory/booleans/circuit_propagator.cpp \
	theory/booleans/circuit_propagator.h \
	theory/booleans/theory_bool.cpp \
	theory/booleans/theory_bool.h \
	theory/booleans/theory_bool_rewriter.cpp \
	theory/booleans/theory_bool_rewriter.h \
	theory/booleans/theory_bool_type_rules.h \
	theory/booleans/type_enumerator.h \
	theory/builtin/theory_builtin.cpp \
	theory/builtin/theory_builtin.h \
	theory/builtin/theory_builtin_rewriter.cpp \
	theory/builtin/theory_builtin_rewriter.h \
	theory/builtin/theory_builtin_type_rules.h \
	theory/builtin/type_enumerator.cpp \
	theory/builtin/type_enumerator.h \
	theory/bv/abstraction.cpp \
	theory/bv/abstraction.h \
	theory/bv/aig_bitblaster.cpp \
	theory/bv/bitblast_strategies_template.h \
	theory/bv/bitblast_utils.h \
	theory/bv/bitblaster_template.h \
	theory/bv/bv_eager_solver.cpp \
	theory/bv/bv_eager_solver.h \
	theory/bv/bv_inequality_graph.cpp \
	theory/bv/bv_inequality_graph.h \
	theory/bv/bv_quick_check.cpp \
	theory/bv/bv_quick_check.h \
	theory/bv/bv_subtheory.h \
	theory/bv/bv_subtheory_algebraic.cpp \
	theory/bv/bv_subtheory_algebraic.h \
	theory/bv/bv_subtheory_bitblast.cpp \
	theory/bv/bv_subtheory_bitblast.h \
	theory/bv/bv_subtheory_core.cpp \
	theory/bv/bv_subtheory_core.h \
	theory/bv/bv_subtheory_inequality.cpp \
	theory/bv/bv_subtheory_inequality.h \
	theory/bv/bv_to_bool.cpp \
	theory/bv/bv_to_bool.h \
	theory/bv/bvgauss.cpp \
	theory/bv/bvgauss.h \
	theory/bv/bvintropow2.cpp \
	theory/bv/bvintropow2.h \
	theory/bv/eager_bitblaster.cpp \
	theory/bv/lazy_bitblaster.cpp \
	theory/bv/slicer.cpp \
	theory/bv/slicer.h \
	theory/bv/theory_bv.cpp \
	theory/bv/theory_bv.h \
	theory/bv/theory_bv_rewrite_rules.h \
	theory/bv/theory_bv_rewrite_rules_constant_evaluation.h \
	theory/bv/theory_bv_rewrite_rules_core.h \
	theory/bv/theory_bv_rewrite_rules_normalization.h \
	theory/bv/theory_bv_rewrite_rules_operator_elimination.h \
	theory/bv/theory_bv_rewrite_rules_simplification.h \
	theory/bv/theory_bv_rewriter.cpp \
	theory/bv/theory_bv_rewriter.h \
	theory/bv/theory_bv_type_rules.h \
	theory/bv/theory_bv_utils.cpp \
	theory/bv/theory_bv_utils.h \
	theory/bv/type_enumerator.h \
	theory/datatypes/datatypes_rewriter.cpp \
	theory/datatypes/datatypes_rewriter.h \
	theory/datatypes/datatypes_sygus.cpp \
	theory/datatypes/datatypes_sygus.h \
	theory/datatypes/theory_datatypes.cpp \
	theory/datatypes/theory_datatypes.h \
	theory/datatypes/theory_datatypes_type_rules.h \
	theory/datatypes/type_enumerator.cpp \
	theory/datatypes/type_enumerator.h \
	theory/fp/theory_fp.cpp \
	theory/fp/theory_fp.h \
	theory/fp/theory_fp_rewriter.cpp \
	theory/fp/theory_fp_rewriter.h \
	theory/fp/theory_fp_type_rules.h \
	theory/fp/type_enumerator.h \
	theory/fp/fp_converter.h \
	theory/fp/fp_converter.cpp \
	theory/idl/idl_assertion.cpp \
	theory/idl/idl_assertion.h \
	theory/idl/idl_assertion_db.cpp \
	theory/idl/idl_assertion_db.h \
	theory/idl/idl_model.cpp \
	theory/idl/idl_model.h \
	theory/idl/theory_idl.cpp \
	theory/idl/theory_idl.h \
	theory/quantifiers/alpha_equivalence.cpp \
	theory/quantifiers/alpha_equivalence.h \
	theory/quantifiers/anti_skolem.cpp \
	theory/quantifiers/anti_skolem.h \
	theory/quantifiers/bv_inverter.cpp \
	theory/quantifiers/bv_inverter.h \
	theory/quantifiers/candidate_generator.cpp \
	theory/quantifiers/candidate_generator.h \
	theory/quantifiers/cegqi/ceg_instantiator.cpp \
	theory/quantifiers/cegqi/ceg_instantiator.h \
	theory/quantifiers/cegqi/ceg_t_instantiator.cpp \
	theory/quantifiers/cegqi/ceg_t_instantiator.h \
	theory/quantifiers/cegqi/inst_strategy_cbqi.cpp \
	theory/quantifiers/cegqi/inst_strategy_cbqi.h \
	theory/quantifiers/conjecture_generator.cpp \
	theory/quantifiers/conjecture_generator.h \
	theory/quantifiers/dynamic_rewrite.cpp \
	theory/quantifiers/dynamic_rewrite.h \
	theory/quantifiers/ematching/ho_trigger.cpp \
	theory/quantifiers/ematching/ho_trigger.h \
	theory/quantifiers/ematching/inst_match_generator.cpp \
	theory/quantifiers/ematching/inst_match_generator.h \
	theory/quantifiers/ematching/inst_strategy_e_matching.cpp \
	theory/quantifiers/ematching/inst_strategy_e_matching.h \
	theory/quantifiers/ematching/instantiation_engine.cpp \
	theory/quantifiers/ematching/instantiation_engine.h \
	theory/quantifiers/ematching/trigger.cpp \
	theory/quantifiers/ematching/trigger.h \
	theory/quantifiers/equality_query.cpp \
	theory/quantifiers/equality_query.h \
	theory/quantifiers/equality_infer.cpp \
	theory/quantifiers/equality_infer.h \
	theory/quantifiers/extended_rewrite.cpp \
	theory/quantifiers/extended_rewrite.h \
	theory/quantifiers/first_order_model.cpp \
	theory/quantifiers/first_order_model.h \
	theory/quantifiers/fmf/ambqi_builder.cpp \
	theory/quantifiers/fmf/ambqi_builder.h \
	theory/quantifiers/fmf/bounded_integers.cpp \
	theory/quantifiers/fmf/bounded_integers.h \
	theory/quantifiers/fmf/full_model_check.cpp \
	theory/quantifiers/fmf/full_model_check.h \
	theory/quantifiers/fmf/model_builder.cpp \
	theory/quantifiers/fmf/model_builder.h \
	theory/quantifiers/fmf/model_engine.cpp \
	theory/quantifiers/fmf/model_engine.h \
	theory/quantifiers/fun_def_engine.cpp \
	theory/quantifiers/fun_def_engine.h \
	theory/quantifiers/fun_def_process.cpp \
	theory/quantifiers/fun_def_process.h \
	theory/quantifiers/global_negate.cpp \
	theory/quantifiers/global_negate.h \
	theory/quantifiers/instantiate.cpp \
	theory/quantifiers/instantiate.h \
	theory/quantifiers/inst_match.cpp \
	theory/quantifiers/inst_match.h \
	theory/quantifiers/inst_match_trie.cpp \
	theory/quantifiers/inst_match_trie.h \
	theory/quantifiers/inst_propagator.cpp \
	theory/quantifiers/inst_propagator.h \
	theory/quantifiers/inst_strategy_enumerative.cpp \
	theory/quantifiers/inst_strategy_enumerative.h \
	theory/quantifiers/local_theory_ext.cpp \
	theory/quantifiers/local_theory_ext.h \
	theory/quantifiers/macros.cpp \
	theory/quantifiers/macros.h \
	theory/quantifiers/quant_conflict_find.cpp \
	theory/quantifiers/quant_conflict_find.h \
	theory/quantifiers/quant_epr.cpp \
	theory/quantifiers/quant_epr.h \
	theory/quantifiers/quant_equality_engine.cpp \
	theory/quantifiers/quant_equality_engine.h \
	theory/quantifiers/quant_relevance.cpp \
	theory/quantifiers/quant_relevance.h \
	theory/quantifiers/quant_split.cpp \
	theory/quantifiers/quant_split.h \
	theory/quantifiers/quant_util.cpp \
	theory/quantifiers/quant_util.h \
	theory/quantifiers/quantifiers_attributes.cpp \
	theory/quantifiers/quantifiers_attributes.h \
	theory/quantifiers/quantifiers_rewriter.cpp \
	theory/quantifiers/quantifiers_rewriter.h \
	theory/quantifiers/relevant_domain.cpp \
	theory/quantifiers/relevant_domain.h \
	theory/quantifiers/rewrite_engine.cpp \
	theory/quantifiers/rewrite_engine.h \
	theory/quantifiers/single_inv_partition.cpp \
	theory/quantifiers/single_inv_partition.h \
	theory/quantifiers/skolemize.cpp \
	theory/quantifiers/skolemize.h \
	theory/quantifiers/sygus/cegis.cpp \
	theory/quantifiers/sygus/cegis.h \
	theory/quantifiers/sygus/ce_guided_conjecture.cpp \
	theory/quantifiers/sygus/ce_guided_conjecture.h \
	theory/quantifiers/sygus/ce_guided_instantiation.cpp \
	theory/quantifiers/sygus/ce_guided_instantiation.h \
	theory/quantifiers/sygus/ce_guided_single_inv.cpp \
	theory/quantifiers/sygus/ce_guided_single_inv.h \
	theory/quantifiers/sygus/sygus_pbe.cpp \
	theory/quantifiers/sygus/sygus_pbe.h \
	theory/quantifiers/sygus/ce_guided_single_inv_sol.cpp \
	theory/quantifiers/sygus/ce_guided_single_inv_sol.h \
	theory/quantifiers/sygus/sygus_explain.cpp \
	theory/quantifiers/sygus/sygus_explain.h \
	theory/quantifiers/sygus/sygus_invariance.cpp \
	theory/quantifiers/sygus/sygus_invariance.h \
	theory/quantifiers/sygus/sygus_grammar_cons.cpp \
	theory/quantifiers/sygus/sygus_grammar_cons.h \
	theory/quantifiers/sygus/sygus_grammar_norm.cpp \
	theory/quantifiers/sygus/sygus_grammar_norm.h \
	theory/quantifiers/sygus/sygus_grammar_red.cpp \
	theory/quantifiers/sygus/sygus_grammar_red.h \
	theory/quantifiers/sygus/sygus_module.cpp \
	theory/quantifiers/sygus/sygus_module.h \
	theory/quantifiers/sygus/sygus_process_conj.cpp \
	theory/quantifiers/sygus/sygus_process_conj.h \
	theory/quantifiers/sygus/term_database_sygus.cpp \
	theory/quantifiers/sygus/term_database_sygus.h \
	theory/quantifiers/sygus_sampler.cpp \
	theory/quantifiers/sygus_sampler.h \
	theory/quantifiers/symmetry_breaking.cpp \
	theory/quantifiers/symmetry_breaking.h \
	theory/quantifiers/term_database.cpp \
	theory/quantifiers/term_database.h \
	theory/quantifiers/term_enumeration.cpp \
	theory/quantifiers/term_enumeration.h \
	theory/quantifiers/term_util.cpp \
	theory/quantifiers/term_util.h \
	theory/quantifiers/theory_quantifiers.cpp \
	theory/quantifiers/theory_quantifiers.h \
	theory/quantifiers/theory_quantifiers_type_rules.h \
	theory/sep/theory_sep.cpp \
	theory/sep/theory_sep.h \
	theory/sep/theory_sep_rewriter.cpp \
	theory/sep/theory_sep_rewriter.h \
	theory/sep/theory_sep_type_rules.h \
	theory/sets/normal_form.h \
	theory/sets/rels_utils.h \
	theory/sets/theory_sets.cpp \
	theory/sets/theory_sets.h \
	theory/sets/theory_sets_private.cpp \
	theory/sets/theory_sets_private.h \
	theory/sets/theory_sets_rels.cpp \
	theory/sets/theory_sets_rels.h \
	theory/sets/theory_sets_rewriter.cpp \
	theory/sets/theory_sets_rewriter.h \
	theory/sets/theory_sets_type_enumerator.h \
	theory/sets/theory_sets_type_rules.h \
	theory/strings/regexp_operation.cpp \
	theory/strings/regexp_operation.h \
	theory/strings/theory_strings.cpp \
	theory/strings/theory_strings.h \
	theory/strings/theory_strings_preprocess.cpp \
	theory/strings/theory_strings_preprocess.h \
	theory/strings/theory_strings_rewriter.cpp \
	theory/strings/theory_strings_rewriter.h \
	theory/strings/theory_strings_type_rules.h \
	theory/strings/type_enumerator.h \
	theory/uf/equality_engine.cpp \
	theory/uf/equality_engine.h \
	theory/uf/equality_engine_types.h \
	theory/uf/symmetry_breaker.cpp \
	theory/uf/symmetry_breaker.h \
	theory/uf/theory_uf.cpp \
	theory/uf/theory_uf.h \
	theory/uf/theory_uf_model.cpp \
	theory/uf/theory_uf_model.h \
	theory/uf/theory_uf_rewriter.h \
	theory/uf/theory_uf_strong_solver.cpp \
	theory/uf/theory_uf_strong_solver.h \
	theory/uf/theory_uf_type_rules.h

nodist_libcvc4_la_SOURCES = \
	theory/rewriter_tables.h \
	theory/theory_traits.h \
	theory/type_enumerator.cpp

libcvc4_la_LIBADD = \
	@builddir@/base/libbase.la \
	@builddir@/options/liboptions.la \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/smt_util/libsmtutil.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/prop/bvminisat/libbvminisat.la
if CVC4_PROOF
libcvc4_la_LIBADD += \
	@top_builddir@/proofs/signatures/libsignatures.la
endif

libcvc4_la_LIBADD += \
	@builddir@/lib/libreplacements.la

if CVC4_USE_GLPK
libcvc4_la_LIBADD += $(GLPK_LIBS)
libcvc4_la_LDFLAGS += $(GLPK_LDFLAGS)
endif

if CVC4_USE_ABC
libcvc4_la_LIBADD += $(ABC_LIBS)
libcvc4_la_LDFLAGS += $(ABC_LDFLAGS)
endif

if CVC4_USE_CRYPTOMINISAT
libcvc4_la_LIBADD += $(CRYPTOMINISAT_LIBS)
libcvc4_la_LDFLAGS += $(CRYPTOMINISAT_LDFLAGS)
endif

if CVC4_USE_LFSC
libcvc4_la_LIBADD += $(LFSC_LIBS)
libcvc4_la_LDFLAGS += $(LFSC_LDFLAGS)
endif



BUILT_SOURCES = \
	theory/rewriter_tables.h \
	theory/theory_traits.h \
	theory/type_enumerator.cpp \
	$(top_builddir)/src/.subdirs

CLEANFILES = \
	svn_versioninfo.cpp \
	svninfo.tmp \
	svninfo \
	git_versioninfo.cpp \
	gitinfo.tmp \
	gitinfo \
	theory/rewriter_tables.h \
	theory/theory_traits.h \
	theory/type_enumerator.cpp \
	$(top_builddir)/src/.subdirs

EXTRA_DIST = \
	Makefile.theories \
	cvc4.i \
	include/cvc4.h \
	include/cvc4_private.h \
	include/cvc4_private_library.h \
	include/cvc4_public.h \
	include/cvc4parser_private.h \
	include/cvc4parser_public.h \
	mksubdirs \
	smt/command.i \
	smt/logic_exception.i \
	smt/smt_engine.i \
	proof/unsat_core.i \
	theory/arith/kinds \
	theory/arrays/kinds \
	theory/booleans/kinds \
	theory/builtin/kinds \
	theory/bv/kinds \
	theory/datatypes/kinds \
	theory/example/ecdata.cpp \
	theory/example/ecdata.h \
	theory/example/theory_uf_tim.cpp \
	theory/example/theory_uf_tim.h \
	theory/fp/kinds \
	theory/idl/kinds \
	theory/logic_info.i \
	theory/mkrewriter \
	theory/mktheorytraits \
	theory/quantifiers/kinds \
	theory/rewriter_tables_template.h \
	theory/sep/kinds \
	theory/sets/kinds \
	theory/strings/kinds \
	theory/theory_traits_template.h \
	theory/type_enumerator_template.cpp \
	theory/uf/kinds

svn_versioninfo.cpp: svninfo
	$(AM_V_GEN)( \
	  if test -s svninfo; then \
	    issvn=true; \
	    branch=`grep '^URL: ' svninfo | sed 's,.*/cvc4/,,'`; \
	    rev=`grep '^Revision: ' svninfo | awk '{print$$2}'`; \
	    mods=`grep '^Modifications: ' svninfo | awk '{print$$2} END { if(!NR) print "false" }'`; \
	  else \
	    issvn=false; \
	    branch=unknown; \
	    rev=0; \
	    mods=false; \
	  fi; \
	  echo "#include \"base/configuration.h\""; \
	  echo "const bool ::CVC4::Configuration::IS_SUBVERSION_BUILD = $$issvn;"; \
	  echo "const char* const ::CVC4::Configuration::SUBVERSION_BRANCH_NAME = \"$$branch\";"; \
	  echo "const unsigned ::CVC4::Configuration::SUBVERSION_REVISION = $$rev;"; \
	  echo "const bool ::CVC4::Configuration::SUBVERSION_HAS_MODIFICATIONS = $$mods;"; \
	) >"$@"
# This .tmp business is to keep from having to re-compile options.cpp
# (and then re-link the libraries) if nothing has changed.
svninfo: svninfo.tmp
	$(AM_V_GEN)if diff -q svninfo.tmp svninfo &>/dev/null; then rm -f svninfo.tmp; else mv svninfo.tmp svninfo; fi
# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: svninfo.tmp
svninfo.tmp:
	$(AM_V_GEN)(cd "$(top_srcdir)" && svn info && echo "Modifications: `test -z \"\`svn status -q\`\" && echo false || echo true`") >"$@" 2>/dev/null || true

git_versioninfo.cpp: gitinfo
	$(AM_V_GEN)( \
	  if test -s gitinfo; then \
	    isgit=true; \
	    branch=`head -1 gitinfo`; \
	    rev=`head -2 gitinfo | tail -1 | awk '{print$$1}'`; \
	    mods=`grep '^Modifications: ' gitinfo | awk '{print$$2} END { if(!NR) print "false" }'`; \
	  else \
	    isgit=false; \
	    branch=unknown; \
	    rev=unknown; \
	    mods=false; \
	  fi; \
	  echo "#include \"base/configuration.h\""; \
	  echo "const bool ::CVC4::Configuration::IS_GIT_BUILD = $$isgit;"; \
	  echo "const char* const ::CVC4::Configuration::GIT_BRANCH_NAME = \"$$branch\";"; \
	  echo "const char* const ::CVC4::Configuration::GIT_COMMIT = \"$$rev\";"; \
	  echo "const bool ::CVC4::Configuration::GIT_HAS_MODIFICATIONS = $$mods;"; \
	) >"$@"
# This .tmp business is to keep from having to re-compile options.cpp
# (and then re-link the libraries) if nothing has changed.
gitinfo: gitinfo.tmp
	$(AM_V_GEN)if diff -q gitinfo.tmp gitinfo &>/dev/null; then rm -f gitinfo.tmp; else mv gitinfo.tmp gitinfo; fi || true
# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: gitinfo.tmp
gitinfo.tmp:
	$(AM_V_GEN)(cd "$(top_srcdir)"; if test -e .git/HEAD; then if ! grep -q '^ref: refs/heads/' .git/HEAD; then echo; fi; sed 's,^ref: refs/heads/,,' .git/HEAD; git show-ref refs/heads/`sed 's,^ref: refs/heads/,,' .git/HEAD`; echo "Modifications: `test -z \"\`git status -s -uno\`\" && echo false || echo true`"; fi) >"$@" 2>/dev/null || true

install-data-local:
	(echo include/cvc4.h; \
	 echo include/cvc4_public.h; \
	 echo include/cvc4parser_public.h; \
	 echo util/integer.h; \
	 echo util/rational.h; \
	 find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"'; \
	(cd "$(srcdir)" && find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"')) | \
	while read f; do \
		if expr "$$f" : ".*_\(template\|private\|private_library\|test_utils\)\.h$$" &>/dev/null; then \
			continue; \
		fi; \
		d="$$(echo "$$f" | sed 's,^include/,,')"; \
		$(mkinstalldirs) "$$(dirname "$(DESTDIR)$(includedir)/cvc4/$$d")"; \
		if [ -e "$$f" ]; then \
			path="$$f"; \
		else \
			path="$(srcdir)/$$f"; \
		fi; \
		fixpath="$(top_builddir)/header_install.fix"; \
		sed 's,^\([ \t]*#[ \t]*include[ \t*]\)"\(.*\)"\([ \t]*\)$$,\1<cvc4/\2>\3,' "$$path" > "$$fixpath" || exit 1; \
		echo $(INSTALL_DATA) "$$fixpath" "$(DESTDIR)$(includedir)/cvc4/$$d"; \
		if $(INSTALL_DATA) "$$fixpath" "$(DESTDIR)$(includedir)/cvc4/$$d"; then \
			rm -f "$$fixpath"; \
		else \
			rm -f "$$fixpath"; \
			exit 1; \
		fi; \
	done

uninstall-local:
	-(echo include/cvc4.h; \
	  echo include/cvc4_public.h; \
	  echo include/cvc4parser_public.h; \
	  echo util/integer.h; \
	  echo util/rational.h; \
	  find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"'; \
	(cd "$(srcdir)" && find * -name '*.h' | \
		xargs grep -l '^# *include  *"cvc4.*_public\.h"')) | \
	while read f; do \
		if expr "$$f" : ".*_\(template\|private\|private_library\|test_utils\)\.h$$" &>/dev/null; then \
			continue; \
		fi; \
		d="$$(echo "$$f" | sed 's,^include/,,')"; \
		rm -f "$(DESTDIR)$(includedir)/cvc4/$$d"; \
	done
	-rmdir "$(DESTDIR)$(includedir)/cvc4/bindings/compat"
	-rmdir "$(DESTDIR)$(includedir)/cvc4/bindings"
	-rmdir "$(DESTDIR)$(includedir)/cvc4"
	-rmdir "$(DESTDIR)$(libdir)/ocaml/cvc4"

# This rule is ugly.  It's needed to ensure that automake's dependence
# includes are available during distclean, even though they come from
# directories that are cleaned first.  Without this rule, "distclean"
# fails.
%.Plo:; $(MKDIR_P) "$(dir $@)" && : > "$@"

#include @top_srcdir@/src/theory/Makefile.subdirs
$(top_builddir)/src/.subdirs: $(top_srcdir)/src/Makefile.theories  @top_srcdir@/src/mksubdirs
	$(AM_V_at)test -d $(top_builddir)/src || mkdir $(top_builddir)/src
	$(AM_V_at)chmod +x @top_srcdir@/src/mksubdirs
	$(AM_V_at)( @top_srcdir@/src/mksubdirs "$(top_srcdir)" ) > $(top_builddir)/src/.subdirs.tmp
	@if ! diff -q $(top_builddir)/src/.subdirs $(top_builddir)/src/.subdirs.tmp &>/dev/null; then \
		echo "  GEN   " $@; \
		$(am__mv) $(top_builddir)/src/.subdirs.tmp $(top_builddir)/src/.subdirs; \
	fi

theory/rewriter_tables.h: theory/rewriter_tables_template.h theory/mkrewriter @top_builddir@/src/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)test -d $(top_builddir)/src/theory || mkdir -p @top_builddir@/src/theory
	$(AM_V_at)chmod +x @srcdir@/theory/mkrewriter
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/theory/mkrewriter \
		$< \
		`cat @top_builddir@/src/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

theory/theory_traits.h: theory/theory_traits_template.h theory/mktheorytraits @top_builddir@/src/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)test -d $(top_builddir)/src/theory || mkdir -p @top_builddir@/src/theory
	$(AM_V_at)chmod +x @srcdir@/theory/mktheorytraits
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/theory/mktheorytraits \
		$< \
		`cat @top_builddir@/src/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

theory/type_enumerator.cpp: theory/type_enumerator_template.cpp theory/mktheorytraits @top_builddir@/src/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)test -d $(top_builddir)/src/theory || mkdir -p @top_builddir@/src/theory
	$(AM_V_at)chmod +x @srcdir@/theory/mktheorytraits
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/theory/mktheorytraits \
		$< \
		`cat @top_builddir@/src/.subdirs` \
	> $@) || (rm -f $@ && exit 1)
