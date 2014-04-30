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
	-I@builddir@ -I@srcdir@/include -I@srcdir@ -I@top_srcdir@/proofs/lfsc_checker
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas -Wno-parentheses $(FLAG_VISIBILITY_HIDDEN)

SUBDIRS = lib options expr util prop/minisat prop/bvminisat . parser compat bindings main
THEORIES = builtin booleans uf arith bv arrays datatypes sets strings quantifiers idl

lib_LTLIBRARIES = libcvc4.la

libcvc4_la_LDFLAGS = -version-info $(LIBCVC4_VERSION)

# This "tricks" automake into linking us as a C++ library (rather than
# as a C library, which messes up exception handling support)
nodist_EXTRA_libcvc4_la_SOURCES = dummy.cpp
libcvc4_la_SOURCES = \
	git_versioninfo.cpp \
	svn_versioninfo.cpp \
	context/context.cpp \
	context/context.h \
	context/context_mm.cpp \
	context/context_mm.h \
	context/cdo.h \
	context/cdlist.h \
	context/cdchunk_list.h \
	context/cdlist_forward.h \
	context/cdqueue.h \
	context/cdtrail_queue.h \
	context/cdtrail_hashmap.h \
	context/cdtrail_hashmap_forward.h \
	context/cdinsert_hashmap.h \
	context/cdinsert_hashmap_forward.h \
	context/cdhashmap.h \
	context/cdhashmap_forward.h \
	context/cdhashset.h \
	context/cdhashset_forward.h \
	context/cdvector.h \
	context/cdmaybe.h \
	context/stacking_map.h \
	context/stacking_vector.h \
	context/cddense_set.h \
	decision/decision_mode.h \
	decision/decision_mode.cpp \
	decision/decision_engine.h \
	decision/decision_engine.cpp \
	decision/decision_strategy.h \
	decision/justification_heuristic.h \
	decision/justification_heuristic.cpp \
	decision/options_handlers.h \
	printer/printer.h \
	printer/printer.cpp \
	printer/dagification_visitor.h \
	printer/dagification_visitor.cpp \
	printer/model_format_mode.h \
	printer/model_format_mode.cpp \
	printer/ast/ast_printer.h \
	printer/ast/ast_printer.cpp \
	printer/smt1/smt1_printer.h \
	printer/smt1/smt1_printer.cpp \
	printer/smt2/smt2_printer.h \
	printer/smt2/smt2_printer.cpp \
	printer/cvc/cvc_printer.h \
	printer/cvc/cvc_printer.cpp \
	printer/tptp/tptp_printer.h \
	printer/tptp/tptp_printer.cpp \
	printer/options_handlers.h \
	proof/proof.h \
	proof/sat_proof.h \
	proof/sat_proof.cpp \
	proof/cnf_proof.h \
	proof/cnf_proof.cpp \
	proof/theory_proof.h \
	proof/theory_proof.cpp \
	proof/proof_manager.h \
	proof/proof_manager.cpp \
	prop/registrar.h \
	prop/prop_engine.cpp \
	prop/prop_engine.h \
	prop/theory_proxy.h \
	prop/theory_proxy.cpp \
	prop/cnf_stream.h \
	prop/cnf_stream.cpp \
	prop/sat_solver.h \
	prop/sat_solver_types.h \
	prop/sat_solver_factory.h \
	prop/sat_solver_factory.cpp \
	prop/sat_solver_registry.h \
	prop/sat_solver_registry.cpp \
	prop/options_handlers.h \
	smt/smt_engine.cpp \
	smt/smt_engine_check_proof.cpp \
	smt/smt_engine.h \
	smt/model_postprocessor.cpp \
	smt/model_postprocessor.h \
	smt/smt_engine_scope.cpp \
	smt/smt_engine_scope.h \
	smt/command_list.cpp \
	smt/command_list.h \
	smt/modal_exception.h \
	smt/boolean_terms.h \
	smt/boolean_terms.cpp \
	smt/logic_exception.h \
	smt/logic_request.h \
	smt/simplification_mode.h \
	smt/simplification_mode.cpp \
	smt/options_handlers.h \
	theory/decision_attributes.h \
	theory/logic_info.h \
	theory/logic_info.cpp \
	theory/output_channel.h \
	theory/interrupted.h \
	theory/type_enumerator.h \
	theory/theory_engine.h \
	theory/theory_engine.cpp \
	theory/theory_test_utils.h \
	theory/theory.h \
	theory/theory.cpp \
	theory/theoryof_mode.h \
	theory/theory_registrar.h \
	theory/rewriter.h \
	theory/rewriter_attributes.h \
	theory/rewriter.cpp \
	theory/substitutions.h \
	theory/substitutions.cpp \
	theory/valuation.h \
	theory/valuation.cpp \
	theory/shared_terms_database.h \
	theory/shared_terms_database.cpp \
	theory/term_registration_visitor.h \
	theory/term_registration_visitor.cpp \
	theory/ite_utilities.h \
	theory/ite_utilities.cpp \
	theory/unconstrained_simplifier.h \
	theory/unconstrained_simplifier.cpp \
	theory/quantifiers_engine.h \
	theory/quantifiers_engine.cpp \
	theory/theory_model.h \
	theory/theory_model.cpp \
	theory/rep_set.h \
	theory/rep_set.cpp \
	theory/atom_requests.h \
	theory/atom_requests.cpp \
	theory/options_handlers.h \
	theory/uf/theory_uf.h \
	theory/uf/theory_uf.cpp \
	theory/uf/theory_uf_type_rules.h \
	theory/uf/theory_uf_rewriter.h \
	theory/uf/equality_engine.h \
	theory/uf/equality_engine_types.h \
	theory/uf/equality_engine.cpp \
	theory/uf/symmetry_breaker.h \
	theory/uf/symmetry_breaker.cpp \
	theory/uf/theory_uf_strong_solver.h \
	theory/uf/theory_uf_strong_solver.cpp \
	theory/uf/theory_uf_model.h \
	theory/uf/theory_uf_model.cpp \
	theory/uf/options_handlers.h \
	theory/bv/theory_bv_utils.h \
	theory/bv/type_enumerator.h \
	theory/bv/bitblaster.h \
	theory/bv/bitblaster.cpp \
	theory/bv/bv_to_bool.h \
	theory/bv/bv_to_bool.cpp \
	theory/bv/bv_subtheory.h \
	theory/bv/bv_subtheory_core.h \
	theory/bv/bv_subtheory_core.cpp \
	theory/bv/bv_subtheory_bitblast.h \
	theory/bv/bv_subtheory_bitblast.cpp \
	theory/bv/bv_subtheory_inequality.h \
	theory/bv/bv_subtheory_inequality.cpp \
	theory/bv/bv_inequality_graph.h \
	theory/bv/bv_inequality_graph.cpp \
	theory/bv/bitblast_strategies.h \
	theory/bv/bitblast_strategies.cpp \
	theory/bv/slicer.h \
	theory/bv/slicer.cpp \
	theory/bv/theory_bv.h \
	theory/bv/theory_bv.cpp \
	theory/bv/theory_bv_rewrite_rules.h \
	theory/bv/theory_bv_rewrite_rules_core.h \
	theory/bv/theory_bv_rewrite_rules_operator_elimination.h \
	theory/bv/theory_bv_rewrite_rules_constant_evaluation.h \
	theory/bv/theory_bv_rewrite_rules_normalization.h \
	theory/bv/theory_bv_rewrite_rules_simplification.h \
	theory/bv/theory_bv_type_rules.h \
	theory/bv/theory_bv_rewriter.h \
	theory/bv/theory_bv_rewriter.cpp \
	theory/bv/cd_set_collection.h \
	theory/idl/idl_model.h \
	theory/idl/idl_model.cpp \
	theory/idl/idl_assertion.h \
	theory/idl/idl_assertion.cpp \
	theory/idl/idl_assertion_db.h \
	theory/idl/idl_assertion_db.cpp \
	theory/idl/theory_idl.h \
	theory/idl/theory_idl.cpp \
	theory/builtin/theory_builtin_type_rules.h \
	theory/builtin/type_enumerator.h \
	theory/builtin/theory_builtin_rewriter.h \
	theory/builtin/theory_builtin_rewriter.cpp \
	theory/builtin/theory_builtin.h \
	theory/builtin/theory_builtin.cpp \
	theory/datatypes/theory_datatypes_type_rules.h \
	theory/datatypes/type_enumerator.h \
	theory/datatypes/theory_datatypes.h \
	theory/datatypes/datatypes_rewriter.h \
	theory/datatypes/theory_datatypes.cpp \
	theory/sets/expr_patterns.h \
	theory/sets/options_handlers.h \
	theory/sets/scrutinize.h \
	theory/sets/term_info.h \
	theory/sets/theory_sets.cpp \
	theory/sets/theory_sets.h \
	theory/sets/theory_sets_private.cpp \
	theory/sets/theory_sets_private.h \
	theory/sets/theory_sets_rewriter.cpp \
	theory/sets/theory_sets_rewriter.h \
	theory/sets/theory_sets_type_enumerator.h \
	theory/sets/theory_sets_type_rules.h \
	theory/strings/theory_strings.h \
	theory/strings/theory_strings.cpp \
	theory/strings/theory_strings_rewriter.h \
	theory/strings/theory_strings_rewriter.cpp \
	theory/strings/theory_strings_type_rules.h \
	theory/strings/type_enumerator.h \
	theory/strings/theory_strings_preprocess.h \
	theory/strings/theory_strings_preprocess.cpp \
	theory/strings/regexp_operation.cpp \
	theory/strings/regexp_operation.h \
	theory/arrays/theory_arrays_type_rules.h \
	theory/arrays/type_enumerator.h \
	theory/arrays/theory_arrays_rewriter.h \
	theory/arrays/theory_arrays_rewriter.cpp \
	theory/arrays/theory_arrays.h \
	theory/arrays/theory_arrays.cpp \
	theory/arrays/union_find.h \
	theory/arrays/union_find.cpp \
	theory/arrays/array_info.h \
	theory/arrays/array_info.cpp \
	theory/arrays/static_fact_manager.h \
	theory/arrays/static_fact_manager.cpp \
	theory/quantifiers/theory_quantifiers_type_rules.h \
	theory/quantifiers/theory_quantifiers.h \
	theory/quantifiers/quantifiers_rewriter.h \
	theory/quantifiers/quantifiers_rewriter.cpp \
	theory/quantifiers/theory_quantifiers.cpp \
	theory/quantifiers/instantiation_engine.h \
	theory/quantifiers/instantiation_engine.cpp \
	theory/quantifiers/trigger.h \
	theory/quantifiers/trigger.cpp \
	theory/quantifiers/candidate_generator.h \
	theory/quantifiers/candidate_generator.cpp \
	theory/quantifiers/inst_match.h \
	theory/quantifiers/inst_match.cpp \
	theory/quantifiers/model_engine.h \
	theory/quantifiers/model_engine.cpp \
	theory/quantifiers/modes.cpp \
	theory/quantifiers/modes.h \
	theory/quantifiers/term_database.h \
	theory/quantifiers/term_database.cpp \
	theory/quantifiers/first_order_model.h \
	theory/quantifiers/first_order_model.cpp \
	theory/quantifiers/model_builder.h \
	theory/quantifiers/model_builder.cpp \
	theory/quantifiers/quantifiers_attributes.h \
	theory/quantifiers/quantifiers_attributes.cpp \
	theory/quantifiers/inst_gen.h \
	theory/quantifiers/inst_gen.cpp \
	theory/quantifiers/quant_util.h \
	theory/quantifiers/quant_util.cpp \
	theory/quantifiers/inst_match_generator.h \
	theory/quantifiers/inst_match_generator.cpp \
	theory/quantifiers/macros.h \
	theory/quantifiers/macros.cpp \
	theory/quantifiers/inst_strategy_e_matching.h \
	theory/quantifiers/inst_strategy_e_matching.cpp \
	theory/quantifiers/inst_strategy_cbqi.h \
	theory/quantifiers/inst_strategy_cbqi.cpp \
	theory/quantifiers/full_model_check.h \
	theory/quantifiers/full_model_check.cpp \
	theory/quantifiers/bounded_integers.h \
	theory/quantifiers/bounded_integers.cpp \
	theory/quantifiers/first_order_reasoning.h \
	theory/quantifiers/first_order_reasoning.cpp \
	theory/quantifiers/rewrite_engine.h \
	theory/quantifiers/rewrite_engine.cpp \
	theory/quantifiers/relevant_domain.h \
	theory/quantifiers/relevant_domain.cpp \
	theory/quantifiers/symmetry_breaking.h \
	theory/quantifiers/symmetry_breaking.cpp \
	theory/quantifiers/qinterval_builder.h \
	theory/quantifiers/qinterval_builder.cpp \
	theory/quantifiers/quant_conflict_find.h \
	theory/quantifiers/quant_conflict_find.cpp \
	theory/quantifiers/options_handlers.h \
	theory/arith/theory_arith_type_rules.h \
	theory/arith/type_enumerator.h \
	theory/arith/arithvar.h \
	theory/arith/arithvar.cpp \
	theory/arith/bound_counts.h \
	theory/arith/arith_ite_utils.h \
	theory/arith/arith_ite_utils.cpp \
	theory/arith/arith_rewriter.h \
	theory/arith/arith_rewriter.cpp \
	theory/arith/arith_static_learner.h \
	theory/arith/arith_static_learner.cpp \
	theory/arith/constraint_forward.h \
	theory/arith/constraint.h \
	theory/arith/constraint.cpp \
	theory/arith/congruence_manager.h \
	theory/arith/congruence_manager.cpp \
	theory/arith/normal_form.h\
	theory/arith/normal_form.cpp \
	theory/arith/arith_utilities.h \
	theory/arith/delta_rational.h \
	theory/arith/delta_rational.cpp \
	theory/arith/partial_model.h \
	theory/arith/partial_model.cpp \
	theory/arith/linear_equality.h \
	theory/arith/linear_equality.cpp \
	theory/arith/simplex_update.h \
	theory/arith/simplex_update.cpp \
	theory/arith/callbacks.h \
	theory/arith/callbacks.cpp \
	theory/arith/matrix.h \
	theory/arith/matrix.cpp \
	theory/arith/tableau.h \
	theory/arith/tableau.cpp \
	theory/arith/tableau_sizes.h \
	theory/arith/tableau_sizes.cpp \
	theory/arith/error_set.h \
	theory/arith/error_set.cpp \
	theory/arith/simplex.h \
	theory/arith/simplex.cpp \
	theory/arith/dual_simplex.h \
	theory/arith/dual_simplex.cpp \
	theory/arith/fc_simplex.h \
	theory/arith/fc_simplex.cpp \
	theory/arith/soi_simplex.h \
	theory/arith/soi_simplex.cpp \
	theory/arith/infer_bounds.h \
	theory/arith/infer_bounds.cpp \
	theory/arith/approx_simplex.h \
	theory/arith/approx_simplex.cpp \
	theory/arith/attempt_solution_simplex.h \
	theory/arith/attempt_solution_simplex.cpp \
	theory/arith/theory_arith.h \
	theory/arith/theory_arith.cpp \
	theory/arith/theory_arith_private_forward.h \
	theory/arith/theory_arith_private.h \
	theory/arith/theory_arith_private.cpp \
	theory/arith/dio_solver.h \
	theory/arith/dio_solver.cpp \
	theory/arith/arith_heuristic_pivot_rule.h \
	theory/arith/arith_heuristic_pivot_rule.cpp \
	theory/arith/arith_unate_lemma_mode.h \
	theory/arith/arith_unate_lemma_mode.cpp \
	theory/arith/arith_propagation_mode.h \
	theory/arith/arith_propagation_mode.cpp \
	theory/arith/cut_log.h \
	theory/arith/cut_log.cpp \
	theory/arith/options_handlers.h \
	theory/booleans/type_enumerator.h \
	theory/booleans/theory_bool.h \
	theory/booleans/theory_bool.cpp \
	theory/booleans/theory_bool_type_rules.h \
	theory/booleans/theory_bool_rewriter.h \
	theory/booleans/theory_bool_rewriter.cpp \
	theory/booleans/circuit_propagator.h \
	theory/booleans/circuit_propagator.cpp \
	theory/booleans/boolean_term_conversion_mode.h \
	theory/booleans/boolean_term_conversion_mode.cpp \
	theory/booleans/options_handlers.h

nodist_libcvc4_la_SOURCES = \
	smt/smt_options.cpp \
	theory/rewriter_tables.h \
	theory/theory_traits.h \
	theory/type_enumerator.cpp

libcvc4_la_LIBADD = \
	@builddir@/options/liboptions.la \
	@builddir@/util/libutil.la \
	@builddir@/expr/libexpr.la \
	@builddir@/prop/minisat/libminisat.la \
	@builddir@/prop/bvminisat/libbvminisat.la
if CVC4_PROOF
libcvc4_la_LIBADD += \
	@top_builddir@/proofs/lfsc_checker/liblfsc_checker.la \
	@top_builddir@/proofs/signatures/libsignatures.la
endif

if CVC4_NEEDS_REPLACEMENT_FUNCTIONS
libcvc4_la_LIBADD += \
	@builddir@/lib/libreplacements.la
endif

if CVC4_USE_GLPK
libcvc4_la_LIBADD += $(GLPK_LIBS)
endif

BUILT_SOURCES = \
	theory/rewriter_tables.h \
	theory/theory_traits.h \
	theory/type_enumerator.cpp

CLEANFILES = \
	svn_versioninfo.cpp \
	svninfo.tmp \
	svninfo \
	git_versioninfo.cpp \
	gitinfo.tmp \
	gitinfo \
	theory/rewriter_tables.h \
	theory/theory_traits.h \
	theory/type_enumerator.cpp

EXTRA_DIST = \
	include/cvc4_private_library.h \
	include/cvc4parser_private.h \
	include/cvc4parser_public.h \
	include/cvc4_private.h \
	include/cvc4_public.h \
	include/cvc4.h \
	cvc4.i \
	smt/smt_options_template.cpp \
	smt/modal_exception.i \
	smt/logic_exception.i \
	smt/smt_engine.i \
	theory/logic_info.i \
	theory/rewriter_tables_template.h \
	theory/theory_traits_template.h \
	theory/type_enumerator_template.cpp \
	theory/mktheorytraits \
	theory/mkrewriter \
	theory/Makefile.subdirs \
	theory/uf/kinds \
	theory/bv/kinds \
	theory/idl/kinds \
	theory/builtin/kinds \
	theory/datatypes/kinds \
	theory/sets/kinds \
	theory/strings/kinds \
	theory/arrays/kinds \
	theory/quantifiers/kinds \
	theory/arith/kinds \
	theory/booleans/kinds \
	theory/example/ecdata.h \
	theory/example/ecdata.cpp \
	theory/example/theory_uf_tim.h \
	theory/example/theory_uf_tim.cpp

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
	  echo "#include \"util/configuration.h\""; \
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
	  echo "#include \"util/configuration.h\""; \
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
	 echo util/tls.h; \
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
	  echo util/tls.h; \
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

include @top_srcdir@/src/theory/Makefile.subdirs

theory/rewriter_tables.h: theory/rewriter_tables_template.h theory/mkrewriter @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/theory/mkrewriter
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/theory/mkrewriter \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

theory/theory_traits.h: theory/theory_traits_template.h theory/mktheorytraits @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/theory/mktheorytraits
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/theory/mktheorytraits \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)

theory/type_enumerator.cpp: theory/type_enumerator_template.cpp theory/mktheorytraits @top_builddir@/src/theory/.subdirs @top_srcdir@/src/theory/*/kinds
	$(AM_V_at)chmod +x @srcdir@/theory/mktheorytraits
	$(AM_V_at)$(am__mv) $@ $@~ 2>/dev/null || true
	$(AM_V_GEN)(@srcdir@/theory/mktheorytraits \
		$< \
		`cat @top_builddir@/src/theory/.subdirs` \
	> $@) || (rm -f $@ && exit 1)
