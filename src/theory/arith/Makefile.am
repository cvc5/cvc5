AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libarith.la

libarith_la_SOURCES = \
	theory_arith_type_rules.h \
	type_enumerator.h \
	arithvar.h \
	arithvar.cpp \
	bound_counts.h \
	arith_rewriter.h \
	arith_rewriter.cpp \
	arith_static_learner.h \
	arith_static_learner.cpp \
	constraint_forward.h \
	constraint.h \
	constraint.cpp \
	congruence_manager.h \
	congruence_manager.cpp \
	normal_form.h\
	normal_form.cpp \
	arith_utilities.h \
	delta_rational.h \
	delta_rational.cpp \
	partial_model.h \
	partial_model.cpp \
	linear_equality.h \
	linear_equality.cpp \
	simplex_update.h \
	simplex_update.cpp \
	callbacks.h \
	callbacks.cpp \
	matrix.h \
	matrix.cpp \
	tableau.h \
	tableau.cpp \
	tableau_sizes.h \
	tableau_sizes.cpp \
	error_set.h \
	error_set.cpp \
	simplex.h \
	simplex.cpp \
	dual_simplex.h \
	dual_simplex.cpp \
	fc_simplex.h \
	fc_simplex.cpp \
	soi_simplex.h \
	soi_simplex.cpp \
	approx_simplex.h \
	approx_simplex.cpp \
	pure_update_simplex.h \
	pure_update_simplex.cpp \
	theory_arith.h \
	theory_arith.cpp \
	theory_arith_private.h \
	theory_arith_private.cpp \
	dio_solver.h \
	dio_solver.cpp \
	arith_heuristic_pivot_rule.h \
	arith_heuristic_pivot_rule.cpp \
	arith_unate_lemma_mode.h \
	arith_unate_lemma_mode.cpp \
	arith_propagation_mode.h \
	arith_propagation_mode.cpp

EXTRA_DIST = \
	kinds \
	options_handlers.h
