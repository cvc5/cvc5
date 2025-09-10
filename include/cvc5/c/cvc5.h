/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C API.
 */

#ifndef CVC5__C_API__CVC5_H
#define CVC5__C_API__CVC5_H

#include <cvc5/cvc5_export.h>

#if __cplusplus
extern "C" {
#endif

#define CVC5_API_USE_C_ENUMS
#include <cvc5/cvc5_kind.h>
#include <cvc5/cvc5_proof_rule.h>
#include <cvc5/cvc5_skolem_id.h>
#include <cvc5/cvc5_types.h>
#undef CVC5_API_USE_C_ENUMS

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// char32_t is a built-in keyword in C++11 and defined in C11 via <uchar.h>. See:
//   https://en.cppreference.com/w/cpp/keyword/char32_t.html
//   https://en.cppreference.com/w/c/header/uchar.html
// However, the uchar.h header is missing in Apple Clang. See:
//   https://github.com/llvm/llvm-project/issues/41443
// This workaround defines char32_t when uchar.h is not available (in C mode)
#ifndef __cplusplus
  #ifdef __has_include
    #if __has_include(<uchar.h>)
      #include <uchar.h>
    #else
      typedef uint_least32_t char32_t;
    #endif
  #else
    // Fallback if __has_include is not supported
    typedef uint_least32_t char32_t;
  #endif
#endif

/* -------------------------------------------------------------------------- */

/**
 * Encapsulation of a three-valued solver result, with explanations.
 */
typedef struct cvc5_result_t* Cvc5Result;

/**
 * Encapsulation of a solver synth result.
 *
 * This is the return value of the API functions:
 *   - cvc5_check_synth()
 *   - cvc5_check_synth_next()
 *
 * which we call "synthesis queries".  This class indicates whether the
 * synthesis query has a solution, has no solution, or is unknown.
 */
typedef struct cvc5_synth_result_t* Cvc5SynthResult;

/**
 * The sort of a cvc5 term.
 */
typedef struct cvc5_sort_t* Cvc5Sort;

/** A cvc5 term. */
typedef struct cvc5_term_t* Cvc5Term;

/**
 * A cvc5 operator.
 *
 * An operator is a term that represents certain operators, instantiated
 * with its required parameters, e.g., a Term of kind
 * #CVC5_KIND_BITVECTOR_EXTRACT.
 */
typedef struct cvc5_op_t* Cvc5Op;

/** A cvc5 datatype. */
typedef struct cvc5_dt_t* Cvc5Datatype;
/**
 * A cvc5 datatype selector.
 */
typedef struct cvc5_dt_sel_t* Cvc5DatatypeSelector;
/**
 * A cvc5 datatype constructor.
 */
typedef struct cvc5_dt_cons_t* Cvc5DatatypeConstructor;
/**
 * A cvc5 datatype constructor declaration. A datatype constructor declaration
 * is a specification used for creating a datatype constructor.
 */
typedef struct cvc5_dt_cons_decl_t* Cvc5DatatypeConstructorDecl;
/**
 * A cvc5 datatype declaration. A datatype declaration is not itself a datatype
 * (see Datatype), but a specification for creating a datatype sort.
 *
 * The interface for a datatype declaration coincides with the syntax for the
 * SMT-LIB 2.6 command `declare-datatype`, or a single datatype within the
 * `declare-datatypes` command.
 *
 * Datatype sorts can be constructed from a Cvc5DatatypeDecl using:
 *   - cvc5_mk_datatype_sort()
 *   - cvc5_mk_datatype_sorts()
 */
typedef struct cvc5_dt_decl_t* Cvc5DatatypeDecl;

/**
 * A Sygus Grammar. This can be used to define a context-free grammar
 * of terms. Its interface coincides with the definition of grammars
 * (``GrammarDef``) in the SyGuS IF 2.1 standard.
 */
typedef struct cvc5_grammar_t* Cvc5Grammar;

/**
 * A cvc5 solver.
 */
typedef struct Cvc5 Cvc5;

/**
 * A cvc5 term (and sort) manager.
 */
typedef struct Cvc5TermManager Cvc5TermManager;

/**
 * A cvc5 option info.
 */
typedef struct Cvc5OptionInfo Cvc5OptionInfo;

/**
 * A cvc5 proof.
 */
typedef struct cvc5_proof_t* Cvc5Proof;

/**
 * A cvc5 statistic.
 */
typedef struct cvc5_stat_t* Cvc5Stat;

/**
 * A cvc5 statistics instance.
 */
typedef struct cvc5_stats_t* Cvc5Statistics;

/* -------------------------------------------------------------------------- */
/* Cvc5Result                                                                 */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5result
 *  @{
 */

/**
 * Make copy of result, increases reference counter of `result`.
 *
 * @param result The result to copy.
 * @return The same result with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5Result cvc5_result_copy(Cvc5Result result);

/**
 * Release copy of result, decrements reference counter of `result`.
 *
 * @param result The result to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a copy
 *       that is owned by the callee of the function and thus, can be released.
 */
CVC5_EXPORT void cvc5_result_release(Cvc5Result result);

/**
 * Determine if a given result is empty (a nullary result) and not an actual
 * result returned from a `cvc5_check_sat()` (and friends) query.
 * @param result The result.
 * @return True if the given result is a nullary result.
 */
CVC5_EXPORT bool cvc5_result_is_null(const Cvc5Result result);

/**
 * Determine if given result is from a satisfiable `cvc5_check_sat()` or
 * cvc5_check_sat_ssuming() query.
 * @param result The result.
 * @return True if result is from a satisfiable query.
 */
CVC5_EXPORT bool cvc5_result_is_sat(const Cvc5Result result);

/**
 * Determine if given result is from an unsatisfiable `cvc5_check_sat()` or
 * cvc5_check_sat_assuming() query.
 * @param result The result.
 * @return True if result is from an unsatisfiable query.
 */
CVC5_EXPORT bool cvc5_result_is_unsat(const Cvc5Result result);

/**
 * Determine if given result is from a `cvc5_check_sat()` or
 * cvc5_check_sat_assuming() query and cvc5 was not able to determine
 * (un)satisfiability.
 * @param result The result.
 * @return True if result is from a query where cvc5 was not able to determine
 *         (un)satisfiability.
 */
CVC5_EXPORT bool cvc5_result_is_unknown(const Cvc5Result result);

/**
 * Determine equality of two results.
 * @param a The first result to compare to for equality.
 * @param b The second result to compare to for equality.
 * @return True if the results are equal.
 */
CVC5_EXPORT bool cvc5_result_is_equal(const Cvc5Result a, const Cvc5Result b);

/**
 * Operator overloading for disequality of two results.
 * @param a The first result to compare to for disequality.
 * @param b The second result to compare to for disequality.
 * @return True if the results are disequal.
 */
CVC5_EXPORT bool cvc5_result_is_disequal(const Cvc5Result a,
                                         const Cvc5Result b);

/**
 * Get the explanation for an unknown result.
 * @param result The result.
 * @return An explanation for an unknown query result.
 */
CVC5_EXPORT Cvc5UnknownExplanation
cvc5_result_get_unknown_explanation(const Cvc5Result result);

/**
 * Get the string representation of a given result.
 * @param result The result.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_result_to_string(const Cvc5Result result);

/**
 * Compute the hash value of a result.
 * @param result The result.
 * @return The hash value of the result.
 */
CVC5_EXPORT size_t cvc5_result_hash(Cvc5Result result);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5SynthResult                                                            */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5synthresult
 *  @{
 */

/**
 * Determine if a given synthesis result is empty (a nullary result) and not an
 * actual result returned from a synthesis query.
 * @param result The result.
 * @return True if the given result is a nullary result.
 */
CVC5_EXPORT bool cvc5_synth_result_is_null(const Cvc5SynthResult result);

/**
 * Determine if the given result is from a synthesis query that has a solution.
 * @param result The result.
 * @return True if the synthesis query has a solution.
 */
CVC5_EXPORT bool cvc5_synth_result_has_solution(const Cvc5SynthResult result);

/**
 * Determine if the given result is from a synthesis query that has no solution.
 * @param result The result.
 * @return True if the synthesis query has no solution. In this case, it
 *         was determined that there was no solution.
 */
CVC5_EXPORT bool cvc5_synth_result_has_no_solution(
    const Cvc5SynthResult result);

/**
 * Determine if the given result is from a synthesis query where its result
 * could not be determined.
 * @param result The result.
 * @return True if the result of the synthesis query could not be determined.
 */
CVC5_EXPORT bool cvc5_synth_result_is_unknown(const Cvc5SynthResult result);

/**
 * Determine equality of two synthesis results.
 * @param a The first synthesis result to compare to for equality.
 * @param b The second synthesis result to compare to for equality.
 * @return True if the synthesis results are equal.
 */
CVC5_EXPORT bool cvc5_synth_result_is_equal(const Cvc5SynthResult a,
                                            const Cvc5SynthResult b);

/**
 * Operator overloading for disequality of two synthesis results.
 * @param a The first synthesis result to compare to for disequality.
 * @param b The second synthesis result to compare to for disequality.
 * @return True if the synthesis results are disequal.
 */
CVC5_EXPORT bool cvc5_synth_result_is_disequal(const Cvc5SynthResult a,
                                               const Cvc5SynthResult b);

/**
 * Get the string representation of a given result.
 * @param result The result.
 * @return A string representation of the given synthesis result.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_synth_result_to_string(
    const Cvc5SynthResult result);

/**
 * Compute the hash value of a synthesis result.
 * @param result The synthesis result.
 * @return The hash value of the synthesis result.
 */
CVC5_EXPORT size_t cvc5_synth_result_hash(Cvc5SynthResult result);

/**
 * Make copy of synthesis result, increases reference counter of `result`.
 *
 * @param result The synthesis  result to copy.
 * @return The same result with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5SynthResult cvc5_synth_result_copy(Cvc5SynthResult result);

/**
 * Release copy of synthesis result, decrements reference counter of `result`.
 *
 * @param result The result to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a copy
 *       that is owned by the callee of the function and thus, can be released.
 */
CVC5_EXPORT void cvc5_synth_result_release(Cvc5SynthResult result);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Sort                                                                   */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5sort
 *  @{
 */

/**
 * Make copy of sort, increases reference counter of `sort`.
 *
 * @param sort The sort to copy.
 * @return The same sort with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_copy(Cvc5Sort sort);

/**
 * Release copy of sort, decrements reference counter of `sort`.
 *
 * @param sort The sort to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a
 *       Cvc5Sort returns a copy that is owned by the callee of the function
 *       and thus, can be released.
 */
CVC5_EXPORT void cvc5_sort_release(Cvc5Sort sort);

/**
 * Compare two sorts for structural equality.
 * @param a The first sort.
 * @param b The second sort.
 * @return True if the sorts are equal.
 */
CVC5_EXPORT bool cvc5_sort_is_equal(Cvc5Sort a, Cvc5Sort b);

/**
 * Compare two sorts for structural disequality.
 * @param a The first sort.
 * @param b The second sort.
 * @return True if the sorts are not equal.
 */
CVC5_EXPORT bool cvc5_sort_is_disequal(Cvc5Sort a, Cvc5Sort b);

/**
 * Compare two sorts for ordering.
 * @param a The first sort.
 * @param b The second sort.
 * @return An integer value indicating the ordering: 0 if both sorts are equal,
 *         `-1` if `a < b`, and `1` if `b > a`.
 */
CVC5_EXPORT int64_t cvc5_sort_compare(Cvc5Sort a, Cvc5Sort b);

/**
 * Get the kind of the given sort.
 * @param sort The sort.
 * @return The kind of the sort.
 *
 * @warning This function is experimental and may change in future versions.
 */
CVC5_EXPORT Cvc5SortKind cvc5_sort_get_kind(Cvc5Sort sort);

/**
 * Determine if the given sort has a symbol (a name).
 *
 * For example, uninterpreted sorts and uninterpreted sort constructors have
 * symbols.
 *
 * @param sort The sort.
 * @return True if the sort has a symbol.
 */
CVC5_EXPORT bool cvc5_sort_has_symbol(Cvc5Sort sort);

/**
 * Get the symbol of this Sort.
 *
 * @note Asserts cvc5_sort_has_symbol().
 *
 * The symbol of this sort is the string that was
 * provided when constructing it via
 * cvc5_mk_uninterpreted_sort(),
 * cvc5_mk_unresolved_sort(), or
 * cvc5_mk_uninterpreted_sort_constructor_sort().
 *
 * @param sort The sort.
 * @return The raw symbol of the sort.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_sort_get_symbol(Cvc5Sort sort);

/**
 * Determine if given sort is the Boolean sort (SMT-LIB: `Bool`).
 * @param sort The sort.
 * @return True if given sort is the Boolean sort.
 */
CVC5_EXPORT bool cvc5_sort_is_boolean(Cvc5Sort sort);

/**
 * Determine if given sort is the integer sort (SMT-LIB: `Int`).
 * @param sort The sort.
 * @return True if given sort is the integer sort.
 */
CVC5_EXPORT bool cvc5_sort_is_integer(Cvc5Sort sort);

/**
 * Determine if given sort is the real sort (SMT-LIB: `Real`).
 * @param sort The sort.
 * @return True if given sort is the real sort.
 */
CVC5_EXPORT bool cvc5_sort_is_real(Cvc5Sort sort);

/**
 * Determine if given sort is the string sort (SMT-LIB: `String`).
 * @param sort The sort.
 * @return True if given sort is the string sort.
 */
CVC5_EXPORT bool cvc5_sort_is_string(Cvc5Sort sort);

/**
 * Determine if given sort is the regular expression sort (SMT-LIB: `RegLan`).
 * @param sort The sort.
 * @return True if given sort is the regular expression sort.
 */
CVC5_EXPORT bool cvc5_sort_is_regexp(Cvc5Sort sort);

/**
 * Determine if given sort is the rounding mode sort
 * (SMT-LIB: `Cvc5RoundingMode`).
 * @param sort The sort.
 * @return True if given sort is the rounding mode sort.
 */
CVC5_EXPORT bool cvc5_sort_is_rm(Cvc5Sort sort);

/**
 * Determine if given sort is a bit-vector sort (SMT-LIB: `(_ BitVec i)`).
 * @param sort The sort.
 * @return True if given sort is a bit-vector sort.
 */
CVC5_EXPORT bool cvc5_sort_is_bv(Cvc5Sort sort);

/**
 * Determine if given sort is a floatingpoint sort
 * (SMT-LIB: `(_ FloatingPoint eb sb)`).
 * @param sort The sort.
 * @return True if given sort is a floating-point sort.
 */
CVC5_EXPORT bool cvc5_sort_is_fp(Cvc5Sort sort);

/**
 * Determine if given sort is a datatype sort.
 * @param sort The sort.
 * @return True if given sort is a datatype sort.
 */
CVC5_EXPORT bool cvc5_sort_is_dt(Cvc5Sort sort);

/**
 * Determine if given sort is a datatype constructor sort.
 * @param sort The sort.
 * @return True if given sort is a datatype constructor sort.
 */
CVC5_EXPORT bool cvc5_sort_is_dt_constructor(Cvc5Sort sort);

/**
 * Determine if given sort is a datatype selector sort.
 * @param sort The sort.
 * @return True if given sort is a datatype selector sort.
 */
CVC5_EXPORT bool cvc5_sort_is_dt_selector(Cvc5Sort sort);

/**
 * Determine if given sort is a datatype tester sort.
 * @param sort The sort.
 * @return True if given sort is a datatype tester sort.
 */
CVC5_EXPORT bool cvc5_sort_is_dt_tester(Cvc5Sort sort);

/**
 * Determine if given sort is a datatype updater sort.
 * @param sort The sort.
 * @return True if given sort is a datatype updater sort.
 */
CVC5_EXPORT bool cvc5_sort_is_dt_updater(Cvc5Sort sort);

/**
 * Determine if given sort is a function sort.
 * @param sort The sort.
 * @return True if given sort is a function sort.
 */
CVC5_EXPORT bool cvc5_sort_is_fun(Cvc5Sort sort);

/**
 * Determine if given sort is a predicate sort.
 *
 * A predicate sort is a function sort that maps to the Boolean sort. All
 * predicate sorts are also function sorts.
 *
 * @param sort The sort.
 * @return True if given sort is a predicate sort.
 */
CVC5_EXPORT bool cvc5_sort_is_predicate(Cvc5Sort sort);

/**
 * Determine if given sort is a tuple sort.
 * @param sort The sort.
 * @return True if given sort is a tuple sort.
 */
CVC5_EXPORT bool cvc5_sort_is_tuple(Cvc5Sort sort);

/**
 * Determine if given sort is a nullable sort.
 * @param sort The sort.
 * @return True if given sort is a nullable sort.
 */
CVC5_EXPORT bool cvc5_sort_is_nullable(Cvc5Sort sort);

/**
 * Determine if given sort is a record sort.
 * @warning This function is experimental and may change in future versions.
 * @param sort The sort.
 * @return True if the sort is a record sort.
 */
CVC5_EXPORT bool cvc5_sort_is_record(Cvc5Sort sort);

/**
 * Determine if given sort is an array sort.
 * @param sort The sort.
 * @return True if the sort is an array sort.
 */
CVC5_EXPORT bool cvc5_sort_is_array(Cvc5Sort sort);

/**
 * Determine if given sort is a finite field sort.
 * @param sort The sort.
 * @return True if the sort is a finite field sort.
 */
CVC5_EXPORT bool cvc5_sort_is_ff(Cvc5Sort sort);

/**
 * Determine if given sort is a Set sort.
 * @param sort The sort.
 * @return True if the sort is a Set sort.
 */
CVC5_EXPORT bool cvc5_sort_is_set(Cvc5Sort sort);

/**
 * Determine if given sort is a Bag sort.
 * @param sort The sort.
 * @return True if the sort is a Bag sort.
 */
CVC5_EXPORT bool cvc5_sort_is_bag(Cvc5Sort sort);

/**
 * Determine if given sort is a Sequence sort.
 * @param sort The sort.
 * @return True if the sort is a Sequence sort.
 */
CVC5_EXPORT bool cvc5_sort_is_sequence(Cvc5Sort sort);

/**
 * Determine if given sort is an abstract sort.
 * @param sort The sort.
 * @return True if the sort is a abstract sort.
 *
 * @warning This function is experimental and may change in future versions.
 */
CVC5_EXPORT bool cvc5_sort_is_abstract(Cvc5Sort sort);

/**
 * Determine if given sort is an uninterpreted sort.
 * @param sort The sort.
 * @return True if given sort is an uninterpreted sort.
 */
CVC5_EXPORT bool cvc5_sort_is_uninterpreted_sort(Cvc5Sort sort);

/**
 * Determine if given sort is an uninterpreted sort constructor.
 *
 * An uninterpreted sort constructor has arity > 0 and can be instantiated to
 * construct uninterpreted sorts with given sort parameters.
 *
 * @param sort The sort.
 * @return True if given sort is of sort constructor kind.
 */
CVC5_EXPORT bool cvc5_sort_is_uninterpreted_sort_constructor(Cvc5Sort sort);

/**
 * Determine if given sort is an instantiated (parametric datatype or
 * uninterpreted sort constructor) sort.
 *
 * An instantiated sort is a sort that has been constructed from
 * instantiating a sort with sort arguments (see cvc5_sort_instantiate().
 *
 * @param sort The sort.
 * @return True if given sort is an instantiated sort.
 */
CVC5_EXPORT bool cvc5_sort_is_instantiated(Cvc5Sort sort);

/**
 * Get the associated uninterpreted sort constructor of an instantiated
 * uninterpreted sort.
 *
 * @param sort The sort.
 * @return The uninterpreted sort constructor sort.
 */
CVC5_EXPORT Cvc5Sort
cvc5_sort_get_uninterpreted_sort_constructor(Cvc5Sort sort);

/**
 * Get the underlying datatype of a datatype sort.
 * @param sort The sort.
 * @return The underlying datatype of a datatype sort.
 */
CVC5_EXPORT Cvc5Datatype cvc5_sort_get_datatype(Cvc5Sort sort);

/**
 * Instantiate a parameterized datatype sort or uninterpreted sort
 * constructor sort.
 *
 * Create sort parameters with cvc5_mk_param_sort().
 *
 * @param sort   The sort to instantiate.
 * @param size   The number of sort parameters to instantiate with.
 * @param params The list of sort parameters to instantiate with.
 * @return The instantiated sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_instantiate(Cvc5Sort sort,
                                           size_t size,
                                           const Cvc5Sort params[]);

/**
 * Get the sorts used to instantiate the sort parameters of a given parametric
 * sort (parametric datatype or uninterpreted sort constructor sort,
 * see cvc5_sort_instantiate();
 *
 * @param sort The sort.
 * @param size The size of the resulting array of sorts.
 * @return The sorts used to instantiate the sort parameters of a
 *         parametric sort
 */
CVC5_EXPORT const Cvc5Sort* cvc5_sort_get_instantiated_parameters(Cvc5Sort sort,
                                                                  size_t* size);

/**
 * Substitution of Sorts.
 *
 * Note that this replacement is applied during a pre-order traversal and
 * only once to the sort. It is not run until fix point.
 *
 * For example,
 * `(Array A B).substitute({A, C}, {(Array C D), (Array A B)})` will
 * return `(Array (Array C D) B)`.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param sort The sort.
 * @param s    The subsort to be substituted within the given sort.
 * @param replacement The sort replacing the substituted subsort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_substitute(Cvc5Sort sort,
                                          Cvc5Sort s,
                                          Cvc5Sort replacement);

/**
 * Simultaneous substitution of Sorts.
 *
 * Note that this replacement is applied during a pre-order traversal and
 * only once to the sort. It is not run until fix point. In the case that
 * sorts contains duplicates, the replacement earliest in the vector takes
 * priority.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param sort The sort.
 * @param sorts The subsorts to be substituted within the given sort.
 * @param replacements The sort replacing the substituted subsorts.
 * @param size The size of `sorts` and `replacements`.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_substitute_sorts(Cvc5Sort sort,
                                                size_t size,
                                                const Cvc5Sort sorts[],
                                                const Cvc5Sort replacements[]);

/**
 * Get a string representation of a given sort.
 * @param sort The sort.
 * @return A string representation of the given sort.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_sort_to_string(Cvc5Sort sort);

/**
 * Compute the hash value of a sort.
 * @param sort The sort.
 * @return The hash value of the sort.
 */
CVC5_EXPORT size_t cvc5_sort_hash(Cvc5Sort sort);

/* Datatype constructor sort ------------------------------------------- */

/**
 * Get the arity of a datatype constructor sort.
 * @param sort The sort.
 * @return The arity of a datatype constructor sort.
 */
CVC5_EXPORT size_t cvc5_sort_dt_constructor_get_arity(Cvc5Sort sort);

/**
 * Get the domain sorts of a datatype constructor sort.
 * @param sort The sort.
 * @param size The size of the resulting array of domain sorts.
 * @return The domain sorts of a datatype constructor sort.
 */
CVC5_EXPORT const Cvc5Sort* cvc5_sort_dt_constructor_get_domain(Cvc5Sort sort,
                                                                size_t* size);

/**
 * Get the codomain sort of a datatype constructor sort.
 * @param sort The sort.
 * @return The codomain sort of a constructor sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_dt_constructor_get_codomain(Cvc5Sort sort);

/* Dataype Selector sort ------------------------------------------------ */

/**
 * Get the domain sort of a given datatype selector sort.
 * @param sort The sort.
 * @return The domain sort of a datatype selector sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_dt_selector_get_domain(Cvc5Sort sort);

/**
 * Get the codomain sort of a given datatype selector sort.
 * @param sort The sort.
 * @return The codomain sort of a datatype selector sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_dt_selector_get_codomain(Cvc5Sort sort);

/* Datatype Tester sort ------------------------------------------------ */

/**
 * Get the domain sort of a given datatype tester sort.
 * @param sort The sort.
 * @return The domain sort of a datatype tester sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_dt_tester_get_domain(Cvc5Sort sort);

/**
 * Get the codomain dort of a given datatype tester sort (the Boolean sort).
 * @param sort The sort.
 * @return The codomain sort of a datatype tester sort.
 *
 * @note We mainly need this for the symbol table, which doesn't have
 *       access to the solver object.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_dt_tester_get_codomain(Cvc5Sort sort);

/* Function sort ------------------------------------------------------- */

/**
 * Get the aritye of a given function sort.
 * @param sort The sort.
 * @return The arity of a function sort.
 */
CVC5_EXPORT size_t cvc5_sort_fun_get_arity(Cvc5Sort sort);

/**
 * Get the domain of a given function sort.
 * @param sort The sort.
 * @param size The size of the resulting array of domain sorts.
 * @return The domain sorts of a function sort.
 */
CVC5_EXPORT const Cvc5Sort* cvc5_sort_fun_get_domain(Cvc5Sort sort,
                                                     size_t* size);

/**
 * Get the codomain of a given function sort.
 * @param sort The sort.
 * @return The codomain sort of a function sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_fun_get_codomain(Cvc5Sort sort);

/* Array sort ---------------------------------------------------------- */

/**
 * Get the index sort of a given array sort.
 * @param sort The sort.
 * @return The array index sort of an array sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_array_get_index_sort(Cvc5Sort sort);

/**
 * Get the element sort of a given array sort.
 * @param sort The sort.
 * @return The array element sort of an array sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_array_get_element_sort(Cvc5Sort sort);

/* Set sort ------------------------------------------------------------ */

/**
 * Get the element sort of a given set sort.
 * @param sort The sort.
 * @return The element sort of a set sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_set_get_element_sort(Cvc5Sort sort);

/* Bag sort ------------------------------------------------------------ */

/**
 * Get the element sort of a given bag sort.
 * @param sort The sort.
 * @return The element sort of a bag sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_bag_get_element_sort(Cvc5Sort sort);

/* Sequence sort ------------------------------------------------------- */

/**
 * Get the element sort of a sequence sort.
 * @param sort The sort.
 * @return The element sort of a sequence sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_sequence_get_element_sort(Cvc5Sort sort);

/* Abstract sort ------------------------------------------------------- */

/**
 * Get the kind of an abstract sort, which denotes the sort kinds that the
 * abstract sort denotes.
 *
 * @param sort The sort.
 * @return The kind of an abstract sort.
 *
 * @warning This function is experimental and may change in future versions.
 */
CVC5_EXPORT Cvc5SortKind cvc5_sort_abstract_get_kind(Cvc5Sort sort);

/* Uninterpreted sort constructor sort --------------------------------- */

/**
 * Get the arity of an uninterpreted sort constructor sort.
 * @param sort The sort.
 * @return The arity of an uninterpreted sort constructor sort.
 */
CVC5_EXPORT size_t
cvc5_sort_uninterpreted_sort_constructor_get_arity(Cvc5Sort sort);

/* Bit-vector sort ----------------------------------------------------- */

/**
 * Get the size of a bit-vector sort.
 * @param sort The sort.
 * @return The bit-width of the bit-vector sort.
 */
CVC5_EXPORT uint32_t cvc5_sort_bv_get_size(Cvc5Sort sort);

/* Finite field sort --------------------------------------------------- */

/**
 * Get the size of a finite field sort.
 * @param sort The sort.
 * @return The size of the finite field sort.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_sort_ff_get_size(Cvc5Sort sort);

/* Floating-point sort ------------------------------------------------- */

/**
 * Get the exponent size of a floating-point sort.
 * @param sort The sort.
 * @return The bit-width of the exponent of the floating-point sort.
 */
CVC5_EXPORT uint32_t cvc5_sort_fp_get_exp_size(Cvc5Sort sort);

/**
 * Get the significand size of a floating-point sort.
 * @param sort The sort.
 * @return The width of the significand of the floating-point sort.
 */
CVC5_EXPORT uint32_t cvc5_sort_fp_get_sig_size(Cvc5Sort sort);

/* Datatype sort ------------------------------------------------------- */

/**
 * Get the arity of a datatype sort, which is the number of type parameters
 * if the datatype is parametric, or 0 otherwise.
 * @param sort The sort.
 * @return The arity of a datatype sort.
 */
CVC5_EXPORT size_t cvc5_sort_dt_get_arity(Cvc5Sort sort);

/* Tuple sort ---------------------------------------------------------- */

/**
 * Get the length of a tuple sort.
 * @param sort The sort.
 * @return The length of a tuple sort.
 */
CVC5_EXPORT size_t cvc5_sort_tuple_get_length(Cvc5Sort sort);

/**
 * Get the element sorts of a tuple sort.
 * @param sort The sort.
 * @param size The size of the resulting array of tuple element sorts.
 * @return The element sorts of a tuple sort.
 */
CVC5_EXPORT const Cvc5Sort* cvc5_sort_tuple_get_element_sorts(Cvc5Sort sort,
                                                              size_t* size);

/**
 * Get the element sort of a nullable sort.
 * @param sort The sort.
 * @return The element sort of a nullable sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_sort_nullable_get_element_sort(Cvc5Sort sort);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Op                                                                     */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5op
 *  @{
 */

/**
 * Make copy of operator, increases reference counter of `op`.
 *
 * @param op The op to copy.
 * @return The same op with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5Op cvc5_op_copy(Cvc5Op op);

/**
 * Release copy of operator, decrements reference counter of `op`.
 *
 * @param op The op to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a
 *       Cvc5Op returns a copy that is owned by the callee of the function
 *       and thus, can be released.
 */
CVC5_EXPORT void cvc5_op_release(Cvc5Op op);

/**
 * Compare two operators for syntactic equality.
 *
 * @param a The first operator.
 * @param b The second operator.
 * @return True if both operators are syntactically identical.
 */
CVC5_EXPORT bool cvc5_op_is_equal(Cvc5Op a, Cvc5Op b);

/**
 * Compare two operators for syntactic disequality.
 *
 * @param a The first operator.
 * @param b The second operator.
 * @return True if both operators are syntactically disequal.
 */
CVC5_EXPORT bool cvc5_op_is_disequal(Cvc5Op a, Cvc5Op b);

/**
 * Get the kind of a given operator.
 * @param op The operator.
 * @return The kind of the operator.
 */
CVC5_EXPORT Cvc5Kind cvc5_op_get_kind(Cvc5Op op);

/**
 * Determine if a given operator is indexed.
 * @param op The operator.
 * @return True iff the operator is indexed.
 */
CVC5_EXPORT bool cvc5_op_is_indexed(Cvc5Op op);

/**
 * Get the number of indices of a given operator.
 * @param op The operator.
 * @return The number of indices of the operator.
 */
CVC5_EXPORT size_t cvc5_op_get_num_indices(Cvc5Op op);

/**
 * Get the index at position `i` of an indexed operator.
 * @param op The operator.
 * @param i  The position of the index to return.
 * @return The index at position i.
 */
CVC5_EXPORT Cvc5Term cvc5_op_get_index(Cvc5Op op, size_t i);

/**
 * Get a string representation of a given operator.
 * @param op The operator.
 * @return A string representation of the operator.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_op_to_string(Cvc5Op op);

/**
 * Compute the hash value of an operator.
 * @param op The operator.
 * @return The hash value of the operator.
 */
CVC5_EXPORT size_t cvc5_op_hash(Cvc5Op op);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Term                                                                   */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5term
 *  @{
 */

/**
 * Make copy of term, increases reference counter of `term`.
 *
 * @param term The term to copy.
 * @return The same term with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5Term cvc5_term_copy(Cvc5Term term);

/**
 * Release copy of term, decrements reference counter of `term`.
 *
 * @param term The term to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a copy
 *       that is owned by the callee of the function and thus, can be released.
 */
CVC5_EXPORT void cvc5_term_release(Cvc5Term term);

/**
 * Compare two terms for syntactic equality.
 * @param a The first term.
 * @param b The second term.
 * @return True if both term are syntactically identical.
 */
CVC5_EXPORT bool cvc5_term_is_equal(Cvc5Term a, Cvc5Term b);

/**
 * Compare two terms for syntactic disequality.
 * @param a The first term.
 * @param b The second term.
 * @return True if both term are syntactically disequal.
 */
CVC5_EXPORT bool cvc5_term_is_disequal(Cvc5Term a, Cvc5Term b);

/**
 * Compare two terms for ordering.
 * @param a The first term.
 * @param b The second term.
 * @return An integer value indicating the ordering: 0 if both terms are equal,
 *         `-1` if `a < b`, and `1` if `b > a`.
 */
CVC5_EXPORT int64_t cvc5_term_compare(Cvc5Term a, Cvc5Term b);

/**
 * Get the number of children of a given term.
 * @param term The term.
 * @return The number of children of this term.
 */
CVC5_EXPORT size_t cvc5_term_get_num_children(Cvc5Term term);

/**
 * Get the child term of a given term at a given index.
 * @param term  The term.
 * @param index The index of the child.
 * @return The child term at the given index.
 */
CVC5_EXPORT Cvc5Term cvc5_term_get_child(Cvc5Term term, size_t index);

/**
 * Get the id of a given term.
 * @param term The term.
 * @return The id of the term.
 */
CVC5_EXPORT uint64_t cvc5_term_get_id(Cvc5Term term);

/**
 * Get the kind of a given term.
 * @param term The term.
 * @return The kind of the term.
 */
CVC5_EXPORT Cvc5Kind cvc5_term_get_kind(Cvc5Term term);

/**
 * Get the sort of a given term.
 * @param term The term.
 * @return The sort of the term.
 */
CVC5_EXPORT Cvc5Sort cvc5_term_get_sort(Cvc5Term term);

/**
 * Replace a given term `t` with term `replacement` in a given term.
 *
 * @param term        The term.
 * @param t           The term to replace.
 * @param replacement The term to replace it with.
 * @return The result of replacing `term` with `replacement` in the term.
 *
 * @note This replacement is applied during a pre-order traversal and
 *       only once (it is not run until fixed point).
 */
CVC5_EXPORT Cvc5Term cvc5_term_substitute_term(Cvc5Term term,
                                               Cvc5Term t,
                                               Cvc5Term replacement);

/**
 * Simultaneously replace given terms `terms` with terms `replacements` in a
 * given term.
 *
 * In the case that `terms` contains duplicates, the replacement earliest in
 * the vector takes priority. For example, calling substitute on `f(x,y)`
 * with `terms = { x, z }`, `replacements = { g(z), w }` results in the term
 * `f(g(z),y)`.
 *
 * @note Requires that `terms` and `replacements` are of equal size (they are
 *       interpreted as 1 : 1 mapping).
 *
 * @note This replacement is applied during a pre-order traversal and
 *       only once (it is not run until fixed point).
 *
 * @param term        The term.
 * @param size         The size of `terms` and `replacements`.
 * @param terms        The terms to replace.
 * @param replacements The replacement terms.
 * @return The result of simultaneously replacing `terms` with `replacements`
 *         in the given term.
 */
CVC5_EXPORT Cvc5Term cvc5_term_substitute_terms(Cvc5Term term,
                                                size_t size,
                                                const Cvc5Term terms[],
                                                const Cvc5Term replacements[]);

/**
 * Determine if a given term has an operator.
 * @param term The term.
 * @return True iff the term has an operator.
 */
CVC5_EXPORT bool cvc5_term_has_op(Cvc5Term term);

/**
 * Get the operator of a term with an operator.
 *
 * @note Requires that the term has an operator (see cvc5_term_has_op()).
 *
 * @param term        The term.
 * @return The Op used to create the term.
 */
CVC5_EXPORT Cvc5Op cvc5_term_get_op(Cvc5Term term);

/**
 * Determine if a given term has a symbol (a name).
 *
 * For example, free constants and variables have symbols.
 *
 * @param term The term.
 * @return True if the term has a symbol.
 */
CVC5_EXPORT bool cvc5_term_has_symbol(Cvc5Term term);

/**
 * Get the symbol of a given term with a symbol.
 *
 * @note Requires that the term has a symbol (see cvc5_term_has_symbol()).
 *
 * The symbol of the term is the string that was
 * provided when constructing it via cvc5_mk_const() or cvc5_mk_var().
 *
 * @param term The term.
 * @return The raw symbol of the term.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_term_get_symbol(Cvc5Term term);

/**
 * Get a string representation of a given term.
 * @param term The term.
 * @return A string representation of the term.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_term_to_string(Cvc5Term term);

/**
 * Get the sign of a given integer or real value.
 * @note Requires that given term is an integer or real value.
 * @param term The value term.
 * @return 0 if the term is zero, -1 if the term is a negative real or
 *         integer value, 1 if the term is a positive real or integer value.
 */
CVC5_EXPORT int32_t cvc5_term_get_real_or_integer_value_sign(Cvc5Term term);
/**
 * Determine if a given term is an int32 value.
 * @note This will return true for integer constants and real constants that
 *       have integer value.
 * @param term The term.
 * @return True if the term is an integer value that fits within int32_t.
 */
CVC5_EXPORT bool cvc5_term_is_int32_value(Cvc5Term term);
/**
 * Get the `int32_t` representation of a given integral value.
 * @note Requires that the term is an int32 value (see
 *       cvc5_term_is_int32_value()).
 * @param term The term.
 * @return The given term as `int32_t` value.
 */
CVC5_EXPORT int32_t cvc5_term_get_int32_value(Cvc5Term term);
/**
 * Determine if a given term is an uint32 value.
 * @note This will return true for integer constants and real constants that
 *       have integral value.
 * @return True if the term is an integral value and fits within uint32_t.
 */
CVC5_EXPORT bool cvc5_term_is_uint32_value(Cvc5Term term);
/**
 * Get the `uint32_t` representation of a given integral value.
 * @note Requires that the term is an uint32 value (see
 *       cvc5_term_is_uint32_value()).
 * @param term The term.
 * @return The term as `uint32_t` value.
 */
CVC5_EXPORT uint32_t cvc5_term_get_uint32_value(Cvc5Term term);
/**
 * Determine if a given term is an int64 value.
 * @note This will return true for integer constants and real constants that
 *       have integral value.
 * @param term The term.
 * @return True if the term is an integral value that fits within int64_t.
 */
CVC5_EXPORT bool cvc5_term_is_int64_value(Cvc5Term term);
/**
 * Get the `int64_t` representation of a given integral value.
 * @note Requires that the term is an int64 value (see
 *       cvc5_term_is_int64_value()).
 * @param term The term.
 * @return The term as `int64_t` value.
 */
CVC5_EXPORT int64_t cvc5_term_get_int64_value(Cvc5Term term);
/**
 * Determine if a given term is an uint64 value.
 * @note This will return true for integer constants and real constants that
 *       have integral value.
 * @param term The term.
 * @return True if the term is an integral value that fits within uint64_t.
 */
CVC5_EXPORT bool cvc5_term_is_uint64_value(Cvc5Term term);
/**
 * Get the `uint64_t` representation of a given integral value.
 * @note Requires that the term is an uint64 value (see
 *       cvc5_term_is_uint64_value()).
 * @param term The term.
 * @return The term as `uint64_t` value.
 */
CVC5_EXPORT uint64_t cvc5_term_get_uint64_value(Cvc5Term term);
/**
 * Determine if a given term is an integral value.
 * @param term The term.
 * @return True if the term is an integer constant or a real constant that
 *         has an integral value.
 */
CVC5_EXPORT bool cvc5_term_is_integer_value(Cvc5Term term);
/**
 * Get a string representation of a given integral value.
 * @note Requires that the term is an integral value (see
 *       cvc5_term_is_integer_value()).
 * @param term The term.
 * @return The integral term in (decimal) string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_term_get_integer_value(Cvc5Term term);

/**
 * Determine if a given term is a string value.
 * @param term The term.
 * @return True if the term is a string value.
 */
CVC5_EXPORT bool cvc5_term_is_string_value(Cvc5Term term);
/**
 * Get the native string representation of a string value.
 * @note Requires that the term is a string value (see
 *       cvc5_term_is_string_value()).
 * @note This is not to be confused with cvc5_term_to_string(), which returns
 *       some string representation of the term, whatever data it may hold.
 * @param term The term.
 * @return The string term as a native string value.
 *
 * @warning This function is deprecated and replaced by
 *          cvc5_term_get_u32string_value(). It will be removed in a future
 *          release.
 */
CVC5_EXPORT __attribute__((deprecated("Use cvc5_term_get_u32string_value instead")))
const wchar_t* cvc5_term_get_string_value(Cvc5Term term);

/**
 * Get the native UTF-32 string representation of a string value.
 * @note Requires that the term is a string value (see
 *       cvc5_term_is_string_value()).
 * @note This is not to be confused with cvc5_term_to_string(), which returns
 *       some string representation of the term, whatever data it may hold.
 * @param term The term.
 * @return The string term as a native UTF-32 string value.
 */
CVC5_EXPORT const char32_t* cvc5_term_get_u32string_value(Cvc5Term term);

/**
 * Determine if a given term is a rational value whose numerator fits into an
 * int32 value and its denominator fits into a uint32 value.
 * @param term The term.
 * @return True if the term is a rational and its numerator and denominator
 *         fit into 32 bit integer values.
 */
CVC5_EXPORT bool cvc5_term_is_real32_value(Cvc5Term term);
/**
 * Get the 32 bit integer representations of the numerator and denominator of
 * a rational value.
 * @note Requires that the term is a rational value and its numerator and
 *       denominator fit into 32 bit integer values (see
 *       cvc5_term_is_real32_value()).
 * @param term The term.
 * @param num  The resulting int32_t representation of the numerator.
 * @param den  The resulting uint32_t representation of the denominator.
 */
CVC5_EXPORT void cvc5_term_get_real32_value(Cvc5Term term,
                                            int32_t* num,
                                            uint32_t* den);
/**
 * Determine if a given term is a rational value whose numerator fits into an
 * int64 value and its denominator fits into a uint64 value.
 * @param term The term.
 * @return True if the term is a rational value whose numerator and
 *         denominator fit within int64_t and uint64_t, respectively.
 */
CVC5_EXPORT bool cvc5_term_is_real64_value(Cvc5Term term);
/**
 * Get the 64 bit integer representations of the numerator and denominator of
 * a rational value.
 * @note Requires that the term is a rational value and its numerator and
 *       denominator fit into 64 bit integer values (see
 *       cvc5_term_is_real64_value()).
 * @param term The term.
 * @param num  The resulting int64_t representation of the numerator.
 * @param den  The resulting uint64_t representation of the denominator.
 */
CVC5_EXPORT void cvc5_term_get_real64_value(Cvc5Term term,
                                            int64_t* num,
                                            uint64_t* den);
/**
 * Determine if a given term is a rational value.
 * @note A term of kind PI is not considered to be a real value.
 * @param term The term.
 * @return True if the term is a rational value.
 */
CVC5_EXPORT bool cvc5_term_is_real_value(Cvc5Term term);
/**
 * Get a string representation of a given rational value.
 * @note Requires that the term is a rational value (see
 *       cvc5_term_is_real_value()).
 * @param term The term.
 * @return The representation of a rational value as a (rational) string.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_term_get_real_value(Cvc5Term term);

/**
 * Determine if a given term is a constant array.
 * @param term The term.
 * @return True if the term is a constant array.
 */
CVC5_EXPORT bool cvc5_term_is_const_array(Cvc5Term term);
/**
 * Determine the base (element stored at all indices) of a constant array.
 * @note Requires that the term is a constant array (see isConstArray()).
 * @param term The term.
 * @return The base term.
 */
CVC5_EXPORT Cvc5Term cvc5_term_get_const_array_base(Cvc5Term term);

/**
 * Determine if a given term is a Boolean value.
 * @param term The term.
 * @return True if the term is a Boolean value.
 */
CVC5_EXPORT bool cvc5_term_is_boolean_value(Cvc5Term term);
/**
 * Get the value of a Boolean term as a native Boolean value.
 * @note Asserts cvc5_term_is_boolean_value().
 * @param term The term.
 * @return The representation of a Boolean value as a native Boolean value.
 */
CVC5_EXPORT bool cvc5_term_get_boolean_value(Cvc5Term term);

/**
 * Determine if a given term is a bit-vector value.
 * @param term The term.
 * @return True if the term is a bit-vector value.
 */
CVC5_EXPORT bool cvc5_term_is_bv_value(Cvc5Term term);
/**
 * Get the string representation of a bit-vector value.
 * @note Asserts cvc5_term_is_bv_value().
 * @param term The term.
 * @param base `2` for binary, `10` for decimal, and `16` for hexadecimal.
 * @return The string representation of a bit-vector value.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_term_get_bv_value(Cvc5Term term, uint32_t base);

/**
 * Determine if a given term is a finite field value.
 * @param term The term.
 * @return True if the term is a finite field value.
 */
CVC5_EXPORT bool cvc5_term_is_ff_value(Cvc5Term term);
/**
 * Get the string representation of a finite field value (base 10).
 *
 * @note Asserts cvc5_term_is_ff_value().
 *
 * @note Uses the integer representative of smallest absolute value.
 *
 * @param term The term.
 * @return The string representation of the integer representation of the
 *         finite field value.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_term_get_ff_value(Cvc5Term term);

/**
 * Determine if a given term is an uninterpreted sort value.
 * @param term The term.
 * @return True if the term is an abstract value.
 */
CVC5_EXPORT bool cvc5_term_is_uninterpreted_sort_value(Cvc5Term term);
/**
 * Get a string representation of an uninterpreted sort value.
 * @note Asserts cvc5_term_is_uninterpreted_sort_value().
 * @param term The term.
 * @return The representation of an uninterpreted sort value as a string.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_term_get_uninterpreted_sort_value(Cvc5Term term);

/**
 * Determine if a given term is a tuple value.
 * @param term The term.
 * @return True if the term is a tuple value.
 */
CVC5_EXPORT bool cvc5_term_is_tuple_value(Cvc5Term term);
/**
 * Get a tuple value as an array of terms.
 * @note Asserts cvc5_term_is_tuple_value().
 * @param term The term.
 * @param size The size of the resulting array.
 * @return The representation of a tuple value as an array of terms.
 */
CVC5_EXPORT const Cvc5Term* cvc5_term_get_tuple_value(Cvc5Term term,
                                                      size_t* size);

/**
 * Determine if a given term is a floating-point rounding mode value.
 * @param term The term.
 * @return True if the term is a rounding mode value.
 */
CVC5_EXPORT bool cvc5_term_is_rm_value(Cvc5Term term);
/**
 * Get the Cvc5RoundingMode value of a given rounding-mode value term.
 * @note Asserts cvc5_term_is_rounding_mode_value().
 * @param term The term.
 * @return The floating-point rounding mode value of the term.
 */
CVC5_EXPORT Cvc5RoundingMode cvc5_term_get_rm_value(Cvc5Term term);

/**
 * Determine if a given term is a floating-point positive zero value
 * (+zero).
 * @param term The term.
 * @return True if the term is the floating-point value for positive zero.
 */
CVC5_EXPORT bool cvc5_term_is_fp_pos_zero(Cvc5Term term);
/**
 * Determine if a given term is a floating-point negative zero value (-zero).
 * @param term The term.
 * @return True if the term is the floating-point value for negative zero.
 */
CVC5_EXPORT bool cvc5_term_is_fp_neg_zero(Cvc5Term term);
/**
 * Determine if a given term is a floating-point positive infinity value (+oo).
 * @param term The term.
 * @return True if the term is the floating-point value for positive.
 *         infinity.
 */
CVC5_EXPORT bool cvc5_term_is_fp_pos_inf(Cvc5Term term);
/**
 * Determine if a given term is a floating-point negative infinity value (-oo).
 * @param term The term.
 * @return True if the term is the floating-point value for negative.
 *         infinity.
 */
CVC5_EXPORT bool cvc5_term_is_fp_neg_inf(Cvc5Term term);
/**
 * Determine if a given term is a floating-point NaN value.
 * @param term The term.
 * @return True if the term is the floating-point value for not a number.
 */
CVC5_EXPORT bool cvc5_term_is_fp_nan(Cvc5Term term);
/**
 * Determine if a given term is a floating-point value.
 * @param term The term.
 * @return True if the term is a floating-point value.
 */
CVC5_EXPORT bool cvc5_term_is_fp_value(Cvc5Term term);
/**
 * Get the representation of a floating-point value as its exponent width,
 * significand width and a bit-vector value term.
 * @note Asserts cvc5_term_is_fp_value().
 * @param term The term.
 * @param ew   The resulting exponent width.
 * @param sw   The resulting significand width.
 * @param val  The resulting bit-vector value term.
 */
CVC5_EXPORT void cvc5_term_get_fp_value(Cvc5Term term,
                                        uint32_t* ew,
                                        uint32_t* sw,
                                        Cvc5Term* val);

/**
 * Determine if a given term is a set value.
 *
 * A term is a set value if it is considered to be a (canonical) constant set
 * value.  A canonical set value is one whose AST is:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
 * \endverbatim
 *
 * where @f$c_1 ... c_n@f$ are values ordered by id such that
 * @f$c_1 > ... > c_n@f$.
 *
 * @note A universe set term (kind #CVC5_KIND_SET_UNIVERSE) is not considered
 *       to be a set value.
 *
 * @param term The term.
 * @return True if the term is a set value.
 */
CVC5_EXPORT bool cvc5_term_is_set_value(Cvc5Term term);
/**
 * Get a set value as an array of terms.
 * @note Asserts cvc5_term_is_set_value().
 * @param term The term.
 * @param size The size of the resulting array.
 * @return The representation of a set value as an array of terms.
 */
CVC5_EXPORT const Cvc5Term* cvc5_term_get_set_value(Cvc5Term term,
                                                    size_t* size);

/**
 * Determine if a given term is a sequence value.
 *
 * A term is a sequence value if it has kind #CVC5_KIND_CONST_SEQUENCE. In
 * contrast to values for the set sort (as described in isSetValue()), a
 * sequence value is represented as a Term with no children.
 *
 * Semantically, a sequence value is a concatenation of unit sequences
 * whose elements are themselves values. For example:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (seq.++ (seq.unit 0) (seq.unit 1))
 * \endverbatim
 *
 * The above term has two representations in Term. One is as the sequence
 * concatenation term:
 *
 * \rst
 * .. code:: lisp
 *
 *     (SEQ_CONCAT (SEQ_UNIT 0) (SEQ_UNIT 1))
 * \endrst
 *
 * where 0 and 1 are the terms corresponding to the integer constants 0 and 1.
 *
 * Alternatively, the above term is represented as the constant sequence
 * value:
 *
 * \rst
 * .. code:: lisp
 *
 *     CONST_SEQUENCE_{0,1}
 * \endrst
 *
 * where calling getSequenceValue() on the latter returns the vector `{0, 1}`.
 *
 * The former term is not a sequence value, but the latter term is.
 *
 * Constant sequences cannot be constructed directly via the API. They are
 * returned in response to API calls such cvc5_get_value() and cvc5_simplify().
 *
 * @param term The term.
 * @return True if the term is a sequence value.
 */
CVC5_EXPORT bool cvc5_term_is_sequence_value(Cvc5Term term);
/**
 * Get a sequence value as an array of terms.
 * @note Asserts cvc5_term_is_sequence_value().
 * @param term The term.
 * @param size The size of the resulting array.
 * @return The representation of a sequence value as a vector of terms.
 */
CVC5_EXPORT const Cvc5Term* cvc5_term_get_sequence_value(Cvc5Term term,
                                                         size_t* size);

/**
 * Determine if a given term is a cardinality constraint.
 * @param term The term.
 * @return True if the term is a cardinality constraint.
 */
CVC5_EXPORT bool cvc5_term_is_cardinality_constraint(Cvc5Term term);
/**
 * Get a cardinality constraint as a pair of its sort and upper bound.
 * @note Asserts cvc5_term_is_cardinality_constraint().
 * @param term  The term.
 * @param sort  The resulting sort.
 * @param upper The resulting upper bound.
 */
CVC5_EXPORT void cvc5_term_get_cardinality_constraint(Cvc5Term term,
                                                      Cvc5Sort* sort,
                                                      uint32_t* upper);

/**
 * Determine if a given term is a real algebraic number.
 * @param term  The term.
 * @return True if the term is a real algebraic number.
 */
CVC5_EXPORT bool cvc5_term_is_real_algebraic_number(Cvc5Term term);
/**
 * Get the defining polynomial for a real algebraic number term, expressed in
 * terms of the given variable.
 * @note Asserts cvc5_term_is_real_algebraic_number().
 * @param term The real algebraic number term.
 * @param v    The variable over which to express the polynomial.
 * @return The defining polynomial.
 */
CVC5_EXPORT Cvc5Term cvc5_term_get_real_algebraic_number_defining_polynomial(
    Cvc5Term term, Cvc5Term v);
/**
 * Get the lower bound for a real algebraic number value.
 * @note Asserts cvc5_term_is_real_algebraic_number().
 * @param term The real algebraic number value.
 * @return The lower bound.
 */
CVC5_EXPORT Cvc5Term
cvc5_term_get_real_algebraic_number_lower_bound(Cvc5Term term);
/**
 * Get the upper bound for a real algebraic number value.
 * @note Asserts cvc5_term_is_real_algebraic_number().
 * @param term The real algebraic number value.
 * @return The upper bound.
 */
CVC5_EXPORT Cvc5Term
cvc5_term_get_real_algebraic_number_upper_bound(Cvc5Term term);

/**
 * Is the given term a skolem?
 * @warning This function is experimental and may change in future versions.
 * @param term The skolem.
 * @return True if the term is a skolem function.
 */
CVC5_EXPORT bool cvc5_term_is_skolem(Cvc5Term term);
/**
 * Get skolem identifier of a term.
 * @note Asserts isSkolem().
 * @warning This function is experimental and may change in future versions.
 * @param term The skolem.
 * @return The skolem identifier of the term.
 */
CVC5_EXPORT Cvc5SkolemId cvc5_term_get_skolem_id(Cvc5Term term);
/**
 * Get the skolem indices of a term.
 * @note Asserts isSkolem().
 * @warning This function is experimental and may change in future versions.
 * @param term The skolem.
 * @param size The size of the resulting array.
 * @return The skolem indices of the term. This is list of terms that the
 *         skolem function is indexed by. For example, the array diff skolem
 *         `Cvc5SkolemId::ARRAY_DEQ_DIFF` is indexed by two arrays.
 */
CVC5_EXPORT const Cvc5Term* cvc5_term_get_skolem_indices(Cvc5Term term,
                                                         size_t* size);

/**
 * Compute the hash value of a term.
 * @param term The term.
 * @return The hash value of the term.
 */
CVC5_EXPORT size_t cvc5_term_hash(Cvc5Term term);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5DatatypeConstructorDecl                                                */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5dtconsdecl
 *  @{
 */

/**
 * Make copy of datatype constructor declaration, increases reference counter
 * of `decl`.
 *
 * @param decl The datatype constructor declaration to copy.
 * @return The same datatype constructor declaration with its reference count
 *         increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5DatatypeConstructorDecl
cvc5_dt_cons_decl_copy(Cvc5DatatypeConstructorDecl decl);

/**
 * Release copy of datatype constructor declaration, decrements reference
 * counter of `decl`.
 *
 * @param decl The datatype constructor declaration to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a
 *       Cvc5DatatypeConstructorDecl returns a copy that is owned by the callee
 *       of the function and thus, can be released.
 */
CVC5_EXPORT void cvc5_dt_cons_decl_release(Cvc5DatatypeConstructorDecl decl);

/**
 * Compare two datatype constructor declarations for structural equality.
 * @param a The first datatype constructor declaration.
 * @param b The second datatype constructor declaration.
 * @return True if the datatype constructor declarations are equal.
 */
CVC5_EXPORT bool cvc5_dt_cons_decl_is_equal(Cvc5DatatypeConstructorDecl a,
                                            Cvc5DatatypeConstructorDecl b);

/**
 * Add datatype selector declaration to a given constructor declaration.
 * @param decl The datatype constructor declaration.
 * @param name The name of the datatype selector declaration to add.
 * @param sort The codomain sort of the datatype selector declaration to add.
 */
CVC5_EXPORT void cvc5_dt_cons_decl_add_selector(
    Cvc5DatatypeConstructorDecl decl, const char* name, Cvc5Sort sort);
/**
 * Add datatype selector declaration whose codomain type is the datatype
 * itself to a given constructor declaration.
 * @param decl The datatype constructor declaration.
 * @param name The name of the datatype selector declaration to add.
 */
CVC5_EXPORT void cvc5_dt_cons_decl_add_selector_self(
    Cvc5DatatypeConstructorDecl decl, const char* name);

/**
 * Add datatype selector declaration whose codomain sort is an unresolved
 * datatype with the given name to a given constructor declaration.
 * @param decl       The datatype constructor declaration.
 * @param name       The name of the datatype selector declaration to add.
 * @param unres_name The name of the unresolved datatype. The codomain of the
 *                   selector will be the resolved datatype with the given name.
 */
CVC5_EXPORT void cvc5_dt_cons_decl_add_selector_unresolved(
    Cvc5DatatypeConstructorDecl decl, const char* name, const char* unres_name);
/**
 * Get a string representation of a given constructor declaration.
 * @param decl The datatype constructor declaration.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_cons_decl_to_string(
    Cvc5DatatypeConstructorDecl decl);

/**
 * Compute the hash value of a datatype constructor declaration.
 * @param decl The datatype constructor declaration.
 * @return The hash value of the datatype constructor declaration.
 */
CVC5_EXPORT size_t cvc5_dt_cons_decl_hash(Cvc5DatatypeConstructorDecl decl);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5DatatypeDecl                                                           */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5dtdecl
 *  @{
 */

/**
 * Make copy of datatype declaration, increases reference counter of `decl`.
 *
 * @param decl The datatype declaration to copy.
 * @return The same datatype declarationwith its reference count increased by
 *         one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5DatatypeDecl cvc5_dt_decl_copy(Cvc5DatatypeDecl decl);

/**
 * Release copy of datatype declaration, decrements reference counter of `decl`.
 *
 * @param decl The datatype declaration to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a
 *       Cvc5DatatypeDecl returns a copy that is owned by the callee of the
 *       function and thus, can be released.
 */
CVC5_EXPORT void cvc5_dt_decl_release(Cvc5DatatypeDecl decl);

/**
 * Compare two datatype declarations for structural equality.
 * @param a The first datatype declaration.
 * @param b The second datatype declaration.
 * @return True if the datatype declarations are equal.
 */
CVC5_EXPORT bool cvc5_dt_decl_is_equal(Cvc5DatatypeDecl a, Cvc5DatatypeDecl b);

/**
 * Add datatype constructor declaration.
 * @param decl The datatype declaration.
 * @param ctor The datatype constructor declaration to add.
 */
CVC5_EXPORT void cvc5_dt_decl_add_constructor(Cvc5DatatypeDecl decl,
                                              Cvc5DatatypeConstructorDecl ctor);

/**
 * Get the number of constructors for a given Datatype declaration.
 * @param decl The datatype declaration.
 * @return The number of constructors.
 */
CVC5_EXPORT size_t cvc5_dt_decl_get_num_constructors(Cvc5DatatypeDecl decl);

/**
 * Determine if a given Datatype declaration is parametric.
 * @warning This function is experimental and may change in future versions.
 * @param decl The datatype declaration.
 * @return True if the datatype declaration is parametric.
 */
CVC5_EXPORT bool cvc5_dt_decl_is_parametric(Cvc5DatatypeDecl decl);

/**
 * Determine if a given datatype declaration is resolved (has already been
 * used to declare a datatype).
 * @param decl The datatype declaration.
 * @return True if the datatype declaration is resolved.
 */
CVC5_EXPORT bool cvc5_dt_decl_is_resolved(Cvc5DatatypeDecl decl);

/**
 * Get a string representation of a given datatype declaration.
 * @param decl The datatype declaration.
 * @return A string representation of the datatype declaration.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_decl_to_string(Cvc5DatatypeDecl decl);

/**
 * Get the name of a given datatype declaration.
 * @param decl The datatype declaration.
 * @return The name of the datatype declaration.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_decl_get_name(Cvc5DatatypeDecl decl);

/**
 * Compute the hash value of a datatype declaration.
 * @param decl The datatype declaration.
 * @return The hash value of the datatype declaration.
 */
CVC5_EXPORT size_t cvc5_dt_decl_hash(Cvc5DatatypeDecl decl);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5DatatypeSelector                                                       */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5dtsel
 *  @{
 */

/**
 * Make copy of datatype selector, increases reference counter of `sel`.
 *
 * @param sel The datatype selector to copy.
 * @return The same datatype selector with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5DatatypeSelector cvc5_dt_sel_copy(Cvc5DatatypeSelector sel);

/**
 * Release copy of datatype selector, decrements reference counter of `sel`.
 *
 * @param sel The datatype selector to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a
 *       Cvc5DatatypeSelector returns a copy that is owned by the callee of the
 *       function and thus, can be released.
 */
CVC5_EXPORT void cvc5_dt_sel_release(Cvc5DatatypeSelector sel);
/**
 * Compare two datatype selectors for structural equality.
 * @param a The first datatype selector.
 * @param b The second datatype selector.
 * @return True if the datatype selectors are equal.
 */
CVC5_EXPORT bool cvc5_dt_sel_is_equal(Cvc5DatatypeSelector a,
                                      Cvc5DatatypeSelector b);

/**
 * Get the name of a given datatype selector.
 * @param sel The datatype selector.
 * @return The name of the Datatype selector.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_sel_get_name(Cvc5DatatypeSelector sel);

/**
 * Get the selector term of a given datatype selector.
 *
 * Selector terms are a class of function-like terms of selector
 * sort (cvc5_sort_is_dt_selector()), and should be used as the first
 * argument of Terms of kind #CVC5_KIND_APPLY_SELECTOR.
 *
 * @param sel The datatype selector.
 * @return The selector term.
 */
CVC5_EXPORT Cvc5Term cvc5_dt_sel_get_term(Cvc5DatatypeSelector sel);

/**
 * Get the updater term of a given datatype selector.
 *
 * Similar to selectors, updater terms are a class of function-like terms of
 * updater Sort (cvc5_sort_is_dt_updater()), and should be used as the first
 * argument of Terms of kind #CVC5_KIND_APPLY_UPDATER.
 *
 * @param sel The datatype selector.
 * @return The updater term.
 */
CVC5_EXPORT Cvc5Term cvc5_dt_sel_get_updater_term(Cvc5DatatypeSelector sel);

/**
 * Get the codomain sort of a given datatype selector.
 * @param sel The datatype selector.
 * @return The codomain sort of the selector.
 */
CVC5_EXPORT Cvc5Sort cvc5_dt_sel_get_codomain_sort(Cvc5DatatypeSelector sel);

/**
 * Get the string representation of a given datatype selector.
 * @param sel The datatype selector.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_sel_to_string(Cvc5DatatypeSelector sel);

/**
 * Compute the hash value of a datatype selector.
 * @param sel The datatype selector.
 * @return The hash value of the datatype selector.
 */
CVC5_EXPORT size_t cvc5_dt_sel_hash(Cvc5DatatypeSelector sel);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5DatatypeConstructor                                                    */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5dtcons
 *  @{
 */

/**
 * Make copy of datatype constructor, increases reference counter of `cons`.
 *
 * @param cons The datatype constructor to copy.
 * @return The same datatype constructor with its reference count increased by
 *         one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5DatatypeConstructor
cvc5_dt_cons_copy(Cvc5DatatypeConstructor cons);

/**
 * Release copy of datatype constructor, decrements reference counter of `cons`.
 *
 * @param cons The datatype constructor to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a
 *       Cvc5DatatypeConstructor returns a copy that is owned by the callee of
 *       the function and thus, can be released.
 */
CVC5_EXPORT void cvc5_dt_cons_release(Cvc5DatatypeConstructor cons);

/**
 * Compare two datatype constructors for structural equality.
 * @param a The first datatype constructor.
 * @param b The second datatype constructor.
 * @return True if the datatype constructors are equal.
 */
CVC5_EXPORT bool cvc5_dt_cons_is_equal(Cvc5DatatypeConstructor a,
                                       Cvc5DatatypeConstructor b);

/**
 * Get the name of a given datatype constructor.
 * @param cons The datatype constructor.
 * @return The name.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_cons_get_name(Cvc5DatatypeConstructor cons);

/**
 * Get the constructor term of a given datatype constructor.
 *
 * Datatype constructors are a special class of function-like terms whose sort
 * is datatype constructor (cvc5_sort_is_dt_constructor()). All datatype
 * constructors, including nullary ones, should be used as the
 * first argument to Terms whose kind is #CVC5_KIND_APPLY_CONSTRUCTOR.
 * For example, the nil list can be constructed by
 * `cvc5_mk_term(CVC5_KIND_APPLY_CONSTRUCTOR, {t})`, where `t` is the term
 * returned by this function.
 *
 * @note This function should not be used for parametric datatypes. Instead,
 *       use the function cvc5_dt_cons_get_instantiated_term() below.
 *
 * @param cons The datatype constructor.
 * @return The constructor term.
 */
CVC5_EXPORT Cvc5Term cvc5_dt_cons_get_term(Cvc5DatatypeConstructor cons);

/**
 * Get the constructor term of this datatype constructor whose return
 * type is `sort`.
 *
 * This function is intended to be used on constructors of parametric datatypes
 * and can be seen as returning the constructor term that has been explicitly
 * cast to the given sort.
 *
 * This function is required for constructors of parametric datatypes whose
 * return type cannot be determined by type inference. For example, given:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-datatype List
 *         (par (T) ((nil) (cons (head T) (tail (List T))))))
 * \endverbatim
 *
 * The type of nil terms must be provided by the user. In SMT version 2.6,
 * this is done via the syntax for qualified identifiers:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (as nil (List Int))
 * \endverbatim
 *
 * This function is equivalent of applying the above, where the
 * datatype constructor is the one corresponding to `nil`, and `sort` is
 * `(List Int)`.
 *
 * @note The returned constructor term `t` is used to construct the above
 *       (nullary) application of `nil` with
 *       `cvc5_mk_term(CVC5_KIND_APPLY_CONSTRUCTOR, {t})`.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cons The datatype constructor.
 * @param sort The desired return sort of the constructor.
 * @return The constructor term.
 */
CVC5_EXPORT Cvc5Term
cvc5_dt_cons_get_instantiated_term(Cvc5DatatypeConstructor cons, Cvc5Sort sort);

/**
 * Get the tester term of a given datatype constructor.
 *
 * Similar to constructors, testers are a class of function-like terms of
 * tester sort (cvc5_sort_is_dt_constructor()) which should be used as the
 * first argument of Terms of kind #CVC5_KIND_APPLY_TESTER.
 *
 * @param cons The datatype constructor.
 * @return The tester term.
 */
CVC5_EXPORT Cvc5Term cvc5_dt_cons_get_tester_term(Cvc5DatatypeConstructor cons);

/**
 * Get the number of selectors of a given datatype constructor.
 * @param cons The datatype constructor.
 * @return The number of selectors.
 */
CVC5_EXPORT size_t cvc5_dt_cons_get_num_selectors(Cvc5DatatypeConstructor cons);

/**
 * Get the selector at index `i` of a given datatype constructor.
 * @param cons  The datatype constructor.
 * @param index The index of the selector.
 * @return The i^th DatatypeSelector.
 */
CVC5_EXPORT Cvc5DatatypeSelector
cvc5_dt_cons_get_selector(Cvc5DatatypeConstructor cons, size_t index);
/**
 * Get the datatype selector with the given name.
 * @note This is a linear search through the selectors, so in case of
 *       multiple, similarly-named selectors, the first is returned.
 * @param cons The datatype constructor.
 * @param name The name of the datatype selector.
 * @return The first datatype selector with the given name.
 */
CVC5_EXPORT Cvc5DatatypeSelector cvc5_dt_cons_get_selector_by_name(
    Cvc5DatatypeConstructor cons, const char* name);

/**
 * Get a string representation of a given datatype constructor.
 * @param cons The datatype constructor.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_cons_to_string(Cvc5DatatypeConstructor cons);

/**
 * Compute the hash value of a datatype constructor.
 * @param cons The datatype constructor.
 * @return The hash value of the datatype constructor.
 */
CVC5_EXPORT size_t cvc5_dt_cons_hash(Cvc5DatatypeConstructor cons);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Datatype                                                               */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5dt
 *  @{
 */

/**
 * Make copy of datatype, increases reference counter of `dt`.
 *
 * @param dt The datatype to copy.
 * @return The same datatype with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5Datatype cvc5_dt_copy(Cvc5Datatype dt);

/**
 * Release copy of datatype, decrements reference counter of `dt`.
 *
 * @param dt The datatype to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a
 *       Cvc5Datatype returns a copy that is owned by the callee of the
 *       function and thus, can be released.
 */
CVC5_EXPORT void cvc5_dt_release(Cvc5Datatype dt);

/**
 * Compare two datatypes for structural equality.
 * @param a The first datatype.
 * @param b The second datatype.
 * @return True if the datatypes are equal.
 */
CVC5_EXPORT bool cvc5_dt_is_equal(Cvc5Datatype a, Cvc5Datatype b);

/**
 * Get the datatype constructor of a given datatype at a given index.
 * @param dt  The datatype.
 * @param idx The index of the datatype constructor to return.
 * @return The datatype constructor with the given index.
 */
CVC5_EXPORT Cvc5DatatypeConstructor cvc5_dt_get_constructor(Cvc5Datatype dt,
                                                            size_t idx);

/**
 * Get the datatype constructor of a given datatype with the given name.
 * @note This is a linear search through the constructors, so in case of
 * multiple, similarly-named constructors, the first is returned.
 * @param dt  The datatype.
 * @param name The name of the datatype constructor.
 * @return The datatype constructor with the given name.
 */
CVC5_EXPORT Cvc5DatatypeConstructor
cvc5_dt_get_constructor_by_name(Cvc5Datatype dt, const char* name);

/**
 * Get the datatype selector of a given datatype with the given name.
 * @note This is a linear search through the constructors and their selectors,
 *       so in case of multiple, similarly-named selectors, the first is
 *       returned.
 * @param dt   The datatype.
 * @param name The name of the datatype selector.
 * @return The datatype selector with the given name.
 */
CVC5_EXPORT Cvc5DatatypeSelector cvc5_dt_get_selector(Cvc5Datatype dt,
                                                      const char* name);

/**
 * Get the name of a given datatype.
 * @param dt   The datatype.
 * @return The name.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_get_name(Cvc5Datatype dt);

/**
 * Get the number of constructors of a given datatype.
 * @param dt   The datatype.
 * @return The number of constructors.
 */
CVC5_EXPORT size_t cvc5_dt_get_num_constructors(Cvc5Datatype dt);

/**
 * Get the parameters of a given datatype, if it is parametric.
 * @note Asserts that this datatype is parametric.
 * @warning This function is experimental and may change in future versions.
 * @param dt The datatype.
 * @param size The size of the resulting array.
 * @return The parameters of this datatype.
 */
CVC5_EXPORT const Cvc5Sort* cvc5_dt_get_parameters(Cvc5Datatype dt,
                                                   size_t* size);

/**
 * Determine if a given datatype is parametric.
 * @warning This function is experimental and may change in future versions.
 * @param dt The datatype.
 * @return True if the datatype is parametric.
 */
CVC5_EXPORT bool cvc5_dt_is_parametric(Cvc5Datatype dt);

/**
 * Determine if a given datatype corresponds to a co-datatype.
 * @param dt The datatype.
 * @return True if the datatype corresponds to a co-datatype.
 */
CVC5_EXPORT bool cvc5_dt_is_codatatype(Cvc5Datatype dt);

/**
 * Determine if a given datatype corresponds to a tuple.
 * @param dt The datatype.
 * @return True if this datatype corresponds to a tuple.
 */
CVC5_EXPORT bool cvc5_dt_is_tuple(Cvc5Datatype dt);

/**
 * Determine if a given datatype corresponds to a record.
 * @warning This function is experimental and may change in future versions.
 * @param dt The datatype.
 * @return True if the datatype corresponds to a record.
 */
CVC5_EXPORT bool cvc5_dt_is_record(Cvc5Datatype dt);

/**
 * Determine if a given datatype is finite.
 * @param dt The datatype.
 * @return True if the datatype is finite.
 */
CVC5_EXPORT bool cvc5_dt_is_finite(Cvc5Datatype dt);

/**
 * Determine if a given datatype is well-founded.
 *
 * If the datatype is not a codatatype, this returns false if there are no
 * values of the datatype that are of finite size.
 *
 * @param dt The datatype.
 * @return True if the datatype is well-founded.
 */
CVC5_EXPORT bool cvc5_dt_is_well_founded(Cvc5Datatype dt);

/**
 * Get a string representation of a given datatype.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_dt_to_string(Cvc5Datatype dt);

/**
 * Compute the hash value of a datatype.
 * @param dt The datatype.
 * @return The hash value of the datatype.
 */
CVC5_EXPORT size_t cvc5_dt_hash(Cvc5Datatype dt);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Grammar                                                                */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5grammar
 *  @{
 */

/**
 * Add `rule` to the set of rules corresponding to `symbol` of a given grammar.
 * @param grammar The grammar.
 * @param symbol  The non-terminal to which the rule is added.
 * @param rule The rule to add.
 */
CVC5_EXPORT void cvc5_grammar_add_rule(Cvc5Grammar grammar,
                                       Cvc5Term symbol,
                                       Cvc5Term rule);

/**
 * Add `rules` to the set of rules corresponding to `symbol` of a given grammar.
 * @param grammar The grammar.
 * @param symbol The non-terminal to which the rules are added.
 * @param size   The number of rules to add.
 * @param rules The rules to add.
 */
CVC5_EXPORT void cvc5_grammar_add_rules(Cvc5Grammar grammar,
                                        Cvc5Term symbol,
                                        size_t size,
                                        const Cvc5Term rules[]);

/**
 * Allow `symbol` to be an arbitrary constant of a given grammar.
 * @param grammar The grammar.
 * @param symbol The non-terminal allowed to be any constant.
 */
CVC5_EXPORT void cvc5_grammar_add_any_constant(Cvc5Grammar grammar,
                                               Cvc5Term symbol);

/**
 * Allow `symbol` to be any input variable of a given grammar to corresponding
 * synth-fun/synth-inv with the same sort as `symbol`.
 * @param grammar The grammar.
 * @param symbol The non-terminal allowed to be any input variable.
 */
CVC5_EXPORT void cvc5_grammar_add_any_variable(Cvc5Grammar grammar,
                                               Cvc5Term symbol);

/**
 * Get a string representation of a given grammar.
 * @param grammar The grammar.
 * @return A string representation of the grammar.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_grammar_to_string(const Cvc5Grammar grammar);

/**
 * Compare two grammars for referential equality.
 * @param a The first grammar.
 * @param b The second grammar.
 * @return  True if both grammar pointers point to the same internal grammar
 *          object.
 */
CVC5_EXPORT bool cvc5_grammar_is_equal(Cvc5Grammar a, Cvc5Grammar b);

/**
 * Compare two grammars for referential disequality.
 * @param a The first grammar.
 * @param b The second grammar.
 * @return  True if both grammar pointers point to different internal grammar
 *          objects.
 */
CVC5_EXPORT bool cvc5_grammar_is_disequal(Cvc5Grammar a, Cvc5Grammar b);

/**
 * Compute the hash value of a grammar.
 * @param grammar The grammar.
 * @return The hash value of the grammar.
 */
CVC5_EXPORT size_t cvc5_grammar_hash(Cvc5Grammar grammar);

/**
 * Make copy of grammar, increases reference counter of `grammar`.
 *
 * @param grammar The grammar to copy.
 * @return The same grammar with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5Grammar cvc5_grammar_copy(Cvc5Grammar grammar);

/**
 * Release copy of grammar, decrements reference counter of `grammar`.
 *
 * @param grammar The grammar to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a copy
 *       that is owned by the callee of the function and thus, can be released.
 */
CVC5_EXPORT void cvc5_grammar_release(Cvc5Grammar grammar);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5TermManager                                                            */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5termmanager
 *  @{
 */

/**
 * Construct a new instance of a cvc5 term manager.
 * @return The cvc5 term manager.
 */
CVC5_EXPORT Cvc5TermManager* cvc5_term_manager_new();

/**
 * Delete a cvc5 term manager instance.
 * @param tm The term manager instance.
 */
CVC5_EXPORT void cvc5_term_manager_delete(Cvc5TermManager* tm);

/**
 * Release all managed references.
 *
 * This will free all memory used by any managed objects allocated by the
 * term manager.
 *
 * @note This invalidates all managed objects created by the term manager.
 *
 * @param tm The term manager instance.
 */
CVC5_EXPORT void cvc5_term_manager_release(Cvc5TermManager* tm);

/**
 * Print the term manager statistics to the given file descriptor, suitable for
 * usage in signal handlers.
 * @param tm The term manager instance.
 * @param fd The file descriptor.
 */
CVC5_EXPORT void cvc5_term_manager_print_stats_safe(Cvc5TermManager* tm,
                                                    int fd);

/**
 * Get a snapshot of the current state of the statistic values of this term
 * manager. The returned object is completely decoupled from the term manager
 * and will not change when the term manager is used again.
 * @param tm The term manager instance.
 * @return A snapshot of the current state of the statistic values.
 */
CVC5_EXPORT Cvc5Statistics
cvc5_term_manager_get_statistics(Cvc5TermManager* tm);

/** @} */

/* .................................................................... */
/* Sorts Handling                                                       */
/* .................................................................... */

/** \addtogroup c_sort_creation
 *  @{
 */

/**
 * Get the Boolean sort.
 * @param tm The term manager instance.
 * @return Sort Boolean.
 */
CVC5_EXPORT Cvc5Sort cvc5_get_boolean_sort(Cvc5TermManager* tm);

/**
 * Get the Integer sort.
 * @param tm The term manager instance.
 * @return Sort Integer.
 */
CVC5_EXPORT Cvc5Sort cvc5_get_integer_sort(Cvc5TermManager* tm);

/**
 * Get the Real sort.
 * @param tm The term manager instance.
 * @return Sort Real.
 */
CVC5_EXPORT Cvc5Sort cvc5_get_real_sort(Cvc5TermManager* tm);

/**
 * Get the regular expression sort.
 * @param tm The term manager instance.
 * @return Sort RegExp.
 */
CVC5_EXPORT Cvc5Sort cvc5_get_regexp_sort(Cvc5TermManager* tm);

/**
 * Get the rounding mode sort.
 * @param tm The term manager instance.
 * @return The rounding mode sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_get_rm_sort(Cvc5TermManager* tm);

/**
 * Get the string sort.
 * @param tm The term manager instance.
 * @return Sort String.
 */
CVC5_EXPORT Cvc5Sort cvc5_get_string_sort(Cvc5TermManager* tm);

/**
 * Create an array sort.
 * @param tm The term manager instance.
 * @param index The array index sort.
 * @param elem  The array element sort.
 * @return The array sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_array_sort(Cvc5TermManager* tm,
                                        Cvc5Sort index,
                                        Cvc5Sort elem);

/**
 * Create a bit-vector sort.
 * @param tm The term manager instance.
 * @param size The bit-width of the bit-vector sort.
 * @return The bit-vector sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_bv_sort(Cvc5TermManager* tm, uint32_t size);

/**
 * Create a floating-point sort.
 * @param tm The term manager instance.
 * @param exp The bit-width of the exponent of the floating-point sort.
 * @param sig The bit-width of the significand of the floating-point sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_fp_sort(Cvc5TermManager* tm,
                                     uint32_t exp,
                                     uint32_t sig);

/**
 * Create a finite-field sort from a given string of
 * base n.
 *
 * @param tm The term manager instance.
 * @param size The modulus of the field. Must be prime.
 * @param base The base of the string representation of `size`.
 * @return The finite-field sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_ff_sort(Cvc5TermManager* tm,
                                     const char* size,
                                     uint32_t base);

/**
 * Create a datatype sort.
 * @param tm   The term manager instance.
 * @param decl The datatype declaration from which the sort is created.
 * @return The datatype sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_dt_sort(Cvc5TermManager* tm,
                                     Cvc5DatatypeDecl decl);

/**
 * Create a vector of datatype sorts.
 * @note The names of the datatype declarations must be distinct.
 * @param tm    The term manager instance.
 * @param size  The number of datatype declarations.
 * @param decls The datatype declarations from which the sort is created.
 * @return The datatype sorts.
 */
CVC5_EXPORT const Cvc5Sort* cvc5_mk_dt_sorts(Cvc5TermManager* tm,
                                             size_t size,
                                             const Cvc5DatatypeDecl decls[]);
/**
 * Create function sort.
 * @param tm    The term manager instance.
 * @param size  The number of domain sorts.
 * @param sorts The sort of the function arguments (the domain sorts).
 * @param codomain The sort of the function return value.
 * @return The function sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_fun_sort(Cvc5TermManager* tm,
                                      size_t size,
                                      const Cvc5Sort sorts[],
                                      Cvc5Sort codomain);

/**
 * Create a sort parameter.
 * @warning This function is experimental and may change in future versions.
 * @param tm     The term manager instance.
 * @param symbol The name of the sort, may be NULL.
 * @return The sort parameter.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_param_sort(Cvc5TermManager* tm,
                                        const char* symbol);

/**
 * Create a predicate sort.
 * @note This is equivalent to calling mkFunctionSort() with the Boolean sort
 * as the codomain.
 * @param tm    The term manager instance.
 * @param size  The number of sorts.
 * @param sorts The list of sorts of the predicate.
 * @return The predicate sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_predicate_sort(Cvc5TermManager* tm,
                                            size_t size,
                                            const Cvc5Sort sorts[]);

/**
 * Create a record sort
 * @warning This function is experimental and may change in future versions.
 * @param tm    The term manager instance.
 * @param size  The number of fields of the record.
 * @param names The names of the fields of the record.
 * @param sorts The sorts of the fields of the record.
 * @return The record sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_record_sort(Cvc5TermManager* tm,
                                         size_t size,
                                         const char* names[],
                                         const Cvc5Sort sorts[]);
/**
 * Create a set sort.
 * @param tm   The term manager instance.
 * @param sort The sort of the set elements.
 * @return The set sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_set_sort(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create a bag sort.
 * @param tm   The term manager instance.
 * @param sort The sort of the bag elements.
 * @return The bag sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_bag_sort(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create a sequence sort.
 * @param tm   The term manager instance.
 * @param sort The sort of the sequence elements.
 * @return The sequence sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_sequence_sort(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create an abstract sort. An abstract sort represents a sort for a given
 * kind whose parameters and arguments are unspecified.
 *
 * The kind `k` must be the kind of a sort that can be abstracted, i.e., a
 * sort that has indices or argument sorts. For example,
 * #CVC5_SORT_KIND_ARRAY_SORT and #CVC5_SORT_KIND_BITVECTOR_SORT can be passed
 * as the kind `k` to this function, while #CVC5_SORT_KIND_INTEGER_SORT and
 * #CVC5_SORT_KIND_STRING_SORT cannot.
 *
 * @note Providing the kind #CVC5_SORT_KIND_ABSTRACT_SORT as an argument to
 *       this function returns the (fully) unspecified sort, denoted `?`.
 *
 * @note Providing a kind `k` that has no indices and a fixed arity
 *       of argument sorts will return the sort of kind `k` whose arguments are
 *       the unspecified sort. For example,
 *       `cvc5_mk_abstract_sort(tm, CVC5_SORT_KIND_ARRAY_SORT)` will return the
 *       sort `(ARRAY_SORT ? ?)` instead of the abstract sort whose abstract
 *       kind is #CVC5_SORT_KIND_ARRAY_SORT.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param tm The term manager instance.
 * @param k The kind of the abstract sort
 * @return The abstract sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_abstract_sort(Cvc5TermManager* tm, Cvc5SortKind k);

/**
 * Create an uninterpreted sort.
 * @param tm The term manager instance.
 * @param symbol The name of the sort, may be NULL.
 * @return The uninterpreted sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_uninterpreted_sort(Cvc5TermManager* tm,
                                                const char* symbol);

/**
 * Create an unresolved datatype sort.
 *
 * This is for creating yet unresolved sort placeholders for mutually
 * recursive parametric datatypes.
 *
 * @param tm The term manager instance.
 * @param symbol The symbol of the sort.
 * @param arity The number of sort parameters of the sort.
 * @return The unresolved sort.
 *
 * @warning This function is experimental and may change in future versions.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_unresolved_dt_sort(Cvc5TermManager* tm,
                                                const char* symbol,
                                                size_t arity);

/**
 * Create an uninterpreted sort constructor sort.
 *
 * An uninterpreted sort constructor is an uninterpreted sort with arity > 0.
 *
 * @param tm The term manager instance.
 * @param symbol The symbol of the sort.
 * @param arity The arity of the sort (must be > 0)
 * @return The uninterpreted sort constructor sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_uninterpreted_sort_constructor_sort(
    Cvc5TermManager* tm, size_t arity, const char* symbol);

/**
 * Create a tuple sort.
 * @param tm The term manager instance.
 * @param size The number of sorts.
 * @param sorts The sorts of f the elements of the tuple.
 * @return The tuple sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_tuple_sort(Cvc5TermManager* tm,
                                        size_t size,
                                        const Cvc5Sort sorts[]);

/**
 * Create a nullable sort.
 * @param tm The term manager instance.
 * @param sort The sort of the element of the nullable.
 * @return The nullable sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_mk_nullable_sort(Cvc5TermManager* tm, Cvc5Sort sort);

/** @} */

/* .................................................................... */
/* Create Operators                                                     */
/* .................................................................... */

/** \addtogroup c_op_creation
 *  @{
 */

/**
 * Create operator of Kind:
 *   - #CVC5_KIND_BITVECTOR_EXTRACT
 *   - #CVC5_KIND_BITVECTOR_REPEAT
 *   - #CVC5_KIND_BITVECTOR_ROTATE_LEFT
 *   - #CVC5_KIND_BITVECTOR_ROTATE_RIGHT
 *   - #CVC5_KIND_BITVECTOR_SIGN_EXTEND
 *   - #CVC5_KIND_BITVECTOR_ZERO_EXTEND
 *   - #CVC5_KIND_DIVISIBLE
 *   - #CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_FP
 *   - #CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_IEEE_BV
 *   - #CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_REAL
 *   - #CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_SBV
 *   - #CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_UBV
 *   - #CVC5_KIND_FLOATINGPOINT_TO_SBV
 *   - #CVC5_KIND_FLOATINGPOINT_TO_UBV
 *   - #CVC5_KIND_INT_TO_BITVECTOR
 *   - #CVC5_KIND_TUPLE_PROJECT
 *
 * See `Cvc5Kind` for a description of the parameters.
 *
 * @param tm The term manager instance.
 * @param kind The kind of the operator.
 * @param size The number of indices of the operator.
 * @param idxs The indices.
 *
 * @note If `idxs` is empty, the Cvc5Op simply wraps the Cvc5Kind. The Cvc5Kind
 * can be used in cvc5_mk_term directly without creating a Cvc5Op first.
 */
CVC5_EXPORT Cvc5Op cvc5_mk_op(Cvc5TermManager* tm,
                              Cvc5Kind kind,
                              size_t size,
                              const uint32_t idxs[]);

/**
 * Create operator of kind:
 *   - #CVC5_KIND_DIVISIBLE (to support arbitrary precision integers)
 *
 * See CKind for a description of the parameters.
 *
 * @param tm The term manager instance.
 * @param kind The kind of the operator.
 * @param arg The string argument to this operator.
 */
CVC5_EXPORT Cvc5Op cvc5_mk_op_from_str(Cvc5TermManager* tm,
                                       Cvc5Kind kind,
                                       const char* arg);

/** @} */

/* .................................................................... */
/* Create Terms                                                         */
/* .................................................................... */

/** \addtogroup c_term_creation
 *  @{
 */

/**
 * Create n-ary term of given kind.
 * @param tm The term manager instance.
 * @param kind The kind of the term.
 * @param size The number of childrens.
 * @param children The children of the term.
 * @return The Term */
CVC5_EXPORT Cvc5Term cvc5_mk_term(Cvc5TermManager* tm,
                                  Cvc5Kind kind,
                                  size_t size,
                                  const Cvc5Term children[]);

/**
 * Create n-ary term of given kind from a given operator.
 * Create operators with `cvc5_mk_op()` and `cvc5_mk_op_from_str()`.
 * @param tm The term manager instance.
 * @param op The operator.
 * @param size The number of children.
 * @param children The children of the term.
 * @return The Term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_term_from_op(Cvc5TermManager* tm,
                                          Cvc5Op op,
                                          size_t size,
                                          const Cvc5Term children[]);

/**
 * Create a tuple term.
 * @param tm The term manager instance.
 * @param size The number of elements in the tuple.
 * @param terms The elements.
 * @return The tuple Term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_tuple(Cvc5TermManager* tm,
                                   size_t size,
                                   const Cvc5Term terms[]);

/**
 * Create a nullable some term.
 * @param tm The term manager instance.
 * @param term The element value.
 * @return the Element value wrapped in some constructor.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_nullable_some(Cvc5TermManager* tm, Cvc5Term term);

/**
 * Create a selector for nullable term.
 * @param tm The term manager instance.
 * @param term A nullable term.
 * @return The element value of the nullable term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_nullable_val(Cvc5TermManager* tm, Cvc5Term term);
/**
 * Create a null tester for a nullable term.
 * @param tm The term manager instance.
 * @param term A nullable term.
 * @return A tester whether term is null.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_nullable_is_null(Cvc5TermManager* tm,
                                              Cvc5Term term);
/**
 * Create a some tester for a nullable term.
 * @param tm The term manager instance.
 * @param term A nullable term.
 * @return A tester whether term is some.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_nullable_is_some(Cvc5TermManager* tm,
                                              Cvc5Term term);

/**
 * Create a constant representing an null of the given sort.
 * @param tm The term manager instance.
 * @param sort The sort of the Nullable element.
 * @return The null constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_nullable_null(Cvc5TermManager* tm, Cvc5Sort sort);
/**
 * Create a term that lifts kind to nullable terms.
 *
 * Example:
 * If we have the term ((_ nullable.lift +) x y),
 * where x, y of type (Nullable Int), then
 * kind would be ADD, and args would be [x, y].
 * This function would return
 * (nullable.lift (lambda ((a Int) (b Int)) (+ a b)) x y)
 *
 * @param tm The term manager instance.
 * @param kind The lifted operator.
 * @param size The number of arguments of the lifted operator.
 * @param args The arguments of the lifted operator.
 * @return A term of kind #CVC5_KIND_NULLABLE_LIFT where the first child
 *         is a lambda expression, and the remaining children are
 *         the original arguments.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_nullable_lift(Cvc5TermManager* tm,
                                           Cvc5Kind kind,
                                           size_t size,
                                           const Cvc5Term args[]);
/**
 * Create a skolem.
 * @param tm      The term manager instance.
 * @param id      The skolem identifier.
 * @param size    The number of arguments of the lifted operator.
 * @param indices The indices of the skolem.
 * @return The skolem.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_skolem(Cvc5TermManager* tm,
                                    Cvc5SkolemId id,
                                    size_t size,
                                    const Cvc5Term indices[]);

/**
 * Get the number of indices for a skolem id.
 * @param tm The term manager instance.
 * @param id The skolem id.
 * @return The number of indices for the skolem id.
 */
CVC5_EXPORT size_t cvc5_get_num_idxs_for_skolem_id(Cvc5TermManager* tm,
                                                   Cvc5SkolemId id);

/* .................................................................... */
/* Create Constants                                                     */
/* .................................................................... */

/**
 * Create a Boolean true constant.
 * @param tm The term manager instance.
 * @return The true constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_true(Cvc5TermManager* tm);

/**
 * Create a Boolean false constant.
 * @param tm The term manager instance.
 * @return The false constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_false(Cvc5TermManager* tm);

/**
 * Create a Boolean constant.
 * @param tm The term manager instance.
 * @return The Boolean constant.
 * @param val The value of the constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_boolean(Cvc5TermManager* tm, bool val);

/**
 * Create a constant representing the number Pi.
 * @param tm The term manager instance.
 * @return A constant representing Pi.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_pi(Cvc5TermManager* tm);
/**
 * Create an integer constant from a string.
 * @param tm The term manager instance.
 * @param s The string representation of the constant, may represent an
 *          integer (e.g., "123").
 * @return A constant of sort Integer assuming `s` represents an integer)
 */
CVC5_EXPORT Cvc5Term cvc5_mk_integer(Cvc5TermManager* tm, const char* s);

/**
 * Create an integer constant from a c++ int.
 * @param tm The term manager instance.
 * @param val The value of the constant.
 * @return A constant of sort Integer.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_integer_int64(Cvc5TermManager* tm, int64_t val);

/**
 * Create a real constant from a string.
 * @param tm The term manager instance.
 * @param s The string representation of the constant, may represent an
 *          integer (e.g., "123") or real constant (e.g., "12.34" or "12/34").
 * @return A constant of sort Real.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_real(Cvc5TermManager* tm, const char* s);

/**
 * Create a real constant from an integer.
 * @param tm The term manager instance.
 * @param val The value of the constant.
 * @return A constant of sort Integer.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_real_int64(Cvc5TermManager* tm, int64_t val);

/**
 * Create a real constant from a rational.
 * @param tm The term manager instance.
 * @param num The value of the numerator.
 * @param den The value of the denominator.
 * @return A constant of sort Real.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_real_num_den(Cvc5TermManager* tm,
                                          int64_t num,
                                          int64_t den);

/**
 * Create a regular expression all (re.all) term.
 * @param tm The term manager instance.
 * @return The all term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_regexp_all(Cvc5TermManager* tm);

/**
 * Create a regular expression allchar (re.allchar) term.
 * @param tm The term manager instance.
 * @return The allchar term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_regexp_allchar(Cvc5TermManager* tm);

/**
 * Create a regular expression none (re.none) term.
 * @param tm The term manager instance.
 * @return The none term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_regexp_none(Cvc5TermManager* tm);

/**
 * Create a constant representing an empty set of the given sort.
 * @param tm The term manager instance.
 * @param sort The sort of the set elements.
 * @return The empty set constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_empty_set(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create a constant representing an empty bag of the given sort.
 * @param tm The term manager instance.
 * @param sort The sort of the bag elements.
 * @return The empty bag constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_empty_bag(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create a separation logic empty term.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param tm The term manager instance.
 * @return The separation logic empty term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_sep_emp(Cvc5TermManager* tm);

/**
 * Create a separation logic nil term.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param tm The term manager instance.
 * @param sort The sort of the nil term.
 * @return The separation logic nil term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_sep_nil(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create a String constant from a regular character string which may contain
 * SMT-LIB compatible escape sequences like `\u1234` to encode unicode
 * characters.
 * @param tm The term manager instance.
 * @param s The string this constant represents.
 * @param use_esc_seq Determines whether escape sequences in `s` should.
 * be converted to the corresponding unicode character
 * @return The String constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_string(Cvc5TermManager* tm,
                                    const char* s,
                                    bool use_esc_seq);

/**
 * Create a String constant from a wide character string.
 * This function does not support escape sequences as wide character already
 * supports unicode characters.
 * @param tm The term manager instance.
 * @param s The string this constant represents.
 * @return The String constant.
 *
 * @warning This function is deprecated and replaced by
 *          cvc5_mk_string_from_char32(). It will be removed in a future
 *          release.
 */
CVC5_EXPORT __attribute__((deprecated("Use cvc5_mk_string_from_char32 instead")))
Cvc5Term cvc5_mk_string_from_wchar(Cvc5TermManager* tm,
                                   const wchar_t* s);

/**
 * Create a String constant from a UTF-32 string.
 * This function does not support escape sequences as wide character already
 * supports unicode characters.
 * @param tm The term manager instance.
 * @param s The UTF-32 string this constant represents.
 * @return The String constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_string_from_char32(Cvc5TermManager* tm,
                                                const char32_t* s);

/**
 * Create an empty sequence of the given element sort.
 * @param tm The term manager instance.
 * @param sort The element sort of the sequence.
 * @return The empty sequence with given element sort.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_empty_sequence(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create a universe set of the given sort.
 * @param tm The term manager instance.
 * @param sort The sort of the set elements.
 * @return The universe set constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_universe_set(Cvc5TermManager* tm, Cvc5Sort sort);

/**
 * Create a bit-vector constant of given size and value.
 *
 * @note The given value must fit into a bit-vector of the given size.
 *
 * @param tm The term manager instance.
 * @param size The bit-width of the bit-vector sort.
 * @param val The value of the constant.
 * @return The bit-vector constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_bv_uint64(Cvc5TermManager* tm,
                                       uint32_t size,
                                       uint64_t val);

/**
 * Create a bit-vector constant of a given bit-width from a given string of
 * base 2, 10 or 16.
 *
 * @note The given value must fit into a bit-vector of the given size.
 *
 * @param tm The term manager instance.
 * @param size The bit-width of the constant.
 * @param s The string representation of the constant.
 * @param base The base of the string representation (`2` for binary, `10` for
 * decimal, and `16` for hexadecimal).
 * @return The bit-vector constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_bv(Cvc5TermManager* tm,
                                uint32_t size,
                                const char* s,
                                uint32_t base);

/**
 * Create a finite field constant in a given field from a given string
 * of base n.
 *
 * @param tm    The term manager instance.
 * @param value The string representation of the constant.
 * @param sort  The field sort.
 * @param base  The base of the string representation of `value`.
 *
 * If `size` is the field size, the constant needs not be in the range
 * [0,size). If it is outside this range, it will be reduced modulo size
 * before being constructed.
 *
 */
CVC5_EXPORT Cvc5Term cvc5_mk_ff_elem(Cvc5TermManager* tm,
                                     const char* value,
                                     Cvc5Sort sort,
                                     uint32_t base);
/**
 * Create a constant array with the provided constant value stored at every
 * index.
 * @param tm The term manager instance.
 * @param sort The sort of the constant array (must be an array sort).
 * @param val The constant value to store (must match the sort's element sort).
 * @return The constant array term.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_const_array(Cvc5TermManager* tm,
                                         Cvc5Sort sort,
                                         Cvc5Term val);

/**
 * Create a positive infinity floating-point constant (SMT-LIB: `+oo`).
 * @param tm The term manager instance.
 * @param exp Number of bits in the exponent.
 * @param sig Number of bits in the significand.
 * @return The floating-point constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_fp_pos_inf(Cvc5TermManager* tm,
                                        uint32_t exp,
                                        uint32_t sig);

/**
 * Create a negative infinity floating-point constant (SMT-LIB: `-oo`).
 * @param tm The term manager instance.
 * @param exp Number of bits in the exponent.
 * @param sig Number of bits in the significand.
 * @return The floating-point constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_fp_neg_inf(Cvc5TermManager* tm,
                                        uint32_t exp,
                                        uint32_t sig);

/**
 * Create a not-a-number floating-point constant (Cvc5TermManager* tm, SMT-LIB:
 * `NaN`).
 * @param tm The term manager instance.
 * @param exp Number of bits in the exponent.
 * @param sig Number of bits in the significand.
 * @return The floating-point constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_fp_nan(Cvc5TermManager* tm,
                                    uint32_t exp,
                                    uint32_t sig);

/**
 * Create a positive zero floating-point constant (Cvc5TermManager* tm, SMT-LIB:
 * +zero).
 * @param tm The term manager instance.
 * @param exp Number of bits in the exponent.
 * @param sig Number of bits in the significand.
 * @return The floating-point constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_fp_pos_zero(Cvc5TermManager* tm,
                                         uint32_t exp,
                                         uint32_t sig);

/**
 * Create a negative zero floating-point constant (Cvc5TermManager* tm, SMT-LIB:
 * -zero).
 * @param tm The term manager instance.
 * @param exp Number of bits in the exponent.
 * @param sig Number of bits in the significand.
 * @return The floating-point constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_fp_neg_zero(Cvc5TermManager* tm,
                                         uint32_t exp,
                                         uint32_t sig);

/**
 * Create a rounding mode value.
 * @param tm The term manager instance.
 * @param rm The floating point rounding mode this constant represents.
 * @return The rounding mode value.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_rm(Cvc5TermManager* tm, Cvc5RoundingMode rm);

/**
 * Create a floating-point value from a bit-vector given in IEEE-754 format.
 * @param tm The term manager instance.
 * @param exp Size of the exponent.
 * @param sig Size of the significand.
 * @param val Value of the floating-point constant as a bit-vector term.
 * @return The floating-point value.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_fp(Cvc5TermManager* tm,
                                uint32_t exp,
                                uint32_t sig,
                                Cvc5Term val);
/**
 * Create a floating-point value from its three IEEE-754 bit-vector
 * value components (sign bit, exponent, significand).
 * @param tm The term manager instance.
 * @param sign The sign bit.
 * @param exp  The bit-vector representing the exponent.
 * @param sig The bit-vector representing the significand.
 * @return The floating-point value.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_fp_from_ieee(Cvc5TermManager* tm,
                                          Cvc5Term sign,
                                          Cvc5Term exp,
                                          Cvc5Term sig);

/**
 * Create a cardinality constraint for an uninterpreted sort.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param tm The term manager instance.
 * @param sort The sort the cardinality constraint is for.
 * @param upperBound The upper bound on the cardinality of the sort.
 * @return The cardinality constraint.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_cardinality_constraint(Cvc5TermManager* tm,
                                                    Cvc5Sort sort,
                                                    uint32_t upperBound);

/* .................................................................... */
/* Create Variables                                                     */
/* .................................................................... */

/**
 * Create a free constant.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-const <symbol> <sort>)
 *     (declare-fun <symbol> () <sort>)
 * \endverbatim
 *
 * @param tm The term manager instance.
 * @param sort The sort of the constant.
 * @param symbol The name of the constant, may be NULL.
 * @return The constant.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_const(Cvc5TermManager* tm,
                                   Cvc5Sort sort,
                                   const char* symbol);

/**
 * Create a bound variable to be used in a binder (i.e., a quantifier, a
 * lambda, or a witness binder).
 * @param tm The term manager instance.
 * @param sort The sort of the variable.
 * @param symbol The name of the variable, may be NULL.
 * @return The variable.
 */
CVC5_EXPORT Cvc5Term cvc5_mk_var(Cvc5TermManager* tm,
                                 Cvc5Sort sort,
                                 const char* symbol);

/** @} */

/* .................................................................... */
/* Create datatype constructor declarations                             */
/* .................................................................... */

/** \addtogroup c_dt_cons_decl_creation
 *  @{
 */

/**
 * Create a datatype constructor declaration.
 * @param tm The term manager instance.
 * @param name The name of the datatype constructor.
 * @return The DatatypeConstructorDecl.
 */
CVC5_EXPORT Cvc5DatatypeConstructorDecl
cvc5_mk_dt_cons_decl(Cvc5TermManager* tm, const char* name);

/** @} */

/* .................................................................... */
/* Create datatype declarations                                         */
/* .................................................................... */

/** \addtogroup c_dt_decl_creation
 *  @{
 */

/**
 * Create a datatype declaration.
 * @param tm The term manager instance.
 * @param name The name of the datatype.
 * @param is_codt True if a codatatype is to be constructed.
 * @return The Cvc5DatatypeDecl.
 */
CVC5_EXPORT Cvc5DatatypeDecl cvc5_mk_dt_decl(Cvc5TermManager* tm,
                                             const char* name,
                                             bool is_codt);

/**
 * Create a datatype declaration.
 * Create sorts parameter with `cvc5_mk_param_sort()`.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param tm The term manager instance.
 * @param name The name of the datatype.
 * @param size The number of sort parameters.
 * @param params A list of sort parameters.
 * @param is_codt True if a codatatype is to be constructed.
 * @return The Cvc5DatatypeDecl.
 */
CVC5_EXPORT Cvc5DatatypeDecl
cvc5_mk_dt_decl_with_params(Cvc5TermManager* tm,
                            const char* name,
                            size_t size,
                            const Cvc5Sort params[],
                            bool is_codt);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5OptionInfo                                                             */
/* -------------------------------------------------------------------------- */

typedef enum
{
  /** The empty option info, does not hold value information. */
  CVC5_OPTION_INFO_VOID,
  /** Information for option with boolean option value. */
  CVC5_OPTION_INFO_BOOL,
  /** Information for option with string option value. */
  CVC5_OPTION_INFO_STR,
  /** Information for option with int64 option value. */
  CVC5_OPTION_INFO_INT64,
  /** Information for option with uint64 option value. */
  CVC5_OPTION_INFO_UINT64,
  /** Information for option with double value. */
  CVC5_OPTION_INFO_DOUBLE,
  /** Information for option with option modes. */
  CVC5_OPTION_INFO_MODES,
} Cvc5OptionInfoKind;

/**
 * \verbatim embed:rst:leading-asterisk
 * Holds information about a specific option, including its name, its
 * aliases, whether the option was explicitly set by the user, and information
 * concerning its value.
 * It can be obtained via :cpp:func:`cvc5_get_option_info()` and allows for a
 * more detailed inspection of options than :cpp:func:`cvc5_get_option()`.
 * Union member ``info`` holds any of the following alternatives:
 *
 * - Neither of the following if the option holds no value (or the value has no
 *   native type). In that case, the kind of the option will be denoted as
 *   #CVC5_OPTION_INFO_VOID.
 * - Struct ``BoolInfo`` if the option is of type ``bool``. It holds the current
 *   value and the default value of the option. Option kind is denoted as
 *   #CVC5_OPTION_INFO_BOOL.
 * - Struct ``StringInfo`` if the option is of type ``const char*``. It holds
 *   the current value and the default value of the option. Option kind is
 *   denoted as #CVC5_OPTION_INFO_STR.
 * - Struct ``IntInfo`` if the option is of type ``int64_t``. It holds the
 *   current, default, minimum and maximum value of the option. Option kind is
 *   denoted as #CVC5_OPTION_INFO_INT64.
 * - Struct ``UIntInfo`` if the option is of type ``uint64_t``. It holds the
 *   current, default, minimum and maximum value of the option. Option kind is
 *   denoted as #CVC5_OPTION_INFO_UINT64.
 * - Struct ``DoubleInfo`` if the option is of type ``double``. It holds the
 *   current, default, minimum and maximum value of the option. Option kind is
 *   denoted as #CVC5_OPTION_INFO_DOUBLE.
 * - Struct ``ModeInfo`` if the option has modes. It holds the current and
 *   default valuesof the option, as well as a list of valid modes. Option kind
 *   is denoted as #CVC5_OPTION_INFO_MODES.
 *
 * \endverbatim
 *
 *  @note A typedef alias with the same name is also available for convenience.
 */
struct Cvc5OptionInfo
{
  /** The kind of the option info. */
  Cvc5OptionInfoKind kind;
  /** The option name */
  const char* name;
  /** The number of option name aliases */
  size_t num_aliases;
  /** The option name aliases */
  const char** aliases;
  /** The number of unsupported features */
  size_t num_no_supports;
  /** The unsupported features */
  const char** no_supports;
  /** True if the option was explicitly set by the user */
  bool is_set_by_user;
  /**
   * True if the option is an expert option
   * @warning This field is deprecated and replaced by `category`. It will be
   *          removed in a future release.
   */
  bool is_expert
      __attribute__((deprecated("Query Cvc5OptionCategory category for "
                                "CVC5_OPTION_CATEGORY_EXPERT instead")));
  /**
   * True if the option is a regular option
   * @warning This field is deprecated and replaced by `category`. It will be
   *          removed in a future release.
   */
  bool is_regular
      __attribute__((deprecated("Query Cvc5OptionCategory category for "
                                "CVC5_OPTION_CATEGORY_REGULAR instead")));
  /** The category of this option. */
  Cvc5OptionCategory category;

  /** Information for boolean option values. */
  struct BoolInfo
  {
    /** The default value. */
    bool dflt;
    /** The current value. */
    bool cur;
  } info_bool;

  /** Information for string option values. */
  struct StringInfo
  {
    /** The default value. */
    const char* dflt;
    /** The current value. */
    const char* cur;
  } info_str;

  /** Information for int64 values. */
  struct IntInfo
  {
    /** The default value. */
    int64_t dflt;
    /** The current value. */
    int64_t cur;
    /** The minimum value. */
    int64_t min;
    /** The maximum value. */
    int64_t max;
    /** True if option has a minimum value. */
    bool has_min;
    /** True if option has a maximum value. */
    bool has_max;
  } info_int;

  /** Information for uint64 values. */
  struct UIntInfo
  {
    /** The default value. */
    uint64_t dflt;
    /** The current value. */
    uint64_t cur;
    /** The minimum value. */
    uint64_t min;
    /** The maximum value. */
    uint64_t max;
    /** True if option has a minimum value. */
    bool has_min;
    /** True if option has a maximum value. */
    bool has_max;
  } info_uint;

  /** Information for double values. */
  struct DoubleInfo
  {
    /** The default value. */
    double dflt;
    /** The current value. */
    double cur;
    /** The minimum value. */
    double min;
    /** The maximum value. */
    double max;
    /** True if option has a minimum value. */
    bool has_min;
    /** True if option has a maximum value. */
    bool has_max;
  } info_double;

  /** Information for mode option values. */
  struct ModeInfo
  {
    /** The default value. */
    const char* dflt;
    /** The current value. */
    const char* cur;
    /** The number of possible modes. */
    size_t num_modes;
    /** The possible modes. */
    const char** modes;
  } info_mode;

  /** The associated C++ info. For internal use, only. */
  void* d_cpp_info;
};

/** \addtogroup c_cvc5optioninfo
 *  @{
 */

/**
 * Get a string representation of a given option info.
 * @param info The option info.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_option_info_to_string(const Cvc5OptionInfo* info);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Plugin                                                                 */
/* -------------------------------------------------------------------------- */

/**
 * A cvc5 plugin.
 *
 * @note A typedef alias with the same name is also available for convenience.
 */
struct Cvc5Plugin
{
  /**
   * Call to check, return list of lemmas to add to the SAT solver.
   * This method is called periodically, roughly at every SAT decision.
   * @param size  The size of the returned array of lemmas.
   * @param state The state data for the function, may be NULL.
   * @return The vector of lemmas to add to the SAT solver.
   * @note This function pointer may be NULL to use the default implementation.
   */
  const Cvc5Term* (*check)(size_t* size, void* state);
  /**
   * Notify SAT clause, called when `clause` is learned by the SAT solver.
   * @param clause The learned clause.
   * @param state The state data for the function, may be NULL.
   * @note This function pointer may be NULL to use the default implementation.
   */
  void (*notify_sat_clause)(const Cvc5Term clause, void* state);
  /**
   * Notify theory lemma, called when `lemma` is sent by a theory solver.
   * @param lemma The theory lemma.
   * @param state The state data for the function, may be NULL.
   * @note This function pointer may be NULL to use the default implementation.
   */
  void (*notify_theory_lemma)(const Cvc5Term lemma, void* state);
  /**
   * Get the name of the plugin (for debugging).
   * @return The name of the plugin.
   * @note This function pointer may NOT be NULL.
   */
  const char* (*get_name)();

  /** The state to pass into `check`. */
  void* d_check_state;
  /** The state to pass into `notify_sat_clause`. */
  void* d_notify_sat_clause_state;
  /** The state to pass into `notify_theory_lemma`. */
  void* d_notify_theory_lemma_state;
};

typedef struct Cvc5Plugin Cvc5Plugin;

/* -------------------------------------------------------------------------- */
/* Cvc5Proof                                                                  */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5proof
 *  @{
 */

/**
 * Get the proof rule used by the root step of a given proof.
 * @return The proof rule.
 */
CVC5_EXPORT Cvc5ProofRule cvc5_proof_get_rule(Cvc5Proof proof);

/**
 * Get the proof rewrite rule used  by the root step of the proof.
 *
 * Requires that `cvc5_proof_get_rule()` does not return
 * #CVC5_PROOF_RULE_DSL_REWRITE or #CVC5_PROOF_RULE_THEORY_REWRITE.
 *
 * @param proof The proof.
 * @return The proof rewrite rule.
 */
CVC5_EXPORT Cvc5ProofRewriteRule cvc5_proof_get_rewrite_rule(Cvc5Proof proof);

/**
 * Get the conclusion of the root step of a given proof.
 * @param proof The proof.
 * @return The conclusion term.
 */
CVC5_EXPORT Cvc5Term cvc5_proof_get_result(Cvc5Proof proof);

/**
 * Get the premises of the root step of a given proof.
 * @param proof The proof.
 * @param size  Output parameter to store the number of resulting premise
 *              proofs.
 * @return The premise proofs.
 * @note The returned Cvc5Proof array pointer is only valid until the next call
 *       to this function.
 */
CVC5_EXPORT const Cvc5Proof* cvc5_proof_get_children(Cvc5Proof proof,
                                                     size_t* size);

/**
 * Get the arguments of the root step of a given proof.
 * @param proof The proof.
 * @param size  Output parameter to store the number of resulting argument
 *              terms.
 * @return The argument terms.
 */
CVC5_EXPORT const Cvc5Term* cvc5_proof_get_arguments(Cvc5Proof proof,
                                                     size_t* size);

/**
 * Compare two proofs for referential equality.
 * @param a The first proof.
 * @param b The second proof.
 * @return  True if both proof pointers point to the same internal proof object.
 */
CVC5_EXPORT bool cvc5_proof_is_equal(Cvc5Proof a, Cvc5Proof b);

/**
 * Compare two proofs for referential disequality.
 * @param a The first proof.
 * @param b The second proof.
 * @return  True if both proof pointers point to different internal proof
 *          objects.
 */
CVC5_EXPORT bool cvc5_proof_is_disequal(Cvc5Proof a, Cvc5Proof b);

/**
 * Compute the hash value of a proof.
 * @param proof The proof.
 * @return The hash value of the proof.
 */
CVC5_EXPORT size_t cvc5_proof_hash(Cvc5Proof proof);

/**
 * Make copy of proof, increases reference counter of `proof`.
 *
 * @param proof The proof to copy.
 * @return The same proof with its reference count increased by one.
 *
 * @note This step is optional and allows users to manage resources in a more
 *       fine-grained manner.
 */
CVC5_EXPORT Cvc5Proof cvc5_proof_copy(Cvc5Proof proof);

/**
 * Release copy of proof, decrements reference counter of `proof`.
 *
 * @param proof The proof to release.
 *
 * @note This step is optional and allows users to release resources in a more
 *       fine-grained manner. Further, any API function that returns a copy
 *       that is owned by the callee of the function and thus, can be released.
 */
CVC5_EXPORT void cvc5_proof_release(Cvc5Proof proof);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Stat                                                                   */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5stat
 *  @{
 */

/**
 * Determine if a given statistic is intended for internal use only.
 * @param stat The statistic.
 * @return True if this is an internal statistic.
 */
CVC5_EXPORT bool cvc5_stat_is_internal(Cvc5Stat stat);

/**
 * Determine if a given statistics statistic holds the default value.
 * @param stat The statistic.
 * @return True if this is a defaulted statistic.
 */
CVC5_EXPORT bool cvc5_stat_is_default(Cvc5Stat stat);

/**
 * Determine if a given statistic holds an integer value.
 * @param stat The statistic.
 * @return True if this value is an integer.
 */
CVC5_EXPORT bool cvc5_stat_is_int(Cvc5Stat stat);

/**
 * Get the value of an integer statistic.
 * @param stat The statistic.
 * @return The integer value.
 */
CVC5_EXPORT int64_t cvc5_stat_get_int(Cvc5Stat stat);

/**
 * Determine if a given statistic holds a double value.
 * @param stat The statistic.
 * @return True if this value is a double.
 */
CVC5_EXPORT bool cvc5_stat_is_double(Cvc5Stat stat);

/**
 * Get the value of a double statistic.
 * @param stat The statistic.
 * @return The double value.
 */
CVC5_EXPORT double cvc5_stat_get_double(Cvc5Stat stat);

/**
 * Determine if a given statistic holds a string value.
 * @param stat The statistic.
 * @return True if this value is a string.
 */
CVC5_EXPORT bool cvc5_stat_is_string(Cvc5Stat stat);

/**
 * Get value of a string statistic.
 * @param stat The statistic.
 * @return The string value.
 * @note The returned char pointer is only valid until the next call
 *       to this function.
 */
CVC5_EXPORT const char* cvc5_stat_get_string(Cvc5Stat stat);

/**
 * Determine if a given statistic holds a histogram.
 * @param stat The statistic.
 * @return True if this value is a histogram.
 */
CVC5_EXPORT bool cvc5_stat_is_histogram(Cvc5Stat stat);

/**
 * Get the value of a histogram statistic.
 * @param stat   The statistic.
 * @param keys   The resulting arrays with the keys of the statistic, map to the
 *               values given in the resulting `values` array..
 * @param values The resulting arrays with the values of the statistic.
 * @param size   The size of the resulting keys/values arrays.
 */
CVC5_EXPORT void cvc5_stat_get_histogram(Cvc5Stat stat,
                                         const char** keys[],
                                         uint64_t* values[],
                                         size_t* size);

/**
 * Get a string representation of a given statistic.
 * @param stat The statistic.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_stat_to_string(Cvc5Stat stat);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5Statistics                                                             */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5statistics
 *  @{
 */

/**
 * Initialize iteration over the statistics values.
 * By default, only entries that are public and have been set
 * are visible while the others are skipped.
 * @param stat The statistics.
 * @param internal If set to true, internal statistics are shown as well.
 * @param dflt     If set to true, defaulted statistics are shown as well.
 */
CVC5_EXPORT void cvc5_stats_iter_init(Cvc5Statistics stat,
                                      bool internal,
                                      bool dflt);

/**
 * Determine if statistics iterator has more statitics to query.
 * @note Requires that iterator was initialized with `cvc5_stats_iter_init()`.
 * @param stat The statistics.
 * @return True if the iterator has more statistics to query.
 */
CVC5_EXPORT bool cvc5_stats_iter_has_next(Cvc5Statistics stat);

/**
 * Get next statistic and increment iterator.
 * @note Requires that iterator was initialized with `cvc5_stats_iter_init()`
 *       and that `cvc5_stats_iter_has_next()`.
 * @param stat The statistics.
 * @param name The output parameter for the name of the returned statistic.
 *             May be NULL to ignore.
 * @note       The returned char* pointer are only valid until the next call to
 *             this function.
 * @return The next statistic.
 */
CVC5_EXPORT Cvc5Stat cvc5_stats_iter_next(Cvc5Statistics stat,
                                          const char** name);

/**
 * Retrieve the statistic with the given name.
 * @note Requires that a statistic with the given name actually exists.
 * @param stat The statistics.
 * @param name The name of the statistic.
 * @return The statistic with the given name.
 */
CVC5_EXPORT Cvc5Stat cvc5_stats_get(Cvc5Statistics stat, const char* name);

/**
 * Get a string representation of a given statistics object.
 * @param stat The statistics.
 * @return The string representation.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_stats_to_string(Cvc5Statistics stat);

/** @} */

/* -------------------------------------------------------------------------- */
/* Cvc5                                                                       */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_cvc5
 *  @{
 */

/**
 * Construct a new instance of a cvc5 solver.
 * @param tm The associated term manager instance.
 * @return The cvc5 solver instance.
 */
CVC5_EXPORT Cvc5* cvc5_new(Cvc5TermManager* tm);

/**
 * Delete a cvc5 solver instance.
 * @param cvc5 The solver instance.
 */
CVC5_EXPORT void cvc5_delete(Cvc5* cvc5);

/**
 * Get the associated term manager of a cvc5 solver instance.
 * @param cvc5 The solver instance.
 * @return The term manager.
 */
CVC5_EXPORT Cvc5TermManager* cvc5_get_tm(Cvc5* cvc5);

/* .................................................................... */
/* SMT-LIB-style Term/Sort Creation                                     */
/* .................................................................... */

/**
 * Create datatype sort.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-datatype <symbol> <datatype_decl>)
 * \endverbatim
 *
 * @param cvc5   The solver instance.
 * @param symbol The name of the datatype sort.
 * @param size The number of constructor declarations of the datatype sort.
 * @param ctors The constructor declarations.
 * @return The datatype sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_declare_dt(Cvc5* cvc5,
                                     const char* symbol,
                                     size_t size,
                                     const Cvc5DatatypeConstructorDecl ctors[]);

/**
 * Declare n-ary function symbol.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-fun <symbol> ( <sort>* ) <sort>)
 * \endverbatim
 *
 * @param cvc5   The solver instance.
 * @param symbol The name of the function.
 * @param size   The number of domain sorts of the function.
 * @param sorts  The domain sorts of the function.
 * @param sort   The codomain sort of the function.
 * @param fresh  If true, then this method always returns a new Term. Otherwise,
 *               this method will always return the same Term for each call with
 *               the given sorts and symbol where fresh is false.
 * @return The function.
 */
CVC5_EXPORT Cvc5Term cvc5_declare_fun(Cvc5* cvc5,
                                      const char* symbol,
                                      size_t size,
                                      const Cvc5Sort sorts[],
                                      Cvc5Sort sort,
                                      bool fresh);

/**
 * Declare uninterpreted sort.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-sort <symbol> <numeral>)
 * \endverbatim
 *
 * @note This corresponds to
 *       `cvc5_mk_uninterpreted_sort()` if arity = 0, and to
 *       `cvc5_mk_uninterpreted_sort_constructor_sort()` if arity > 0.
 *
 * @param cvc5   The solver instance.
 * @param symbol The name of the sort.
 * @param arity  The arity of the sort.
 * @param fresh  If true, then this method always returns a new Sort.
 * @return The sort.
 */
CVC5_EXPORT Cvc5Sort cvc5_declare_sort(Cvc5* cvc5,
                                       const char* symbol,
                                       uint32_t arity,
                                       bool fresh);

/**
 * Define n-ary function.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (define-fun <function_def>)
 * \endverbatim
 *
 * @param cvc5   The cvc5 solver instance.
 * @param symbol The name of the function.
 * @param size   The number of parameters of the function.
 * @param vars   The parameters.
 * @param sort   The sort of the return value of this function.
 * @param term   The function body.
 * @param global Determines whether this definition is global (i.e., persists
 *               when popping the context).
 * @return The function.
 */
CVC5_EXPORT Cvc5Term cvc5_define_fun(Cvc5* cvc5,
                                     const char* symbol,
                                     size_t size,
                                     const Cvc5Term vars[],
                                     const Cvc5Sort sort,
                                     const Cvc5Term term,
                                     bool global);

/**
 * Define recursive function.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (define-fun-rec <function_def>)
 * \endverbatim
 *
 * @param cvc5   The cvc5 solver instance.
 * @param symbol The name of the function.
 * @param size   The number of parameters of the function.
 * @param vars   The parameters to this function.
 * @param sort   The sort of the return value of this function.
 * @param term   The function body.
 * @param global Determines whether this definition is global (i.e., persists
 *               when popping the context).
 * @return The function.
 */
CVC5_EXPORT Cvc5Term cvc5_define_fun_rec(Cvc5* cvc5,
                                         const char* symbol,
                                         size_t size,
                                         const Cvc5Term vars[],
                                         const Cvc5Sort sort,
                                         const Cvc5Term term,
                                         bool global);
/**
 * Define recursive function.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (define-fun-rec <function_def>)
 * \endverbatim
 *
 * Create parameter `fun` with mkConst().
 *
 * @param cvc5   The cvc5 solver instance.
 * @param fun    The sorted function.
 * @param size   The number of parameters of the function.
 * @param vars   The parameters to this function.
 * @param term   The function body.
 * @param global Determines whether this definition is global (i.e., persists
 *               when popping the context).
 * @return The function.
 */
CVC5_EXPORT Cvc5Term cvc5_define_fun_rec_from_const(Cvc5* cvc5,
                                                    Cvc5Term fun,
                                                    size_t size,
                                                    const Cvc5Term vars[],
                                                    const Cvc5Term term,
                                                    bool global);
/**
 * Define recursive functions.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (define-funs-rec
 *         ( <function_decl>_1 ... <function_decl>_n )
 *         ( <term>_1 ... <term>_n )
 *     )
 * \endverbatim
 *
 * Create elements of parameter `funs` with `cvc5_mk_const()`.
 *
 * @param cvc5   The cvc5 solver instance.
 * @param nfuns  The number of sorted functions.
 * @param funs   The sorted functions.
 * @param nvars  The numbers of parameters for each function.
 * @param vars   The list of parameters to the functions.
 * @param terms  The list of function bodies of the functions.
 * @param global Determines whether this definition is global (i.e., persists
 *               when popping the context).
 */
CVC5_EXPORT void cvc5_define_funs_rec(Cvc5* cvc5,
                                      size_t nfuns,
                                      const Cvc5Term funs[],
                                      size_t nvars[],
                                      const Cvc5Term* vars[],
                                      const Cvc5Term terms[],
                                      bool global);

/* .................................................................... */
/* Other commands                                                       */
/* .................................................................... */

/**
 * Simplify a formula without doing "much" work.
 *
 * Does not involve the SAT Engine in the simplification, but uses the
 * current definitions, and assertions.  It also involves theory
 * normalization.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5       The solver instance.
 * @param term       The formula to simplify.
 * @param apply_subs True to apply substitutions for solved variables.
 * @return The simplified formula.
 */
CVC5_EXPORT Cvc5Term cvc5_simplify(Cvc5* cvc5, Cvc5Term term, bool apply_subs);

/**
 * Assert a formula.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (assert <term>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param term The formula to assert.
 */
CVC5_EXPORT void cvc5_assert_formula(Cvc5* cvc5, Cvc5Term term);

/**
 * Check satisfiability.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (check-sat)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @return The result of the satisfiability check.
 */
CVC5_EXPORT Cvc5Result cvc5_check_sat(Cvc5* cvc5);

/**
 * Check satisfiability assuming the given formulas.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (check-sat-assuming ( <prop_literal>+ ))
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param size The number of assumptions.
 * @param assumptions The formulas to assume.
 * @return The result of the satisfiability check.
 */
CVC5_EXPORT Cvc5Result cvc5_check_sat_assuming(Cvc5* cvc5,
                                               size_t size,
                                               const Cvc5Term assumptions[]);
/**
 * Get the list of asserted formulas.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-assertions)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param size The size of the resulting assertions array.
 * @return The list of asserted formulas.
 * @note The returned Cvc5Term array pointer is only valid until the next call
 *       to this function.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_assertions(Cvc5* cvc5, size_t* size);

/**
 * Get info from the solver.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-info <info_flag>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param flag The info flag.
 * @return The info.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_get_info(Cvc5* cvc5, const char* flag);

/**
 * Get the value of a given option.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-option <keyword>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param option The option for which the value is queried.
 * @return A string representation of the option value.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_get_option(Cvc5* cvc5, const char* option);

/**
 * Get all option names that can be used with `cvc5_set_option()`,
 * `cvc5_get_option()` and `cvc5_get_option_info()`.
 * @param cvc5 The solver instance.
 * @param size The size of the resulting option names array.
 * @return All option names.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char** cvc5_get_option_names(Cvc5* cvc5, size_t* size);

/**
 * Get some information about a given option.
 * See struct Cvc5OptionInfo for more details on which information is available.
 * @param cvc5   The solver instance.
 * @param option The option for which the info is queried.
 * @param info   The output parameter for the queried info.
 * @note The returned Cvc5OptionInfo data is only valid until the next call
 *       to this function.
 */
CVC5_EXPORT void cvc5_get_option_info(Cvc5* cvc5,
                                      const char* option,
                                      Cvc5OptionInfo* info);

/**
 * Get the set of unsat ("failed") assumptions.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-unsat-assumptions)
 *
 * Requires to enable option
 * :ref:`produce-unsat-assumptions <lbl-option-produce-unsat-assumptions>`.
 * \endverbatim
 *
 * @note The returned Cvc5Term array pointer is only valid until the next call
 *       to this function.
 *
 * @param cvc5 The solver instance.
 * @param size The number of the resulting unsat assumptions.
 * @return The set of unsat assumptions.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_unsat_assumptions(Cvc5* cvc5,
                                                       size_t* size);

/**
 * Get the unsatisfiable core.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-unsat-core)
 *
 * Requires to enable option
 * :ref:`produce-unsat-cores <lbl-option-produce-unsat-cores>`.
 *
 * .. note::
 *   In contrast to SMT-LIB, cvc5's API does not distinguish between named
 *   and unnamed assertions when producing an unsatisfiable core.
 *   Additionally, the API allows this option to be called after a check with
 *   assumptions. A subset of those assumptions may be included in the
 *   unsatisfiable core returned by this function.
 * \endverbatim
 *
 * @note The returned Cvc5Term array pointer is only valid until the next call
 *       to this function.
 *
 * @param cvc5 The solver instance.
 * @param size The size of the resulting unsat core.
 * @return A set of terms representing the unsatisfiable core.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_unsat_core(Cvc5* cvc5, size_t* size);

/**
 * Get the lemmas used to derive unsatisfiability.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-unsat-core-lemmas)
 *
 * Requires the SAT proof unsat core mode, so to enable option
 * :ref:`unsat-cores-mode=sat-proof <lbl-option-unsat-cores-mode>`.
 *
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @note The returned Cvc5Term array pointer is only valid until the next call
 *       to this function.
 *
 * @param cvc5 The solver instance.
 * @param size The size of the resulting unsat core.
 * @return A set of terms representing the lemmas used to derive
 *         unsatisfiability.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_unsat_core_lemmas(Cvc5* cvc5,
                                                       size_t* size);

/**
 * Get a difficulty estimate for an asserted formula. This function is
 * intended to be called immediately after any response to a checkSat.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @note The resulting mapping from `inputs` (which is a subset of the inputs)
 * to real `values` is an estimate of how difficult each assertion was to solve.
 * Unmentioned assertions can be assumed to have zero difficulty.
 *
 * @param cvc5   The solver instance.
 * @param size   The resulting size of `inputs` and `values`.
 * @param inputs The resulting inputs that are mapped to the resulting `values`.
 * @param values The resulting real values.
 *
 * @note The resulting `inputs` and `values` array pointers are only valid
 *       until the next call to this function.
 */
CVC5_EXPORT void cvc5_get_difficulty(Cvc5* cvc5,
                                     size_t* size,
                                     Cvc5Term* inputs[],
                                     Cvc5Term* values[]);

/**
 * Get a timeout core.
 *
 * \verbatim embed:rst:leading-asterisk
 * This function computes a subset of the current assertions that cause a
 * timeout. It may make multiple checks for satisfiability internally, each
 * limited by the timeout value given by
 * :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`.
 *
 * If the result is unknown and the reason is timeout, then the list of
 * formulas correspond to a subset of the current assertions that cause a
 * timeout in the specified time :ref:`timeout-core-timeout
 * <lbl-option-timeout-core-timeout>`. If the result is unsat, then the list of
 * formulas correspond to an unsat core for the current assertions. Otherwise,
 * the result is sat, indicating that the current assertions are satisfiable,
 * and the returned set of assertions is empty.
 * \endverbatim
 *
 * @note This command  does not require being preceeded by a call to
 *       `cvc5_check_sat()`.
 *
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-timeout-core)
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5   The solver instance.
 * @param result The resulting result.
 * @param size   The resulting size of the timeout core.
 *
 * @return The list of assertions determined to be the timeout core. The
 *         resulting result is stored in `result`.
 *
 * @note The resulting `result` and term array pointer are only valid
 *       until the next call to this function.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_timeout_core(Cvc5* cvc5,
                                                  Cvc5Result* result,
                                                  size_t* size);

/**
 * Get a timeout core of the given assumptions.
 *
 * This function computes a subset of the given assumptions that cause a
 * timeout when added to the current assertions.
 *
 * \verbatim embed:rst:leading-asterisk
 * If the result is unknown and the reason is timeout, then the set of
 * assumptions corresponds to a subset of the given assumptions that cause a
 * timeout when added to the current assertions in the specified time
 * :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`. If the result
 * is unsat, then the set of assumptions together with the current assertions
 * correspond to an unsat core for the current assertions. Otherwise, the
 * result is sat, indicating that the given assumptions plus the current
 * assertions are satisfiable, and the returned set of assumptions is empty.
 * \endverbatim
 *
 * @note This command does not require being preceeded by a call to
 *       `cvc5_check_sat()`.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-timeout-core (<assert>*))
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5        The solver instance.
 * @param size        The number of assumptions.
 * @param assumptions The (non-empty) set of formulas to assume.
 * @param result      The resulting result.
 * @param rsize       The resulting size of the timeout core.
 *
 * @return The list of assumptions determined to be the timeout core. The
 *         resulting result is stored in `result`.
 *
 * @note The resulting `result` and term array pointer are only valid
 *       until the next call to this function.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_timeout_core_assuming(
    Cvc5* cvc5,
    size_t size,
    const Cvc5Term assumptions[],
    Cvc5Result* result,
    size_t* rsize);

/**
 * Get a proof associated with the most recent call to checkSat.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-proof :c)
 *
 * Requires to enable option
 * :ref:`produce-proofs <lbl-option-produce-proofs>`.
 * The string representation depends on the value of option
 * :ref:`produce-proofs <lbl-option-proof-format-mode>`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param c    The component of the proof to return
 * @param size The size of the resulting array of proofs.
 * @return An array of proofs.
 *
 * @note The returned Cvc5Proof array pointer is only valid until the next call
 *       to this function.
 */
CVC5_EXPORT const Cvc5Proof* cvc5_get_proof(Cvc5* cvc5,
                                            Cvc5ProofComponent c,
                                            size_t* size);

/**
 * Get a list of learned literals that are entailed by the current set of
 * assertions.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param type The type of learned literalsjto return
 * @param size The size of the resulting list of literals.
 * @return A list of literals that were learned at top-level.
 *
 * @note The resulting Cvc5Term array pointer is only valid until the next call
 *       to this function.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_learned_literals(Cvc5* cvc5,
                                                      Cvc5LearnedLitType type,
                                                      size_t* size);

/**
 * Get the value of the given term in the current model.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-value ( <term> ))
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param term The term for which the value is queried.
 * @return The value of the given term.
 */
CVC5_EXPORT Cvc5Term cvc5_get_value(Cvc5* cvc5, Cvc5Term term);

/**
 * Get the values of the given terms in the current model.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-value ( <term>* ))
 * \endverbatim
 *
 * @param cvc5  The solver instance.
 * @param size  The number of terms for which the value is queried.
 * @param terms The terms.
 * @param rsize The resulting size of the timeout core.
 * @return The values of the given terms.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_values(Cvc5* cvc5,
                                            size_t size,
                                            const Cvc5Term terms[],
                                            size_t* rsize);

/**
 * Get the domain elements of uninterpreted sort s in the current model. The
 * current model interprets s as the finite sort whose domain elements are
 * given in the return value of this function.
 *
 * @param cvc5 The solver instance.
 * @param sort The uninterpreted sort in question.
 * @param size The size of the resulting domain elements array.
 * @return The domain elements of s in the current model.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_model_domain_elements(Cvc5* cvc5,
                                                           Cvc5Sort sort,
                                                           size_t* size);

/**
 * Determine if the model value of the given free constant was essential for
 * showing satisfiability of the last `cvc5_check_sat()` query based on the
 * current model.
 *
 * For any free constant `v`, this will only return false if
 * \verbatim embed:rst:inline :ref:`model-cores
 * <lbl-option-model-cores>`\endverbatim
 * has been set to true.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param v The term in question.
 * @return True if `v` was essential and is thus a model core symbol.
 */
CVC5_EXPORT bool cvc5_is_model_core_symbol(Cvc5* cvc5, Cvc5Term v);

/**
 * Get the model
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-model)
 *
 * Requires to enable option
 * :ref:`produce-models <lbl-option-produce-models>`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param nsorts The number of uninterpreted sorts that should be printed in
 *              the model.
 * @param sorts The list of uninterpreted sorts.
 * @param nconsts The size of the list of free constants that should be printed
 *                in the model.
 * @param consts The list of free constants that should be printed in the
 *             model. A subset of these may be printed based on
 *             isModelCoreSymbol().
 * @return A string representing the model.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_get_model(Cvc5* cvc5,
                                       size_t nsorts,
                                       const Cvc5Sort sorts[],
                                       size_t nconsts,
                                       const Cvc5Term consts[]);

/**
 * Do quantifier elimination.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-qe <q>)
 * \endverbatim
 *
 * @note Quantifier Elimination is is only complete for logics such as LRA,
 *       LIA and BV.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param q A quantified formula of the form
 *          @f$Q\bar{x}_1... Q\bar{x}_n. P( x_1...x_i, y_1...y_j)@f$
 *          where
 *          @f$Q\bar{x}@f$ is a set of quantified variables of the form
 *          @f$Q x_1...x_k@f$ and
 *          @f$P( x_1...x_i, y_1...y_j )@f$ is a quantifier-free formula
 * @return A formula @f$\phi@f$  such that, given the current set of formulas
 *         @f$A@f$ asserted to this solver:
 *         - @f$(A \wedge q)@f$ and @f$(A \wedge \phi)@f$ are equivalent
 *         - @f$\phi@f$ is quantifier-free formula containing only free
 *           variables in @f$y_1...y_n@f$.
 */
CVC5_EXPORT Cvc5Term cvc5_get_quantifier_elimination(Cvc5* cvc5, Cvc5Term q);

/**
 * Do partial quantifier elimination, which can be used for incrementally
 * computing the result of a quantifier elimination.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-qe-disjunct <q>)
 * \endverbatim
 *
 * @note Quantifier Elimination is is only complete for logics such as LRA,
 * LIA and BV.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param q A quantified formula of the form
 *          @f$Q\bar{x}_1... Q\bar{x}_n. P( x_1...x_i, y_1...y_j)@f$
 *          where
 *          @f$Q\bar{x}@f$ is a set of quantified variables of the form
 *          @f$Q x_1...x_k@f$ and
 *          @f$P( x_1...x_i, y_1...y_j )@f$ is a quantifier-free formula
 * @return A formula @f$\phi@f$ such that, given the current set of formulas
 *         @f$A@f$ asserted to this solver:
 *         - @f$(A \wedge q \implies A \wedge \phi)@f$ if @f$Q@f$ is
 *           @f$\forall@f$, and @f$(A \wedge \phi \implies A \wedge q)@f$ if
 *           @f$Q@f$ is @f$\exists@f$
 *         - @f$\phi@f$ is quantifier-free formula containing only free
 *           variables in @f$y_1...y_n@f$
 *         - If @f$Q@f$ is @f$\exists@f$, let @f$(A \wedge Q_n)@f$ be the
 *           formula
 *           @f$(A \wedge \neg (\phi \wedge Q_1) \wedge ... \wedge
 *           \neg (\phi \wedge Q_n))@f$
 *           where for each @f$i = 1...n@f$,
 *           formula @f$(\phi \wedge Q_i)@f$ is the result of calling
 *           cvc5_get_quantifier_elimination_disjunct() for @f$q@f$ with the
 *           set of assertions @f$(A \wedge Q_{i-1})@f$.
 *           Similarly, if @f$Q@f$ is @f$\forall@f$, then let
 *           @f$(A \wedge Q_n)@f$ be
 *           @f$(A \wedge (\phi \wedge Q_1) \wedge ... \wedge (\phi \wedge
 *           Q_n))@f$
 *           where @f$(\phi \wedge Q_i)@f$ is the same as above.
 *           In either case, we have that @f$(\phi \wedge Q_j)@f$ will
 *           eventually be true or false, for some finite j.
 */
CVC5_EXPORT Cvc5Term cvc5_get_quantifier_elimination_disjunct(Cvc5* cvc5,
                                                              Cvc5Term q);

/**
 * When using separation logic, this sets the location sort and the
 * datatype sort to the given ones. This function should be invoked exactly
 * once, before any separation logic constraints are provided.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param loc The location sort of the heap.
 * @param data The data sort of the heap.
 */
CVC5_EXPORT void cvc5_declare_sep_heap(Cvc5* cvc5, Cvc5Sort loc, Cvc5Sort data);

/**
 * When using separation logic, obtain the term for the heap.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @return The term for the heap.
 */
CVC5_EXPORT Cvc5Term cvc5_get_value_sep_heap(Cvc5* cvc5);

/**
 * When using separation logic, obtain the term for nil.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @return The term for nil.
 */
CVC5_EXPORT Cvc5Term cvc5_get_value_sep_nil(Cvc5* cvc5);

/**
 * Declare a symbolic pool of terms with the given initial value.
 *
 * For details on how pools are used to specify instructions for quantifier
 * instantiation, see documentation for the #CVC5_KIND_INST_POOL kind.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-pool <symbol> <sort> ( <term>* ))
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param symbol The name of the pool.
 * @param sort The sort of the elements of the pool.
 * @param size The number of initial values of the pool.
 * @param init_value The initial value of the pool.
 * @return The pool symbol.
 */
CVC5_EXPORT Cvc5Term cvc5_declare_pool(Cvc5* cvc5,
                                       const char* symbol,
                                       Cvc5Sort sort,
                                       size_t size,
                                       const Cvc5Term init_value[]);
/**
 * Declare an oracle function with reference to an implementation.
 *
 * Oracle functions have a different semantics with respect to ordinary
 * declared functions. In particular, for an input to be satisfiable,
 * its oracle functions are implicitly universally quantified.
 *
 * This function is used in part for implementing this command:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-oracle-fun <sym> (<sort>*) <sort> <sym>)
 * \endverbatim
 *
 * In particular, the above command is implemented by constructing a
 * function over terms that wraps a call to binary sym via a text interface.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5   The solver instance.
 * @param symbol The name of the oracle
 * @param size   The number of domain sorts of the oracle function.
 * @param sorts  The domain sorts.
 * @param sort   The sort of the return value of this function.
 * @param state  The state data for the oracle function, may be NULL.
 * @param fun    The function that implements the oracle function, taking a
 *               an array of term arguments and its size and a void pointer
 *               to optionally capture any state data the function may need.
 * @return The oracle function.
 */
CVC5_EXPORT Cvc5Term cvc5_declare_oracle_fun(Cvc5* cvc5,
                                             const char* symbol,
                                             size_t size,
                                             const Cvc5Sort sorts[],
                                             Cvc5Sort sort,
                                             void* state,
                                             Cvc5Term (*fun)(size_t,
                                                             const Cvc5Term*,
                                                             void*));
/**
 * Add plugin to this solver. Its callbacks will be called throughout the
 * lifetime of this solver.
 * @warning This function is experimental and may change in future versions.
 * @param cvc5   The solver instance.
 * @param plugin The plugin to add to this solver.
 */
CVC5_EXPORT void cvc5_add_plugin(Cvc5* cvc5, Cvc5Plugin* plugin);

/**
 * Get an interpolant.
 *
 * Given that @f$A \rightarrow B@f$ is valid,
 * this function determines a term @f$I@f$
 * over the shared variables of @f$A@f$ and @f$B@f$,
 * such that @f$A \rightarrow I@f$ and
 * @f$I \rightarrow B@f$ are valid, if such a term exits. @f$A@f$ is the
 * current set of assertions and @f$B@f$ is the conjecture, given as `conj`.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-interpolant <symbol> <conj>)
 *
 * .. note:: In SMT-LIB, `<symbol>` assigns a symbol to the interpolant.
 *
 * .. note:: Requires option
 *          :ref:`produce-interpolants <lbl-option-produce-interpolants>` to
 *          be set to a mode different from `none`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param conj The conjecture term.
 * @return The interpolant, if an interpolant exists, else the null term.
 */
CVC5_EXPORT Cvc5Term cvc5_get_interpolant(Cvc5* cvc5, Cvc5Term conj);

/**
 * Get an interpolant
 *
 * Given that @f$A \rightarrow B@f$ is valid,
 * this function determines a term @f$I@f$
 * over the shared variables of @f$A@f$ and @f$B@f$,
 * with respect to a given grammar, such that
 * @f$A \rightarrow I@f$ and @f$I \rightarrow B@f$ are valid, if such a term
 * exits. @f$A@f$ is the current set of assertions and @f$B@f$ is the
 * conjecture, given as `conj`.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-interpolant <symbol> <conj> <grammar>)
 *
 * .. note:: In SMT-LIB, `<symbol>` assigns a symbol to the interpolant.
 *
 * .. note:: Requires option
 *          :ref:`produce-interpolants <lbl-option-produce-interpolants>` to
 *          be set to a mode different from `none`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param conj The conjecture term.
 * @param grammar The grammar for the interpolant I.
 * @return The interpolant, if an interpolant exists, else the null term.
 */
CVC5_EXPORT Cvc5Term cvc5_get_interpolant_with_grammar(Cvc5* cvc5,
                                                       Cvc5Term conj,
                                                       Cvc5Grammar grammar);

/**
 * Get the next interpolant. Can only be called immediately after a successful
 * call to get-interpolant or get-interpolant-next. Is guaranteed to produce a
 * syntactically different interpolant wrt the last returned interpolant if
 * successful.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-interpolant-next)
 *
 * Requires to enable incremental mode, and option
 * :ref:`produce-interpolants <lbl-option-produce-interpolants>` to be set to
 * a mode different from `none`. \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @return A Term @f$I@f$ such that @f$A \rightarrow I@f$ and
 *         @f$I \rightarrow B@f$ are valid, where @f$A@f$ is the
 *         current set of assertions and @f$B@f$ is given in the input by
 *         `conj`, or the null term if such a term cannot be found.
 */
CVC5_EXPORT Cvc5Term cvc5_get_interpolant_next(Cvc5* cvc5);

/**
 * Get an abduct.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-abduct <conj>)
 *
 * Requires to enable option
 * :ref:`produce-abducts <lbl-option-produce-abducts>`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param conj The conjecture term.
 * @return A term @f$C@f$ such that @f$(A \wedge C)@f$ is satisfiable,
 *         and @f$(A \wedge \neg B \wedge C)@f$ is unsatisfiable, where
 *         @f$A@f$ is the current set of assertions and @f$B@f$ is
 *         given in the input by ``conj``, or the null term if such a term
 *         cannot be found.
 */
CVC5_EXPORT Cvc5Term cvc5_get_abduct(Cvc5* cvc5, Cvc5Term conj);

/**
 * Get an abduct.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-abduct <conj> <grammar>)
 *
 * Requires to enable option
 * :ref:`produce-abducts <lbl-option-produce-abducts>`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param conj The conjecture term.
 * @param grammar The grammar for the abduct @f$C@f$
 * @return A term C such that @f$(A \wedge C)@f$ is satisfiable, and
 *        @f$(A \wedge \neg B \wedge C)@f$ is unsatisfiable, where @f$A@f$ is
 *        the current set of assertions and @f$B@f$ is given in the input by
 *        `conj`, or the null term if such a term cannot be found.
 */
CVC5_EXPORT Cvc5Term cvc5_get_abduct_with_grammar(Cvc5* cvc5,
                                                  Cvc5Term conj,
                                                  Cvc5Grammar grammar);

/**
 * Get the next abduct. Can only be called immediately after a successful
 * call to get-abduct or get-abduct-next. Is guaranteed to produce a
 * syntactically different abduct wrt the last returned abduct if successful.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (get-abduct-next)
 *
 * Requires to enable incremental mode, and option
 * :ref:`produce-abducts <lbl-option-produce-abducts>`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @return A term C such that @f$(A \wedge C)@f$ is satisfiable, and
 *        @f$(A \wedge \neg B \wedge C)@f$ is unsatisfiable, where @f$A@f$ is
 *        the current set of assertions and @f$B@f$ is given in the input by
 *        the last call to getAbduct(), or the null term if such a term
 *        cannot be found.
 */
CVC5_EXPORT Cvc5Term cvc5_get_abduct_next(Cvc5* cvc5);

/**
 * Block the current model. Can be called only if immediately preceded by a
 * SAT or INVALID query.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (block-model)
 *
 * Requires enabling option
 * :ref:`produce-models <lbl-option-produce-models>`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @param mode The mode to use for blocking.
 */
CVC5_EXPORT void cvc5_block_model(Cvc5* cvc5, Cvc5BlockModelsMode mode);

/**
 * Block the current model values of (at least) the values in terms. Can be
 * called only if immediately preceded by a SAT query.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (block-model-values ( <terms>+ ))
 *
 * Requires enabling option
 * :ref:`produce-models <lbl-option-produce-models>`.
 * \endverbatim
 *
 * @warning This function is experimental and may change in future versions.
 * @param cvc5 The solver instance.
 * @param size The number of values to block.
 * @param terms The values to block.
 */
CVC5_EXPORT void cvc5_block_model_values(Cvc5* cvc5,
                                         size_t size,
                                         const Cvc5Term terms[]);

/**
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5 The solver instance.
 * @return A string that contains information about all instantiations made
 *         by the quantifiers module.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_get_instantiations(Cvc5* cvc5);

/**
 * Push (a) level(s) to the assertion stack.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (push <numeral>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param nscopes The number of levels to push.
 */
CVC5_EXPORT void cvc5_push(Cvc5* cvc5, uint32_t nscopes);

/**
 * Pop (a) level(s) from the assertion stack.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (pop <numeral>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param nscopes The number of levels to pop.
 */
CVC5_EXPORT void cvc5_pop(Cvc5* cvc5, uint32_t nscopes);

/**
 * Remove all assertions.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (reset-assertions)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 */
CVC5_EXPORT void cvc5_reset_assertions(Cvc5* cvc5);

/**
 * Set info.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (set-info <attribute>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param keyword The info flag.
 * @param value The value of the info flag.
 */
CVC5_EXPORT void cvc5_set_info(Cvc5* cvc5,
                               const char* keyword,
                               const char* value);

/**
 * Set logic.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (set-logic <symbol>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param logic The logic to set.
 */
CVC5_EXPORT void cvc5_set_logic(Cvc5* cvc5, const char* logic);

/**
 * Determine if `cvc5_set_logic()` has been called.
 *
 * @return True if `setLogic()` has already been called for the given solver
 *         instance.
 */
CVC5_EXPORT bool cvc5_is_logic_set(Cvc5* cvc5);

/**
 * Get the logic set the solver.
 * @note Asserts `cvc5_is_logic_set()1.
 * @return The logic used by the solver.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_get_logic(Cvc5* cvc5);

/**
 * Set option.
 *
 * SMT-LIB:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (set-option :<option> <value>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param option The option name.
 * @param value The option value.
 */
CVC5_EXPORT void cvc5_set_option(Cvc5* cvc5,
                                 const char* option,
                                 const char* value);

/**
 * Append \p symbol to the current list of universal variables.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (declare-var <symbol> <sort>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param sort The sort of the universal variable.
 * @param symbol The name of the universal variable.
 * @return The universal variable.
 */
CVC5_EXPORT Cvc5Term cvc5_declare_sygus_var(Cvc5* cvc5,
                                            const char* symbol,
                                            Cvc5Sort sort);

/**
 * Create a Sygus grammar. The first non-terminal is treated as the starting
 * non-terminal, so the order of non-terminals matters.
 *
 * @param cvc5        The solver instance.
 * @param nbound_vars The number of bound variabls.
 * @param bound_vars  The parameters to corresponding synth-fun/synth-inv.
 * @param nsymbols    The number of symbols.
 * @param symbols     The pre-declaration of the non-terminal symbols.
 * @return The grammar.
 */
CVC5_EXPORT Cvc5Grammar cvc5_mk_grammar(Cvc5* cvc5,
                                        size_t nbound_vars,
                                        const Cvc5Term bound_vars[],
                                        size_t nsymbols,
                                        const Cvc5Term symbols[]);

/**
 * Synthesize n-ary function.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (synth-fun <symbol> ( <boundVars>* ) <sort>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param symbol The name of the function.
 * @param size The number of parameters.
 * @param bound_vars The parameters to this function.
 * @param sort The sort of the return value of this function.
 * @return The function.
 */
CVC5_EXPORT Cvc5Term cvc5_synth_fun(Cvc5* cvc5,
                                    const char* symbol,
                                    size_t size,
                                    const Cvc5Term bound_vars[],
                                    Cvc5Sort sort);

/**
 * Synthesize n-ary function following specified syntactic constraints.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (synth-fun <symbol> ( <boundVars>* ) <sort> <grammar>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param symbol The name of the function.
 * @param size The number of parameters.
 * @param bound_vars The parameters to this function.
 * @param sort The sort of the return value of this function.
 * @param grammar The syntactic constraints.
 * @return The function.
 */
CVC5_EXPORT Cvc5Term cvc5_synth_fun_with_grammar(Cvc5* cvc5,
                                                 const char* symbol,
                                                 size_t size,
                                                 const Cvc5Term bound_vars[],
                                                 Cvc5Sort sort,
                                                 Cvc5Grammar grammar);

/**
 * Add a forumla to the set of Sygus constraints.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (constraint <term>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param term The formula to add as a constraint.
 */
CVC5_EXPORT void cvc5_add_sygus_constraint(Cvc5* cvc5, Cvc5Term term);

/**
 * Get the list of sygus constraints.
 *
 * @param cvc5 The solver instance.
 * @param size The size of the resulting list of sygus constraints.
 * @return The list of sygus constraints.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_sygus_constraints(Cvc5* cvc5,
                                                       size_t* size);

/**
 * Add a forumla to the set of Sygus assumptions.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (assume <term>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param term The formula to add as an assumption.
 */
CVC5_EXPORT void cvc5_add_sygus_assume(Cvc5* cvc5, Cvc5Term term);

/**
 * Get the list of sygus assumptions.
 *
 * @param cvc5 The solver instance.
 * @param size The size of the resulting list of sygus assumptions.
 * @return The list of sygus assumptions.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_sygus_assumptions(Cvc5* cvc5,
                                                       size_t* size);

/**
 * Add a set of Sygus constraints to the current state that correspond to an
 * invariant synthesis problem.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (inv-constraint <inv> <pre> <trans> <post>)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @param inv The function-to-synthesize.
 * @param pre The pre-condition.
 * @param trans The transition relation.
 * @param post The post-condition.
 */
CVC5_EXPORT void cvc5_add_sygus_inv_constraint(
    Cvc5* cvc5, Cvc5Term inv, Cvc5Term pre, Cvc5Term trans, Cvc5Term post);

/**
 * Try to find a solution for the synthesis conjecture corresponding to the
 * current list of functions-to-synthesize, universal variables and
 * constraints.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (check-synth)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @return The result of the check, which is "solution" if the check found a
 *         solution in which case solutions are available via
 *         getSynthSolutions, "no solution" if it was determined there is no
 *         solution, or "unknown" otherwise.
 */
CVC5_EXPORT Cvc5SynthResult cvc5_check_synth(Cvc5* cvc5);

/**
 * Try to find a next solution for the synthesis conjecture corresponding to
 * the current list of functions-to-synthesize, universal variables and
 * constraints. Must be called immediately after a successful call to
 * check-synth or check-synth-next.
 *
 * @note Requires incremental mode.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (check-synth-next)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @return The result of the check, which is "solution" if the check found a
 *         solution in which case solutions are available via
 *         getSynthSolutions, "no solution" if it was determined there is no
 *         solution, or "unknown" otherwise.
 */
CVC5_EXPORT Cvc5SynthResult cvc5_check_synth_next(Cvc5* cvc5);

/**
 * Get the synthesis solution of the given term. This function should be
 * called immediately after the solver answers unsat for sygus input.
 * @param cvc5 The solver instance.
 * @param term The term for which the synthesis solution is queried.
 * @return The synthesis solution of the given term.
 */
CVC5_EXPORT Cvc5Term cvc5_get_synth_solution(Cvc5* cvc5, Cvc5Term term);

/**
 * Get the synthesis solutions of the given terms. This function should be
 * called immediately after the solver answers unsat for sygus input.
 * @param cvc5  The solver instance.
 * @param size  The size of the terms array.
 * @param terms The terms for which the synthesis solutions is queried.
 * @return The synthesis solutions of the given terms.
 */
CVC5_EXPORT const Cvc5Term* cvc5_get_synth_solutions(Cvc5* cvc5,
                                                     size_t size,
                                                     const Cvc5Term terms[]);

/**
 * Find a target term of interest using sygus enumeration, with no provided
 * grammar.
 *
 * The solver will infer which grammar to use in this call, which by default
 * will be the grammars specified by the function(s)-to-synthesize in the
 * current context.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (find-synth :target)
 * \endverbatim
 *
 * @param cvc5   The solver instance.
 * @param target The identifier specifying what kind of term to find
 * @return The result of the find, which is the null term if this call failed.
 *
 * @warning This function is experimental and may change in future versions.
 */
CVC5_EXPORT Cvc5Term cvc5_find_synth(Cvc5* cvc5, Cvc5FindSynthTarget target);

/**
 * Find a target term of interest using sygus enumeration with a provided
 * grammar.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (find-synth :target G)
 * \endverbatim
 *
 * @param cvc5    The solver instance.
 * @param target  The identifier specifying what kind of term to find
 * @param grammar The grammar for the term
 * @return The result of the find, which is the null term if this call failed.
 *
 * @warning This function is experimental and may change in future versions.
 */
CVC5_EXPORT Cvc5Term cvc5_find_synth_with_grammar(Cvc5* cvc5,
                                                  Cvc5FindSynthTarget target,
                                                  Cvc5Grammar grammar);
/**
 * Try to find a next target term of interest using sygus enumeration. Must
 * be called immediately after a successful call to find-synth or
 * find-synth-next.
 *
 * SyGuS v2:
 *
 * \verbatim embed:rst:leading-asterisk
 * .. code:: smtlib
 *
 *     (find-synth-next)
 * \endverbatim
 *
 * @param cvc5 The solver instance.
 * @return The result of the find, which is the null term if this call failed.
 *
 * @warning This function is experimental and may change in future versions.
 */
CVC5_EXPORT Cvc5Term cvc5_find_synth_next(Cvc5* cvc5);

/**
 * Get a snapshot of the current state of the statistic values of this
 * solver. The returned object is completely decoupled from the solver and
 * will not change when the solver is used again.
 * @param cvc5 The solver instance.
 * @return A snapshot of the current state of the statistic values.
 */
CVC5_EXPORT Cvc5Statistics cvc5_get_statistics(Cvc5* cvc5);

/**
 * Print the statistics to the given file descriptor, suitable for usage in
 * signal handlers.
 * @param cvc5 The solver instance.
 * @param fd The file descriptor.
 */
CVC5_EXPORT void cvc5_print_stats_safe(Cvc5* cvc5, int fd);

/**
 * Determines if the output stream for the given tag is enabled. Tags can be
 * enabled with the `output` option (and `-o <tag>` on the command line).
 *
 * @note Requires that a valid tag is given.
 *
 * @param cvc5 The solver instance.
 * @param tag  The output tag.
 * @return True if the given tag is enabled.
 */
CVC5_EXPORT bool cvc5_is_output_on(Cvc5* cvc5, const char* tag);

/**
 * Configure a file to write the output for a given tag.
 *
 * Tags can be enabled with the `output` option (and `-o <tag>` on the command
 * line). Requires that the given tag is valid.
 *
 * @note Close file `filename` before reading via `cvc5_close_output()`.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5     The solver instance.
 * @param tag      The output tag.
 * @param filename The file to write the output to. Use `<stdout>` to configure
 *                 to write to stdout.
 */
CVC5_EXPORT void cvc5_get_output(Cvc5* cvc5,
                                 const char* tag,
                                 const char* filename);

/**
 * Close output file configured for an output tag via `cvc5_get_output()`.
 *
 * @note This is required before reading the file.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5     The solver instance.
 * @param filename The file to close.
 */
CVC5_EXPORT void cvc5_close_output(Cvc5* cvc5, const char* filename);

/**
 * Get a string representation of the version of this solver.
 * @param cvc5 The solver instance.
 * @return The version string.
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_get_version(Cvc5* cvc5);

/**
 * Prints a proof as a string in a selected proof format mode.
 * Other aspects of printing are taken from the solver options.
 *
 * @warning This function is experimental and may change in future versions.
 *
 * @param cvc5       The solver instance.
 * @param proof      A proof, usually obtained from Solver::getProof().
 * @param format     The proof format used to print the proof.  Must be
 *                   `modes::ProofFormat::NONE` if the proof is from a component
 *                   other than `modes::ProofComponent::FULL`.
 * @param size       The number of assertions to names mappings given.
 * @param assertions The list of assertions that are mapped to
 *                   `assertions_names`. May be NULL if `assertions_size` is 0.
 * @param names      The names of the `assertions` (1:1 mapping). May by NULL
 *                   if `assertions` is NULL.
 *
 * @return The string representation of the proof in the given format.
 *
 * @note The returned char* pointer is only valid until the next call to this
 *       function.
 */
CVC5_EXPORT const char* cvc5_proof_to_string(Cvc5* cvc5,
                                             Cvc5Proof proof,
                                             Cvc5ProofFormat format,
                                             size_t size,
                                             const Cvc5Term assertions[],
                                             const char* names[]);
/** @} */

#if __cplusplus
}
#endif
#endif
