/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check macros for the cvc5 C++ API.
 *
 * These macros implement guards for the cvc5 C++ API functions.
 */

#include "cvc5_public.h"

#ifndef CVC5__API__CHECKS_H
#define CVC5__API__CHECKS_H

namespace cvc5 {
namespace api {

/* -------------------------------------------------------------------------- */
/* Basic check macros.                                                        */
/* -------------------------------------------------------------------------- */

/**
 * The base check macro.
 * Throws a CVC5ApiException if 'cond' is false.
 */
#define CVC5_API_CHECK(cond) \
  CVC5_PREDICT_TRUE(cond)    \
  ? (void)0 : OstreamVoider() & CVC5ApiExceptionStream().ostream()

/**
 * The base check macro for throwing recoverable exceptions.
 * Throws a CVC5ApiRecoverableException if 'cond' is false.
 */
#define CVC5_API_RECOVERABLE_CHECK(cond) \
  CVC5_PREDICT_TRUE(cond)                \
  ? (void)0 : OstreamVoider() & CVC5ApiRecoverableExceptionStream().ostream()

/* -------------------------------------------------------------------------- */
/* Not null checks.                                                           */
/* -------------------------------------------------------------------------- */

/** Check it 'this' is not a null object. */
#define CVC5_API_CHECK_NOT_NULL                     \
  CVC5_API_CHECK(!isNullHelper())                   \
      << "Invalid call to '" << __PRETTY_FUNCTION__ \
      << "', expected non-null object";

/** Check if given argument is not a null object. */
#define CVC5_API_ARG_CHECK_NOT_NULL(arg) \
  CVC5_API_CHECK(!arg.isNull()) << "Invalid null argument for '" << #arg << "'";

/** Check if given argument is not a null pointer. */
#define CVC5_API_ARG_CHECK_NOT_NULLPTR(arg) \
  CVC5_API_CHECK(arg != nullptr)            \
      << "Invalid null argument for '" << #arg << "'";
/**
 * Check if given argument at given index in container 'args' is not a null
 * object.
 */
#define CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(what, arg, args, idx)      \
  CVC5_API_CHECK(!arg.isNull()) << "Invalid null " << (what) << " in '" \
                                << #args << "' at index " << (idx);

/* -------------------------------------------------------------------------- */
/* Kind checks.                                                               */
/* -------------------------------------------------------------------------- */

/** Check if given kind is a valid kind. */
#define CVC5_API_KIND_CHECK(kind)     \
  CVC5_API_CHECK(isDefinedKind(kind)) \
      << "Invalid kind '" << kindToString(kind) << "'";

/**
 * Check if given kind is a valid kind.
 * Creates a stream to provide a message that identifies what kind was expected
 * if given kind is invalid.
 */
#define CVC5_API_KIND_CHECK_EXPECTED(cond, kind) \
  CVC5_PREDICT_TRUE(cond)                        \
  ? (void)0                                      \
  : OstreamVoider()                              \
          & CVC5ApiExceptionStream().ostream()   \
                << "Invalid kind '" << kindToString(kind) << "', expected "

/* -------------------------------------------------------------------------- */
/* Argument checks.                                                           */
/* -------------------------------------------------------------------------- */

/**
 * Check condition 'cond' for given argument 'arg'.
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false and throws a non-recoverable exception.
 */
#define CVC5_API_ARG_CHECK_EXPECTED(cond, arg)                      \
  CVC5_PREDICT_TRUE(cond)                                           \
  ? (void)0                                                         \
  : OstreamVoider()                                                 \
          & CVC5ApiExceptionStream().ostream()                      \
                << "Invalid argument '" << arg << "' for '" << #arg \
                << "', expected "

/**
 * Check condition 'cond' for given argument 'arg'.
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false and throws a recoverable exception.
 */
#define CVC5_API_RECOVERABLE_ARG_CHECK_EXPECTED(cond, arg)          \
  CVC5_PREDICT_TRUE(cond)                                           \
  ? (void)0                                                         \
  : OstreamVoider()                                                 \
          & CVC5ApiRecoverableExceptionStream().ostream()           \
                << "Invalid argument '" << arg << "' for '" << #arg \
                << "', expected "

/**
 * Check condition 'cond' for given argument 'arg'.
 * Provides a more specific error message than CVC5_API_ARG_CHECK_EXPECTED,
 * it identifies that this check is a size check.
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false and throws a recoverable exception.
 */
#define CVC5_API_ARG_SIZE_CHECK_EXPECTED(cond, arg) \
  CVC5_PREDICT_TRUE(cond)                           \
  ? (void)0                                         \
  : OstreamVoider()                                 \
          & CVC5ApiExceptionStream().ostream()      \
                << "Invalid size of argument '" << #arg << "', expected "

/**
 * Check condition 'cond' for the argument at given index in container 'args'.
 * Argument 'what' identifies what is being checked (e.g., "term").
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false.
 * Usage:
 *   CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(
 *     <condition>, "what", <container>, <idx>) << "message";
 */
#define CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(cond, what, args, idx)          \
  CVC5_PREDICT_TRUE(cond)                                                    \
  ? (void)0                                                                  \
  : OstreamVoider()                                                          \
          & CVC5ApiExceptionStream().ostream()                               \
                << "Invalid " << (what) << " in '" << #args << "' at index " \
                << (idx) << ", expected "

/* -------------------------------------------------------------------------- */
/* Solver checks.                                                             */
/* -------------------------------------------------------------------------- */

/**
 * Solver check for member functions of classes other than class Solver.
 * Check if given solver matches the solver object this object is associated
 * with.
 */
#define CVC5_API_ARG_CHECK_SOLVER(what, arg)                              \
  CVC5_API_CHECK(this->d_solver == arg.d_solver)                          \
      << "Given " << (what) << " is not associated with the solver this " \
      << "object is associated with";

/* -------------------------------------------------------------------------- */
/* Sort checks.                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Sort check for member functions of classes other than class Solver.
 * Check if given sort is not null and associated with the solver object this
 * object is associated with.
 */
#define CVC5_API_CHECK_SORT(sort)            \
  do                                         \
  {                                          \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);       \
    CVC5_API_ARG_CHECK_SOLVER("sort", sort); \
  } while (0)

/**
 * Sort check for member functions of classes other than class Solver.
 * Check if each sort in the given container of sorts is not null and
 * associated with the solver object this object is associated with.
 */
#define CVC5_API_CHECK_SORTS(sorts)                                         \
  do                                                                        \
  {                                                                         \
    size_t i = 0;                                                           \
    for (const auto& s : sorts)                                             \
    {                                                                       \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", s, sorts, i);            \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == s.d_solver, "sort", sorts, i)                   \
          << "a sort associated with the solver this object is associated " \
             "with";                                                        \
      i += 1;                                                               \
    }                                                                       \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Term checks.                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Term check for member functions of classes other than class Solver.
 * Check if given term is not null and associated with the solver object this
 * object is associated with.
 */
#define CVC5_API_CHECK_TERM(term)            \
  do                                         \
  {                                          \
    CVC5_API_ARG_CHECK_NOT_NULL(term);       \
    CVC5_API_ARG_CHECK_SOLVER("term", term); \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term in the given container of terms is not null and
 * associated with the solver object this object is associated with.
 */
#define CVC5_API_CHECK_TERMS(terms)                                         \
  do                                                                        \
  {                                                                         \
    size_t i = 0;                                                           \
    for (const auto& s : terms)                                             \
    {                                                                       \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", s, terms, i);            \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == s.d_solver, "term", terms, i)                   \
          << "a term associated with the solver this object is associated " \
             "with";                                                        \
      i += 1;                                                               \
    }                                                                       \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term and sort in the given map (which maps terms to sorts) is
 * not null and associated with the solver object this object is associated
 * with.
 */
#define CVC5_API_CHECK_TERMS_MAP(map)                                       \
  do                                                                        \
  {                                                                         \
    size_t i = 0;                                                           \
    for (const auto& p : map)                                               \
    {                                                                       \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", p.first, map, i);        \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == p.first.d_solver, "term", map, i)               \
          << "a term associated with the solver this object is associated " \
             "with";                                                        \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", p.second, map, i);       \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == p.second.d_solver, "sort", map, i)              \
          << "a sort associated with the solver this object is associated " \
             "with";                                                        \
      i += 1;                                                               \
    }                                                                       \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term in the given container is not null, associated with the
 * solver object this object is associated with, and of the given sort.
 */
#define CVC5_API_CHECK_TERMS_WITH_SORT(terms, sort)                            \
  do                                                                           \
  {                                                                            \
    size_t i = 0;                                                              \
    for (const auto& t : terms)                                                \
    {                                                                          \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t, terms, i);               \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                    \
          this->d_solver == t.d_solver, "term", terms, i)                      \
          << "a term associated with the solver this object is associated "    \
             "with";                                                           \
      CVC5_API_CHECK(t.getSort() == sort)                                      \
          << "Expected term with sort " << sort << " at index " << i << " in " \
          << #terms;                                                           \
      i += 1;                                                                  \
    }                                                                          \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term in both the given container is not null, associated with
 * the solver object this object is associated with, and their sorts are
 * pairwise comparable to.
 */
#define CVC5_API_TERM_CHECK_TERMS_WITH_TERMS_COMPARABLE_TO(terms1, terms2)  \
  do                                                                        \
  {                                                                         \
    size_t i = 0;                                                           \
    for (const auto& t1 : terms1)                                           \
    {                                                                       \
      const auto& t2 = terms2[i];                                           \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t1, terms1, i);          \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == t1.d_solver, "term", terms1, i)                 \
          << "a term associated with the solver this object is associated " \
             "with";                                                        \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t2, terms2, i);          \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == t2.d_solver, "term", terms2, i)                 \
          << "a term associated with the solver this object is associated " \
             "with";                                                        \
      CVC5_API_CHECK(t1.getSort().isComparableTo(t2.getSort()))             \
          << "Expecting terms of comparable sort at index " << i;           \
      i += 1;                                                               \
    }                                                                       \
  } while (0)

/* -------------------------------------------------------------------------- */
/* DatatypeDecl checks.                                                       */
/* -------------------------------------------------------------------------- */

/**
 * DatatypeDecl check for member functions of classes other than class Solver.
 * Check if given datatype declaration is not null and associated with the
 * solver object this DatatypeDecl object is associated with.
 */
#define CVC5_API_CHECK_DTDECL(decl)                          \
  do                                                         \
  {                                                          \
    CVC5_API_ARG_CHECK_NOT_NULL(decl);                       \
    CVC5_API_ARG_CHECK_SOLVER("datatype declaration", decl); \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Checks for class Solver.                                                   */
/* -------------------------------------------------------------------------- */

/* Sort checks. ------------------------------------------------------------- */

/**
 * Sort checks for member functions of class Solver.
 * Check if given sort is not null and associated with this solver.
 */
#define CVC5_API_SOLVER_CHECK_SORT(sort)                    \
  do                                                        \
  {                                                         \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);                      \
    CVC5_API_CHECK(this == sort.d_solver)                   \
        << "Given sort is not associated with this solver"; \
  } while (0)

/**
 * Sort checks for member functions of class Solver.
 * Check if each sort in the given container of sorts is not null and
 * associated with this solver.
 */
#define CVC5_API_SOLVER_CHECK_SORTS(sorts)                        \
  do                                                              \
  {                                                               \
    size_t i = 0;                                                 \
    for (const auto& s : sorts)                                   \
    {                                                             \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sorts", s, sorts, i); \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                       \
          this == s.d_solver, "sort", sorts, i)                   \
          << "a sort associated with this solver";                \
      i += 1;                                                     \
    }                                                             \
  } while (0)

/**
 * Sort checks for member functions of class Solver.
 * Check if each sort in the given container of sorts is not null, associated
 * with this solver, and not function-like.
 */
#define CVC5_API_SOLVER_CHECK_SORTS_NOT_FUNCTION_LIKE(sorts)      \
  do                                                              \
  {                                                               \
    size_t i = 0;                                                 \
    for (const auto& s : sorts)                                   \
    {                                                             \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sorts", s, sorts, i); \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                       \
          this == s.d_solver, "sort", sorts, i)                   \
          << "a sorts associated with this solver";               \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                       \
          !s.isFunctionLike(), "sort", sorts, i)                  \
          << "non-function-like sort";                            \
      i += 1;                                                     \
    }                                                             \
  } while (0)

/**
 * Domain sort check for member functions of class Solver.
 * Check if domain sort is not null, associated with this solver, and a
 * first-class sort.
 */
#define CVC5_API_SOLVER_CHECK_DOMAIN_SORT(sort)             \
  do                                                        \
  {                                                         \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);                      \
    CVC5_API_CHECK(this == sort.d_solver)                   \
        << "Given sort is not associated with this solver"; \
    CVC5_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)  \
        << "first-class sort as domain sort";               \
  } while (0)

/**
 * Domain sort checks for member functions of class Solver.
 * Check if each domain sort in the given container of sorts is not null,
 * associated with this solver, and a first-class sort.
 */
#define CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts)                       \
  do                                                                    \
  {                                                                     \
    size_t i = 0;                                                       \
    for (const auto& s : sorts)                                         \
    {                                                                   \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("domain sort", s, sorts, i); \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                             \
          this == s.d_solver, "domain sort", sorts, i)                  \
          << "a sort associated with this solver object";               \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                             \
          s.isFirstClass(), "domain sort", sorts, i)                    \
          << "first-class sort as domain sort";                         \
      i += 1;                                                           \
    }                                                                   \
  } while (0)

/**
 * Codomain sort check for member functions of class Solver.
 * Check if codomain sort is not null, associated with this solver, and a
 * first-class, non-function sort.
 */
#define CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(sort)           \
  do                                                        \
  {                                                         \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);                      \
    CVC5_API_CHECK(this == sort.d_solver)                   \
        << "Given sort is not associated with this solver"; \
    CVC5_API_ARG_CHECK_EXPECTED(sort.isFirstClass(), sort)  \
        << "first-class sort as codomain sort";             \
    CVC5_API_ARG_CHECK_EXPECTED(!sort.isFunction(), sort)   \
        << "function sort as codomain sort";                \
  } while (0)

/* Term checks. ------------------------------------------------------------- */

/**
 * Term checks for member functions of class Solver.
 * Check if given term is not null and associated with this solver.
 */
#define CVC5_API_SOLVER_CHECK_TERM(term)                    \
  do                                                        \
  {                                                         \
    CVC5_API_ARG_CHECK_NOT_NULL(term);                      \
    CVC5_API_CHECK(this == term.d_solver)                   \
        << "Given term is not associated with this solver"; \
  } while (0)

/**
 * Term checks for member functions of class Solver.
 * Check if each term in the given container of terms is not null and
 * associated with this solver.
 */
#define CVC5_API_SOLVER_CHECK_TERMS(terms)                        \
  do                                                              \
  {                                                               \
    size_t i = 0;                                                 \
    for (const auto& t : terms)                                   \
    {                                                             \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("terms", t, terms, i); \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                       \
          this == t.d_solver, "term", terms, i)                   \
          << "a term associated with this solver";                \
      i += 1;                                                     \
    }                                                             \
  } while (0)

/**
 * Term checks for member functions of class Solver.
 * Check if given term is not null, associated with this solver, and of given
 * sort.
 */
#define CVC5_API_SOLVER_CHECK_TERM_WITH_SORT(term, sort) \
  do                                                     \
  {                                                      \
    CVC5_API_SOLVER_CHECK_TERM(term);                    \
    CVC5_API_CHECK(term.getSort() == sort)               \
        << "Expected term with sort " << sort;           \
  } while (0)

/**
 * Term checks for member functions of class Solver.
 * Check if each term in the given container is not null, associated with this
 * solver, and of the given sort.
 */
#define CVC5_API_SOLVER_CHECK_TERMS_WITH_SORT(terms, sort)                     \
  do                                                                           \
  {                                                                            \
    size_t i = 0;                                                              \
    for (const auto& t : terms)                                                \
    {                                                                          \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t, terms, i);               \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                    \
          this == t.d_solver, "term", terms, i)                                \
          << "a term associated with this solver";                             \
      CVC5_API_CHECK(t.getSort() == sort)                                      \
          << "Expected term with sort " << sort << " at index " << i << " in " \
          << #terms;                                                           \
      i += 1;                                                                  \
    }                                                                          \
  } while (0)

/**
 * Bound variable checks for member functions of class Solver.
 * Check if each term in the given container is not null, associated with this
 * solver, and a bound variable.
 */
#define CVC5_API_SOLVER_CHECK_BOUND_VARS(bound_vars)            \
  do                                                            \
  {                                                             \
    size_t i = 0;                                               \
    for (const auto& bv : bound_vars)                           \
    {                                                           \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(                     \
          "bound variable", bv, bound_vars, i);                 \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                     \
          this == bv.d_solver, "bound variable", bound_vars, i) \
          << "a term associated with this solver object";       \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                     \
          bv.d_node->getKind() == cvc5::Kind::BOUND_VARIABLE,   \
          "bound variable",                                     \
          bound_vars,                                           \
          i)                                                    \
          << "a bound variable";                                \
      i += 1;                                                   \
    }                                                           \
  } while (0)

/**
 * Bound variable checks for member functions of class Solver that define
 * functions.
 * Check if each term in the given container is not null, associated with this
 * solver, a bound variable, matches theh corresponding sort in 'domain_sorts',
 * and is a first-class term.
 */
#define CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN(                             \
    fun, bound_vars, domain_sorts)                                            \
  do                                                                          \
  {                                                                           \
    size_t size = bound_vars.size();                                          \
    CVC5_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bound_vars) \
        << "'" << domain_sorts.size() << "'";                                 \
    size_t i = 0;                                                             \
    for (const auto& bv : bound_vars)                                         \
    {                                                                         \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(                                   \
          "bound variable", bv, bound_vars, i);                               \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          this == bv.d_solver, "bound variable", bound_vars, i)               \
          << "a term associated with this solver object";                     \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          bv.d_node->getKind() == cvc5::Kind::BOUND_VARIABLE,                 \
          "bound variable",                                                   \
          bound_vars,                                                         \
          i)                                                                  \
          << "a bound variable";                                              \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          domain_sorts[i] == bound_vars[i].getSort(),                         \
          "sort of parameter",                                                \
          bound_vars,                                                         \
          i);                                                                 \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          domain_sorts[i].isFirstClass(), "domain sort", domain_sorts, i)     \
          << "first-class sort of parameter of defined function";             \
      i += 1;                                                                 \
    }                                                                         \
  } while (0)

/* Op checks. --------------------------------------------------------------- */

/**
 * Op checks for member functions of class Solver.
 * Check if given operator is not null and associated with this solver.
 */
#define CVC5_API_SOLVER_CHECK_OP(op)                            \
  do                                                            \
  {                                                             \
    CVC5_API_ARG_CHECK_NOT_NULL(op);                            \
    CVC5_API_CHECK(this == op.d_solver)                         \
        << "Given operator is not associated with this solver"; \
  } while (0)

/* Datatype checks. --------------------------------------------------------- */

/**
 * DatatypeDecl checks for member functions of class Solver.
 * Check if given datatype declaration is not null and associated with this
 * solver.
 */
#define CVC5_API_SOLVER_CHECK_DTDECL(decl)                                     \
  do                                                                           \
  {                                                                            \
    CVC5_API_ARG_CHECK_NOT_NULL(decl);                                         \
    CVC5_API_CHECK(this == decl.d_solver)                                      \
        << "Given datatype declaration is not associated with this solver";    \
    CVC5_API_ARG_CHECK_EXPECTED(dtypedecl.getNumConstructors() > 0, dtypedecl) \
        << "a datatype declaration with at least one constructor";             \
  } while (0)

/**
 * DatatypeDecl checks for member functions of class Solver.
 * Check if each datatype declaration in the given container of declarations is
 * not null and associated with this solver.
 */
#define CVC5_API_SOLVER_CHECK_DTDECLS(decls)                            \
  do                                                                    \
  {                                                                     \
    size_t i = 0;                                                       \
    for (const auto& d : decls)                                         \
    {                                                                   \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(                             \
          "datatype declaration", d, decls, i);                         \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                             \
          this == d.d_solver, "datatype declaration", decls, i)         \
          << "a datatype declaration associated with this solver";      \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                             \
          d.getNumConstructors() > 0, "datatype declaration", decls, i) \
          << "a datatype declaration with at least one constructor";    \
      i += 1;                                                           \
    }                                                                   \
  } while (0)

/**
 * DatatypeConstructorDecl checks for member functions of class Solver.
 * Check if each datatype constructor declaration in the given container of
 * declarations is not null and associated with this solver.
 */
#define CVC5_API_SOLVER_CHECK_DTCTORDECLS(decls)                               \
  do                                                                           \
  {                                                                            \
    size_t i = 0;                                                              \
    for (const auto& d : decls)                                                \
    {                                                                          \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(                                    \
          "datatype constructor declaration", d, decls, i);                    \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                    \
          this == d.d_solver, "datatype constructor declaration", decls, i)    \
          << "a datatype constructor declaration associated with this solver " \
             "object";                                                         \
      i += 1;                                                                  \
    }                                                                          \
  } while (0)
}  // namespace api
}  // namespace cvc5
#endif
