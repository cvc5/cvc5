/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check macros for the cvc5 C++ API.
 *
 * These macros implement guards for the cvc5 C++ API functions.
 */

#include "cvc5_private.h"

#ifndef CVC5__API__CHECKS_H
#define CVC5__API__CHECKS_H

#include <cvc5/cvc5.h>

#include <sstream>

#include "base/modal_exception.h"
#include "options/option_exception.h"

namespace cvc5 {

#define CVC5_API_TRY_CATCH_BEGIN \
  try                            \
  {
#define CVC5_API_TRY_CATCH_END                         \
  }                                                    \
  catch (const internal::OptionException& e)           \
  {                                                    \
    throw CVC5ApiOptionException(e.getMessage());      \
  }                                                    \
  catch (const internal::RecoverableModalException& e) \
  {                                                    \
    throw CVC5ApiRecoverableException(e.getMessage()); \
  }                                                    \
  catch (const internal::Exception& e)                 \
  {                                                    \
    throw CVC5ApiException(e.getMessage());            \
  }                                                    \
  catch (const std::invalid_argument& e) { throw CVC5ApiException(e.what()); }

/* -------------------------------------------------------------------------- */
/* API guard helpers                                                          */
/* -------------------------------------------------------------------------- */

class CVC5ApiExceptionStream
{
 public:
  CVC5ApiExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC5ApiExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC5ApiException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

class CVC5ApiRecoverableExceptionStream
{
 public:
  CVC5ApiRecoverableExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC5ApiRecoverableExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC5ApiRecoverableException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

class CVC5ApiUnsupportedExceptionStream
{
 public:
  CVC5ApiUnsupportedExceptionStream() {}
  /* Note: This needs to be explicitly set to 'noexcept(false)' since it is
   * a destructor that throws an exception and in C++11 all destructors
   * default to noexcept(true) (else this triggers a call to std::terminate). */
  ~CVC5ApiUnsupportedExceptionStream() noexcept(false)
  {
    if (std::uncaught_exceptions() == 0)
    {
      throw CVC5ApiUnsupportedException(d_stream.str());
    }
  }

  std::ostream& ostream() { return d_stream; }

 private:
  std::stringstream d_stream;
};

/* -------------------------------------------------------------------------- */
/* Basic check macros.                                                        */
/* -------------------------------------------------------------------------- */

/**
 * The base check macro.
 * Throws a CVC5ApiException if 'cond' is false.
 */
#define CVC5_API_CHECK(cond) \
  CVC5_PREDICT_TRUE(cond)    \
  ? (void)0                  \
  : cvc5::internal::OstreamVoider() & cvc5::CVC5ApiExceptionStream().ostream()

/**
 * The base check macro for throwing recoverable exceptions.
 * Throws a CVC5ApiRecoverableException if 'cond' is false.
 */
#define CVC5_API_RECOVERABLE_CHECK(cond) \
  CVC5_PREDICT_TRUE(cond)                \
  ? (void)0                              \
  : cvc5::internal::OstreamVoider()      \
          & cvc5::CVC5ApiRecoverableExceptionStream().ostream()

/**
 * The base check macro for throwing unsupported exceptions.
 * Throws a CVC5ApiUnsupportedException if 'cond' is false.
 */
#define CVC5_API_UNSUPPORTED_CHECK(cond) \
  CVC5_PREDICT_TRUE(cond)                \
  ? (void)0                              \
  : cvc5::internal::OstreamVoider()      \
          & cvc5::CVC5ApiUnsupportedExceptionStream().ostream()

/* -------------------------------------------------------------------------- */
/* Not null checks.                                                           */
/* -------------------------------------------------------------------------- */

/** Check it 'this' is not a null object. */
#define CVC5_API_CHECK_NOT_NULL                     \
  CVC5_API_CHECK(!isNullHelper())                   \
      << "invalid call to '" << __PRETTY_FUNCTION__ \
      << "', expected non-null object"

/** Check if given argument is not a null object. */
#define CVC5_API_ARG_CHECK_NOT_NULL(arg) \
  CVC5_API_CHECK(!arg.isNull()) << "invalid null argument for '" << #arg << "'";

/** Check if given argument is not a null pointer. */
#define CVC5_API_ARG_CHECK_NOT_NULLPTR(arg) \
  CVC5_API_CHECK(arg != nullptr)            \
      << "invalid null argument for '" << #arg << "'"
/**
 * Check if given argument at given index in container 'args' is not a null
 * object.
 */
#define CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(what, arg, args, idx)      \
  CVC5_API_CHECK(!arg.isNull()) << "invalid null " << (what) << " in '" \
                                << #args << "' at index " << (idx)

/* -------------------------------------------------------------------------- */
/* Kind checks.                                                               */
/* -------------------------------------------------------------------------- */

/** Check if given kind is a valid kind. */
#define CVC5_API_KIND_CHECK(kind)     \
  CVC5_API_CHECK(isDefinedKind(kind)) \
      << "invalid kind '" << std::to_string(kind) << "'"

/**
 * Check if given kind is a valid kind.
 * Creates a stream to provide a message that identifies what kind was expected
 * if given kind is invalid.
 */
#define CVC5_API_KIND_CHECK_EXPECTED(cond, kind) \
  CVC5_PREDICT_TRUE(cond)                        \
  ? (void)0                                      \
  : cvc5::internal::OstreamVoider()              \
          & CVC5ApiExceptionStream().ostream()   \
                << "invalid kind '" << std::to_string(kind) << "', expected "

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
  : cvc5::internal::OstreamVoider()                                 \
          & CVC5ApiExceptionStream().ostream()                      \
                << "invalid argument '" << arg << "' for '" << #arg \
                << "', expected "

/**
 * Check condition 'cond' for given argument 'arg'.
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false and throws a recoverable exception.
 */
#define CVC5_API_RECOVERABLE_ARG_CHECK_EXPECTED(cond, arg)          \
  CVC5_PREDICT_TRUE(cond)                                           \
  ? (void)0                                                         \
  : cvc5::internal::OstreamVoider()                                 \
          & CVC5ApiRecoverableExceptionStream().ostream()           \
                << "invalid argument '" << arg << "' for '" << #arg \
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
  : cvc5::internal::OstreamVoider()                 \
          & CVC5ApiExceptionStream().ostream()      \
                << "invalid size of argument '" << #arg << "', expected "

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
  : cvc5::internal::OstreamVoider()                                          \
          & CVC5ApiExceptionStream().ostream()                               \
                << "invalid " << (what) << " in '" << #args << "' at index " \
                << (idx) << ", expected "

/**
 * Check condition 'cond' for given operator index `index` in list of indices
 * `args`. Creates a stream to provide a message that identifies what was
 * expected to hold if condition is false and throws a non-recoverable
 * exception.
 */
#define CVC5_API_CHECK_OP_INDEX(cond, args, index)                            \
  CVC5_PREDICT_TRUE(cond)                                                     \
  ? (void)0                                                                   \
  : cvc5::internal::OstreamVoider()                                           \
          & CVC5ApiExceptionStream().ostream()                                \
                << "invalid value '" << args[index] << "' at index " << index \
                << " for operator, expected "

/* -------------------------------------------------------------------------- */
/* Term manager check.                                                        */
/* -------------------------------------------------------------------------- */

/**
 * Term manager check for member functions of classes other than class Solver.
 * Check if given term manager matches the term manager this solver object is
 * associated with.
 */
#define CVC5_API_ARG_CHECK_TM(what, arg)                  \
  CVC5_API_CHECK(d_tm->d_nm == arg.d_tm->d_nm)            \
      << "Given " << (what)                               \
      << " is not associated with the term manager this " \
      << "object is associated with"

/* -------------------------------------------------------------------------- */
/* Sort checks.                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Sort check for member functions of classes other than class Solver.
 * Check if given sort is not null and associated with the term manager this
 * object is associated with.
 */
#define CVC5_API_CHECK_SORT(sort)        \
  do                                     \
  {                                      \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);   \
    CVC5_API_ARG_CHECK_TM("sort", sort); \
  } while (0)

/**
 * Sort check for member functions of classes other than class Solver.
 * Check if each sort in the given container of sorts is not null and
 * associated with the term manager this object is associated with.
 */
#define CVC5_API_CHECK_SORTS(sorts)                                           \
  do                                                                          \
  {                                                                           \
    size_t i = 0;                                                             \
    for (const auto& s : sorts)                                               \
    {                                                                         \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", s, sorts, i);              \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          d_tm->d_nm == s.d_tm->d_nm, "sort", sorts, i)                       \
          << "a sort associated with term manager this object is associated " \
             "with";                                                          \
      i += 1;                                                                 \
    }                                                                         \
  } while (0)

/**
 * Sort check for member functions of classes other than class Solver.
 * Check if each sort in the given container of sorts is not null, is
 * associated with the term manager this object is associated with, and is a
 * first-class sort.
 */
#define CVC5_API_CHECK_DOMAIN_SORTS(sorts)                             \
  do                                                                   \
  {                                                                    \
    size_t i = 0;                                                      \
    for (const auto& s : sorts)                                        \
    {                                                                  \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", s, sorts, i);       \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                            \
          d_tm->d_nm == s.d_tm->d_nm, "sort", sorts, i)                \
          << "a sort associated with the term manager this object is " \
             "associated "                                             \
             "with";                                                   \
      CVC5_API_ARG_CHECK_EXPECTED(s.getTypeNode().isFirstClass(), s)   \
          << "first-class sort as domain sort";                        \
      i += 1;                                                          \
    }                                                                  \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Term checks.                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Term check for member functions of classes other than class Solver.
 * Check if given term is not null and associated with the term manager this
 * object is associated with.
 */
#define CVC5_API_CHECK_TERM(term)        \
  do                                     \
  {                                      \
    CVC5_API_ARG_CHECK_NOT_NULL(term);   \
    CVC5_API_ARG_CHECK_TM("term", term); \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term in the given container of terms is not null and
 * associated with the term manager this object is associated with.
 */
#define CVC5_API_CHECK_TERMS(terms)                                    \
  do                                                                   \
  {                                                                    \
    size_t i = 0;                                                      \
    for (const auto& s : terms)                                        \
    {                                                                  \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", s, terms, i);       \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                            \
          d_tm->d_nm == s.d_tm->d_nm, "term", terms, i)                \
          << "a term associated with the term manager this object is " \
             "associated "                                             \
             "with";                                                   \
      i += 1;                                                          \
    }                                                                  \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term and sort in the given map (which maps terms to sorts) is
 * not null and associated with the term manager this object is associated
 * with.
 */
#define CVC5_API_CHECK_TERMS_MAP(map)                                  \
  do                                                                   \
  {                                                                    \
    size_t i = 0;                                                      \
    for (const auto& p : map)                                          \
    {                                                                  \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", p.first, map, i);   \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                            \
          d_tm->d_nm == p.first.d_tm->d_nm, "term", map, i)            \
          << "a term associated with the term manager this object is " \
             "associated "                                             \
             "with";                                                   \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", p.second, map, i);  \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                            \
          d_tm->d_nm == p.second.d_tm->d_nm, "sort", map, i)           \
          << "a sort associated with the term manager this object is " \
             "associated "                                             \
             "with";                                                   \
      i += 1;                                                          \
    }                                                                  \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term in the given container is not null, associated with the
 * term manager object this object is associated with, and of the given sort.
 */
#define CVC5_API_CHECK_TERMS_WITH_SORT(terms, sort)                            \
  do                                                                           \
  {                                                                            \
    size_t i = 0;                                                              \
    for (const auto& t : terms)                                                \
    {                                                                          \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t, terms, i);               \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                    \
          d_tm->d_nm == t.d_tm->d_nm, "term", terms, i)                        \
          << "a term associated with the term manager this object is "         \
             "associated "                                                     \
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
 * the term manager this object is associated with, and their sorts are
 * pairwise equal.
 */
#define CVC5_API_TERM_CHECK_TERMS_WITH_TERMS_SORT_EQUAL_TO(terms1, terms2) \
  do                                                                       \
  {                                                                        \
    size_t i = 0;                                                          \
    for (const auto& t1 : terms1)                                          \
    {                                                                      \
      const auto& t2 = terms2[i];                                          \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t1, terms1, i);         \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                \
          d_tm->d_nm == t1.d_tm->d_nm, "term", terms1, i)                  \
          << "a term associated with the term manager this object is "     \
             "associated "                                                 \
             "with";                                                       \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t2, terms2, i);         \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                \
          d_tm->d_nm == t2.d_tm->d_nm, "term", terms2, i)                  \
          << "a term associated with the term manager this object is "     \
             "associated "                                                 \
             "with";                                                       \
      CVC5_API_CHECK(t1.getSort() == t2.getSort())                         \
          << "expecting terms of the same sort at index " << i;            \
      i += 1;                                                              \
    }                                                                      \
  } while (0)

/* -------------------------------------------------------------------------- */
/* DatatypeDecl checks.                                                       */
/* -------------------------------------------------------------------------- */

/**
 * DatatypeDecl check for member functions of classes other than class Solver.
 * Check if given datatype declaration is not null and associated with the
 * term manager this DatatypeDecl object is associated with.
 */
#define CVC5_API_CHECK_DTDECL(decl)                                      \
  do                                                                     \
  {                                                                      \
    CVC5_API_ARG_CHECK_NOT_NULL(decl);                                   \
    CVC5_API_CHECK(d_tm->d_nm == decl.d_tm->d_nm)                        \
        << "Given datatype declaration is not associated with the term " \
           "manager this "                                               \
        << "object is associated with";                                  \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Checks for class TermManager.                                              */
/* -------------------------------------------------------------------------- */

/**
 * Term manager check for member functions of class TermManager.
 * Check if given term manager matches the term manager this term manager.
 */
#define CVC5_API_ARG_TM_CHECK_TM(what, arg) \
  CVC5_API_CHECK(d_nm == arg.d_tm->d_nm)    \
      << "Given " << (what) << " is not associated with this term manager"
/**
 * Sort check for member functions of class TermManager.
 * Check if given sort is not null and associated with this term manager.
 */
#define CVC5_API_TM_CHECK_SORT(sort)        \
  do                                        \
  {                                         \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);      \
    CVC5_API_ARG_TM_CHECK_TM("sort", sort); \
  } while (0)

/**
 * Sort check for member functions of class TermManager.
 * Check if given sort at given index of given sorts is not null and associated
 * with this term manager.
 */
#define CVC5_API_TM_CHECK_SORT_AT_INDEX(sort, sorts, index)       \
  do                                                              \
  {                                                               \
    CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", sort, sorts, i); \
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                         \
        d_nm == sort.d_tm->d_nm, "sort", sorts, i)                \
        << "a sort associated with this term manager";            \
  } while (0)

/**
 * Sort checks for member functions of class TermManager.
 * Check if each sort in the given container of sorts is not null and
 * associated with the term manager of this solver.
 */
#define CVC5_API_TM_CHECK_SORTS(sorts)              \
  do                                                \
  {                                                 \
    size_t i = 0;                                   \
    for (const auto& s : sorts)                     \
    {                                               \
      CVC5_API_TM_CHECK_SORT_AT_INDEX(s, sorts, i); \
      i += 1;                                       \
    }                                               \
  } while (0)

/**
 * Domain sort checks for member functions of class TermManager.
 * Check if each domain sort in the given container of sorts is not null,
 * associated with this term manager, and a first-class sort.
 */
#define CVC5_API_TM_CHECK_DOMAIN_SORTS(sorts)                           \
  do                                                                    \
  {                                                                     \
    size_t i = 0;                                                       \
    for (const auto& s : sorts)                                         \
    {                                                                   \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("domain sort", s, sorts, i); \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                             \
          d_nm == s.d_tm->d_nm, "domain sort", sorts, i)                \
          << "a sort associated with this term manager";                \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                             \
          s.getTypeNode().isFirstClass(), "domain sort", sorts, i)      \
          << "first-class sort as domain sort";                         \
      i += 1;                                                           \
    }                                                                   \
  } while (0)

/**
 * Domain sort check for member functions of class TermManager.
 * Check if domain sort is not null, associated with this term manager, and a
 * first-class sort.
 */
#define CVC5_API_TM_CHECK_DOMAIN_SORT(sort)                              \
  do                                                                     \
  {                                                                      \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);                                   \
    CVC5_API_CHECK(d_nm == sort.d_tm->d_nm)                              \
        << "Given sort is not associated with "                          \
           "this term manager";                                          \
    CVC5_API_ARG_CHECK_EXPECTED(sort.getTypeNode().isFirstClass(), sort) \
        << "first-class sort as domain sort";                            \
  } while (0)

/**
 * Codomain sort check for member functions of class TermManager.
 * Check if codomain sort is not null, associated with this term manager, and a
 * first-class, non-function sort.
 */
#define CVC5_API_TM_CHECK_CODOMAIN_SORT(sort)             \
  do                                                      \
  {                                                       \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);                    \
    CVC5_API_CHECK(d_nm == sort.d_tm->d_nm)               \
        << "Given sort is not associated with "           \
           "this term manager";                           \
    CVC5_API_ARG_CHECK_EXPECTED(!sort.isFunction(), sort) \
        << "non-function sort as codomain sort";          \
  } while (0)

/**
 * Op checks for member functions of class TermManager.
 * Check if given operator is not null and associated with this term manager.
 */
#define CVC5_API_TM_CHECK_OP(op)               \
  do                                           \
  {                                            \
    CVC5_API_ARG_CHECK_NOT_NULL(op);           \
    CVC5_API_CHECK(d_nm == op.d_tm->d_nm)      \
        << "Given operator is not associated " \
           "with this term manager";           \
  } while (0)

/**
 * Term check for member functions of class TermManager.
 * Check if given term is not null and associated with this term manager.
 */
#define CVC5_API_TM_CHECK_TERM(term)        \
  do                                        \
  {                                         \
    CVC5_API_ARG_CHECK_NOT_NULL(term);      \
    CVC5_API_ARG_TM_CHECK_TM("term", term); \
  } while (0)

/**
 * Term checks for member functions of class TermManager.
 * Check if given term 't' (which is stored at index 'idx' of 'terms') is not
 * null and associated with this term manager.
 */
#define CVC5_API_TM_CHECK_TERM_AT_INDEX(t, terms, idx)           \
  do                                                             \
  {                                                              \
    CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t, terms, idx); \
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                        \
        d_nm == t.d_tm->d_nm, "term", terms, idx)                \
        << "a term associated with this term manager";           \
  } while (0)

/**
 * Term checks for member functions of class TermManager.
 * Check if each term in the given container of terms is not null and
 * associated with this term manager.
 */
#define CVC5_API_TM_CHECK_TERMS(terms)                   \
  for (size_t i = 0, size = terms.size(); i < size; ++i) \
  {                                                      \
    CVC5_API_TM_CHECK_TERM_AT_INDEX(terms[i], terms, i); \
  }

/**
 * DatatypeDecl checks for member functions of class TermManager.
 * Check if given datatype declaration is not null and associated with this
 * term manager.
 */
#define CVC5_API_TM_CHECK_DTDECL(decl)                                    \
  do                                                                      \
  {                                                                       \
    CVC5_API_ARG_CHECK_NOT_NULL(decl);                                    \
    CVC5_API_ARG_TM_CHECK_TM("datatype declaration", decl);               \
    CVC5_API_CHECK(!decl.isResolved())                                    \
        << "Given datatype declaration is already resolved (has already " \
        << "been used to create a datatype sort)";                        \
    CVC5_API_ARG_CHECK_EXPECTED(                                          \
        dtypedecl.getDatatype().getNumConstructors() > 0, dtypedecl)      \
        << "a datatype declaration with at least one constructor";        \
  } while (0)

/**
 * DatatypeDecl checks for member functions of class TermManager.
 * Check if each datatype declaration in the given container of declarations is
 * not null and associated with this term manager.
 */
#define CVC5_API_TM_CHECK_DTDECLS(decls)                                 \
  do                                                                     \
  {                                                                      \
    size_t i = 0;                                                        \
    for (const auto& d : decls)                                          \
    {                                                                    \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(                              \
          "datatype declaration", d, decls, i);                          \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                              \
          d_nm == d.d_tm->d_nm, "datatype declaration", decls, i)        \
          << "a datatype declaration associated with this term manager"; \
      CVC5_API_CHECK(!d.isResolved())                                    \
          << "Given datatype declaration is already resolved (has "      \
          << "already been used to create a datatype sort)";             \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                              \
          d.getDatatype().getNumConstructors() > 0,                      \
          "datatype declaration",                                        \
          decls,                                                         \
          i)                                                             \
          << "a datatype declaration with at least one constructor";     \
      i += 1;                                                            \
    }                                                                    \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Checks for class Solver.                                                   */
/* -------------------------------------------------------------------------- */

/* Sort checks. ------------------------------------------------------------- */

/**
 * Sort checks for member functions of class Solver.
 * Check if given sort is not null and associated with the term manager of this
 * solver.
 */
#define CVC5_API_SOLVER_CHECK_SORT(sort)         \
  do                                             \
  {                                              \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);           \
    CVC5_API_CHECK(d_tm.d_nm == sort.d_tm->d_nm) \
        << "Given sort is not associated with "  \
           "the term manager of this solver";    \
  } while (0)

/**
 * Sort checks for member functions of class Solver.
 * Check if each sort in the given container of sorts is not null and
 * associated with the term manager of this solver.
 */
#define CVC5_API_SOLVER_CHECK_SORTS(sorts)                             \
  do                                                                   \
  {                                                                    \
    size_t i = 0;                                                      \
    for (const auto& s : sorts)                                        \
    {                                                                  \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("sorts", s, sorts, i);      \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                            \
          d_tm.d_nm == s.d_tm->d_nm, "sort", sorts, i)                 \
          << "a sort associated with the term manager of this solver"; \
      i += 1;                                                          \
    }                                                                  \
  } while (0)

/**
 * Domain sort checks for member functions of class Solver.
 * Check if each domain sort in the given container of sorts is not null,
 * associated with the term manager of this solver, and a first-class sort.
 */
#define CVC5_API_SOLVER_CHECK_DOMAIN_SORTS(sorts)                             \
  do                                                                          \
  {                                                                           \
    size_t i = 0;                                                             \
    for (const auto& s : sorts)                                               \
    {                                                                         \
      CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("domain sort", s, sorts, i);       \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          d_tm.d_nm == s.d_tm->d_nm, "domain sort", sorts, i)                 \
          << "a sort associated with the term manager of this solver object"; \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          s.getTypeNode().isFirstClass(), "domain sort", sorts, i)            \
          << "first-class sort as domain sort";                               \
      i += 1;                                                                 \
    }                                                                         \
  } while (0)

/**
 * Codomain sort check for member functions of class Solver.
 * Check if codomain sort is not null, associated with the term manager of this
 * solver, and a first-class, non-function sort.
 */
#define CVC5_API_SOLVER_CHECK_CODOMAIN_SORT(sort)         \
  do                                                      \
  {                                                       \
    CVC5_API_ARG_CHECK_NOT_NULL(sort);                    \
    CVC5_API_CHECK(d_tm.d_nm == sort.d_tm->d_nm)          \
        << "Given sort is not associated with "           \
           "the term manager of this solver";             \
    CVC5_API_ARG_CHECK_EXPECTED(!sort.isFunction(), sort) \
        << "non-function sort as codomain sort";          \
  } while (0)

/* Term checks. ------------------------------------------------------------- */

/**
 * Term checks for member functions of class Solver.
 * Check if given term is not null and associated with the term manager of this
 * solver.
 */
#define CVC5_API_SOLVER_CHECK_TERM(term)         \
  do                                             \
  {                                              \
    CVC5_API_ARG_CHECK_NOT_NULL(term);           \
    CVC5_API_CHECK(d_tm.d_nm == term.d_tm->d_nm) \
        << "Given term is not associated with "  \
           "the term manager of this solver";    \
  } while (0)

/**
 * Term checks for member functions of class Solver.
 * Check if given term 't' (which is stored at index 'idx' of 'terms') is not
 * null and associated with the term manager of this solver.
 */
#define CVC5_API_SOLVER_CHECK_TERM_AT_INDEX(t, terms, idx)           \
  do                                                                 \
  {                                                                  \
    CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t, terms, idx);     \
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                            \
        d_tm.d_nm == t.d_tm->d_nm, "term", terms, idx)               \
        << "a term associated with the term manager of this solver"; \
  } while (0)

/**
 * Term checks for member functions of class Solver.
 * Check if each term in the given container of terms is not null and
 * associated with the term manager of this solver.
 */
#define CVC5_API_SOLVER_CHECK_TERMS(terms)              \
  do                                                    \
  {                                                     \
    size_t i = 0;                                       \
    for (const auto& t : terms)                         \
    {                                                   \
      CVC5_API_SOLVER_CHECK_TERM_AT_INDEX(t, terms, i); \
      i += 1;                                           \
    }                                                   \
  } while (0)

/**
 * Term checks for member functions of class Solver.
 * Check if given term is not null, associated with the term manager of this
 * solver, and of given sort.
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
 * Check if each term in the given container is not null, associated with the
 * term manager of this solver, and of the given sort.
 */
#define CVC5_API_SOLVER_CHECK_TERMS_WITH_SORT(terms, sort)                   \
  for (size_t i = 0, size = terms.size(); i < size; ++i)                     \
  {                                                                          \
    CVC5_API_SOLVER_CHECK_TERM_AT_INDEX(terms[i], terms, i);                 \
    CVC5_API_CHECK(terms[i].getSort() == sort)                               \
        << "Expected term with sort " << sort << " at index " << i << " in " \
        << #terms;                                                           \
  }

/**
 * Bound variable checks for member functions of class Solver.
 * Check if given term 'bv' (which is stored at index 'idx' of 'bound_vars') is
 * not null, associated with the term manager of this solver, and a bound
 * variable.
 */
#define CVC5_API_SOLVER_CHECK_BOUND_VAR_AT_INDEX(bv, bound_vars, idx) \
  do                                                                  \
  {                                                                   \
    CVC5_API_SOLVER_CHECK_TERM_AT_INDEX(bv, bound_vars, idx);         \
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                             \
        bv.d_node->getKind() == cvc5::internal::Kind::BOUND_VARIABLE, \
        "bound variable",                                             \
        bound_vars,                                                   \
        idx)                                                          \
        << "a bound variable";                                        \
  } while (0)

/**
 * Bound variable checks for member functions of class Solver.
 * Check if each term in the given container is not null, associated with the
 * term manager of this solver, and a bound variable.
 */
#define CVC5_API_SOLVER_CHECK_BOUND_VARS(bound_vars)                        \
  for (size_t i = 0, size = bound_vars.size(); i < size; ++i)               \
  {                                                                         \
    CVC5_API_SOLVER_CHECK_BOUND_VAR_AT_INDEX(bound_vars[i], bound_vars, i); \
  }

/**
 * Additional bound variable checks for member functions of class Solver that
 * define functions.
 * Check if each term in the given container matches the corresponding sort in
 * 'domain_sorts', and is a first-class term.
 */
#define CVC5_API_SOLVER_CHECK_BOUND_VARS_DEF_FUN_SORTS(bound_vars,            \
                                                       domain_sorts)          \
  do                                                                          \
  {                                                                           \
    size_t size = bound_vars.size();                                          \
    CVC5_API_ARG_SIZE_CHECK_EXPECTED(size == domain_sorts.size(), bound_vars) \
        << "'" << domain_sorts.size() << "'";                                 \
    for (size_t i = 0; i < size; ++i)                                         \
    {                                                                         \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          domain_sorts[i] == bound_vars[i].getSort(),                         \
          "sort of parameter",                                                \
          bound_vars,                                                         \
          i)                                                                  \
          << "sort '" << domain_sorts[i] << "'";                              \
      CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(                                   \
          domain_sorts[i].getTypeNode().isFirstClass(),                       \
          "domain sort",                                                      \
          domain_sorts,                                                       \
          i)                                                                  \
          << "first-class sort of parameter of defined function";             \
    }                                                                         \
  } while (0)

/**
 * Grammar checks for member functions of class Solver.
 * Check if given grammar is not null and associated with the term manager of
 * this solver.
 */
#define CVC5_API_SOLVER_CHECK_GRAMMAR(grammar)      \
  do                                                \
  {                                                 \
    CVC5_API_ARG_CHECK_NOT_NULL(grammar);           \
    CVC5_API_CHECK(d_tm.d_nm == grammar.d_tm->d_nm) \
        << "Given grammar is not associated with "  \
           "the term manager of this solver";       \
  } while (0)

/* Datatype checks. --------------------------------------------------------- */

/**
 * DatatypeConstructorDecl checks for member functions of class Solver.
 * Check if a given datatype constructor declaration at the index in the given
 * container of declarations is not null and associated with the term manager of
 * this solver.
 */
#define CVC5_API_SOLVER_CHECK_DTCTORDECL_AT_INDEX(decl, decls, idx)          \
  do                                                                         \
  {                                                                          \
    CVC5_API_ARG_AT_INDEX_CHECK_NOT_NULL(                                    \
        "datatype constructor declaration", decl, decls, idx);               \
    CVC5_API_ARG_AT_INDEX_CHECK_EXPECTED(d_tm.d_nm == decl.d_tm->d_nm,       \
                                         "datatype constructor declaration", \
                                         decls,                              \
                                         idx)                                \
        << "a datatype constructor declaration associated with the term "    \
           "manager of this solver "                                         \
           "object";                                                         \
  } while (0)

/**
 * DatatypeConstructorDecl checks for member functions of class Solver.
 * Check if each datatype constructor declaration in the given container of
 * declarations is not null and associated with the term manager of this solver.
 */
#define CVC5_API_SOLVER_CHECK_DTCTORDECLS(decls)                   \
  for (size_t i = 0, size = decls.size(); i < size; ++i)           \
  {                                                                \
    CVC5_API_SOLVER_CHECK_DTCTORDECL_AT_INDEX(decls[i], decls, i); \
  }

/**
 * Argument number checks for mkOp.
 */
#define CVC5_API_OP_CHECK_ARITY(nargs, expected, kind)                      \
  CVC5_API_CHECK(nargs == expected)                                         \
      << "invalid number of indices for operator " << kind << ", expected " \
      << expected << " but got " << nargs << "."

}  // namespace cvc5
#endif
