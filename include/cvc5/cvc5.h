/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C++ API.
 */

#include <cvc5/cvc5_export.h>

#ifndef CVC5__API__CVC5_H
#define CVC5__API__CVC5_H

#include <cvc5/cvc5_kind.h>
#include <cvc5/cvc5_sort_kind.h>
#include <cvc5/cvc5_types.h>

#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

namespace cvc5 {

namespace main {
class CommandExecutor;
}  // namespace main

namespace internal {

#ifndef DOXYGEN_SKIP
template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
#endif

class DType;
class DTypeConstructor;
class DTypeSelector;
class NodeManager;
class SolverEngine;
class TypeNode;
class Options;
class Random;
class Rational;
class Result;
class SygusGrammar;
class SynthResult;
class StatisticsRegistry;
}  // namespace internal

namespace parser {
class Command;
}

class Solver;
class Statistics;
struct APIStatistics;
class Term;

/* -------------------------------------------------------------------------- */
/* Exception                                                                  */
/* -------------------------------------------------------------------------- */

/**
 * Base class for all API exceptions.
 * If thrown, all API objects may be in an unsafe state.
 */
class CVC5_EXPORT CVC5ApiException : public std::exception
{
 public:
  /**
   * Construct with message from a string.
   * @param str The error message.
   */
  CVC5ApiException(const std::string& str) : d_msg(str) {}
  /**
   * Construct with message from a string stream.
   * @param stream The error message.
   */
  CVC5ApiException(const std::stringstream& stream) : d_msg(stream.str()) {}
  /**
   * Retrieve the message from this exception.
   * @return The error message.
   */
  const std::string& getMessage() const { return d_msg; }
  /**
   * Retrieve the message as a C-style array.
   * @return The error message.
   */
  const char* what() const noexcept override { return d_msg.c_str(); }

 private:
  /** The stored error message. */
  std::string d_msg;
};

/**
 * A recoverable API exception.
 * If thrown, API objects can still be used.
 */
class CVC5_EXPORT CVC5ApiRecoverableException : public CVC5ApiException
{
 public:
  /**
   * Construct with message from a string.
   * @param str The error message.
   */
  CVC5ApiRecoverableException(const std::string& str) : CVC5ApiException(str) {}
  /**
   * Construct with message from a string stream.
   * @param stream The error message.
   */
  CVC5ApiRecoverableException(const std::stringstream& stream)
      : CVC5ApiException(stream.str())
  {
  }
};

/**
 * Exception for unsupported command arguments.
 * If thrown, API objects can still be used.
 */
class CVC5_EXPORT CVC5ApiUnsupportedException
    : public CVC5ApiRecoverableException
{
 public:
  /**
   * Construct with message from a string.
   * @param str The error message.
   */
  CVC5ApiUnsupportedException(const std::string& str)
      : CVC5ApiRecoverableException(str)
  {
  }
  /**
   * Construct with message from a string stream.
   * @param stream The error message.
   */
  CVC5ApiUnsupportedException(const std::stringstream& stream)
      : CVC5ApiRecoverableException(stream.str())
  {
  }
};

/**
 * An option-related API exception.
 * If thrown, API objects can still be used.
 */
class CVC5_EXPORT CVC5ApiOptionException : public CVC5ApiRecoverableException
{
 public:
  /**
   * Construct with message from a string.
   * @param str The error message.
   */
  CVC5ApiOptionException(const std::string& str)
      : CVC5ApiRecoverableException(str)
  {
  }
  /**
   * Construct with message from a string stream.
   * @param stream The error message.
   */
  CVC5ApiOptionException(const std::stringstream& stream)
      : CVC5ApiRecoverableException(stream.str())
  {
  }
};

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * Encapsulation of a three-valued solver result, with explanations.
 */
class CVC5_EXPORT Result
{
  friend class Solver;

 public:
  /** Constructor. */
  Result();

  /**
   * Return true if Result is empty, i.e., a nullary Result, and not an actual
   * result returned from a checkSat() (and friends) query.
   */
  bool isNull() const;

  /**
   * Return true if query was a satisfiable checkSat() or checkSatAssuming()
   * query.
   */
  bool isSat() const;

  /**
   * Return true if query was an unsatisfiable checkSat() or
   * checkSatAssuming() query.
   */
  bool isUnsat() const;

  /**
   * Return true if query was a checkSat() or checkSatAssuming() query and
   * cvc5 was not able to determine (un)satisfiability.
   */
  bool isUnknown() const;

  /**
   * Operator overloading for equality of two results.
   * @param r The result to compare to for equality.
   * @return True if the results are equal.
   */
  bool operator==(const Result& r) const;

  /**
   * Operator overloading for disequality of two results.
   * @param r The result to compare to for disequality.
   * @return True if the results are disequal.
   */
  bool operator!=(const Result& r) const;

  /**
   * @return An explanation for an unknown query result.
   */
  UnknownExplanation getUnknownExplanation() const;

  /**
   * @return A string representation of this result.
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param r The internal result that is to be wrapped by this result.
   * @return The Result.
   */
  Result(const internal::Result& r);

  /**
   * The internal result wrapped by this result.
   *
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr``
   *       since ``internal::Result`` is not ref counted.
   */
  std::shared_ptr<internal::Result> d_result;
};

/**
 * Serialize a Result to given stream.
 * @param out The output stream.
 * @param r The result to be serialized to the given output stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Result& r) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* SynthResult                                                                */
/* -------------------------------------------------------------------------- */

/**
 * Encapsulation of a solver synth result.
 *
 * This is the return value of the API methods:
 *   - Solver::checkSynth()
 *   - Solver::checkSynthNext()
 *
 * which we call synthesis queries.  This class indicates whether the
 * synthesis query has a solution, has no solution, or is unknown.
 */
class CVC5_EXPORT SynthResult
{
  friend class Solver;

 public:
  /** Constructor. */
  SynthResult();

  /**
   * @return True if SynthResult is null, i.e., not a SynthResult returned
   *         from a synthesis query.
   */
  bool isNull() const;

  /**
   * @return True if the synthesis query has a solution.
   */
  bool hasSolution() const;

  /**
   * @return True if the synthesis query has no solution. In this case, it
   *         was determined that there was no solution.
   */
  bool hasNoSolution() const;

  /**
   * @return True if the result of the synthesis query could not be determined.
   */
  bool isUnknown() const;

  /**
   * @return A string representation of this synthesis result.
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param r The internal synth result that is to be wrapped by this synth.
   *          result
   * @return The SynthResult.
   */
  SynthResult(const internal::SynthResult& r);
  /**
   * The internal result wrapped by this result.
   *
   * @note This is a `std::shared_ptr` rather than a `std::unique_ptr`
   *       since `internal::SynthResult` is not ref counted.
   */
  std::shared_ptr<internal::SynthResult> d_result;
};

/**
 * Serialize a SynthResult to given stream.
 * @param out The output stream.
 * @param r The result to be serialized to the given output stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const SynthResult& r) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

class Datatype;

/**
 * The sort of a cvc5 term.
 */
class CVC5_EXPORT Sort
{
  friend class parser::Command;
  friend class DatatypeConstructor;
  friend class DatatypeConstructorDecl;
  friend class DatatypeSelector;
  friend class DatatypeDecl;
  friend class Datatype;
  friend class Op;
  friend class Solver;
  friend class Grammar;
  friend struct std::hash<Sort>;
  friend class Term;

 public:
  /**
   * Constructor.
   */
  Sort();

  /**
   * Destructor.
   */
  ~Sort();

  /**
   * Comparison for structural equality.
   * @param s The sort to compare to.
   * @return True if the sorts are equal.
   */
  bool operator==(const Sort& s) const;

  /**
   * Comparison for structural disequality.
   * @param s The sort to compare to.
   * @return True if the sorts are not equal.
   */
  bool operator!=(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s The sort to compare to.
   * @return True if this sort is less than s.
   */
  bool operator<(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s The sort to compare to.
   * @return True if this sort is greater than s.
   */
  bool operator>(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s The sort to compare to.
   * @return True if this sort is less than or equal to s.
   */
  bool operator<=(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s The sort to compare to.
   * @return True if this sort is greater than or equal to s.
   */
  bool operator>=(const Sort& s) const;

  /**
   * @return The kind of the sort.
   *
   * @warning This method is experimental and may change in future versions.
   */
  SortKind getKind() const;

  /**
   * Does this sort have a symbol, that is, a name?
   *
   * For example, uninterpreted sorts and uninterpreted sort constructors have
   * symbols.
   * @return True if the sort has a symbol.
   */
  bool hasSymbol() const;

  /**
   * Get the symbol of this Sort.
   *
   * @note Asserts hasSymbol().
   *
   * The symbol of this sort is the string that was
   * provided when constructing it via
   * Solver::mkUninterpretedSort(const std::string&) const,
   * Solver::mkUnresolvedSort(const std::string&, size_t) const, or
   * Solver::mkUninterpretedSortConstructorSort(const std::string&, size_t).
   *
   * @return The raw symbol of the sort.
   */
  std::string getSymbol() const;

  /**
   * Determine if this is the null sort (Sort::Sort()).
   * @return True if this Sort is the null sort.
   */
  bool isNull() const;

  /**
   * Determine if this is the Boolean sort (SMT-LIB: `Bool`).
   * @return True if this sort is the Boolean sort.
   */
  bool isBoolean() const;

  /**
   * Determine if this is the integer sort (SMT-LIB: `Int`).
   * @return True if this sort is the integer sort.
   */
  bool isInteger() const;

  /**
   * Determine if this is the real sort (SMT-LIB: `Real`).
   * @return True if this sort is the real sort.
   */
  bool isReal() const;

  /**
   * Determine if this is the string sort (SMT-LIB: `String`).
   * @return True if this sort is the string sort.
   */
  bool isString() const;

  /**
   * Determine if this is the regular expression sort (SMT-LIB: `RegLan`).
   * @return True if this sort is the regular expression sort.
   */
  bool isRegExp() const;

  /**
   * Determine if this is the rounding mode sort (SMT-LIB: `RoundingMode`).
   * @return True if this sort is the rounding mode sort.
   */
  bool isRoundingMode() const;

  /**
   * Determine if this is a bit-vector sort (SMT-LIB: `(_ BitVec i)`).
   * @return True if this sort is a bit-vector sort.
   */
  bool isBitVector() const;

  /**
   * Determine if this is a floatingpoint sort
   * (SMT-LIB: `(_ FloatingPoint eb sb)`).
   * @return True if this sort is a floating-point sort.
   */
  bool isFloatingPoint() const;

  /**
   * Determine if this is a datatype sort.
   * @return True if this sort is a datatype sort.
   */
  bool isDatatype() const;

  /**
   * Determine if this is a datatype constructor sort.
   * @return True if this sort is a datatype constructor sort.
   */
  bool isDatatypeConstructor() const;

  /**
   * Determine if this is a datatype selector sort.
   * @return True if this sort is a datatype selector sort.
   */
  bool isDatatypeSelector() const;

  /**
   * Determine if this is a datatype tester sort.
   * @return True if this sort is a datatype tester sort.
   */
  bool isDatatypeTester() const;
  /**
   * Determine if this is a datatype updater sort.
   * @return True if this sort is a datatype updater sort.
   */
  bool isDatatypeUpdater() const;
  /**
   * Determine if this is a function sort.
   * @return True if this sort is a function sort.
   */
  bool isFunction() const;

  /**
   * Determine if this is a predicate sort.
   *
   * A predicate sort is a function sort that maps to the Boolean sort. All
   * predicate sorts are also function sorts.
   *
   * @return True if this sort is a predicate sort.
   */
  bool isPredicate() const;

  /**
   * Determine if this a tuple sort.
   * @return True if this sort is a tuple sort.
   */
  bool isTuple() const;

  /**
   * Determine if this is a record sort.
   * @warning This method is experimental and may change in future versions.
   * @return True if the sort is a record sort.
   */
  bool isRecord() const;

  /**
   * Determine if this is an array sort.
   * @return True if the sort is an array sort.
   */
  bool isArray() const;

  /**
   * Determine if this is a finite field sort.
   * @return True if the sort is a finite field sort.
   */
  bool isFiniteField() const;

  /**
   * Determine if this is a Set sort.
   * @return True if the sort is a Set sort.
   */
  bool isSet() const;

  /**
   * Determine if this is a Bag sort.
   * @return True if the sort is a Bag sort.
   */
  bool isBag() const;

  /**
   * Determine if this is a Sequence sort.
   * @return True if the sort is a Sequence sort.
   */
  bool isSequence() const;

  /**
   * Determine if this is an abstract sort.
   * @return True if the sort is a abstract sort.
   *
   * @warning This method is experimental and may change in future versions.
   */
  bool isAbstract() const;

  /**
   * Determine if this is an uninterpreted sort.
   * @return True if this is an uninterpreted sort.
   */
  bool isUninterpretedSort() const;

  /**
   * Determine if this is an uninterpreted sort constructor.
   *
   * An uninterpreted sort constructor has arity > 0 and can be instantiated to
   * construct uninterpreted sorts with given sort parameters.
   *
   * @return True if this is a sort constructor kind.
   */
  bool isUninterpretedSortConstructor() const;

  /**
   * Determine if this is an instantiated (parametric datatype or uninterpreted
   * sort constructor) sort.
   *
   * An instantiated sort is a sort that has been constructed from
   * instantiating a sort with sort arguments
   * (see Sort::instantiate(const std::vector<Sort>&) const)).
   *
   * @return True if this is an instantiated sort.
   */
  bool isInstantiated() const;

  /**
   * Get the associated uninterpreted sort constructor of an instantiated
   * uninterpreted sort.
   *
   * @return The uninterpreted sort constructor sort.
   */
  Sort getUninterpretedSortConstructor() const;

  /**
   * @return The underlying datatype of a datatype sort.
   */
  Datatype getDatatype() const;

  /**
   * Instantiate a parameterized datatype sort or uninterpreted sort
   * constructor sort.
   *
   * Create sort parameters with Solver::mkParamSort().
   *
   * @param params The list of sort parameters to instantiate with.
   * @return The instantiated sort.
   */
  Sort instantiate(const std::vector<Sort>& params) const;

  /**
   * Get the sorts used to instantiate the sort parameters of a parametric
   * sort (parametric datatype or uninterpreted sort constructor sort,
   * see Sort::instantiate(const std::vector<Sort>& const)).
   *
   * @return The sorts used to instantiate the sort parameters of a
   *         parametric sort
   */
  std::vector<Sort> getInstantiatedParameters() const;

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
   * @warning This method is experimental and may change in future versions.
   *
   * @param sort The subsort to be substituted within this sort.
   * @param replacement The sort replacing the substituted subsort.
   */
  Sort substitute(const Sort& sort, const Sort& replacement) const;

  /**
   * Simultaneous substitution of Sorts.
   *
   * Note that this replacement is applied during a pre-order traversal and
   * only once to the sort. It is not run until fix point. In the case that
   * sorts contains duplicates, the replacement earliest in the vector takes
   * priority.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param sorts The subsorts to be substituted within this sort.
   * @param replacements The sort replacing the substituted subsorts.
   */
  Sort substitute(const std::vector<Sort>& sorts,
                  const std::vector<Sort>& replacements) const;

  /**
   * Output a string representation of this sort to a given stream.
   * @param out The output stream.
   */
  void toStream(std::ostream& out) const;

  /**
   * @return A string representation of this sort.
   */
  std::string toString() const;

  /* Datatype constructor sort ------------------------------------------- */

  /**
   * @return The arity of a datatype constructor sort.
   */
  size_t getDatatypeConstructorArity() const;

  /**
   * @return The domain sorts of a datatype constructor sort.
   */
  std::vector<Sort> getDatatypeConstructorDomainSorts() const;

  /**
   * @return The codomain sort of a constructor sort.
   */
  Sort getDatatypeConstructorCodomainSort() const;

  /* Selector sort ------------------------------------------------------- */

  /**
   * @return The domain sort of a datatype selector sort.
   */
  Sort getDatatypeSelectorDomainSort() const;

  /**
   * @return The codomain sort of a datatype selector sort.
   */
  Sort getDatatypeSelectorCodomainSort() const;

  /* Tester sort ------------------------------------------------------- */

  /**
   * @return The domain sort of a datatype tester sort.
   */
  Sort getDatatypeTesterDomainSort() const;

  /**
   * @return The codomain sort of a datatype tester sort, which is the Boolean
   *         sort.
   *
   * @note We mainly need this for the symbol table, which doesn't have
   *       access to the solver object.
   */
  Sort getDatatypeTesterCodomainSort() const;

  /* Function sort ------------------------------------------------------- */

  /**
   * @return The arity of a function sort.
   */
  size_t getFunctionArity() const;

  /**
   * @return The domain sorts of a function sort.
   */
  std::vector<Sort> getFunctionDomainSorts() const;

  /**
   * @return The codomain sort of a function sort.
   */
  Sort getFunctionCodomainSort() const;

  /* Array sort ---------------------------------------------------------- */

  /**
   * @return The array index sort of an array sort.
   */
  Sort getArrayIndexSort() const;

  /**
   * @return The array element sort of an array sort.
   */
  Sort getArrayElementSort() const;

  /* Set sort ------------------------------------------------------------ */

  /**
   * @return The element sort of a set sort.
   */
  Sort getSetElementSort() const;

  /* Bag sort ------------------------------------------------------------ */

  /**
   * @return The element sort of a bag sort.
   */
  Sort getBagElementSort() const;

  /* Sequence sort ------------------------------------------------------- */

  /**
   * @return The element sort of a sequence sort.
   */
  Sort getSequenceElementSort() const;

  /* Abstract sort ------------------------------------------------------- */
  /**
   * @return The sort kind of an abstract sort, which denotes the kind of
   * sorts that this abstract sort denotes.
   *
   * @warning This method is experimental and may change in future versions.
   */
  SortKind getAbstractedKind() const;

  /* Uninterpreted sort constructor sort --------------------------------- */

  /**
   * @return The arity of an uninterpreted sort constructor sort.
   */
  size_t getUninterpretedSortConstructorArity() const;

  /* Bit-vector sort ----------------------------------------------------- */

  /**
   * @return The bit-width of the bit-vector sort.
   */
  uint32_t getBitVectorSize() const;

  /* Finite field sort --------------------------------------------------- */

  /**
   * @return The size of the finite field sort.
   */
  std::string getFiniteFieldSize() const;

  /* Floating-point sort ------------------------------------------------- */

  /**
   * @return The bit-width of the exponent of the floating-point sort.
   */
  uint32_t getFloatingPointExponentSize() const;

  /**
   * @return The width of the significand of the floating-point sort.
   */
  uint32_t getFloatingPointSignificandSize() const;

  /* Datatype sort ------------------------------------------------------- */

  /**
   * Get the arity of a datatype sort, which is the number of type parameters
   * if the datatype is parametric, or 0 otherwise.
   * @return The arity of a datatype sort.
   */
  size_t getDatatypeArity() const;

  /* Tuple sort ---------------------------------------------------------- */

  /**
   * @return The length of a tuple sort.
   */
  size_t getTupleLength() const;

  /**
   * @return The element sorts of a tuple sort.
   */
  std::vector<Sort> getTupleSorts() const;

  /* --------------------------------------------------------------------- */

 private:
  /** @return The internal wrapped TypeNode of this sort. */
  const internal::TypeNode& getTypeNode(void) const;

  /** Helper to convert a vector of Sorts to internal TypeNodes. */
  std::vector<internal::TypeNode> static sortVectorToTypeNodes(
      const std::vector<Sort>& sorts);
  /** Helper to convert a vector of internal TypeNodes to Sorts. */
  std::vector<Sort> static typeNodeVectorToSorts(
      internal::NodeManager* nm, const std::vector<internal::TypeNode>& types);

  /**
   * Constructor.
   * @param nm The associated node manager.
   * @param t The internal type that is to be wrapped by this sort.
   * @return The Sort.
   */
  Sort(internal::NodeManager* nm, const internal::TypeNode& t);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

  /**
   * The internal type wrapped by this sort.
   *
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr`` to
   *       avoid overhead due to memory allocation (``internal::Type`` is
   * already ref counted, so this could be a ``std::unique_ptr`` instead).
   */
  std::shared_ptr<internal::TypeNode> d_type;
};

/**
 * Serialize a sort to given stream.
 * @param out The output stream.
 * @param s The sort to be serialized to the given output stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Sort& s) CVC5_EXPORT;

}  // namespace cvc5

namespace std {

/**
 * Hash function for Sorts.
 */
template <>
struct CVC5_EXPORT hash<cvc5::Sort>
{
  size_t operator()(const cvc5::Sort& s) const;
};

}  // namespace std

namespace cvc5 {

/* -------------------------------------------------------------------------- */
/* Op                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * A cvc5 operator.
 *
 * An operator is a term that represents certain operators, instantiated
 * with its required parameters, e.g., a Term of kind #BITVECTOR_EXTRACT.
 */
class CVC5_EXPORT Op
{
  friend class Solver;
  friend class Term;
  friend struct std::hash<Op>;

 public:
  /**
   * Constructor.
   */
  Op();

  /**
   * Destructor.
   */
  ~Op();

  /**
   * Syntactic equality operator.
   *
   * @note Both operators must belong to the same node manager.
   *
   * @param t The operator to compare to for equality.
   * @return True if both operators are syntactically identical.
   */
  bool operator==(const Op& t) const;

  /**
   * Syntactic disequality operator.
   *
   * @note Both terms must belong to the same node manager.
   *
   * @param t The operator to compare to for disequality.
   * @return True if operators differ syntactically.
   */
  bool operator!=(const Op& t) const;

  /**
   * @return The kind of this operator.
   */
  Kind getKind() const;

  /**
   * @return True if this operator is a null term.
   */
  bool isNull() const;

  /**
   * @return True iff this operator is indexed.
   */
  bool isIndexed() const;

  /**
   * @return The number of indices of this op.
   */
  size_t getNumIndices() const;

  /**
   * Get the index at position `i`.
   * @param i The position of the index to return.
   * @return The index at position i.
   */
  Term operator[](size_t i) const;

  /**
   * @return A string representation of this operator.
   */
  std::string toString() const;

 private:
  /**
   * Constructor for a single kind (non-indexed operator).
   * @param nm The associated node manager.
   * @param k The kind of this Op.
   */
  Op(internal::NodeManager* nm, const Kind k);

  /**
   * Constructor.
   * @param nm The associated node managaer.
   * @param k The kind of this Op.
   * @param n The internal node that is to be wrapped by this term.
   * @return The Term.
   */
  Op(internal::NodeManager* nm, const Kind k, const internal::Node& n);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * @note An indexed operator has a non-null internal node (``d_node``).
   *
   * @note We use a helper method to avoid having API functions call other API
   *       functions (we need to call this internally).
   *
   * @return True iff this Op is indexed.
   */
  bool isIndexedHelper() const;

  /**
   * Helper for getNumIndices
   * @return The number of indices of this op.
   */
  size_t getNumIndicesHelper() const;

  /**
   * Helper for operator[](size_t index).
   * @param index Position of the index. Should be less than
   *              getNumIndicesHelper().
   * @return The index at position index.
   */
  Term getIndexHelper(size_t index) const;

  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

  /** The kind of this operator. */
  Kind d_kind;

  /**
   * The internal node wrapped by this operator.
   *
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr`` to
   *       avoid overhead due to memory allocation (``internal::Node`` is
   * already ref counted, so this could be a ``std::unique_ptr`` instead).
   */
  std::shared_ptr<internal::Node> d_node;
};

/**
 * Serialize an operator to given stream.
 * @param out The output stream.
 * @param t The operator to be serialized to the given output stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Op& t) CVC5_EXPORT;

}  // namespace cvc5

namespace std {
/**
 * Hash function for Ops.
 */
template <>
struct CVC5_EXPORT hash<cvc5::Op>
{
  size_t operator()(const cvc5::Op& t) const;
};
}  // namespace std

namespace cvc5 {
/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

/**
 * A cvc5 Term.
 */
class CVC5_EXPORT Term
{
  friend class parser::Command;
  friend class Datatype;
  friend class DatatypeConstructor;
  friend class DatatypeSelector;
  friend class Solver;
  friend class Grammar;
  friend class SynthResult;
  friend struct std::hash<Term>;

 public:
  /**
   * Constructor for a null term.
   */
  Term();

  /**
   * Destructor.
   */
  ~Term();

  /**
   * Syntactic equality operator.
   * Return true if both terms are syntactically identical.
   * @note Both terms must belong to the same node manager.
   * @param t The term to compare to for equality.
   * @return True if the terms are equal.
   */
  bool operator==(const Term& t) const;

  /**
   * Syntactic disequality operator.
   * Return true if both terms differ syntactically.
   * @note Both terms must belong to the same node manager.
   * @param t The term to compare to for disequality.
   * @return True if terms are disequal.
   */
  bool operator!=(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t The term to compare to.
   * @return True if this term is less than t.
   */
  bool operator<(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t The term to compare to.
   * @return True if this term is greater than t.
   */
  bool operator>(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t The term to compare to.
   * @return True if this term is less than or equal to t.
   */
  bool operator<=(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t The term to compare to.
   * @return True if this term is greater than or equal to t.
   */
  bool operator>=(const Term& t) const;

  /** @return The number of children of this term  */
  size_t getNumChildren() const;

  /**
   * Get the child term at a given index.
   * @param index The index of the child term to return.
   * @return The child term with the given index.
   */
  Term operator[](size_t index) const;

  /**
   * @return The id of this term.
   */
  uint64_t getId() const;

  /**
   * @return The kind of this term.
   */
  Kind getKind() const;

  /**
   * @return The sort of this term.
   */
  Sort getSort() const;

  /**
   * Replace `term` with `replacement` in this term.
   *
   * @return The result of replacing `term` with `replacement` in this term.
   *
   * @note This replacement is applied during a pre-order traversal and
   *       only once (it is not run until fixed point).
   */
  Term substitute(const Term& term, const Term& replacement) const;

  /**
   * Simultaneously replace `terms` with `replacements` in this term.
   *
   * In the case that terms contains duplicates, the replacement earliest in
   * the vector takes priority. For example, calling substitute on `f(x,y)`
   * with `terms = { x, z }`, `replacements = { g(z), w }` results in the term
   * `f(g(z),y)`.
   *
   * @note This replacement is applied during a pre-order traversal and
   *       only once (it is not run until fixed point).
   *
   * @return The result of simultaneously replacing `terms` with `replacements`
   *         in this term.
   */
  Term substitute(const std::vector<Term>& terms,
                  const std::vector<Term>& replacements) const;

  /**
   * @return True iff this term has an operator.
   */
  bool hasOp() const;

  /**
   * @note This is safe to call when hasOp() returns true.
   *
   * @return The Op used to create this term.
   */
  Op getOp() const;

  /**
   * Does the term have a symbol, i.e., a name?
   *
   * For example, free constants and variables have symbols.
   * @return True if the term has a symbol.
   */
  bool hasSymbol() const;

  /**
   * Get the symbol of this Term.
   *
   * @note Asserts hasSymbol().
   *
   * The symbol of the term is the string that was
   * provided when constructing it via Solver::mkConst() or Solver::mkVar().
   *
   * @return The raw symbol of the term.
   */
  std::string getSymbol() const;

  /**
   * @return True if this Term is a null term.
   */
  bool isNull() const;

  /**
   * Boolean negation.
   * @return The Boolean negation of this term.
   */
  Term notTerm() const;

  /**
   * Boolean and.
   * @param t A Boolean term.
   * @return The conjunction of this term and the given term.
   */
  Term andTerm(const Term& t) const;

  /**
   * Boolean or.
   * @param t A Boolean term.
   * @return The disjunction of this term and the given term.
   */
  Term orTerm(const Term& t) const;

  /**
   * Boolean exclusive or.
   * @param t A Boolean term.
   * @return The exclusive disjunction of this term and the given term.
   */
  Term xorTerm(const Term& t) const;

  /**
   * Equality.
   * @param t A Boolean term.
   * @return The Boolean equivalence of this term and the given term.
   */
  Term eqTerm(const Term& t) const;

  /**
   * Boolean implication.
   * @param t A Boolean term.
   * @return The implication of this term and the given term.
   */
  Term impTerm(const Term& t) const;

  /**
   * If-then-else with this term as the Boolean condition.
   * @param then_t The 'then' term.
   * @param else_t The 'else' term.
   * @return The if-then-else term with this term as the Boolean condition.
   */
  Term iteTerm(const Term& then_t, const Term& else_t) const;

  /**
   * @return A string representation of this term.
   */
  std::string toString() const;

  /**
   * Iterator for the children of a Term.
   * @note This treats uninterpreted functions as Term just like any other term
   *       for example, the term ``f(x, y)`` will have Kind ``APPLY_UF`` and
   *       three children: ``f``, ``x``, and ``y``
   */
  class CVC5_EXPORT const_iterator
  {
    friend class Term;

   public:
    /* The following types are required by trait std::iterator_traits */

    /** Iterator tag */
    using iterator_category = std::forward_iterator_tag;

    /** The type of the item */
    using value_type = Term;

    /** The pointer type of the item */
    using pointer = const Term*;

    /** The reference type of the item */
    using reference = const Term&;

    /** The type returned when two iterators are subtracted */
    using difference_type = std::ptrdiff_t;

    /* End of std::iterator_traits required types */

    /**
     * Null Constructor.
     */
    const_iterator();

    /**
     * Constructor
     * @param nm The associated node manager.
     * @param e A ``std::shared pointer`` to the node that we're iterating over.
     * @param p The position of the iterator (e.g. which child it's on).
     */
    const_iterator(internal::NodeManager* nm,
                   const std::shared_ptr<internal::Node>& e,
                   uint32_t p);

    /**
     * Copy constructor.
     */
    const_iterator(const const_iterator& it);

    /**
     * Assignment operator.
     * @param it The iterator to assign to.
     * @return The reference to the iterator after assignment.
     */
    const_iterator& operator=(const const_iterator& it);

    /**
     * Equality operator.
     * @param it The iterator to compare to for equality.
     * @return True if the iterators are equal.
     */
    bool operator==(const const_iterator& it) const;

    /**
     * Disequality operator.
     * @param it The iterator to compare to for disequality.
     * @return True if the iterators are disequal.
     */
    bool operator!=(const const_iterator& it) const;

    /**
     * Increment operator (prefix).
     * @return A reference to the iterator after incrementing by one.
     */
    const_iterator& operator++();

    /**
     * Increment operator (postfix).
     * @return A reference to the iterator after incrementing by one.
     */
    const_iterator operator++(int);

    /**
     * Dereference operator.
     * @return The term this iterator points to.
     */
    Term operator*() const;

   private:
    /**
     * The associated node manager.
     */
    internal::NodeManager* d_nm;
    /** The original node to be iterated over. */
    std::shared_ptr<internal::Node> d_origNode;
    /** Keeps track of the iteration position. */
    uint32_t d_pos;
  };

  /**
   * @return An iterator to the first child of this Term.
   */
  const_iterator begin() const;

  /**
   * @return An iterator to one-off-the-last child of this Term.
   */
  const_iterator end() const;

  /**
   * Get integer or real value sign. Must be called on integer or real values,
   * or otherwise an exception is thrown.
   * @return 0 if this term is zero, -1 if this term is a negative real or
   *         integer value, 1 if this term is a positive real or integer value.
   */
  int32_t getRealOrIntegerValueSign() const;
  /**
   * @return True if the term is an integer value that fits within int32_t.
   * Note that this method will return true for integer constants and real
   * constants that have integer value.
   */
  bool isInt32Value() const;
  /**
   * Get the `int32_t` representation of this integral value.
   * @note Asserts isInt32Value().
   * @return This integer value as a `int32_t`.
   */
  int32_t getInt32Value() const;
  /**
   * @return True if the term is an integer value that fits within uint32_t.
   * Note that this method will return true for integer constants and real
   * constants that have integral value.
   */
  bool isUInt32Value() const;
  /**
   * Get the `uint32_t` representation of this integral value.
   * @note Asserts isUInt32Value().
   * @return This integer value as a `uint32_t`.
   */
  uint32_t getUInt32Value() const;
  /**
   * @return True if the term is an integer value that fits within int64_t.
   * Note that this method will return true for integer constants and real
   * constants that have integral value.
   */
  bool isInt64Value() const;
  /**
   * Get the `int64_t` representation of this integral value.
   * @note Asserts isInt64Value().
   * @return This integer value as a `int64_t`.
   */
  int64_t getInt64Value() const;
  /**
   * @return True if the term is an integer value that fits within uint64_t.
   * Note that this method will return true for integer constants and real
   * constants that have integral value.
   */
  bool isUInt64Value() const;
  /**
   * Get the `uint64_t` representation of this integral value.
   * @note Asserts isUInt64Value().
   * @return This integer value as a `uint64_t`.
   */
  uint64_t getUInt64Value() const;
  /**
   * @return True if the term is an integer constant or a real constant that
   * has an integral value.
   */
  bool isIntegerValue() const;
  /**
   * @note Asserts isIntegerValue().
   * @return The integral term in (decimal) string representation.
   */
  std::string getIntegerValue() const;

  /**
   * @return True if the term is a string value.
   */
  bool isStringValue() const;
  /**
   * @note Asserts isStringValue().
   * @note This method is not to be confused with toString(), which returns
   *       some string representation of the term, whatever data it may hold.
   * @return The string term as a native string value.
   */
  std::wstring getStringValue() const;

  /**
   * @return True if the term is a rational value whose numerator and
   *         denominator fit within int32_t and uint32_t, respectively.
   */
  bool isReal32Value() const;
  /**
   * @note Asserts isReal32Value().
   * @return The representation of a rational value as a pair of its numerator
   *         and denominator.
   */
  std::pair<int32_t, uint32_t> getReal32Value() const;
  /**
   * @return True if the term is a rational value whose numerator and
   *         denominator fit within int64_t and uint64_t, respectively.
   */
  bool isReal64Value() const;
  /**
   * @note Asserts isReal64Value().
   * @return The representation of a rational value as a pair of its numerator
   *         and denominator.
   */
  std::pair<int64_t, uint64_t> getReal64Value() const;
  /**
   * @note A term of kind PI is not considered to be a real value.
   * @return True if the term is a rational value.
   */
  bool isRealValue() const;
  /**
   * @note Asserts isRealValue().
   * @return The representation of a rational value as a (rational) string.
   */
  std::string getRealValue() const;

  /**
   * @return True if the term is a constant array.
   */
  bool isConstArray() const;
  /**
   * @note Asserts isConstArray().
   * @return The base (element stored at all indices) of a constant array.
   */
  Term getConstArrayBase() const;

  /**
   * @return True if the term is a Boolean value.
   */
  bool isBooleanValue() const;
  /**
   * @note Asserts isBooleanValue().
   * @return The representation of a Boolean value as a native Boolean value.
   */
  bool getBooleanValue() const;

  /**
   * @return True if the term is a bit-vector value.
   */
  bool isBitVectorValue() const;
  /**
   * Get the string representation of a bit-vector value.
   *
   * Supported values for `base` are `2` (bit string), `10` (decimal string) or
   * `16` (hexadecimal string).
   *
   * @note Asserts isBitVectorValue().
   *
   * @return The string representation of a bit-vector value.
   */
  std::string getBitVectorValue(uint32_t base = 2) const;

  /**
   * @return True if the term is a finite field value.
   */
  bool isFiniteFieldValue() const;
  /**
   * Get the string representation of a finite field value (base 10).
   *
   * @note Asserts isFiniteFieldValue().
   *
   * @note Uses the integer representative of smallest absolute value.
   *
   * @return The string representation of the integer representation of this
   * finite field value.
   */
  std::string getFiniteFieldValue() const;

  /**
   * @return True if the term is an abstract value.
   */
  bool isUninterpretedSortValue() const;
  /**
   * @note Asserts isUninterpretedSortValue().
   * @return The representation of an uninterpreted sort value as a string.
   */
  std::string getUninterpretedSortValue() const;

  /**
   * @return True if the term is a tuple value.
   */
  bool isTupleValue() const;
  /**
   * @note Asserts isTupleValue().
   * @return The representation of a tuple value as a vector of terms.
   */
  std::vector<Term> getTupleValue() const;

  /**
   * @return True if the term is a floating-point rounding mode value.
   */
  bool isRoundingModeValue() const;
  /**
   * @note Asserts isRoundingModeValue().
   * @return The floating-point rounding mode value held by the term.
   */
  RoundingMode getRoundingModeValue() const;

  /**
   * @return True if the term is the floating-point value for positive zero.
   */
  bool isFloatingPointPosZero() const;
  /**
   * @return True if the term is the floating-point value for negative zero.
   */
  bool isFloatingPointNegZero() const;
  /**
   * @return True if the term is the floating-point value for positive.
   * infinity.
   */
  bool isFloatingPointPosInf() const;
  /**
   * @return True if the term is the floating-point value for negative.
   * infinity.
   */
  bool isFloatingPointNegInf() const;
  /**
   * @return True if the term is the floating-point value for not a number.
   */
  bool isFloatingPointNaN() const;
  /**
   * @return True if the term is a floating-point value.
   */
  bool isFloatingPointValue() const;
  /**
   * @note Asserts isFloatingPointValue().
   * @return The representation of a floating-point value as a tuple of the
   *         exponent width, the significand width and a bit-vector value.
   */
  std::tuple<uint32_t, uint32_t, Term> getFloatingPointValue() const;

  /**
   * @return True if the term is a set value.
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
   * @f$c_1 > ... > c_n@f$ (see @ref Term::operator>(const Term&) const).
   *
   * @note A universe set term (kind `SET_UNIVERSE`) is not considered to be
   *       a set value.
   */
  bool isSetValue() const;
  /**
   * @note Asserts isSetValue().
   * @return The representation of a set value as a set of terms.
   */
  std::set<Term> getSetValue() const;

  /**
   * Determine if this term is a sequence value.
   *
   * A term is a sequence value if it has kind #CONST_SEQUENCE. In contrast to
   * values for the set sort (as described in isSetValue()), a sequence value
   * is represented as a Term with no children.
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
   * returned in response to API calls such Solver::getValue() and
   * Solver::simplify().
   *
   * @return True if the term is a sequence value.
   */
  bool isSequenceValue() const;
  /**
   * @note Asserts isSequenceValue().
   * @return The representation of a sequence value as a vector of terms.
   */
  std::vector<Term> getSequenceValue() const;

  /**
   * @return True if the term is a cardinality constraint.
   */
  bool isCardinalityConstraint() const;
  /**
   * @note Asserts isCardinalityConstraint().
   * @return The sort the cardinality constraint is for and its upper bound.
   */
  std::pair<Sort, uint32_t> getCardinalityConstraint() const;

  /**
   * @return True if the term is a real algebraic number.
   */
  bool isRealAlgebraicNumber() const;
  /**
   * @note Asserts isRealAlgebraicNumber().
   * @param v The variable over which to express the polynomial.
   * @return The defining polynomial for the real algebraic number, expressed in
   * terms of the given variable.
   */
  Term getRealAlgebraicNumberDefiningPolynomial(const Term& v) const;
  /**
   * @note Asserts isRealAlgebraicNumber().
   * @return The lower bound for the value of the real algebraic number.
   */
  Term getRealAlgebraicNumberLowerBound() const;
  /**
   * @note Asserts isRealAlgebraicNumber().
   * @return The upper bound for the value of the real algebraic number.
   */
  Term getRealAlgebraicNumberUpperBound() const;

 protected:
  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

 private:
  /** Helper method to collect all elements of a set. */
  static void collectSet(std::set<Term>& set,
                         const internal::Node& node,
                         internal::NodeManager* nm);
  /** Helper method to collect all elements of a sequence. */
  static void collectSequence(std::vector<Term>& seq,
                              const internal::Node& node,
                              internal::NodeManager* nm);

  /**
   * Constructor.
   * @param nm The associated node manager.
   * @param n The internal node that is to be wrapped by this term.
   * @return The Term.
   */
  Term(internal::NodeManager* nm, const internal::Node& n);

  /** @return The internal wrapped Node of this term. */
  const internal::Node& getNode(void) const;

  /** Helper to convert a vector of Terms to internal Nodes. */
  std::vector<internal::Node> static termVectorToNodes(
      const std::vector<Term>& terms);
  /** Helper to convert a vector of internal Nodes to Terms. */
  std::vector<Term> static nodeVectorToTerms(
      internal::NodeManager* nm, const std::vector<internal::Node>& nodes);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * Helper function that returns the kind of the term, which takes into
   * account special cases of the conversion for internal to external kinds.
   * @return The kind of this term.
   */
  Kind getKindHelper() const;

  /**
   * The internal node wrapped by this term.
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr`` to
   *       avoid overhead due to memory allocation (``internal::Node`` is
   * already ref counted, so this could be a ``std::unique_ptr`` instead).
   */
  std::shared_ptr<internal::Node> d_node;
};

/**
 * Serialize a term to given stream.
 * @param out The output stream.
 * @param t The term to be serialized to the given output stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Term& t) CVC5_EXPORT;

/**
 * Serialize a vector of terms to given stream.
 * @param out The output stream.
 * @param vector The vector of terms to be serialized to the given stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const std::vector<Term>& vector) CVC5_EXPORT;

/**
 * Serialize a set of terms to the given stream.
 * @param out The output stream.
 * @param set The set of terms to be serialized to the given stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const std::set<Term>& set) CVC5_EXPORT;

/**
 * Serialize an unordered_set of terms to the given stream.
 *
 * @param out The output stream.
 * @param unordered_set The set of terms to be serialized to the given stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_set<Term>& unordered_set)
    CVC5_EXPORT;

/**
 * Serialize a map of terms to the given stream.
 *
 * @param out The output stream.
 * @param map The map of terms to be serialized to the given stream.
 * @return The output stream.
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::map<Term, V>& map) CVC5_EXPORT;

/**
 * Serialize an unordered_map of terms to the given stream.
 *
 * @param out The output stream.
 * @param unordered_map The map of terms to be serialized to the given stream.
 * @return The output stream.
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_map<Term, V>& unordered_map)
    CVC5_EXPORT;

}  // namespace cvc5

namespace std {
/**
 * Hash function for Terms.
 */
template <>
struct CVC5_EXPORT hash<cvc5::Term>
{
  size_t operator()(const cvc5::Term& t) const;
};
}  // namespace std

namespace cvc5 {

/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

class DatatypeConstructorIterator;
class DatatypeIterator;

/**
 * A cvc5 datatype constructor declaration. A datatype constructor declaration
 * is a specification used for creating a datatype constructor.
 */
class CVC5_EXPORT DatatypeConstructorDecl
{
  friend class DatatypeDecl;
  friend class Solver;

 public:
  /** Constructor.  */
  DatatypeConstructorDecl();

  /**
   * Destructor.
   */
  ~DatatypeConstructorDecl();

  /**
   * Add datatype selector declaration.
   * @param name The name of the datatype selector declaration to add.
   * @param sort The codomain sort of the datatype selector declaration to add.
   */
  void addSelector(const std::string& name, const Sort& sort);
  /**
   * Add datatype selector declaration whose codomain type is the datatype
   * itself.
   * @param name The name of the datatype selector declaration to add.
   */
  void addSelectorSelf(const std::string& name);

  /**
   * Add datatype selector declaration whose codomain sort is an unresolved
   * datatype with the given name.
   * @param name The name of the datatype selector declaration to add.
   * @param unresDataypeName The name of the unresolved datatype. The codomain
   *                         of the selector will be the resolved datatype with
   *                         the given name.
   */
  void addSelectorUnresolved(const std::string& name,
                             const std::string& unresDataypeName);

  /**
   * @return True if this DatatypeConstructorDecl is a null declaration.
   */
  bool isNull() const;

  /**
   * @return A string representation of this datatype constructor declaration.
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param nm The associated node manager.
   * @param name The name of the datatype constructor.
   * @return The DatatypeConstructorDecl.
   */
  DatatypeConstructorDecl(internal::NodeManager* nm, const std::string& name);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * Is the underlying constructor resolved (i.e,. has it been used to declare
   * a datatype already)?
   */
  bool isResolved() const;

  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

  /**
   * The internal (intermediate) datatype constructor wrapped by this
   * datatype constructor declaration.
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr``
   *       since ``internal::DTypeConstructor`` is not ref counted.
   */
  std::shared_ptr<internal::DTypeConstructor> d_ctor;
};

class Solver;

/**
 * A cvc5 datatype declaration. A datatype declaration is not itself a datatype
 * (see Datatype), but a specification for creating a datatype sort.
 *
 * The interface for a datatype declaration coincides with the syntax for the
 * SMT-LIB 2.6 command `declare-datatype`, or a single datatype within the
 * `declare-datatypes` command.
 *
 * Datatype sorts can be constructed from DatatypeDecl using the methods:
 *   - Solver::mkDatatypeSort()
 *   - Solver::mkDatatypeSorts()
 */
class CVC5_EXPORT DatatypeDecl
{
  friend class DatatypeConstructorArg;
  friend class Solver;

 public:
  /** Constructor.  */
  DatatypeDecl();

  /**
   * Destructor.
   */
  ~DatatypeDecl();

  /**
   * Add datatype constructor declaration.
   * @param ctor The datatype constructor declaration to add.
   */
  void addConstructor(const DatatypeConstructorDecl& ctor);

  /** Get the number of constructors (so far) for this Datatype declaration. */
  size_t getNumConstructors() const;

  /**
   * Determine if this Datatype declaration is parametric.
   *
   * @warning This method is experimental and may change in future versions.
   */
  bool isParametric() const;

  /**
   * Is this datatype declaration resolved (i.e,. has it been used to declare
   * a datatype already)?
   */
  bool isResolved() const;

  /**
   * @return True if this DatatypeDecl is a null object.
   */
  bool isNull() const;

  /**
   * @return A string representation of this datatype declaration.
   */
  std::string toString() const;

  /** @return The name of this datatype declaration. */
  std::string getName() const;

 private:
  /**
   * Constructor.
   * @param nm The associated node manager.
   * @param name The name of the datatype.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  DatatypeDecl(internal::NodeManager* nm,
               const std::string& name,
               bool isCoDatatype = false);

  /**
   * Constructor for parameterized datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param nm The associated node manager.
   * @param name The name of the datatype.
   * @param params A list of sort parameters.
   * @param isCoDatatype True if a codatatype is to be constructed.
   */
  DatatypeDecl(internal::NodeManager* nm,
               const std::string& name,
               const std::vector<Sort>& params,
               bool isCoDatatype = false);

  /** @return The internal wrapped Dtype of this datatype declaration. */
  internal::DType& getDatatype(void) const;

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

  /**
   * The internal (intermediate) datatype wrapped by this datatype
   * declaration.
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr``
   *       since ``internal::DType`` is not ref counted.
   */
  std::shared_ptr<internal::DType> d_dtype;
};

/**
 * A cvc5 datatype selector.
 */
class CVC5_EXPORT DatatypeSelector
{
  friend class Datatype;
  friend class DatatypeConstructor;
  friend class Solver;

 public:
  /**
   * Constructor.
   */
  DatatypeSelector();

  /**
   * Destructor.
   */
  ~DatatypeSelector();

  /** @return The name of this Datatype selector. */
  std::string getName() const;

  /**
   * Get the selector term of this datatype selector.
   *
   * Selector terms are a class of function-like terms of selector
   * sort (Sort::isDatatypeSelector()), and should be used as the first
   * argument of Terms of kind #APPLY_SELECTOR.
   *
   * @return The selector term.
   */
  Term getTerm() const;

  /**
   * Get the updater term of this datatype selector.
   *
   * Similar to selectors, updater terms are a class of function-like terms of
   * updater Sort (Sort::isDatatypeUpdater()), and should be used as the first
   * argument of Terms of kind #APPLY_UPDATER.
   *
   * @return The updater term.
   */
  Term getUpdaterTerm() const;

  /** @return The codomain sort of this selector. */
  Sort getCodomainSort() const;

  /**
   * @return True if this DatatypeSelector is a null object.
   */
  bool isNull() const;

  /**
   * @return A string representation of this datatype selector.
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param nm The associated node manager.
   * @param stor The internal datatype selector to be wrapped.
   * @return The DatatypeSelector.
   */
  DatatypeSelector(internal::NodeManager* nm,
                   const internal::DTypeSelector& stor);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

  /**
   * The internal datatype selector wrapped by this datatype selector.
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr``
   *       since ``internal::DType`` is not ref counted.
   */
  std::shared_ptr<internal::DTypeSelector> d_stor;
};

/**
 * A cvc5 datatype constructor.
 */
class CVC5_EXPORT DatatypeConstructor
{
  friend class Datatype;
  friend class Solver;

 public:
  /**
   * Constructor.
   */
  DatatypeConstructor();

  /**
   * Destructor.
   */
  ~DatatypeConstructor();

  /** @return The name of this Datatype constructor. */
  std::string getName() const;

  /**
   * Get the constructor term of this datatype constructor.
   *
   * Datatype constructors are a special class of function-like terms whose sort
   * is datatype constructor (Sort::isDatatypeConstructor()). All datatype
   * constructors, including nullary ones, should be used as the
   * first argument to Terms whose kind is #APPLY_CONSTRUCTOR. For example,
   * the nil list can be constructed by
   * `Solver::mkTerm(APPLY_CONSTRUCTOR, {t})`, where `t` is the term returned
   * by this method.
   *
   * @note This method should not be used for parametric datatypes. Instead,
   *       use the method DatatypeConstructor::getInstantiatedTerm() below.
   *
   * @return The constructor term.
   */
  Term getTerm() const;

  /**
   * Get the constructor term of this datatype constructor whose return
   * type is `retSort`.
   *
   * This method is intended to be used on constructors of parametric datatypes
   * and can be seen as returning the constructor term that has been explicitly
   * cast to the given sort.
   *
   * This method is required for constructors of parametric datatypes whose
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
   * This method is equivalent of applying the above, where this
   * DatatypeConstructor is the one corresponding to `nil`, and `retSort` is
   * `(List Int)`.
   *
   * @note The returned constructor term `t` is used to construct the above
   *       (nullary) application of `nil` with
   *       `Solver::mkTerm(APPLY_CONSTRUCTOR, {t})`.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param retSort The desired return sort of the constructor.
   * @return The constructor term.
   */
  Term getInstantiatedTerm(const Sort& retSort) const;

  /**
   * Get the tester term of this datatype constructor.
   *
   * Similar to constructors, testers are a class of function-like terms of
   * tester sort (Sort::isDatatypeConstructor()) which should be used as the
   * first argument of Terms of kind #APPLY_TESTER.
   *
   * @return The tester term.
   */
  Term getTesterTerm() const;

  /**
   * @return The number of selectors (so far) of this Datatype constructor.
   */
  size_t getNumSelectors() const;

  /** @return The i^th DatatypeSelector. */
  DatatypeSelector operator[](size_t index) const;
  /**
   * Get the datatype selector with the given name.
   * This is a linear search through the selectors, so in case of
   * multiple, similarly-named selectors, the first is returned.
   * @param name The name of the datatype selector.
   * @return The first datatype selector with the given name.
   */
  DatatypeSelector operator[](const std::string& name) const;
  /**
   * Get the datatype selector with the given name.
   * This is a linear search through the selectors, so in case of
   * multiple, similarly-named selectors, the first is returned.
   * @param name The name of the datatype selector.
   * @return The first datatype selector with the given name.
   */
  DatatypeSelector getSelector(const std::string& name) const;

  /**
   * @return True if this DatatypeConstructor is a null object.
   */
  bool isNull() const;

  /**
   * @return A string representation of this datatype constructor.
   */
  std::string toString() const;

  /**
   * Iterator for the selectors of a datatype constructor.
   */
  class const_iterator
  {
    friend class DatatypeConstructor;  // to access constructor

   public:
    /* The following types are required by trait std::iterator_traits */

    /** Iterator tag */
    using iterator_category = std::forward_iterator_tag;

    /** The type of the item */
    using value_type = DatatypeConstructor;

    /** The pointer type of the item */
    using pointer = const DatatypeConstructor*;

    /** The reference type of the item */
    using reference = const DatatypeConstructor&;

    /** The type returned when two iterators are subtracted */
    using difference_type = std::ptrdiff_t;

    /* End of std::iterator_traits required types */

    /** Nullary constructor (required for Cython). */
    const_iterator();

    /**
     * Assignment operator.
     * @param it The iterator to assign to.
     * @return The reference to the iterator after assignment.
     */
    const_iterator& operator=(const const_iterator& it);

    /**
     * Equality operator.
     * @param it The iterator to compare to for equality.
     * @return True if the iterators are equal.
     */
    bool operator==(const const_iterator& it) const;

    /**
     * Disequality operator.
     * @param it The iterator to compare to for disequality.
     * @return True if the iterators are disequal.
     */
    bool operator!=(const const_iterator& it) const;

    /**
     * Increment operator (prefix).
     * @return A reference to the iterator after incrementing by one.
     */
    const_iterator& operator++();

    /**
     * Increment operator (postfix).
     * @return A reference to the iterator after incrementing by one.
     */
    const_iterator operator++(int);

    /**
     * Dereference operator.
     * @return A reference to the selector this iterator points to.
     */
    const DatatypeSelector& operator*() const;

    /**
     * Dereference operator.
     * @return A pointer to the selector this iterator points to.
     */
    const DatatypeSelector* operator->() const;

   private:
    /**
     * Constructor.
     * @param nm The associated node manager.
     * @param ctor The internal datatype constructor to iterate over.
     * @param begin True if this is a `begin()` iterator.
     */
    const_iterator(internal::NodeManager* nm,
                   const internal::DTypeConstructor& ctor,
                   bool begin);

    /**
     * The associated node manager.
     */
    internal::NodeManager* d_nm;

    /**
     * A pointer to the list of selectors of the internal datatype
     * constructor to iterate over.
     * This pointer is maintained for operators == and != only.
     */
    const void* d_int_stors;

    /** The list of datatype selector (wrappers) to iterate over. */
    std::vector<DatatypeSelector> d_stors;

    /** The current index of the iterator. */
    size_t d_idx;
  };

  /**
   * @return An iterator to the first selector of this constructor.
   */
  const_iterator begin() const;

  /**
   * @return An iterator to one-off-the-last selector of this constructor.
   */
  const_iterator end() const;

 private:
  /**
   * Constructor.
   * @param nm The associated node manager.
   * @param ctor The internal datatype constructor to be wrapped.
   * @return The DatatypeConstructor.
   */
  DatatypeConstructor(internal::NodeManager* nm,
                      const internal::DTypeConstructor& ctor);

  /**
   * Return selector for name.
   * @param name The name of selector to find.
   * @return The selector object for the name.
   */
  DatatypeSelector getSelectorForName(const std::string& name) const;

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

  /**
   * The internal datatype constructor wrapped by this datatype constructor.
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr``
   *       since ``internal::DType`` is not ref counted.
   */
  std::shared_ptr<internal::DTypeConstructor> d_ctor;
};

/**
 * A cvc5 datatype.
 */
class CVC5_EXPORT Datatype
{
  friend class Solver;
  friend class Sort;

 public:
  /** Constructor. */
  Datatype();

  /**
   * Destructor.
   */
  ~Datatype();

  /**
   * Get the datatype constructor at a given index.
   * @param idx The index of the datatype constructor to return.
   * @return The datatype constructor with the given index.
   */
  DatatypeConstructor operator[](size_t idx) const;

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors, so in case of multiple,
   * similarly-named constructors, the first is returned.
   * @param name The name of the datatype constructor.
   * @return The datatype constructor with the given name.
   */
  DatatypeConstructor operator[](const std::string& name) const;
  DatatypeConstructor getConstructor(const std::string& name) const;

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors and their selectors, so
   * in case of multiple, similarly-named selectors, the first is returned.
   * @param name The name of the datatype selector.
   * @return The datatype selector with the given name.
   */
  DatatypeSelector getSelector(const std::string& name) const;

  /** @return The name of this Datatype. */
  std::string getName() const;

  /** @return The number of constructors for this Datatype. */
  size_t getNumConstructors() const;

  /**
   * Get the parameters of this datatype, if it is parametric.
   *
   * @note Asserts that this datatype is parametric.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @return The parameters of this datatype.
   */
  std::vector<Sort> getParameters() const;

  /**
   * @warning This method is experimental and may change in future versions.
   * @return True if this datatype is parametric.
   */
  bool isParametric() const;

  /** @return True if this datatype corresponds to a co-datatype */
  bool isCodatatype() const;

  /** @return True if this datatype corresponds to a tuple */
  bool isTuple() const;

  /**
   * @warning This method is experimental and may change in future versions.
   * @return True if this datatype corresponds to a record.
   */
  bool isRecord() const;

  /** @return True if this datatype is finite */
  bool isFinite() const;

  /**
   * Determine if this datatype is well-founded.
   *
   * If this datatype is not a codatatype, this returns false if there are no
   * values of this datatype that are of finite size.
   *
   * @return True if this datatype is well-founded.
   */
  bool isWellFounded() const;

  /**
   * @return True if this Datatype is a null object.
   */
  bool isNull() const;

  /**
   * @return A string representation of this datatype.
   */
  std::string toString() const;

  /**
   * Iterator for the constructors of a datatype.
   */
  class const_iterator
  {
    friend class Datatype;  // to access constructor

   public:
    /* The following types are required by trait std::iterator_traits */

    /** Iterator tag */
    using iterator_category = std::forward_iterator_tag;

    /** The type of the item */
    using value_type = Datatype;

    /** The pointer type of the item */
    using pointer = const Datatype*;

    /** The reference type of the item */
    using reference = const Datatype&;

    /** The type returned when two iterators are subtracted */
    using difference_type = std::ptrdiff_t;

    /* End of std::iterator_traits required types */

    /** Nullary constructor (required for Cython). */
    const_iterator();

    /**
     * Assignment operator.
     * @param it The iterator to assign to.
     * @return The reference to the iterator after assignment.
     */
    const_iterator& operator=(const const_iterator& it);

    /**
     * Equality operator.
     * @param it The iterator to compare to for equality.
     * @return True if the iterators are equal.
     */
    bool operator==(const const_iterator& it) const;

    /**
     * Disequality operator.
     * @param it The iterator to compare to for disequality.
     * @return True if the iterators are disequal.
     */
    bool operator!=(const const_iterator& it) const;

    /**
     * Increment operator (prefix).
     * @return A reference to the iterator after incrementing by one.
     */
    const_iterator& operator++();

    /**
     * Increment operator (postfix).
     * @return A reference to the iterator after incrementing by one.
     */
    const_iterator operator++(int);

    /**
     * Dereference operator.
     * @return A reference to the constructor this iterator points to.
     */
    const DatatypeConstructor& operator*() const;

    /**
     * Dereference operator.
     * @return A pointer to the constructor this iterator points to.
     */
    const DatatypeConstructor* operator->() const;

   private:
    /**
     * Constructor.
     * @param nm The associated node manager.
     * @param dtype The internal datatype to iterate over.
     * @param begin True if this is a begin() iterator.
     */
    const_iterator(internal::NodeManager* nm,
                   const internal::DType& dtype,
                   bool begin);

    /**
     * The associated node manager.
     */
    internal::NodeManager* d_nm;

    /**
     * A pointer to the list of constructors of the internal datatype
     * to iterate over.
     * This pointer is maintained for operators == and != only.
     */
    const void* d_int_ctors;

    /** The list of datatype constructor (wrappers) to iterate over. */
    std::vector<DatatypeConstructor> d_ctors;

    /** The current index of the iterator. */
    size_t d_idx;
  };

  /**
   * @return An iterator to the first constructor of this datatype.
   */
  const_iterator begin() const;

  /**
   * @return An iterator to one-off-the-last constructor of this datatype.
   */
  const_iterator end() const;

 private:
  /**
   * Constructor.
   * @param nm The associated node manager.
   * @param dtype The internal datatype to be wrapped.
   * @return The Datatype.
   */
  Datatype(internal::NodeManager* nm, const internal::DType& dtype);

  /**
   * Return constructor for name.
   * @param name The name of constructor to find.
   * @return The constructor object for the name.
   */
  DatatypeConstructor getConstructorForName(const std::string& name) const;

  /**
   * Return selector for name.
   * @param name The name of selector to find.
   * @return The selector object for the name.
   */
  DatatypeSelector getSelectorForName(const std::string& name) const;

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated node manager.
   */
  internal::NodeManager* d_nm;

  /**
   * The internal datatype wrapped by this datatype.
   * @note This is a ``std::shared_ptr`` rather than a ``std::unique_ptr``
   *       since ``internal::DType`` is not ref counted.
   */
  std::shared_ptr<internal::DType> d_dtype;
};

/**
 * Serialize a datatype declaration to given stream.
 * @param out The output stream.
 * @param dtdecl The datatype declaration to be serialized to the given stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeDecl& dtdecl) CVC5_EXPORT;

/**
 * Serialize a datatype constructor declaration to given stream.
 * @param out The output stream.
 * @param ctordecl The datatype constructor declaration to be serialized.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructorDecl& ctordecl) CVC5_EXPORT;

/**
 * Serialize a vector of datatype constructor declarations to given stream.
 * @param out The output stream.
 * @param vector The vector of datatype constructor declarations to be.
 * serialized to the given stream
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const std::vector<DatatypeConstructorDecl>& vector)
    CVC5_EXPORT;

/**
 * Serialize a datatype to given stream.
 * @param out The output stream.
 * @param dtype The datatype to be serialized to given stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Datatype& dtype) CVC5_EXPORT;

/**
 * Serialize a datatype constructor to given stream.
 * @param out The output stream.
 * @param ctor The datatype constructor to be serialized to given stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructor& ctor) CVC5_EXPORT;

/**
 * Serialize a datatype selector to given stream.
 * @param out The output stream.
 * @param stor The datatype selector to be serialized to given stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelector& stor) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Grammar                                                                    */
/* -------------------------------------------------------------------------- */

/**
 * A Sygus Grammar. This class can be used to define a context-free grammar
 * of terms. Its interface coincides with the definition of grammars
 * (``GrammarDef``) in the SyGuS IF 2.1 standard.
 */
class CVC5_EXPORT Grammar
{
  friend class parser::Command;
  friend class Solver;

 public:
  /**
   * Add \p rule to the set of rules corresponding to \p ntSymbol.
   * @param ntSymbol The non-terminal to which the rule is added.
   * @param rule The rule to add.
   */
  void addRule(const Term& ntSymbol, const Term& rule);

  /**
   * Add \p rules to the set of rules corresponding to \p ntSymbol.
   * @param ntSymbol The non-terminal to which the rules are added.
   * @param rules The rules to add.
   */
  void addRules(const Term& ntSymbol, const std::vector<Term>& rules);

  /**
   * Allow \p ntSymbol to be an arbitrary constant.
   * @param ntSymbol The non-terminal allowed to be any constant.
   */
  void addAnyConstant(const Term& ntSymbol);

  /**
   * Allow \p ntSymbol to be any input variable to corresponding
   * synth-fun/synth-inv with the same sort as \p ntSymbol.
   * @param ntSymbol The non-terminal allowed to be any input variable.
   */
  void addAnyVariable(const Term& ntSymbol);

  /**
   * @return A string representation of this grammar.
   */
  std::string toString() const;

  /**
   * Nullary constructor. Needed for the Cython API.
   */
  Grammar();

  /**
   * Destructor for bookeeping.
   */
  ~Grammar();

 private:
  /**
   * Constructor.
   * @param slv The solver that created this grammar.
   * @param sygusVars The input variables to synth-fun/synth-var.
   * @param ntSymbols The non-terminals of this grammar.
   */
  Grammar(internal::NodeManager* nm,
          const std::vector<Term>& sygusVars,
          const std::vector<Term>& ntSymbols);

  /**
   * @return The resolved datatype of the Start symbol of the grammar.
   */
  Sort resolve();

  /**
   * Check if \p rule contains variables that are neither parameters of
   * the corresponding synthFun nor non-terminals.
   * @param rule The non-terminal allowed to be any constant.
   * @return True if \p rule contains free variables and false otherwise.
   */
  bool containsFreeVariables(const Term& rule) const;

  /** The node manager associated with this grammar. */
  internal::NodeManager* d_nm;
  /** The internal representation of this grammar. */
  std::shared_ptr<internal::SygusGrammar> d_sg;
};

/**
 * Serialize a grammar to given stream.
 * @param out The output stream.
 * @param g The grammar to be serialized to the given output stream.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const Grammar& g) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Options                                                                    */
/* -------------------------------------------------------------------------- */

/**
 * \verbatim embed:rst:leading-asterisk
 * This class provides type-safe access to a few options that frontends are
 * likely to use, but can not be not be communicated appropriately via the
 * regular :cpp:func:`Solver::getOption() <cvc5::Solver::getOption()>` or
 * :cpp:func:`Solver::getOptionInfo() <cvc5::Solver::getOptionInfo()>` methods.
 * This includes, e.g., the input and output streams that can be configured via
 * :ref:`err <lbl-option-err>`, :ref:`in <lbl-option-in>` and :ref:`out
 * <lbl-option-out>`. This class does not store the options itself, but only
 * acts as a wrapper to the solver object. It can thus no longer be used after
 * the solver object has been destroyed. \endverbatim
 */
class CVC5_EXPORT DriverOptions
{
  friend class Solver;

 public:
  /** Access the solver's input stream */
  std::istream& in() const;
  /** Access the solver's error output stream */
  std::ostream& err() const;
  /** Access the solver's output stream */
  std::ostream& out() const;

 private:
  DriverOptions(const Solver& solver);
  const Solver& d_solver;
};

/**
 * \verbatim embed:rst:leading-asterisk
 * Holds some description about a particular option, including its name, its
 * aliases, whether the option was explicitly set by the user, and information
 * concerning its value. It can be obtained via
 * :cpp:func:`Solver::getOptionInfo() <cvc5::Solver::getOptionInfo()>` and
 * allows for a more detailed inspection of options than
 * :cpp:func:`Solver::getOption() <cvc5::Solver::getOption()>`. The
 * :cpp:member:`valueInfo <cvc5::OptionInfo::valueInfo>` member holds any of the
 * following alternatives:
 *
 * - :cpp:class:`VoidInfo <cvc5::OptionInfo::VoidInfo>` if the option holds no
 *   value (or the value has no native type)
 * - :cpp:class:`ValueInfo <cvc5::OptionInfo::ValueInfo>` if the option is of
 *   type ``bool`` or ``std::string``, holds the current value and the default
 *   value.
 * - :cpp:class:`NumberInfo <cvc5::OptionInfo::NumberInfo>` if the option is of
 *   type ``int64_t``, ``uint64_t`` or ``double``, holds the current and default
 *   value, as well as the minimum and maximum.
 * - :cpp:class:`ModeInfo <cvc5::OptionInfo::ModeInfo>` if the option is a mode
 *   option, holds the current and default values, as well as a list of valid
 *   modes.
 *
 * Additionally, this class provides convenience functions to obtain the
 * current value of an option in a type-safe manner using :cpp:func:`boolValue()
 * <cvc5::OptionInfo::boolValue()>`, :cpp:func:`stringValue()
 * <cvc5::OptionInfo::stringValue()>`, :cpp:func:`intValue()
 * <cvc5::OptionInfo::intValue()>`, :cpp:func:`uintValue()
 * <cvc5::OptionInfo::uintValue()>` and :cpp:func:`doubleValue()
 * <cvc5::OptionInfo::doubleValue()>`. They assert that the option has the
 * respective type and return the current value.
 *
 * If the option has a special type that is not covered by the above
 * alternatives, the :cpp:member:`valueInfo <cvc5::OptionInfo::valueInfo>` holds
 * a :cpp:class:`VoidInfo <cvc5::OptionInfo::VoidInfo>`. Some options, that are
 * expected to be used by frontends (e.g., input and output streams) can also
 * be accessed using :cpp:func:`Solver::getDriverOptions()
 * <cvc5::Solver::getDriverOptions()>`. \endverbatim
 */
struct CVC5_EXPORT OptionInfo
{
  /** Has no value information. */
  struct VoidInfo
  {
  };
  /** Basic information for option values. ``T`` can be ``bool`` or
   * ``std::string``. */
  template <typename T>
  struct ValueInfo
  {
    /** The default value. */
    T defaultValue;
    /** The current value. */
    T currentValue;
  };
  /** Information for numeric values. ``T`` can be ``int64_t``, ``uint64_t`` or
   * ``double``. */
  template <typename T>
  struct NumberInfo
  {
    /** The default value. */
    T defaultValue;
    /** The current value. */
    T currentValue;
    /** The optional minimum value. */
    std::optional<T> minimum;
    /** The optional maximum value. */
    std::optional<T> maximum;
  };
  /** Information for mode option values. */
  struct ModeInfo
  {
    /** The default value. */
    std::string defaultValue;
    /** The current value. */
    std::string currentValue;
    /** The possible modes. */
    std::vector<std::string> modes;
  };

  /** The option name */
  std::string name;
  /** The option name aliases */
  std::vector<std::string> aliases;
  /** Whether the option was explicitly set by the user */
  bool setByUser;
  /** Possible types for ``valueInfo``. */
  using OptionInfoVariant = std::variant<VoidInfo,
                                         ValueInfo<bool>,
                                         ValueInfo<std::string>,
                                         NumberInfo<int64_t>,
                                         NumberInfo<uint64_t>,
                                         NumberInfo<double>,
                                         ModeInfo>;
  /** The option value information */
  OptionInfoVariant valueInfo;
  /**
   * Get the current value as a `bool`.
   * @note Asserts that `valueInfo` holds a `bool`.
   * @return The current value as a `bool`.
   */
  bool boolValue() const;
  /**
   * Get the current value as a `std::string`.
   * @note Asserts that `valueInfo` holds a `std::string`.
   * @return The current value as a `std::string`.
   */
  std::string stringValue() const;
  /**
   * Get the current value as an `int64_t`.
   * @note Asserts that `valueInfo` holds an `int64_t`.
   * @return The current value as a `int64_t`.
   */
  int64_t intValue() const;
  /**
   * Get the current value as a `uint64_t`.
   * @note Asserts that `valueInfo` holds a `uint64_t`.
   * @return The current value as a `uint64_t`.
   */
  uint64_t uintValue() const;
  /**
   * Obtain the current value as a `double`.
   * @note Asserts that `valueInfo` holds a `double`.
   * @return The current value as a `double`.
   */
  double doubleValue() const;
};

/**
 * Print an `OptionInfo` object to an ``std::ostream``.
 */
std::ostream& operator<<(std::ostream& os, const OptionInfo& oi) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Statistics                                                                 */
/* -------------------------------------------------------------------------- */

/**
 * \verbatim embed:rst:leading-asterisk
 * Represents a snapshot of a single statistic value. See :doc:`/statistics` for
 * how statistics can be used.
 * A value can be of type ``int64_t``, ``double``, ``std::string`` or a
 * histogram
 * (``std::map<std::string, uint64_t>``).
 * The value type can be queried (using ``isInt()``, ``isDouble()``, etc.) and
 * the stored value can be accessed (using ``getInt()``, ``getDouble()``, etc.).
 * It is possible to query whether this statistic is an internal statistic by
 * :cpp:func:`isInternal() <cvc5::Stat::isInternal()>` and whether its value is
 * the default value by :cpp:func:`isDefault() <cvc5::Stat::isDefault()>`.
 * \endverbatim
 */
class CVC5_EXPORT Stat
{
  struct StatData;

 public:
  friend class Statistics;
  friend std::ostream& operator<<(std::ostream& os, const Stat& sv);
  /** Representation of a histogram: maps names to frequencies. */
  using HistogramData = std::map<std::string, uint64_t>;
  /**
   * Create an empty statistics object. On such an object all ``isX()`` return
   * false and all ``getX()`` throw an API exception. It solely exists because
   * it makes implementing bindings for other languages much easier.
   */
  Stat();
  /** Copy constructor */
  Stat(const Stat& s);
  /** Destructor */
  ~Stat();
  /** Copy assignment */
  Stat& operator=(const Stat& s);

  /**
   * Determine if this value is intended for internal use only.
   * @return True if this is an internal statistic.
   */
  bool isInternal() const;
  /**
   * Determine if this value holds the default value.
   * @return True if this is a defaulted statistic.
   */
  bool isDefault() const;

  /**
   * Determine if  this value is an integer.
   * @return True if this value is an integer.
   */
  bool isInt() const;
  /**
   * Return the integer value.
   * @return The integer value.
   */
  int64_t getInt() const;
  /**
   * Determine if this value is a double.
   * @return True if this value is a double.
   */
  bool isDouble() const;
  /**
   * Return the double value.
   * @return The double value.
   */
  double getDouble() const;
  /**
   * Determine if this value is a string.
   * @return True if this value is a string.
   */
  bool isString() const;
  /**
   * Return the string value.
   * @return The string value.
   */
  const std::string& getString() const;
  /**
   * Determine if this value is a histogram.
   * @return True if this value is a histogram.
   */
  bool isHistogram() const;
  /**
   * Return the histogram value.
   * @return The histogram value.
   */
  const HistogramData& getHistogram() const;

 private:
  Stat(bool internal, bool def, StatData&& sd);
  /** Whether this statistic is only meant for internal use */
  bool d_internal;
  /** Whether this statistic has the default value */
  bool d_default;
  std::unique_ptr<StatData> d_data;
};

/**
 * Print a `Stat` object to an ``std::ostream``.
 */
std::ostream& operator<<(std::ostream& os, const Stat& sv) CVC5_EXPORT;

/**
 * \verbatim embed:rst:leading-asterisk
 * Represents a snapshot of the solver statistics. See :doc:`/statistics` for
 * how statistics can be used.
 * Once obtained via :cpp:func:`Solver::getStatistics()
 * <cvc5::Solver::getStatistics()>`, an instance of this class is independent of
 * the :cpp:class:`Solver <cvc5::Solver>` object: it will not change when the
 * solvers internal statistics do, and it will not be invalidated if the solver
 * is destroyed. Iterating over this class (via :cpp:func:`begin()
 * <cvc5::Statistics::begin()>` and :cpp:func:`end() <cvc5::Statistics::end()>`)
 * shows only public statistics that have been changed. By passing appropriate
 * flags to :cpp:func:`begin() <cvc5::Statistics::begin()>`, statistics that are
 * internal, defaulted, or both, can be included as well. A single statistic
 * value is represented as :cpp:class:`Stat <cvc5::Stat>`. \endverbatim
 */
class CVC5_EXPORT Statistics
{
 public:
  friend class Solver;
  /** How the statistics are stored internally. */
  using BaseType = std::map<std::string, Stat>;

  /** Custom iterator to hide certain statistics from regular iteration */
  class CVC5_EXPORT iterator
  {
   public:
    friend class Statistics;
    iterator() = default;
    BaseType::const_reference operator*() const;
    BaseType::const_pointer operator->() const;
    iterator& operator++();
    iterator operator++(int);
    iterator& operator--();
    iterator operator--(int);
    bool operator==(const iterator& rhs) const;
    bool operator!=(const iterator& rhs) const;

   private:
    iterator(BaseType::const_iterator it,
             const BaseType& base,
             bool internal,
             bool defaulted);
    bool isVisible() const;
    BaseType::const_iterator d_it;
    const BaseType* d_base;
    bool d_showInternal = false;
    bool d_showDefault = false;
  };

  /** Creates an empty statistics object. */
  Statistics() = default;

  /**
   * Retrieve the statistic with the given name.
   * @note Asserts that a statistic with the given name actually exists and
   *       throws a CVC5ApiRecoverableException if it does not.
   * @param name The name of the statistic.
   * @return The statistic with the given name.
   */
  const Stat& get(const std::string& name);
  /**
   * Begin iteration over the statistics values.
   * By default, only entries that are public and have been set
   * are visible while the others are skipped.
   * @param internal If set to true, internal statistics are shown as well.
   * @param defaulted If set to true, defaulted statistics are shown as well.
   */
  iterator begin(bool internal = false, bool defaulted = false) const;
  /** End iteration */
  iterator end() const;

 private:
  Statistics(const internal::StatisticsRegistry& reg);
  /** Internal data */
  BaseType d_stats;
};
std::ostream& operator<<(std::ostream& out,
                         const Statistics& stats) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * A cvc5 solver.
 */
class CVC5_EXPORT Solver
{
  friend class Datatype;
  friend class DatatypeDecl;
  friend class DatatypeConstructor;
  friend class DatatypeConstructorDecl;
  friend class DatatypeSelector;
  friend class DriverOptions;
  friend class Grammar;
  friend class Op;
  friend class parser::Command;
  friend class main::CommandExecutor;
  friend class Sort;
  friend class Term;

 public:
  /* .................................................................... */
  /* Constructors/Destructors                                             */
  /* .................................................................... */

  /**
   * Constructor.
   * @return The Solver.
   */
  Solver();

  /**
   * Destructor.
   */
  ~Solver();

  /**
   * Disallow copy/assignment.
   */
  Solver(const Solver&) = delete;
  Solver& operator=(const Solver&) = delete;

  /* .................................................................... */
  /* Sorts Handling                                                       */
  /* .................................................................... */

  /**
   * @return Sort Boolean.
   */
  Sort getBooleanSort() const;

  /**
   * @return Sort Integer.
   */
  Sort getIntegerSort() const;

  /**
   * @return Sort Real.
   */
  Sort getRealSort() const;

  /**
   * @return Sort RegExp.
   */
  Sort getRegExpSort() const;

  /**
   * @return Sort RoundingMode.
   */
  Sort getRoundingModeSort() const;

  /**
   * @return Sort String.
   */
  Sort getStringSort() const;

  /**
   * Create an array sort.
   * @param indexSort The array index sort.
   * @param elemSort The array element sort.
   * @return The array sort.
   */
  Sort mkArraySort(const Sort& indexSort, const Sort& elemSort) const;

  /**
   * Create a bit-vector sort.
   * @param size The bit-width of the bit-vector sort.
   * @return The bit-vector sort.
   */
  Sort mkBitVectorSort(uint32_t size) const;

  /**
   * Create a floating-point sort.
   * @param exp The bit-width of the exponent of the floating-point sort.
   * @param sig The bit-width of the significand of the floating-point sort.
   */
  Sort mkFloatingPointSort(uint32_t exp, uint32_t sig) const;

  /**
   * Create a finite-field sort.
   * @param size the modulus of the field. Must be prime.
   * @return The finite-field sort.
   */
  Sort mkFiniteFieldSort(const std::string& size) const;

  /**
   * Create a datatype sort.
   * @param dtypedecl The datatype declaration from which the sort is created.
   * @return The datatype sort.
   */
  Sort mkDatatypeSort(const DatatypeDecl& dtypedecl) const;

  /**
   * Create a vector of datatype sorts. The names of the datatype declarations
   * must be distinct.
   *
   * @param dtypedecls The datatype declarations from which the sort is created.
   * @return The datatype sorts.
   */
  std::vector<Sort> mkDatatypeSorts(
      const std::vector<DatatypeDecl>& dtypedecls) const;

  /**
   * Create function sort.
   * @param sorts The sort of the function arguments.
   * @param codomain The sort of the function return value.
   * @return The function sort.
   */
  Sort mkFunctionSort(const std::vector<Sort>& sorts,
                      const Sort& codomain) const;

  /**
   * Create a sort parameter.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param symbol The name of the sort.
   * @return The sort parameter.
   */
  Sort mkParamSort(
      const std::optional<std::string>& symbol = std::nullopt) const;

  /**
   * Create a predicate sort.
   *
   * This is equivalent to calling mkFunctionSort() with the Boolean sort as the
   * codomain.
   * @param sorts The list of sorts of the predicate.
   * @return The predicate sort.
   */
  Sort mkPredicateSort(const std::vector<Sort>& sorts) const;

  /**
   * Create a record sort
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param fields The list of fields of the record.
   * @return The record sort.
   */
  Sort mkRecordSort(
      const std::vector<std::pair<std::string, Sort>>& fields) const;

  /**
   * Create a set sort.
   * @param elemSort The sort of the set elements.
   * @return The set sort.
   */
  Sort mkSetSort(const Sort& elemSort) const;

  /**
   * Create a bag sort.
   * @param elemSort The sort of the bag elements.
   * @return The bag sort.
   */
  Sort mkBagSort(const Sort& elemSort) const;

  /**
   * Create a sequence sort.
   * @param elemSort The sort of the sequence elements.
   * @return The sequence sort.
   */
  Sort mkSequenceSort(const Sort& elemSort) const;

  /**
   * Create an abstract sort. An abstract sort represents a sort for a given
   * kind whose parameters and arguments are unspecified.
   *
   * The kind `k` must be the kind of a sort that can be abstracted, i.e., a
   * sort that has indices or argument sorts. For example, #ARRAY_SORT and
   * #BITVECTOR_SORT can be passed as the kind `k` to this method, while
   * INTEGER_SORT and STRING_SORT cannot.
   *
   * @note Providing the kind #ABSTRACT_SORT as an argument to this method
   * returns the (fully) unspecified sort, denoted `?`.
   *
   * @note Providing a kind `k` that has no indices and a fixed arity
   * of argument sorts will return the sort of kind `k` whose arguments are the
   * unspecified sort. For example, `mkAbstractSort(ARRAY_SORT)` will return
   * the sort `(ARRAY_SORT ? ?)` instead of the abstract sort whose abstract
   * kind is #ARRAY_SORT.
   *
   * @param k The kind of the abstract sort
   * @return The abstract sort.
   *
   * @warning This method is experimental and may change in future versions.
   */
  Sort mkAbstractSort(SortKind k) const;

  /**
   * Create an uninterpreted sort.
   * @param symbol The name of the sort.
   * @return The uninterpreted sort.
   */
  Sort mkUninterpretedSort(
      const std::optional<std::string>& symbol = std::nullopt) const;

  /**
   * Create an unresolved datatype sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive parametric datatypes.
   *
   * @param symbol The symbol of the sort.
   * @param arity The number of sort parameters of the sort.
   * @return The unresolved sort.
   *
   * @warning This method is experimental and may change in future versions.
   */
  Sort mkUnresolvedDatatypeSort(const std::string& symbol,
                                size_t arity = 0) const;

  /**
   * Create an uninterpreted sort constructor sort.
   *
   * An uninterpreted sort constructor is an uninterpreted sort with arity > 0.
   *
   * @param symbol The symbol of the sort.
   * @param arity The arity of the sort (must be > 0)
   * @return The uninterpreted sort constructor sort.
   */
  Sort mkUninterpretedSortConstructorSort(
      size_t arity,
      const std::optional<std::string>& symbol = std::nullopt) const;

  /**
   * Create a tuple sort.
   * @param sorts Of the elements of the tuple.
   * @return The tuple sort.
   */
  Sort mkTupleSort(const std::vector<Sort>& sorts) const;

  /* .................................................................... */
  /* Create Terms                                                         */
  /* .................................................................... */

  /**
   * Create n-ary term of given kind.
   * @param kind The kind of the term.
   * @param children The children of the term.
   * @return The Term */
  Term mkTerm(Kind kind, const std::vector<Term>& children = {}) const;

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op The operator.
   * @param children The children of the term.
   * @return The Term.
   */
  Term mkTerm(const Op& op, const std::vector<Term>& children = {}) const;

  /**
   * Create a tuple term.
   * @param terms The elements in the tuple.
   * @return The tuple Term.
   */
  Term mkTuple(const std::vector<Term>& terms) const;

  /* .................................................................... */
  /* Create Operators                                                     */
  /* .................................................................... */

  /**
   * Create operator of Kind:
   *   - #BITVECTOR_EXTRACT
   *   - #BITVECTOR_REPEAT
   *   - #BITVECTOR_ROTATE_LEFT
   *   - #BITVECTOR_ROTATE_RIGHT
   *   - #BITVECTOR_SIGN_EXTEND
   *   - #BITVECTOR_ZERO_EXTEND
   *   - #DIVISIBLE
   *   - #FLOATINGPOINT_TO_FP_FROM_FP
   *   - #FLOATINGPOINT_TO_FP_FROM_IEEE_BV
   *   - #FLOATINGPOINT_TO_FP_FROM_REAL
   *   - #FLOATINGPOINT_TO_FP_FROM_SBV
   *   - #FLOATINGPOINT_TO_FP_FROM_UBV
   *   - #FLOATINGPOINT_TO_SBV
   *   - #FLOATINGPOINT_TO_UBV
   *   - #INT_TO_BITVECTOR
   *   - #TUPLE_PROJECT
   *
   * See cvc5::Kind for a description of the parameters.
   * @param kind The kind of the operator.
   * @param args The arguments (indices) of the operator.
   *
   * @note If ``args`` is empty, the Op simply wraps the cvc5::Kind.  The
   * Kind can be used in Solver::mkTerm directly without creating an Op
   * first.
   */
  Op mkOp(Kind kind, const std::vector<uint32_t>& args = {}) const;

#ifndef DOXYGEN_SKIP
  // Overload is only used to disambiguate the std::vector and std::string
  // overloads.
  Op mkOp(Kind kind, const std::initializer_list<uint32_t>& args) const;
#endif

  /**
   * Create operator of kind:
   *   - DIVISIBLE (to support arbitrary precision integers)
   * See cvc5::Kind for a description of the parameters.
   * @param kind The kind of the operator.
   * @param arg The string argument to this operator.
   */
  Op mkOp(Kind kind, const std::string& arg) const;

  /* .................................................................... */
  /* Create Constants                                                     */
  /* .................................................................... */

  /**
   * Create a Boolean true constant.
   * @return The true constant.
   */
  Term mkTrue() const;

  /**
   * Create a Boolean false constant.
   * @return The false constant.
   */
  Term mkFalse() const;

  /**
   * Create a Boolean constant.
   * @return The Boolean constant.
   * @param val The value of the constant.
   */
  Term mkBoolean(bool val) const;

  /**
   * Create a constant representing the number Pi.
   * @return A constant representing Pi.
   */
  Term mkPi() const;
  /**
   * Create an integer constant from a string.
   * @param s The string representation of the constant, may represent an
   *          integer (e.g., "123").
   * @return A constant of sort Integer assuming 's' represents an integer)
   */
  Term mkInteger(const std::string& s) const;

  /**
   * Create an integer constant from a c++ int.
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  Term mkInteger(int64_t val) const;

  /**
   * Create a real constant from a string.
   * @param s The string representation of the constant, may represent an
   *          integer (e.g., "123") or real constant (e.g., "12.34" or "12/34").
   * @return A constant of sort Real.
   */
  Term mkReal(const std::string& s) const;

  /**
   * Create a real constant from an integer.
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  Term mkReal(int64_t val) const;

  /**
   * Create a real constant from a rational.
   * @param num The value of the numerator.
   * @param den The value of the denominator.
   * @return A constant of sort Real.
   */
  Term mkReal(int64_t num, int64_t den) const;

  /**
   * Create a regular expression all (re.all) term.
   * @return The all term.
   */
  Term mkRegexpAll() const;

  /**
   * Create a regular expression allchar (re.allchar) term.
   * @return The allchar term.
   */
  Term mkRegexpAllchar() const;

  /**
   * Create a regular expression none (re.none) term.
   * @return The none term.
   */
  Term mkRegexpNone() const;

  /**
   * Create a constant representing an empty set of the given sort.
   * @param sort The sort of the set elements.
   * @return The empty set constant.
   */
  Term mkEmptySet(const Sort& sort) const;

  /**
   * Create a constant representing an empty bag of the given sort.
   * @param sort The sort of the bag elements.
   * @return The empty bag constant.
   */
  Term mkEmptyBag(const Sort& sort) const;

  /**
   * Create a separation logic empty term.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @return The separation logic empty term.
   */
  Term mkSepEmp() const;

  /**
   * Create a separation logic nil term.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param sort The sort of the nil term.
   * @return The separation logic nil term.
   */
  Term mkSepNil(const Sort& sort) const;

  /**
   * Create a String constant from a `std::string` which may contain SMT-LIB
   * compatible escape sequences like `\u1234` to encode unicode characters.
   * @param s The string this constant represents.
   * @param useEscSequences Determines whether escape sequences in `s` should.
   * be converted to the corresponding unicode character
   * @return The String constant.
   */
  Term mkString(const std::string& s, bool useEscSequences = false) const;

  /**
   * Create a String constant from a `std::wstring`.
   * This method does not support escape sequences as `std::wstring` already
   * supports unicode characters.
   * @param s The string this constant represents.
   * @return The String constant.
   */
  Term mkString(const std::wstring& s) const;

  /**
   * Create an empty sequence of the given element sort.
   * @param sort The element sort of the sequence.
   * @return The empty sequence with given element sort.
   */
  Term mkEmptySequence(const Sort& sort) const;

  /**
   * Create a universe set of the given sort.
   * @param sort The sort of the set elements.
   * @return The universe set constant.
   */
  Term mkUniverseSet(const Sort& sort) const;

  /**
   * Create a bit-vector constant of given size and value.
   *
   * @note The given value must fit into a bit-vector of the given size.
   *
   * @param size The bit-width of the bit-vector sort.
   * @param val The value of the constant.
   * @return The bit-vector constant.
   */
  Term mkBitVector(uint32_t size, uint64_t val = 0) const;

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   *
   * @note The given value must fit into a bit-vector of the given size.
   *
   * @param size The bit-width of the constant.
   * @param s The string representation of the constant.
   * @param base The base of the string representation (2, 10, or 16)
   * @return The bit-vector constant.
   */
  Term mkBitVector(uint32_t size, const std::string& s, uint32_t base) const;

  /**
   * Create a finite field constant in a given field from a given string
   *
   * @param value The string representation of the constant.
   * @param sort The field sort
   *
   * If size is the field size, the constant needs not be in the range [0,size).
   * If it is outside this range, it will be reduced modulo size before being
   * constructed.
   */
  Term mkFiniteFieldElem(const std::string& value, const Sort& sort) const;

  /**
   * Create a constant array with the provided constant value stored at every
   * index
   * @param sort The sort of the constant array (must be an array sort).
   * @param val The constant value to store (must match the sort's element
   *            sort).
   * @return The constant array term.
   */
  Term mkConstArray(const Sort& sort, const Term& val) const;

  /**
   * Create a positive infinity floating-point constant (SMT-LIB: `+oo`).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   */
  Term mkFloatingPointPosInf(uint32_t exp, uint32_t sig) const;

  /**
   * Create a negative infinity floating-point constant (SMT-LIB: `-oo`).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   */
  Term mkFloatingPointNegInf(uint32_t exp, uint32_t sig) const;

  /**
   * Create a not-a-number floating-point constant (SMT-LIB: `NaN`).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   */
  Term mkFloatingPointNaN(uint32_t exp, uint32_t sig) const;

  /**
   * Create a positive zero floating-point constant (SMT-LIB: +zero).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   */
  Term mkFloatingPointPosZero(uint32_t exp, uint32_t sig) const;

  /**
   * Create a negative zero floating-point constant (SMT-LIB: -zero).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   */
  Term mkFloatingPointNegZero(uint32_t exp, uint32_t sig) const;

  /**
   * Create a rounding mode value.
   * @param rm The floating point rounding mode this constant represents.
   * @return The rounding mode value.
   */
  Term mkRoundingMode(RoundingMode rm) const;

  /**
   * Create a floating-point value from a bit-vector given in IEEE-754
   * format.
   * @param exp Size of the exponent.
   * @param sig Size of the significand.
   * @param val Value of the floating-point constant as a bit-vector term.
   * @return The floating-point value.
   */
  Term mkFloatingPoint(uint32_t exp, uint32_t sig, const Term& val) const;
  /**
   * Create a floating-point value from its three IEEE-754 bit-vector
   * value components (sign bit, exponent, significand).
   * @param sign The sign bit.
   * @param exp  The bit-vector representing the exponent.
   * @param sig The bit-vector representing the significand.
   * @return The floating-point value.
   */
  Term mkFloatingPoint(const Term& sign,
                       const Term& exp,
                       const Term& sig) const;

  /**
   * Create a cardinality constraint for an uninterpreted sort.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param sort The sort the cardinality constraint is for.
   * @param upperBound The upper bound on the cardinality of the sort.
   * @return The cardinality constraint.
   */
  Term mkCardinalityConstraint(const Sort& sort, uint32_t upperBound) const;

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
   * @param sort The sort of the constant.
   * @param symbol The name of the constant (optional).
   * @return The constant.
   */
  Term mkConst(const Sort& sort,
               const std::optional<std::string>& symbol = std::nullopt) const;

  /**
   * Create a bound variable to be used in a binder (i.e., a quantifier, a
   * lambda, or a witness binder).
   * @param sort The sort of the variable.
   * @param symbol The name of the variable (optional).
   * @return The variable.
   */
  Term mkVar(const Sort& sort,
             const std::optional<std::string>& symbol = std::nullopt) const;

  /* .................................................................... */
  /* Create datatype constructor declarations                             */
  /* .................................................................... */

  /**
   * Create a datatype constructor declaration.
   * @param name The name of the datatype constructor.
   * @return The DatatypeConstructorDecl.
   */
  DatatypeConstructorDecl mkDatatypeConstructorDecl(const std::string& name);

  /* .................................................................... */
  /* Create datatype declarations                                         */
  /* .................................................................... */

  /**
   * Create a datatype declaration.
   * @param name The name of the datatype.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  DatatypeDecl mkDatatypeDecl(const std::string& name,
                              bool isCoDatatype = false);

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param name The name of the datatype.
   * @param params A list of sort parameters.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  DatatypeDecl mkDatatypeDecl(const std::string& name,
                              const std::vector<Sort>& params,
                              bool isCoDatatype = false);

  /* .................................................................... */
  /* Formula Handling                                                     */
  /* .................................................................... */

  /**
   * Simplify a formula without doing "much" work.
   *
   * Does not involve the SAT Engine in the simplification, but uses the
   * current definitions, and assertions.  It also involves theory
   * normalization.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param t The formula to simplify.
   * @return The simplified formula.
   */
  Term simplify(const Term& t);

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
   * @param term The formula to assert.
   */
  void assertFormula(const Term& term) const;

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
   * @return The result of the satisfiability check.
   */
  Result checkSat() const;

  /**
   * Check satisfiability assuming the given formula.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (check-sat-assuming ( <prop_literal> ))
   * \endverbatim
   *
   * @param assumption The formula to assume.
   * @return The result of the satisfiability check.
   */
  Result checkSatAssuming(const Term& assumption) const;

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
   * @param assumptions The formulas to assume.
   * @return The result of the satisfiability check.
   */
  Result checkSatAssuming(const std::vector<Term>& assumptions) const;

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
   * @param symbol The name of the datatype sort.
   * @param ctors The constructor declarations of the datatype sort.
   * @return The datatype sort.
   */
  Sort declareDatatype(const std::string& symbol,
                       const std::vector<DatatypeConstructorDecl>& ctors) const;

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
   * @param symbol The name of the function.
   * @param sorts The sorts of the parameters to this function.
   * @param sort The sort of the return value of this function.
   * @return The function.
   */
  Term declareFun(const std::string& symbol,
                  const std::vector<Sort>& sorts,
                  const Sort& sort) const;

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
   *       mkUninterpretedSort(const std::optional<std::string>&) const
   *       if arity = 0, and to
   *       mkUninterpretedSortConstructorSort(size_t arity, const std::optional<std::string>&) const
   *       if arity > 0.
   *
   * @param symbol The name of the sort.
   * @param arity The arity of the sort.
   * @return The sort.
   */
  Sort declareSort(const std::string& symbol, uint32_t arity) const;

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
   * @param symbol The name of the function.
   * @param bound_vars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  Term defineFun(const std::string& symbol,
                 const std::vector<Term>& bound_vars,
                 const Sort& sort,
                 const Term& term,
                 bool global = false) const;

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
   * @param symbol The name of the function.
   * @param bound_vars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  Term defineFunRec(const std::string& symbol,
                    const std::vector<Term>& bound_vars,
                    const Sort& sort,
                    const Term& term,
                    bool global = false) const;

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
   * @param fun The sorted function.
   * @param bound_vars The parameters to this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  Term defineFunRec(const Term& fun,
                    const std::vector<Term>& bound_vars,
                    const Term& term,
                    bool global = false) const;

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
   * Create elements of parameter 'funs' with mkConst().
   * @param funs The sorted functions.
   * @param bound_vars The list of parameters to the functions.
   * @param terms The list of function bodies of the functions.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   */
  void defineFunsRec(const std::vector<Term>& funs,
                     const std::vector<std::vector<Term>>& bound_vars,
                     const std::vector<Term>& terms,
                     bool global = false) const;

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
   * @return The list of asserted formulas.
   */
  std::vector<Term> getAssertions() const;

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
   * @return The info.
   */
  std::string getInfo(const std::string& flag) const;

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
   * @param option The option for which the value is queried.
   * @return A string representation of the option value.
   */
  std::string getOption(const std::string& option) const;

  /**
   * Get all option names that can be used with setOption(), getOption() and
   * getOptionInfo().
   * @return All option names.
   */
  std::vector<std::string> getOptionNames() const;

  /**
   * Get some information about the given option.
   *
   * Check the OptionInfo class for more details on which information is
   * available.
   *
   * @return Information about the given option.
   */
  OptionInfo getOptionInfo(const std::string& option) const;

  /**
   * Get the driver options, which provide access to options that can not be
   * communicated properly via getOption() and getOptionInfo().
   * @return A DriverOptions object.
   */
  DriverOptions getDriverOptions() const;

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
   * @return The set of unsat assumptions.
   */
  std::vector<Term> getUnsatAssumptions() const;

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
   *   unsatisfiable core returned by this method.
   * \endverbatim
   *
   * @return A set of terms representing the unsatisfiable core.
   */
  std::vector<Term> getUnsatCore() const;

  /**
   * Get a difficulty estimate for an asserted formula. This method is
   * intended to be called immediately after any response to a checkSat.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @return A map from (a subset of) the input assertions to a real value that.
   *         is an estimate of how difficult each assertion was to solve.
   *         Unmentioned assertions can be assumed to have zero difficulty.
   */
  std::map<Term, Term> getDifficulty() const;

  /**
   * Get a timeout core, which computes a subset of the current assertions that
   * cause a timeout. Note it does not require being proceeded by a call to
   * checkSat.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-timeout-core)
   * \endverbatim
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @return The result of the timeout core computation. This is a pair
   * containing a result and a list of formulas. If the result is unknown
   * and the reason is timeout, then the list of formulas correspond to a
   * subset of the current assertions that cause a timeout in the specified
   * time :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`.
   * If the result is unsat, then the list of formulas correspond to an
   * unsat core for the current assertions. Otherwise, the result is sat,
   * indicating that the current assertions are satisfiable, and
   * the list of formulas is empty.
   *
   * This method may make multiple checks for satisfiability internally, each
   * limited by the timeout value given by
   * :ref:`timeout-core-timeout <lbl-option-timeout-core-timeout>`.
   */
  std::pair<Result, std::vector<Term>> getTimeoutCore() const;

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
   * @warning This method is experimental and may change in future versions.
   *
   * @param c The component of the proof to return
   * @return A string representing the proof. This takes into account
   * :ref:`proof-format-mode <lbl-option-proof-format-mode>` when `c` is
   * `PROOF_COMPONENT_FULL`.
   */
  std::string getProof(
      modes::ProofComponent c = modes::PROOF_COMPONENT_FULL) const;

  /**
   * Get a list of learned literals that are entailed by the current set of
   * assertions.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param t The type of learned literals to return
   * @return A list of literals that were learned at top-level.
   */
  std::vector<Term> getLearnedLiterals(
      modes::LearnedLitType t = modes::LEARNED_LIT_INPUT) const;

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
   * @param term The term for which the value is queried.
   * @return The value of the given term.
   */
  Term getValue(const Term& term) const;

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
   * @param terms The terms for which the value is queried.
   * @return The values of the given terms.
   */
  std::vector<Term> getValue(const std::vector<Term>& terms) const;

  /**
   * Get the domain elements of uninterpreted sort s in the current model. The
   * current model interprets s as the finite sort whose domain elements are
   * given in the return value of this method.
   *
   * @param s The uninterpreted sort in question.
   * @return The domain elements of s in the current model.
   */
  std::vector<Term> getModelDomainElements(const Sort& s) const;

  /**
   * This returns false if the model value of free constant v was not essential
   * for showing the satisfiability of the last call to checkSat using the
   * current model. This method will only return false (for any `v`) if
   * option
   * \verbatim embed:rst:inline :ref:`model-cores <lbl-option-model-cores>`\endverbatim
   * has been set.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param v The term in question.
   * @return True if `v` is a model core symbol.
   */
  bool isModelCoreSymbol(const Term& v) const;

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
   * @warning This method is experimental and may change in future versions.
   *
   * @param sorts The list of uninterpreted sorts that should be printed in
   *              the model.
   * @param vars The list of free constants that should be printed in the
   *             model. A subset of these may be printed based on
   *             isModelCoreSymbol().
   * @return A string representing the model.
   */
  std::string getModel(const std::vector<Sort>& sorts,
                       const std::vector<Term>& vars) const;

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
   * LIA and BV.
   *
   * @warning This method is experimental and may change in future versions.
   *
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
  Term getQuantifierElimination(const Term& q) const;

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
   * @warning This method is experimental and may change in future versions.
   *
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
   *           Solver::getQuantifierEliminationDisjunct() for @f$q@f$ with the
   *           set of assertions @f$(A \wedge Q_{i-1})@f$.
   *           Similarly, if @f$Q@f$ is @f$\forall@f$, then let
   *           @f$(A \wedge Q_n)@f$ be
   *           @f$(A \wedge (\phi \wedge Q_1) \wedge ... \wedge (\phi \wedge
   *           Q_n))@f$
   *           where @f$(\phi \wedge Q_i)@f$ is the same as above.
   *           In either case, we have that @f$(\phi \wedge Q_j)@f$ will
   *           eventually be true or false, for some finite j.
   */
  Term getQuantifierEliminationDisjunct(const Term& q) const;

  /**
   * When using separation logic, this sets the location sort and the
   * datatype sort to the given ones. This method should be invoked exactly
   * once, before any separation logic constraints are provided.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param locSort The location sort of the heap.
   * @param dataSort The data sort of the heap.
   */
  void declareSepHeap(const Sort& locSort, const Sort& dataSort) const;

  /**
   * When using separation logic, obtain the term for the heap.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @return The term for the heap.
   */
  Term getValueSepHeap() const;

  /**
   * When using separation logic, obtain the term for nil.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @return The term for nil.
   */
  Term getValueSepNil() const;

  /**
   * Declare a symbolic pool of terms with the given initial value.
   *
   * For details on how pools are used to specify instructions for quantifier
   * instantiation, see documentation for the #INST_POOL kind.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (declare-pool <symbol> <sort> ( <term>* ))
   * \endverbatim
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param symbol The name of the pool.
   * @param sort The sort of the elements of the pool.
   * @param initValue The initial value of the pool.
   * @return The pool symbol.
   */
  Term declarePool(const std::string& symbol,
                   const Sort& sort,
                   const std::vector<Term>& initValue) const;
  /**
   * Declare an oracle function with reference to an implementation.
   *
   * Oracle functions have a different semantics with respect to ordinary
   * declared functions. In particular, for an input to be satisfiable,
   * its oracle functions are implicitly universally quantified.
   *
   * This method is used in part for implementing this command:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   * (declare-oracle-fun <sym> (<sort>*) <sort> <sym>)
   * \endverbatim
   *
   * In particular, the above command is implemented by constructing a
   * function over terms that wraps a call to binary sym via a text interface.
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param symbol The name of the oracle
   * @param sorts The sorts of the parameters to this function
   * @param sort The sort of the return value of this function
   * @param fn The function that implements the oracle function.
   * @return The oracle function
   */
  Term declareOracleFun(const std::string& symbol,
                        const std::vector<Sort>& sorts,
                        const Sort& sort,
                        std::function<Term(const std::vector<Term>&)> fn) const;
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
   * @param nscopes The number of levels to pop.
   */
  void pop(uint32_t nscopes = 1) const;

  /**
   * Get an interpolant
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-interpolant <conj>)
   *
   * Requires option
   * :ref:`produce-interpolants <lbl-option-produce-interpolants>` to be set to
   * a mode different from `none`. \endverbatim
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @return A Term @f$I@f$ such that @f$A \rightarrow I@f$ and
   *         @f$I \rightarrow B@f$ are valid, where @f$A@f$ is the
   *         current set of assertions and @f$B@f$ is given in the input by
   *         `conj`, or the null term if such a term cannot be found.
   */
  Term getInterpolant(const Term& conj) const;

  /**
   * Get an interpolant
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-interpolant <conj> <grammar>)
   *
   * Requires option
   * :ref:`produce-interpolants <lbl-option-produce-interpolants>` to be set to
   * a mode different from `none`. \endverbatim
   *
   * @warning This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @param grammar The grammar for the interpolant I.
   * @return A Term @f$I@f$ such that @f$A \rightarrow I@f$ and
   *         @f$I \rightarrow B@f$ are valid, where @f$A@f$ is the
   *         current set of assertions and @f$B@f$ is given in the input by
   *         `conj`, or the null term if such a term cannot be found.
   */
  Term getInterpolant(const Term& conj, Grammar& grammar) const;

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
   * @warning This method is experimental and may change in future versions.
   *
   * @return A Term @f$I@f$ such that @f$A \rightarrow I@f$ and
   *         @f$I \rightarrow B@f$ are valid, where @f$A@f$ is the
   *         current set of assertions and @f$B@f$ is given in the input by
   *         `conj`, or the null term if such a term cannot be found.
   */
  Term getInterpolantNext() const;

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
   * @warning This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @return A term @f$C@f$ such that @f$(A \wedge C)@f$ is satisfiable,
   *         and @f$(A \wedge \neg B \wedge C)@f$ is unsatisfiable, where
   *         @f$A@f$ is the current set of assertions and @f$B@f$ is
   *         given in the input by ``conj``, or the null term if such a term
   *         cannot be found.
   */
  Term getAbduct(const Term& conj) const;

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
   * @warning This method is experimental and may change in future versions.
   *
   *
   * @param conj The conjecture term.
   * @param grammar The grammar for the abduct @f$C@f$
   * @return A term C such that @f$(A \wedge C)@f$ is satisfiable, and
   *        @f$(A \wedge \neg B \wedge C)@f$ is unsatisfiable, where @f$A@f$ is
   *        the current set of assertions and @f$B@f$ is given in the input by
   *        `conj`, or the null term if such a term cannot be found.
   */
  Term getAbduct(const Term& conj, Grammar& grammar) const;

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
   * @warning This method is experimental and may change in future versions.
   *
   * @return A term C such that @f$(A \wedge C)@f$ is satisfiable, and
   *        @f$(A \wedge \neg B \wedge C)@f$ is unsatisfiable, where @f$A@f$ is
   *        the current set of assertions and @f$B@f$ is given in the input by
   *        the last call to getAbduct(), or the null term if such a term
   *        cannot be found.
   */
  Term getAbductNext() const;

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
   * @warning This method is experimental and may change in future versions.
   *
   * @param mode The mode to use for blocking.
   */
  void blockModel(modes::BlockModelsMode mode) const;

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
   * @warning This method is experimental and may change in future versions.
   */
  void blockModelValues(const std::vector<Term>& terms) const;

  /**
   * @warning This method is experimental and may change in future versions.
   *
   * @return A string that contains information about all instantiations made
   *         by the quantifiers module.
   */
  std::string getInstantiations() const;

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
   * @param nscopes The number of levels to push.
   */
  void push(uint32_t nscopes = 1) const;

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
   */
  void resetAssertions() const;

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
   * @param keyword The info flag.
   * @param value The value of the info flag.
   */
  void setInfo(const std::string& keyword, const std::string& value) const;

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
   * @param logic The logic to set.
   */
  void setLogic(const std::string& logic) const;

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
   * @param option The option name.
   * @param value The option value.
   */
  void setOption(const std::string& option, const std::string& value) const;

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
   * @param sort The sort of the universal variable.
   * @param symbol The name of the universal variable.
   * @return The universal variable.
   */
  Term declareSygusVar(const std::string& symbol, const Sort& sort) const;

  /**
   * Create a Sygus grammar. The first non-terminal is treated as the starting
   * non-terminal, so the order of non-terminals matters.
   *
   * @param boundVars The parameters to corresponding synth-fun/synth-inv.
   * @param ntSymbols The pre-declaration of the non-terminal symbols.
   * @return The grammar.
   */
  Grammar mkGrammar(const std::vector<Term>& boundVars,
                    const std::vector<Term>& ntSymbols) const;

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
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @return The function.
   */
  Term synthFun(const std::string& symbol,
                const std::vector<Term>& boundVars,
                const Sort& sort) const;

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
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param grammar The syntactic constraints.
   * @return The function.
   */
  Term synthFun(const std::string& symbol,
                const std::vector<Term>& boundVars,
                Sort sort,
                Grammar& grammar) const;

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
   * @param term The formula to add as a constraint.
   */
  void addSygusConstraint(const Term& term) const;

  /**
   * Get the list of sygus constraints.
   *
   * @return The list of sygus constraints.
   */
  std::vector<Term> getSygusConstraints() const;

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
   * @param term The formula to add as an assumption.
   */
  void addSygusAssume(const Term& term) const;

  /**
   * Get the list of sygus assumptions.
   *
   * @return The list of sygus assumptions.
   */
  std::vector<Term> getSygusAssumptions() const;

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
   * @param inv The function-to-synthesize.
   * @param pre The pre-condition.
   * @param trans The transition relation.
   * @param post The post-condition.
   */
  void addSygusInvConstraint(Term inv, Term pre, Term trans, Term post) const;

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
   * @return The result of the check, which is "solution" if the check found a
   *         solution in which case solutions are available via
   *         getSynthSolutions, "no solution" if it was determined there is no
   *         solution, or "unknown" otherwise.
   */
  SynthResult checkSynth() const;

  /**
   * Try to find a next solution for the synthesis conjecture corresponding to
   * the current list of functions-to-synthesize, universal variables and
   * constraints. Must be called immediately after a successful call to
   * check-synth or check-synth-next. Requires incremental mode.
   *
   * SyGuS v2:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (check-synth-next)
   * \endverbatim
   *
   * @return The result of the check, which is "solution" if the check found a
   *         solution in which case solutions are available via
   *         getSynthSolutions, "no solution" if it was determined there is no
   *         solution, or "unknown" otherwise.
   */
  SynthResult checkSynthNext() const;

  /**
   * Get the synthesis solution of the given term. This method should be called
   * immediately after the solver answers unsat for sygus input.
   * @param term The term for which the synthesis solution is queried.
   * @return The synthesis solution of the given term.
   */
  Term getSynthSolution(Term term) const;

  /**
   * Get the synthesis solutions of the given terms. This method should be
   * called immediately after the solver answers unsat for sygus input.
   * @param terms The terms for which the synthesis solutions is queried.
   * @return The synthesis solutions of the given terms.
   */
  std::vector<Term> getSynthSolutions(const std::vector<Term>& terms) const;

  /**
   * Get a snapshot of the current state of the statistic values of this
   * solver. The returned object is completely decoupled from the solver and
   * will not change when the solver is used again.
   * @return A snapshot of the current state of the statistic values.
   */
  Statistics getStatistics() const;

  /**
   * Print the statistics to the given file descriptor, suitable for usage in
   * signal handlers.
   */
  void printStatisticsSafe(int fd) const;

  /**
   * Determines if the output stream for the given tag is enabled. Tags can be
   * enabled with the `output` option (and `-o <tag>` on the command line).
   * Raises an exception when an invalid tag is given.
   * @return True if the given tag is enabled.
   */
  bool isOutputOn(const std::string& tag) const;

  /**
   * Get an output stream for the given tag. Tags can be enabled with the
   * `output` option (and `-o <tag>` on the command line). Raises an exception
   * when an invalid tag is given.
   * @return The output stream.
   */
  std::ostream& getOutput(const std::string& tag) const;

  /**
   * Get a string representation of the version of this solver.
   * @return The version string.
   */
  std::string getVersion() const;

 private:
  /**
   * Helper for mk-functions that call d_nm->mkConst().
   * @param nm The associated node manager.
   * @pram t The value.
   */
  template <typename T>
  static Term mkValHelper(internal::NodeManager* nm, const T& t);
  /**
   * Helper for creating rational values.
   * @param nm The associated node manager.
   * @param r The value (either int or real).
   * @param isInt True to create an integer value.
   */
  static Term mkRationalValHelper(internal::NodeManager*,
                                  const internal::Rational&,
                                  bool);

  /*
   * Constructs a solver with the given original options. This should only be
   * used internally when the Solver is reset.
   */
  Solver(std::unique_ptr<internal::Options>&& original);

  /** @return The node manager of this solver */
  internal::NodeManager* getNodeManager(void) const;
  /** Reset the API statistics */
  void resetStatistics();

  /** Helper to check for API misuse in mkOp functions. */
  void checkMkTerm(Kind kind, uint32_t nchildren) const;
  /** Helper for creating operators. */
  template <typename T>
  Op mkOpHelper(Kind kind, const T& t) const;
  /** Helper for mkReal functions that take a string as argument. */
  Term mkRealOrIntegerFromStrHelper(const std::string& s,
                                    bool isInt = true) const;
  /** Helper for mkBitVector functions that take a string as argument. */
  Term mkBVFromStrHelper(const std::string& s, uint32_t base) const;
  /**
   * Helper for mkBitVector functions that take a string and a size as
   * arguments.
   */
  Term mkBVFromStrHelper(uint32_t size,
                         const std::string& s,
                         uint32_t base) const;
  /** Helper for mkBitVector functions that take an integer as argument. */
  Term mkBVFromIntHelper(uint32_t size, uint64_t val) const;
  /** Helper for functions that create tuple sorts. */
  Sort mkTupleSortHelper(const std::vector<Sort>& sorts) const;
  /** Helper for mkTerm functions that create Term from a Kind */
  Term mkTermFromKind(Kind kind) const;
  /** Helper for mkChar functions that take a string as argument. */
  Term mkCharFromStrHelper(const std::string& s) const;
  /** Get value helper, which accounts for subtyping */
  Term getValueHelper(const Term& term) const;

  /**
   * Create n-ary term of given kind. This handles the cases of left/right
   * associative operators, chainable operators, and cases when the number of
   * children exceeds the maximum arity for the kind.
   * @param kind The kind of the term.
   * @param children The children of the term.
   * @return The Term.
   */
  Term mkTermHelper(Kind kind, const std::vector<Term>& children) const;

  /**
   * Create n-ary term of given kind from a given operator.
   * @param op The operator.
   * @param children The children of the term.
   * @return The Term.
   */
  Term mkTermHelper(const Op& op, const std::vector<Term>& children) const;

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (synth-fun <symbol> ( <boundVars>* ) <sort> <grammar>?)
   * \endverbatim
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param isInv Determines whether this is `synth-fun` or `synth-inv`.
   * @param grammar The syntactic constraints.
   * @return The function.
   */
  Term synthFunHelper(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      const Sort& sort,
                      bool isInv = false,
                      Grammar* grammar = nullptr) const;

  /** Check whether string s is a valid decimal integer. */
  bool isValidInteger(const std::string& s) const;

  /**
   * Check that the given term is a valid closed term, which can be used as an
   * argument to, e.g., assert, get-value, block-model-values, etc.
   *
   * @param t The term to check.
   */
  void ensureWellFormedTerm(const Term& t) const;
  /** Vector version of above. */
  void ensureWellFormedTerms(const std::vector<Term>& ts) const;

  /** Increment the term stats counter. */
  void increment_term_stats(Kind kind) const;
  /** Increment the vars stats (if 'is_var') or consts stats counter. */
  void increment_vars_consts_stats(const Sort& sort, bool is_var) const;

  /** Keep a copy of the original option settings (for resets). */
  std::unique_ptr<internal::Options> d_originalOptions;
  /** The node manager of this solver. */
  internal::NodeManager* d_nm;
  /** The statistics collected on the Api level. */
  std::unique_ptr<APIStatistics> d_stats;
  /** The SMT engine of this solver. */
  std::unique_ptr<internal::SolverEngine> d_slv;
  /** The random number generator of this solver. */
  std::unique_ptr<internal::Random> d_rng;
};

}  // namespace cvc5

#endif
