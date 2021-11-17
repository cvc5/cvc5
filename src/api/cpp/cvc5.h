/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C++ API.
 */

#include "cvc5_export.h"

#ifndef CVC5__API__CVC5_H
#define CVC5__API__CVC5_H

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

#include "api/cpp/cvc5_kind.h"

namespace cvc5 {

#ifndef DOXYGEN_SKIP
template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
#endif

class Command;
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
class StatisticsRegistry;

namespace main {
class CommandExecutor;
}

namespace api {

class Solver;
class Statistics;
struct APIStatistics;

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
class CVC5_EXPORT CVC5ApiUnsupportedException : public CVC5ApiRecoverableException
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
  enum UnknownExplanation
  {
    REQUIRES_FULL_CHECK,
    INCOMPLETE,
    TIMEOUT,
    RESOURCEOUT,
    MEMOUT,
    INTERRUPTED,
    NO_STATUS,
    UNSUPPORTED,
    OTHER,
    UNKNOWN_REASON
  };

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
  bool isSatUnknown() const;

  /**
   * Return true if corresponding query was an entailed checkEntailed() query.
   */
  bool isEntailed() const;

  /**
   * Return true if corresponding query was a checkEntailed() query that is
   * not entailed.
   */
  bool isNotEntailed() const;

  /**
   * Return true if query was a checkEntailed() query and cvc5 was not able to
   * determine if it is entailed.
   */
  bool isEntailmentUnknown() const;

  /**
   * Operator overloading for equality of two results.
   * @param r the result to compare to for equality
   * @return true if the results are equal
   */
  bool operator==(const Result& r) const;

  /**
   * Operator overloading for disequality of two results.
   * @param r the result to compare to for disequality
   * @return true if the results are disequal
   */
  bool operator!=(const Result& r) const;

  /**
   * @return an explanation for an unknown query result.
   */
  UnknownExplanation getUnknownExplanation() const;

  /**
   * @return a string representation of this result.
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param r the internal result that is to be wrapped by this result
   * @return the Result
   */
  Result(const cvc5::Result& r);

  /**
   * The interal result wrapped by this result.
   * Note: This is a shared_ptr rather than a unique_ptr since cvc5::Result is
   *       not ref counted.
   */
  std::shared_ptr<cvc5::Result> d_result;
};

/**
 * Serialize a Result to given stream.
 * @param out the output stream
 * @param r the result to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Result& r) CVC5_EXPORT;

/**
 * Serialize an UnknownExplanation to given stream.
 * @param out the output stream
 * @param e the explanation to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         enum Result::UnknownExplanation e) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

class Datatype;

/**
 * The sort of a cvc5 term.
 */
class CVC5_EXPORT Sort
{
  friend class cvc5::Command;
  friend class DatatypeConstructor;
  friend class DatatypeConstructorDecl;
  friend class DatatypeSelector;
  friend class DatatypeDecl;
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
   * @param s the sort to compare to
   * @return true if the sorts are equal
   */
  bool operator==(const Sort& s) const;

  /**
   * Comparison for structural disequality.
   * @param s the sort to compare to
   * @return true if the sorts are not equal
   */
  bool operator!=(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s the sort to compare to
   * @return true if this sort is less than s
   */
  bool operator<(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s the sort to compare to
   * @return true if this sort is greater than s
   */
  bool operator>(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s the sort to compare to
   * @return true if this sort is less than or equal to s
   */
  bool operator<=(const Sort& s) const;

  /**
   * Comparison for ordering on sorts.
   * @param s the sort to compare to
   * @return true if this sort is greater than or equal to s
   */
  bool operator>=(const Sort& s) const;

  /**
   * @return true if this Sort is a null sort.
   */
  bool isNull() const;

  /**
   * Is this a Boolean sort?
   * @return true if the sort is the Boolean sort
   */
  bool isBoolean() const;

  /**
   * Is this a integer sort?
   * @return true if the sort is the integer sort
   */
  bool isInteger() const;

  /**
   * Is this a real sort?
   * @return true if the sort is the real sort
   */
  bool isReal() const;

  /**
   * Is this a string sort?
   * @return true if the sort is the string sort
   */
  bool isString() const;

  /**
   * Is this a regexp sort?
   * @return true if the sort is the regexp sort
   */
  bool isRegExp() const;

  /**
   * Is this a rounding mode sort?
   * @return true if the sort is the rounding mode sort
   */
  bool isRoundingMode() const;

  /**
   * Is this a bit-vector sort?
   * @return true if the sort is a bit-vector sort
   */
  bool isBitVector() const;

  /**
   * Is this a floating-point sort?
   * @return true if the sort is a floating-point sort
   */
  bool isFloatingPoint() const;

  /**
   * Is this a datatype sort?
   * @return true if the sort is a datatype sort
   */
  bool isDatatype() const;

  /**
   * Is this a parametric datatype sort?
   * @return true if the sort is a parametric datatype sort
   */
  bool isParametricDatatype() const;

  /**
   * Is this a constructor sort?
   * @return true if the sort is a constructor sort
   */
  bool isConstructor() const;

  /**
   * Is this a selector sort?
   * @return true if the sort is a selector sort
   */
  bool isSelector() const;

  /**
   * Is this a tester sort?
   * @return true if the sort is a tester sort
   */
  bool isTester() const;
  /**
   * Is this a datatype updater sort?
   * @return true if the sort is a datatype updater sort
   */
  bool isUpdater() const;
  /**
   * Is this a function sort?
   * @return true if the sort is a function sort
   */
  bool isFunction() const;

  /**
   * Is this a predicate sort?
   * That is, is this a function sort mapping to Boolean? All predicate
   * sorts are also function sorts.
   * @return true if the sort is a predicate sort
   */
  bool isPredicate() const;

  /**
   * Is this a tuple sort?
   * @return true if the sort is a tuple sort
   */
  bool isTuple() const;

  /**
   * Is this a record sort?
   * @return true if the sort is a record sort
   */
  bool isRecord() const;

  /**
   * Is this an array sort?
   * @return true if the sort is an array sort
   */
  bool isArray() const;

  /**
   * Is this a Set sort?
   * @return true if the sort is a Set sort
   */
  bool isSet() const;

  /**
   * Is this a Bag sort?
   * @return true if the sort is a Bag sort
   */
  bool isBag() const;

  /**
   * Is this a Sequence sort?
   * @return true if the sort is a Sequence sort
   */
  bool isSequence() const;

  /**
   * Is this an uninterpreted sort?
   * @return true if this is an uninterpreted sort
   */
  bool isUninterpretedSort() const;

  /**
   * Is this a sort constructor kind?
   * @return true if this is a sort constructor kind
   */
  bool isSortConstructor() const;

  /**
   * Is this a first-class sort?
   * First-class sorts are sorts for which:
   * 1. we handle equalities between terms of that type, and
   * 2. they are allowed to be parameters of parametric sorts (e.g. index or
   * element sorts of arrays).
   *
   * Examples of sorts that are not first-class include sort constructor sorts
   * and regular expression sorts.
   *
   * @return true if this is a first-class sort
   */
  bool isFirstClass() const;

  /**
   * Is this a function-LIKE sort?
   *
   * Anything function-like except arrays (e.g., datatype selectors) is
   * considered a function here. Function-like terms can not be the argument
   * or return value for any term that is function-like.
   * This is mainly to avoid higher order.
   *
   * Note that arrays are explicitly not considered function-like here.
   *
   * @return true if this is a function-like sort
   */
  bool isFunctionLike() const;

  /**
   * Is this sort a subsort of the given sort?
   * @return true if this sort is a subsort of s
   */
  bool isSubsortOf(const Sort& s) const;

  /**
   * Is this sort comparable to the given sort (i.e., do they share
   * a common ancestor in the subsort tree)?
   * @return true if this sort is comparable to s
   */
  bool isComparableTo(const Sort& s) const;

  /**
   * @return the underlying datatype of a datatype sort
   */
  Datatype getDatatype() const;

  /**
   * Instantiate a parameterized datatype/sort sort.
   * Create sorts parameter with Solver::mkParamSort().
   * @param params the list of sort parameters to instantiate with
   */
  Sort instantiate(const std::vector<Sort>& params) const;

  /**
   * Substitution of Sorts.
   * @param sort the subsort to be substituted within this sort.
   * @param replacement the sort replacing the substituted subsort.
   */
  Sort substitute(const Sort& sort, const Sort& replacement) const;

  /**
   * Simultaneous substitution of Sorts.
   * @param sorts the subsorts to be substituted within this sort.
   * @param replacements the sort replacing the substituted subsorts.
   */
  Sort substitute(const std::vector<Sort>& sorts,
                  const std::vector<Sort>& replacements) const;

  /**
   * Output a string representation of this sort to a given stream.
   * @param out the output stream
   */
  void toStream(std::ostream& out) const;

  /**
   * @return a string representation of this sort
   */
  std::string toString() const;

  /* Constructor sort ------------------------------------------------------- */

  /**
   * @return the arity of a constructor sort
   */
  size_t getConstructorArity() const;

  /**
   * @return the domain sorts of a constructor sort
   */
  std::vector<Sort> getConstructorDomainSorts() const;

  /**
   * @return the codomain sort of a constructor sort
   */
  Sort getConstructorCodomainSort() const;

  /* Selector sort ------------------------------------------------------- */

  /**
   * @return the domain sort of a selector sort
   */
  Sort getSelectorDomainSort() const;

  /**
   * @return the codomain sort of a selector sort
   */
  Sort getSelectorCodomainSort() const;

  /* Tester sort ------------------------------------------------------- */

  /**
   * @return the domain sort of a tester sort
   */
  Sort getTesterDomainSort() const;

  /**
   * @return the codomain sort of a tester sort, which is the Boolean sort
   */
  Sort getTesterCodomainSort() const;

  /* Function sort ------------------------------------------------------- */

  /**
   * @return the arity of a function sort
   */
  size_t getFunctionArity() const;

  /**
   * @return the domain sorts of a function sort
   */
  std::vector<Sort> getFunctionDomainSorts() const;

  /**
   * @return the codomain sort of a function sort
   */
  Sort getFunctionCodomainSort() const;

  /* Array sort ---------------------------------------------------------- */

  /**
   * @return the array index sort of an array sort
   */
  Sort getArrayIndexSort() const;

  /**
   * @return the array element sort of an array sort
   */
  Sort getArrayElementSort() const;

  /* Set sort ------------------------------------------------------------ */

  /**
   * @return the element sort of a set sort
   */
  Sort getSetElementSort() const;

  /* Bag sort ------------------------------------------------------------ */

  /**
   * @return the element sort of a bag sort
   */
  Sort getBagElementSort() const;

  /* Sequence sort ------------------------------------------------------- */

  /**
   * @return the element sort of a sequence sort
   */
  Sort getSequenceElementSort() const;

  /* Uninterpreted sort -------------------------------------------------- */

  /**
   * @return the name of an uninterpreted sort
   */
  std::string getUninterpretedSortName() const;

  /**
   * @return true if an uninterpreted sort is parameterized
   */
  bool isUninterpretedSortParameterized() const;

  /**
   * @return the parameter sorts of an uninterpreted sort
   */
  std::vector<Sort> getUninterpretedSortParamSorts() const;

  /* Sort constructor sort ----------------------------------------------- */

  /**
   * @return the name of a sort constructor sort
   */
  std::string getSortConstructorName() const;

  /**
   * @return the arity of a sort constructor sort
   */
  size_t getSortConstructorArity() const;

  /* Bit-vector sort ----------------------------------------------------- */

  /**
   * @return the bit-width of the bit-vector sort
   */
  uint32_t getBitVectorSize() const;

  /* Floating-point sort ------------------------------------------------- */

  /**
   * @return the bit-width of the exponent of the floating-point sort
   */
  uint32_t getFloatingPointExponentSize() const;

  /**
   * @return the width of the significand of the floating-point sort
   */
  uint32_t getFloatingPointSignificandSize() const;

  /* Datatype sort ------------------------------------------------------- */

  /**
   * @return the parameter sorts of a datatype sort
   */
  std::vector<Sort> getDatatypeParamSorts() const;

  /**
   * @return the arity of a datatype sort
   */
  size_t getDatatypeArity() const;

  /* Tuple sort ---------------------------------------------------------- */

  /**
   * @return the length of a tuple sort
   */
  size_t getTupleLength() const;

  /**
   * @return the element sorts of a tuple sort
   */
  std::vector<Sort> getTupleSorts() const;

 private:
  /** @return the internal wrapped TypeNode of this sort. */
  const cvc5::TypeNode& getTypeNode(void) const;

  /** Helper to convert a set of Sorts to internal TypeNodes. */
  std::set<TypeNode> static sortSetToTypeNodes(const std::set<Sort>& sorts);
  /** Helper to convert a vector of Sorts to internal TypeNodes. */
  std::vector<TypeNode> static sortVectorToTypeNodes(
      const std::vector<Sort>& sorts);
  /** Helper to convert a vector of internal TypeNodes to Sorts. */
  std::vector<Sort> static typeNodeVectorToSorts(
      const Solver* slv, const std::vector<TypeNode>& types);

  /**
   * Constructor.
   * @param slv the associated solver object
   * @param t the internal type that is to be wrapped by this sort
   * @return the Sort
   */
  Sort(const Solver* slv, const cvc5::TypeNode& t);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal type wrapped by this sort.
   * Note: This is a shared_ptr rather than a unique_ptr to avoid overhead due
   *       to memory allocation (cvc5::Type is already ref counted, so this
   *       could be a unique_ptr instead).
   */
  std::shared_ptr<cvc5::TypeNode> d_type;
};

/**
 * Serialize a sort to given stream.
 * @param out the output stream
 * @param s the sort to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Sort& s) CVC5_EXPORT;

}  // namespace api
}  // namespace cvc5

namespace std {

/**
 * Hash function for Sorts.
 */
template <>
struct CVC5_EXPORT hash<cvc5::api::Sort>
{
  size_t operator()(const cvc5::api::Sort& s) const;
};

}  // namespace std

namespace cvc5::api {

/* -------------------------------------------------------------------------- */
/* Op                                                                     */
/* -------------------------------------------------------------------------- */

class Term;

/**
 * A cvc5 operator.
 * An operator is a term that represents certain operators, instantiated
 * with its required parameters, e.g., a term of kind BITVECTOR_EXTRACT.
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
   * Return true if both operators are syntactically identical.
   * Both operators must belong to the same solver object.
   * @param t the operator to compare to for equality
   * @return true if the operators are equal
   */
  bool operator==(const Op& t) const;

  /**
   * Syntactic disequality operator.
   * Return true if both operators differ syntactically.
   * Both terms must belong to the same solver object.
   * @param t the operator to compare to for disequality
   * @return true if operators are disequal
   */
  bool operator!=(const Op& t) const;

  /**
   * @return the kind of this operator
   */
  Kind getKind() const;

  /**
   * @return true if this operator is a null term
   */
  bool isNull() const;

  /**
   * @return true iff this operator is indexed
   */
  bool isIndexed() const;

  /**
   * @return the number of indices of this op
   */
  size_t getNumIndices() const;

  /**
   * Get the index at position i.
   * @param i the position of the index to return
   * @return the index at position i
   */

  Term operator[](size_t i) const;

  /**
   * Get the indices used to create this Op.
   * Supports the following template arguments:
   *   - string
   *   - Kind
   *   - uint32_t
   *   - pair<uint32_t, uint32_t>
   * Check the Op Kind with getKind() to determine which argument to use.
   * @return the indices used to create this Op
   */
  template <typename T>
  T getIndices() const;

  /**
   * @return a string representation of this operator
   */
  std::string toString() const;

 private:
  /**
   * Constructor for a single kind (non-indexed operator).
   * @param slv the associated solver object
   * @param k the kind of this Op
   */
  Op(const Solver* slv, const Kind k);

  /**
   * Constructor.
   * @param slv the associated solver object
   * @param k the kind of this Op
   * @param n the internal node that is to be wrapped by this term
   * @return the Term
   */
  Op(const Solver* slv, const Kind k, const cvc5::Node& n);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * Note: An indexed operator has a non-null internal node, d_node
   * Note 2: We use a helper method to avoid having API functions call
   *         other API functions (we need to call this internally)
   * @return true iff this Op is indexed
   */
  bool isIndexedHelper() const;

  /**
   * Helper for getNumIndices
   * @return the number of indices of this op
   */
  size_t getNumIndicesHelper() const;

  /**
   * Helper for operator[](size_t index).
   * @param index position of the index. Should be less than getNumIndicesHelper().
   * @return the index at position index
   */
  Term getIndexHelper(size_t index) const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /** The kind of this operator. */
  Kind d_kind;

  /**
   * The internal node wrapped by this operator.
   * Note: This is a shared_ptr rather than a unique_ptr to avoid overhead due
   *       to memory allocation (cvc5::Node is already ref counted, so this
   *       could be a unique_ptr instead).
   */
  std::shared_ptr<cvc5::Node> d_node;
};

/**
 * Serialize an operator to given stream.
 * @param out the output stream
 * @param t the operator to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Op& t) CVC5_EXPORT;

}  // namespace cvc5::api

namespace std {
/**
 * Hash function for Ops.
 */
template <>
struct CVC5_EXPORT hash<cvc5::api::Op>
{
  size_t operator()(const cvc5::api::Op& t) const;
};
}  // namespace std

namespace cvc5::api {
/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

/**
 * A cvc5 Term.
 */
class CVC5_EXPORT Term
{
  friend class cvc5::Command;
  friend class Datatype;
  friend class DatatypeConstructor;
  friend class DatatypeSelector;
  friend class Solver;
  friend class Grammar;
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
   * Both terms must belong to the same solver object.
   * @param t the term to compare to for equality
   * @return true if the terms are equal
   */
  bool operator==(const Term& t) const;

  /**
   * Syntactic disequality operator.
   * Return true if both terms differ syntactically.
   * Both terms must belong to the same solver object.
   * @param t the term to compare to for disequality
   * @return true if terms are disequal
   */
  bool operator!=(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t the term to compare to
   * @return true if this term is less than t
   */
  bool operator<(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t the term to compare to
   * @return true if this term is greater than t
   */
  bool operator>(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t the term to compare to
   * @return true if this term is less than or equal to t
   */
  bool operator<=(const Term& t) const;

  /**
   * Comparison for ordering on terms by their id.
   * @param t the term to compare to
   * @return true if this term is greater than or equal to t
   */
  bool operator>=(const Term& t) const;

  /** @return the number of children of this term  */
  size_t getNumChildren() const;

  /**
   * Get the child term at a given index.
   * @param index the index of the child term to return
   * @return the child term with the given index
   */
  Term operator[](size_t index) const;

  /**
   * @return the id of this term
   */
  uint64_t getId() const;

  /**
   * @return the kind of this term
   */
  Kind getKind() const;

  /**
   * @return the sort of this term
   */
  Sort getSort() const;

  /**
   * @return the result of replacing 'term' by 'replacement' in this term
   */
  Term substitute(const Term& term, const Term& replacement) const;

  /**
   * @return the result of simultaneously replacing 'terms' by 'replacements'
   * in this term
   */
  Term substitute(const std::vector<Term>& terms,
                  const std::vector<Term>& replacements) const;

  /**
   * @return true iff this term has an operator
   */
  bool hasOp() const;

  /**
   * @return the Op used to create this term
   * Note: This is safe to call when hasOp() returns true.
   */
  Op getOp() const;

  /**
   * @return true if the term has a symbol.
   */
  bool hasSymbol() const;

  /**
   * Asserts hasSymbol().
   * @return the raw symbol of the term.
   */
  std::string getSymbol() const;

  /**
   * @return true if this Term is a null term
   */
  bool isNull() const;

  /**
   * Boolean negation.
   * @return the Boolean negation of this term
   */
  Term notTerm() const;

  /**
   * Boolean and.
   * @param t a Boolean term
   * @return the conjunction of this term and the given term
   */
  Term andTerm(const Term& t) const;

  /**
   * Boolean or.
   * @param t a Boolean term
   * @return the disjunction of this term and the given term
   */
  Term orTerm(const Term& t) const;

  /**
   * Boolean exclusive or.
   * @param t a Boolean term
   * @return the exclusive disjunction of this term and the given term
   */
  Term xorTerm(const Term& t) const;

  /**
   * Equality.
   * @param t a Boolean term
   * @return the Boolean equivalence of this term and the given term
   */
  Term eqTerm(const Term& t) const;

  /**
   * Boolean implication.
   * @param t a Boolean term
   * @return the implication of this term and the given term
   */
  Term impTerm(const Term& t) const;

  /**
   * If-then-else with this term as the Boolean condition.
   * @param then_t the 'then' term
   * @param else_t the 'else' term
   * @return the if-then-else term with this term as the Boolean condition
   */
  Term iteTerm(const Term& then_t, const Term& else_t) const;

  /**
   * @return a string representation of this term
   */
  std::string toString() const;

  /**
   * Iterator for the children of a Term.
   * Note: This treats uninterpreted functions as Term just like any other term
   *       for example, the term f(x, y) will have Kind APPLY_UF and three
   *       children: f, x, and y
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
     * @param slv the associated solver object
     * @param e a shared pointer to the node that we're iterating over
     * @param p the position of the iterator (e.g. which child it's on)
     */
    const_iterator(const Solver* slv,
                   const std::shared_ptr<cvc5::Node>& e,
                   uint32_t p);

    /**
     * Copy constructor.
     */
    const_iterator(const const_iterator& it);

    /**
     * Assignment operator.
     * @param it the iterator to assign to
     * @return the reference to the iterator after assignment
     */
    const_iterator& operator=(const const_iterator& it);

    /**
     * Equality operator.
     * @param it the iterator to compare to for equality
     * @return true if the iterators are equal
     */
    bool operator==(const const_iterator& it) const;

    /**
     * Disequality operator.
     * @param it the iterator to compare to for disequality
     * @return true if the iterators are disequal
     */
    bool operator!=(const const_iterator& it) const;

    /**
     * Increment operator (prefix).
     * @return a reference to the iterator after incrementing by one
     */
    const_iterator& operator++();

    /**
     * Increment operator (postfix).
     * @return a reference to the iterator after incrementing by one
     */
    const_iterator operator++(int);

    /**
     * Dereference operator.
     * @return the term this iterator points to
     */
    Term operator*() const;

   private:
    /**
     * The associated solver object.
     */
    const Solver* d_solver;
    /** The original node to be iterated over. */
    std::shared_ptr<cvc5::Node> d_origNode;
    /** Keeps track of the iteration position. */
    uint32_t d_pos;
  };

  /**
   * @return an iterator to the first child of this Term
   */
  const_iterator begin() const;

  /**
   * @return an iterator to one-off-the-last child of this Term
   */
  const_iterator end() const;

  /**
   * @return true if the term is an integer value that fits within int32_t.
   */
  bool isInt32Value() const;
  /**
   * Asserts isInt32Value().
   * @return the integer term as a int32_t.
   */
  int32_t getInt32Value() const;
  /**
   * @return true if the term is an integer value that fits within uint32_t.
   */
  bool isUInt32Value() const;
  /**
   * Asserts isUInt32Value().
   * @return the integer term as a uint32_t.
   */
  uint32_t getUInt32Value() const;
  /**
   * @return true if the term is an integer value that fits within int64_t.
   */
  bool isInt64Value() const;
  /**
   * Asserts isInt64Value().
   * @return the integer term as a int64_t.
   */
  int64_t getInt64Value() const;
  /**
   * @return true if the term is an integer value that fits within uint64_t.
   */
  bool isUInt64Value() const;
  /**
   * Asserts isUInt64Value().
   * @return the integer term as a uint64_t.
   */
  uint64_t getUInt64Value() const;
  /**
   * @return true if the term is an integer value.
   */
  bool isIntegerValue() const;
  /**
   * Asserts isIntegerValue().
   * @return the integer term in (decimal) string representation.
   */
  std::string getIntegerValue() const;

  /**
   * @return true if the term is a string value.
   */
  bool isStringValue() const;
  /**
   * Note: This method is not to be confused with toString() which returns
   * the term in some string representation, whatever data it may hold. Asserts
   * isStringValue().
   * @return the string term as a native string value.
   */
  std::wstring getStringValue() const;

  /**
   * @return true if the term is a rational value whose numerator and
   * denominator fit within int32_t and uint32_t, respectively.
   */
  bool isReal32Value() const;
  /**
   * Asserts isReal32Value().
   * @return the representation of a rational value as a pair of its numerator
   * and denominator.
   */
  std::pair<int32_t, uint32_t> getReal32Value() const;
  /**
   * @return true if the term is a rational value whose numerator and
   * denominator fit within int64_t and uint64_t, respectively.
   */
  bool isReal64Value() const;
  /**
   * Asserts isReal64Value().
   * @return the representation of a rational value as a pair of its numerator
   * and denominator.
   */
  std::pair<int64_t, uint64_t> getReal64Value() const;
  /**
   * @return true if the term is a rational value.
   *
   * Note that a term of kind PI is not considered to be a real value.
   */
  bool isRealValue() const;
  /**
   * Asserts isRealValue().
   * @return the representation of a rational value as a (rational) string.
   */
  std::string getRealValue() const;

  /**
   * @return true if the term is a constant array.
   */
  bool isConstArray() const;
  /**
   * Asserts isConstArray().
   * @return the base (element stored at all indices) of a constant array
   */
  Term getConstArrayBase() const;

  /**
   * @return true if the term is a Boolean value.
   */
  bool isBooleanValue() const;
  /**
   * Asserts isBooleanValue().
   * @return the representation of a Boolean value as a native Boolean value.
   */
  bool getBooleanValue() const;

  /**
   * @return true if the term is a bit-vector value.
   */
  bool isBitVectorValue() const;
  /**
   * Asserts isBitVectorValue().
   * @return the representation of a bit-vector value in string representation.
   * Supported bases are 2 (bit string), 10 (decimal string) or 16 (hexadecimal
   * string).
   */
  std::string getBitVectorValue(uint32_t base = 2) const;

  /**
   * @return true if the term is an abstract value.
   */
  bool isAbstractValue() const;
  /**
   * Asserts isAbstractValue().
   * @return the representation of an abstract value as a string.
   */
  std::string getAbstractValue() const;

  /**
   * @return true if the term is a tuple value.
   */
  bool isTupleValue() const;
  /**
   * Asserts isTupleValue().
   * @return the representation of a tuple value as a vector of terms.
   */
  std::vector<Term> getTupleValue() const;

  /**
   * @return true if the term is the floating-point value for positive zero.
   */
  bool isFloatingPointPosZero() const;
  /**
   * @return true if the term is the floating-point value for negative zero.
   */
  bool isFloatingPointNegZero() const;
  /**
   * @return true if the term is the floating-point value for positive
   * infinity.
   */
  bool isFloatingPointPosInf() const;
  /**
   * @return true if the term is the floating-point value for negative
   * infinity.
   */
  bool isFloatingPointNegInf() const;
  /**
   * @return true if the term is the floating-point value for not a number.
   */
  bool isFloatingPointNaN() const;
  /**
   * @return true if the term is a floating-point value.
   */
  bool isFloatingPointValue() const;
  /**
   * Asserts isFloatingPointValue().
   * @return the representation of a floating-point value as a tuple of the
   * exponent width, the significand width and a bit-vector value.
   */
  std::tuple<uint32_t, uint32_t, Term> getFloatingPointValue() const;

  /**
   * @return true if the term is a set value.
   *
   * A term is a set value if it is considered to be a (canonical) constant set
   * value.  A canonical set value is one whose AST is:
   * ```
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * ```
   * where `c1 ... cn` are values ordered by id such that `c1 > ... > cn` (see
   * also @ref Term::operator>(const Term&) const).
   *
   * Note that a universe set term (kind SET_UNIVERSE) is not considered to be
   * a set value.
   */
  bool isSetValue() const;
  /**
   * Asserts isSetValue().
   * @return the representation of a set value as a set of terms.
   */
  std::set<Term> getSetValue() const;

  /**
   * @return true if the term is a sequence value.
   */
  bool isSequenceValue() const;
  /**
   * Asserts isSequenceValue().
   * Note that it is usually necessary for sequences to call
   * `Solver::simplify()` to turn a sequence that is constructed by, e.g.,
   * concatenation of unit sequences, into a sequence value.
   * @return the representation of a sequence value as a vector of terms.
   */
  std::vector<Term> getSequenceValue() const;

  /**
   * @return true if the term is a value from an uninterpreted sort.
   */
  bool isUninterpretedValue() const;
  /**
  bool @return() const;
   * Asserts isUninterpretedValue().
   * @return the representation of an uninterpreted value as a pair of its
  sort and its
   * index.
   */
  std::pair<Sort, int32_t> getUninterpretedValue() const;

 protected:
  /**
   * The associated solver object.
   */
  const Solver* d_solver;

 private:
  /** Helper to convert a vector of Terms to internal Nodes. */
  std::vector<Node> static termVectorToNodes(const std::vector<Term>& terms);

  /** Helper method to collect all elements of a set. */
  static void collectSet(std::set<Term>& set,
                         const cvc5::Node& node,
                         const Solver* slv);
  /** Helper method to collect all elements of a sequence. */
  static void collectSequence(std::vector<Term>& seq,
                              const cvc5::Node& node,
                              const Solver* slv);

  /**
   * Constructor.
   * @param slv the associated solver object
   * @param n the internal node that is to be wrapped by this term
   * @return the Term
   */
  Term(const Solver* slv, const cvc5::Node& n);

  /** @return the internal wrapped Node of this term. */
  const cvc5::Node& getNode(void) const;

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * Helper function that returns the kind of the term, which takes into
   * account special cases of the conversion for internal to external kinds.
   * @return the kind of this term
   */
  Kind getKindHelper() const;

  /**
   * @return true if the current term is a constant integer that is casted into
   * real using the operator CAST_TO_REAL, and returns false otherwise
   */
  bool isCastedReal() const;
  /**
   * The internal node wrapped by this term.
   * Note: This is a shared_ptr rather than a unique_ptr to avoid overhead due
   *       to memory allocation (cvc5::Node is already ref counted, so this
   *       could be a unique_ptr instead).
   */
  std::shared_ptr<cvc5::Node> d_node;
};

/**
 * Serialize a term to given stream.
 * @param out the output stream
 * @param t the term to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Term& t) CVC5_EXPORT;

/**
 * Serialize a vector of terms to given stream.
 * @param out the output stream
 * @param vector the vector of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::vector<Term>& vector) CVC5_EXPORT;

/**
 * Serialize a set of terms to the given stream.
 * @param out the output stream
 * @param set the set of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::set<Term>& set) CVC5_EXPORT;

/**
 * Serialize an unordered_set of terms to the given stream.
 *
 * @param out the output stream
 * @param unordered_set the set of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_set<Term>& unordered_set)
    CVC5_EXPORT;

/**
 * Serialize a map of terms to the given stream.
 *
 * @param out the output stream
 * @param map the map of terms to be serialized to the given stream
 * @return the output stream
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::map<Term, V>& map) CVC5_EXPORT;

/**
 * Serialize an unordered_map of terms to the given stream.
 *
 * @param out the output stream
 * @param unordered_map the map of terms to be serialized to the given stream
 * @return the output stream
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_map<Term, V>& unordered_map)
    CVC5_EXPORT;

}  // namespace cvc5::api

namespace std {
/**
 * Hash function for Terms.
 */
template <>
struct CVC5_EXPORT hash<cvc5::api::Term>
{
  size_t operator()(const cvc5::api::Term& t) const;
};
}  // namespace std

namespace cvc5::api {

/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

class DatatypeConstructorIterator;
class DatatypeIterator;

/**
 * A cvc5 datatype constructor declaration.
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
   * @param name the name of the datatype selector declaration to add
   * @param sort the range sort of the datatype selector declaration to add
   */
  void addSelector(const std::string& name, const Sort& sort);
  /**
   * Add datatype selector declaration whose range type is the datatype itself.
   * @param name the name of the datatype selector declaration to add
   */
  void addSelectorSelf(const std::string& name);

  /**
   * @return true if this DatatypeConstructorDecl is a null declaration.
   */
  bool isNull() const;

  /**
   * @return a string representation of this datatype constructor declaration
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param name the name of the datatype constructor
   * @return the DatatypeConstructorDecl
   */
  DatatypeConstructorDecl(const Solver* slv, const std::string& name);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal (intermediate) datatype constructor wrapped by this
   * datatype constructor declaration.
   * Note: This is a shared_ptr rather than a unique_ptr since
   *       cvc5::DTypeConstructor is not ref counted.
   */
  std::shared_ptr<cvc5::DTypeConstructor> d_ctor;
};

class Solver;

/**
 * A cvc5 datatype declaration.
 */
class CVC5_EXPORT DatatypeDecl
{
  friend class DatatypeConstructorArg;
  friend class Solver;
  friend class Grammar;

 public:
  /** Constructor.  */
  DatatypeDecl();

  /**
   * Destructor.
   */
  ~DatatypeDecl();

  /**
   * Add datatype constructor declaration.
   * @param ctor the datatype constructor declaration to add
   */
  void addConstructor(const DatatypeConstructorDecl& ctor);

  /** Get the number of constructors (so far) for this Datatype declaration. */
  size_t getNumConstructors() const;

  /** Is this Datatype declaration parametric? */
  bool isParametric() const;

  /**
   * @return true if this DatatypeDecl is a null object
   */
  bool isNull() const;

  /**
   * @return a string representation of this datatype declaration
   */
  std::string toString() const;

  /** @return the name of this datatype declaration. */
  std::string getName() const;

 private:
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param name the name of the datatype
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl(const Solver* slv,
               const std::string& name,
               bool isCoDatatype = false);

  /**
   * Constructor for parameterized datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param slv the associated solver object
   * @param name the name of the datatype
   * @param param the sort parameter
   * @param isCoDatatype true if a codatatype is to be constructed
   */
  DatatypeDecl(const Solver* slv,
               const std::string& name,
               const Sort& param,
               bool isCoDatatype = false);

  /**
   * Constructor for parameterized datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param slv the associated solver object
   * @param name the name of the datatype
   * @param params a list of sort parameters
   * @param isCoDatatype true if a codatatype is to be constructed
   */
  DatatypeDecl(const Solver* slv,
               const std::string& name,
               const std::vector<Sort>& params,
               bool isCoDatatype = false);

  /** @return the internal wrapped Dtype of this datatype declaration. */
  cvc5::DType& getDatatype(void) const;

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal (intermediate) datatype wrapped by this datatype
   * declaration.
   * Note: This is a shared_ptr rather than a unique_ptr since cvc5::DType is
   *       not ref counted.
   */
  std::shared_ptr<cvc5::DType> d_dtype;
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

  /** @return the name of this Datatype selector. */
  std::string getName() const;

  /**
   * Get the selector operator of this datatype selector.
   * @return the selector term
   */
  Term getSelectorTerm() const;

  /**
   * Get the updater operator of this datatype selector.
   * @return the updater term
   */
  Term getUpdaterTerm() const;

  /** @return the range sort of this selector. */
  Sort getRangeSort() const;

  /**
   * @return true if this DatatypeSelector is a null object
   */
  bool isNull() const;

  /**
   * @return a string representation of this datatype selector
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param stor the internal datatype selector to be wrapped
   * @return the DatatypeSelector
   */
  DatatypeSelector(const Solver* slv, const cvc5::DTypeSelector& stor);

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal datatype selector wrapped by this datatype selector.
   * Note: This is a shared_ptr rather than a unique_ptr since cvc5::DType is
   *       not ref counted.
   */
  std::shared_ptr<cvc5::DTypeSelector> d_stor;
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

  /** @return the name of this Datatype constructor. */
  std::string getName() const;

  /**
   * Get the constructor operator of this datatype constructor.
   * @return the constructor term
   */
  Term getConstructorTerm() const;

  /**
   * Get the constructor operator of this datatype constructor whose return
   * type is retSort. This method is intended to be used on constructors of
   * parametric datatypes and can be seen as returning the constructor
   * term that has been explicitly cast to the given sort.
   *
   * This method is required for constructors of parametric datatypes whose
   * return type cannot be determined by type inference. For example, given:
   *   (declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))
   * The type of nil terms need to be provided by the user. In SMT version 2.6,
   * this is done via the syntax for qualified identifiers:
   *   (as nil (List Int))
   * This method is equivalent of applying the above, where this
   * DatatypeConstructor is the one corresponding to nil, and retSort is
   * (List Int).
   *
   * Furthermore note that the returned constructor term t is an operator,
   * while Solver::mkTerm(APPLY_CONSTRUCTOR, t) is used to construct the above
   * (nullary) application of nil.
   *
   * @param retSort the desired return sort of the constructor
   * @return the constructor term
   */
  Term getSpecializedConstructorTerm(const Sort& retSort) const;

  /**
   * Get the tester operator of this datatype constructor.
   * @return the tester operator
   */
  Term getTesterTerm() const;

  /**
   * @return the number of selectors (so far) of this Datatype constructor.
   */
  size_t getNumSelectors() const;

  /** @return the i^th DatatypeSelector. */
  DatatypeSelector operator[](size_t index) const;
  /**
   * Get the datatype selector with the given name.
   * This is a linear search through the selectors, so in case of
   * multiple, similarly-named selectors, the first is returned.
   * @param name the name of the datatype selector
   * @return the first datatype selector with the given name
   */
  DatatypeSelector operator[](const std::string& name) const;
  DatatypeSelector getSelector(const std::string& name) const;

  /**
   * Get the term representation of the datatype selector with the given name.
   * This is a linear search through the arguments, so in case of multiple,
   * similarly-named arguments, the selector for the first is returned.
   * @param name the name of the datatype selector
   * @return a term representing the datatype selector with the given name
   */
  Term getSelectorTerm(const std::string& name) const;

  /**
   * @return true if this DatatypeConstructor is a null object
   */
  bool isNull() const;

  /**
   * @return a string representation of this datatype constructor
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
     * @param it the iterator to assign to
     * @return the reference to the iterator after assignment
     */
    const_iterator& operator=(const const_iterator& it);

    /**
     * Equality operator.
     * @param it the iterator to compare to for equality
     * @return true if the iterators are equal
     */
    bool operator==(const const_iterator& it) const;

    /**
     * Disequality operator.
     * @param it the iterator to compare to for disequality
     * @return true if the iterators are disequal
     */
    bool operator!=(const const_iterator& it) const;

    /**
     * Increment operator (prefix).
     * @return a reference to the iterator after incrementing by one
     */
    const_iterator& operator++();

    /**
     * Increment operator (postfix).
     * @return a reference to the iterator after incrementing by one
     */
    const_iterator operator++(int);

    /**
     * Dereference operator.
     * @return a reference to the selector this iterator points to
     */
    const DatatypeSelector& operator*() const;

    /**
     * Dereference operator.
     * @return a pointer to the selector this iterator points to
     */
    const DatatypeSelector* operator->() const;

   private:
    /**
     * Constructor.
     * @param slv the associated Solver object
     * @param ctor the internal datatype constructor to iterate over
     * @param begin true if this is a begin() iterator
     */
    const_iterator(const Solver* slv,
                   const cvc5::DTypeConstructor& ctor,
                   bool begin);

    /**
     * The associated solver object.
     */
    const Solver* d_solver;

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
   * @return an iterator to the first selector of this constructor
   */
  const_iterator begin() const;

  /**
   * @return an iterator to one-off-the-last selector of this constructor
   */
  const_iterator end() const;

 private:
  /**
   * Constructor.
   * @param slv the associated solver instance
   * @param ctor the internal datatype constructor to be wrapped
   * @return the DatatypeConstructor
   */
  DatatypeConstructor(const Solver* slv, const cvc5::DTypeConstructor& ctor);

  /**
   * Return selector for name.
   * @param name The name of selector to find
   * @return the selector object for the name
   */
  DatatypeSelector getSelectorForName(const std::string& name) const;

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal datatype constructor wrapped by this datatype constructor.
   * Note: This is a shared_ptr rather than a unique_ptr since cvc5::DType is
   *       not ref counted.
   */
  std::shared_ptr<cvc5::DTypeConstructor> d_ctor;
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
   * @param idx the index of the datatype constructor to return
   * @return the datatype constructor with the given index
   */
  DatatypeConstructor operator[](size_t idx) const;

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors, so in case of multiple,
   * similarly-named constructors, the first is returned.
   * @param name the name of the datatype constructor
   * @return the datatype constructor with the given name
   */
  DatatypeConstructor operator[](const std::string& name) const;
  DatatypeConstructor getConstructor(const std::string& name) const;

  /**
   * Get a term representing the datatype constructor with the given name.
   * This is a linear search through the constructors, so in case of multiple,
   * similarly-named constructors, the
   * first is returned.
   */
  Term getConstructorTerm(const std::string& name) const;

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors and their selectors, so
   * in case of multiple, similarly-named selectors, the first is returned.
   * @param name the name of the datatype selector
   * @return the datatype selector with the given name
   */
  DatatypeSelector getSelector(const std::string& name) const;

  /** @return the name of this Datatype. */
  std::string getName() const;

  /** @return the number of constructors for this Datatype. */
  size_t getNumConstructors() const;

  /** @return true if this datatype is parametric */
  bool isParametric() const;

  /** @return true if this datatype corresponds to a co-datatype */
  bool isCodatatype() const;

  /** @return true if this datatype corresponds to a tuple */
  bool isTuple() const;

  /** @return true if this datatype corresponds to a record */
  bool isRecord() const;

  /** @return true if this datatype is finite */
  bool isFinite() const;

  /**
   * Is this datatype well-founded? If this datatype is not a codatatype,
   * this returns false if there are no values of this datatype that are of
   * finite size.
   *
   * @return true if this datatype is well-founded
   */
  bool isWellFounded() const;

  /**
   * Does this datatype have nested recursion? This method returns false if a
   * value of this datatype includes a subterm of its type that is nested
   * beneath a non-datatype type constructor. For example, a datatype
   * T containing a constructor having a selector with range type (Set T) has
   * nested recursion.
   *
   * @return true if this datatype has nested recursion
   */
  bool hasNestedRecursion() const;

  /**
   * @return true if this Datatype is a null object
   */
  bool isNull() const;

  /**
   * @return a string representation of this datatype
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
     * @param it the iterator to assign to
     * @return the reference to the iterator after assignment
     */
    const_iterator& operator=(const const_iterator& it);

    /**
     * Equality operator.
     * @param it the iterator to compare to for equality
     * @return true if the iterators are equal
     */
    bool operator==(const const_iterator& it) const;

    /**
     * Disequality operator.
     * @param it the iterator to compare to for disequality
     * @return true if the iterators are disequal
     */
    bool operator!=(const const_iterator& it) const;

    /**
     * Increment operator (prefix).
     * @return a reference to the iterator after incrementing by one
     */
    const_iterator& operator++();

    /**
     * Increment operator (postfix).
     * @return a reference to the iterator after incrementing by one
     */
    const_iterator operator++(int);

    /**
     * Dereference operator.
     * @return a reference to the constructor this iterator points to
     */
    const DatatypeConstructor& operator*() const;

    /**
     * Dereference operator.
     * @return a pointer to the constructor this iterator points to
     */
    const DatatypeConstructor* operator->() const;

   private:
    /**
     * Constructor.
     * @param slv the associated Solver object
     * @param dtype the internal datatype to iterate over
     * @param begin true if this is a begin() iterator
     */
    const_iterator(const Solver* slv, const cvc5::DType& dtype, bool begin);

    /**
     * The associated solver object.
     */
    const Solver* d_solver;

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
   * @return an iterator to the first constructor of this datatype
   */
  const_iterator begin() const;

  /**
   * @return an iterator to one-off-the-last constructor of this datatype
   */
  const_iterator end() const;

 private:
  /**
   * Constructor.
   * @param slv the associated solver instance
   * @param dtype the internal datatype to be wrapped
   * @return the Datatype
   */
  Datatype(const Solver* slv, const cvc5::DType& dtype);

  /**
   * Return constructor for name.
   * @param name The name of constructor to find
   * @return the constructor object for the name
   */
  DatatypeConstructor getConstructorForName(const std::string& name) const;

  /**
   * Return selector for name.
   * @param name The name of selector to find
   * @return the selector object for the name
   */
  DatatypeSelector getSelectorForName(const std::string& name) const;

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC5_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal datatype wrapped by this datatype.
   * Note: This is a shared_ptr rather than a unique_ptr since cvc5::DType is
   *       not ref counted.
   */
  std::shared_ptr<cvc5::DType> d_dtype;
};

/**
 * Serialize a datatype declaration to given stream.
 * @param out the output stream
 * @param dtdecl the datatype declaration to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeDecl& dtdecl) CVC5_EXPORT;

/**
 * Serialize a datatype constructor declaration to given stream.
 * @param out the output stream
 * @param ctordecl the datatype constructor declaration to be serialized
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructorDecl& ctordecl) CVC5_EXPORT;

/**
 * Serialize a vector of datatype constructor declarations to given stream.
 * @param out the output stream
 * @param vector the vector of datatype constructor declarations to be
 * serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::vector<DatatypeConstructorDecl>& vector)
    CVC5_EXPORT;

/**
 * Serialize a datatype to given stream.
 * @param out the output stream
 * @param dtype the datatype to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Datatype& dtype) CVC5_EXPORT;

/**
 * Serialize a datatype constructor to given stream.
 * @param out the output stream
 * @param ctor the datatype constructor to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructor& ctor) CVC5_EXPORT;

/**
 * Serialize a datatype selector to given stream.
 * @param out the output stream
 * @param stor the datatype selector to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelector& stor) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Grammar                                                                    */
/* -------------------------------------------------------------------------- */

/**
 * A Sygus Grammar.
 */
class CVC5_EXPORT Grammar
{
  friend class cvc5::Command;
  friend class Solver;

 public:
  /**
   * Add \p rule to the set of rules corresponding to \p ntSymbol.
   * @param ntSymbol the non-terminal to which the rule is added
   * @param rule the rule to add
   */
  void addRule(const Term& ntSymbol, const Term& rule);

  /**
   * Add \p rules to the set of rules corresponding to \p ntSymbol.
   * @param ntSymbol the non-terminal to which the rules are added
   * @param rules the rules to add
   */
  void addRules(const Term& ntSymbol, const std::vector<Term>& rules);

  /**
   * Allow \p ntSymbol to be an arbitrary constant.
   * @param ntSymbol the non-terminal allowed to be any constant
   */
  void addAnyConstant(const Term& ntSymbol);

  /**
   * Allow \p ntSymbol to be any input variable to corresponding
   * synth-fun/synth-inv with the same sort as \p ntSymbol.
   * @param ntSymbol the non-terminal allowed to be any input variable
   */
  void addAnyVariable(const Term& ntSymbol);

  /**
   * @return a string representation of this grammar.
   */
  std::string toString() const;

  /**
   * Nullary constructor. Needed for the Cython API.
   */
  Grammar();

 private:
  /**
   * Constructor.
   * @param slv the solver that created this grammar
   * @param sygusVars the input variables to synth-fun/synth-var
   * @param ntSymbols the non-terminals of this grammar
   */
  Grammar(const Solver* slv,
          const std::vector<Term>& sygusVars,
          const std::vector<Term>& ntSymbols);

  /**
   * @return the resolved datatype of the Start symbol of the grammar
   */
  Sort resolve();

  /**
   * Adds a constructor to sygus datatype <dt> whose sygus operator is <term>.
   *
   * \p ntsToUnres contains a mapping from non-terminal symbols to the
   * unresolved sorts they correspond to. This map indicates how the argument
   * <term> should be interpreted (instances of symbols from the domain of
   * \p ntsToUnres correspond to constructor arguments).
   *
   * The sygus operator that is actually added to <dt> corresponds to replacing
   * each occurrence of non-terminal symbols from the domain of \p ntsToUnres
   * with bound variables via purifySygusGTerm, and binding these variables
   * via a lambda.
   *
   * @param dt the non-terminal's datatype to which a constructor is added
   * @param term the sygus operator of the constructor
   * @param ntsToUnres mapping from non-terminals to their unresolved sorts
   */
  void addSygusConstructorTerm(
      DatatypeDecl& dt,
      const Term& term,
      const std::unordered_map<Term, Sort>& ntsToUnres) const;

  /**
   * Purify SyGuS grammar term.
   *
   * This returns a term where all occurrences of non-terminal symbols (those
   * in the domain of \p ntsToUnres) are replaced by fresh variables. For
   * each variable replaced in this way, we add the fresh variable it is
   * replaced with to \p args, and the unresolved sorts corresponding to the
   * non-terminal symbol to \p cargs (constructor args). In other words,
   * \p args contains the free variables in the term returned by this method
   * (which should be bound by a lambda), and \p cargs contains the sorts of
   * the arguments of the sygus constructor.
   *
   * @param term the term to purify
   * @param args the free variables in the term returned by this method
   * @param cargs the sorts of the arguments of the sygus constructor
   * @param ntsToUnres mapping from non-terminals to their unresolved sorts
   * @return the purfied term
   */
  Term purifySygusGTerm(const Term& term,
                        std::vector<Term>& args,
                        std::vector<Sort>& cargs,
                        const std::unordered_map<Term, Sort>& ntsToUnres) const;

  /**
   * This adds constructors to \p dt for sygus variables in \p d_sygusVars
   * whose sort is argument \p sort. This method should be called when the
   * sygus grammar term (Variable sort) is encountered.
   *
   * @param dt the non-terminal's datatype to which the constructors are added
   * @param sort the sort of the sygus variables to add
   */
  void addSygusConstructorVariables(DatatypeDecl& dt, const Sort& sort) const;

  /**
   * Check if \p rule contains variables that are neither parameters of
   * the corresponding synthFun/synthInv nor non-terminals.
   * @param rule the non-terminal allowed to be any constant
   * @return true if \p rule contains free variables and false otherwise
   */
  bool containsFreeVariables(const Term& rule) const;

  /** The solver that created this grammar. */
  const Solver* d_solver;
  /** Input variables to the corresponding function/invariant to synthesize.*/
  std::vector<Term> d_sygusVars;
  /** The non-terminal symbols of this grammar. */
  std::vector<Term> d_ntSyms;
  /** The mapping from non-terminal symbols to their production terms. */
  std::unordered_map<Term, std::vector<Term>> d_ntsToTerms;
  /** The set of non-terminals that can be arbitrary constants. */
  std::unordered_set<Term> d_allowConst;
  /** The set of non-terminals that can be sygus variables. */
  std::unordered_set<Term> d_allowVars;
  /** Did we call resolve() before? */
  bool d_isResolved;
};

/**
 * Serialize a grammar to given stream.
 * @param out the output stream
 * @param g the grammar to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Grammar& g) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Rounding Mode for Floating-Points                                          */
/* -------------------------------------------------------------------------- */

/**
 * Rounding modes for floating-point numbers.
 *
 * For many floating-point operations, infinitely precise results may not be
 * representable with the number of available bits. Thus, the results are
 * rounded in a certain way to one of the representable floating-point numbers.
 *
 * \verbatim embed:rst:leading-asterisk
 * These rounding modes directly follow the SMT-LIB theory for floating-point
 * arithmetic, which in turn is based on IEEE Standard 754 :cite:`IEEE754`.
 * The rounding modes are specified in Sections 4.3.1 and 4.3.2 of the IEEE
 * Standard 754.
 * \endverbatim
 */
enum RoundingMode
{
  /**
   * Round to the nearest even number.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with an even least
   * significant digit will be delivered.
   */
  ROUND_NEAREST_TIES_TO_EVEN,
  /**
   * Round towards positive infinity (+oo).
   * The result shall be the format's floating-point number (possibly +oo)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_POSITIVE,
  /**
   * Round towards negative infinity (-oo).
   * The result shall be the format's floating-point number (possibly -oo)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_NEGATIVE,
  /**
   * Round towards zero.
   * The result shall be the format's floating-point number closest to and no
   * greater in magnitude than the infinitely precise result.
   */
  ROUND_TOWARD_ZERO,
  /**
   * Round to the nearest number away from zero.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with larger magnitude
   * will be selected.
   */
  ROUND_NEAREST_TIES_TO_AWAY,
};

}  // namespace cvc5::api

namespace std {

/**
 * Hash function for RoundingModes.
 */
template <>
struct CVC5_EXPORT hash<cvc5::api::RoundingMode>
{
  size_t operator()(cvc5::api::RoundingMode rm) const;
};
}  // namespace std
namespace cvc5::api {

/* -------------------------------------------------------------------------- */
/* Options                                                                    */
/* -------------------------------------------------------------------------- */

/**
 * Provides access to options that can not be communicated via the regular
 * getOption() or getOptionInfo() methods. This class does not store the options
 * itself, but only acts as a wrapper to the solver object. It can thus no
 * longer be used after the solver object has been destroyed.
 */
class CVC5_EXPORT DriverOptions
{
  friend class Solver;

 public:
  /** Access the solvers input stream */
  std::istream& in() const;
  /** Access the solvers error output stream */
  std::ostream& err() const;
  /** Access the solvers output stream */
  std::ostream& out() const;

 private:
  DriverOptions(const Solver& solver);
  const Solver& d_solver;
};

/**
 * Holds some description about a particular option, including its name, its
 * aliases, whether the option was explicitly set by the user, and information
 * concerning its value. The `valueInfo` member holds any of the following
 * alternatives:
 * - VoidInfo if the option holds no value (or the value has no native type)
 * - ValueInfo<T> if the option is of type bool or std::string, holds the
 *   current value and the default value.
 * - NumberInfo<T> if the option is of type int64_t, uint64_t or double, holds
 *   the current and default value, as well as the minimum and maximum.
 * - ModeInfo if the option is a mode option, holds the current and default
 *   values, as well as a list of valid modes.
 * Additionally, this class provides convenience functions to obtain the
 * current value of an option in a type-safe manner using boolValue(),
 * stringValue(), intValue(), uintValue() and doubleValue(). They assert that
 * the option has the respective type and return the current value.
 */
struct CVC5_EXPORT OptionInfo
{
  /** Has no value information */
  struct VoidInfo {};
  /** Has the current and the default value */
  template <typename T>
  struct ValueInfo
  {
    T defaultValue;
    T currentValue;
  };
  /** Default value, current value, minimum and maximum of a numeric value */
  template <typename T>
  struct NumberInfo
  {
    T defaultValue;
    T currentValue;
    std::optional<T> minimum;
    std::optional<T> maximum;
  };
  /** Default value, current value and choices of a mode option */
  struct ModeInfo
  {
    std::string defaultValue;
    std::string currentValue;
    std::vector<std::string> modes;
  };

  /** The option name */
  std::string name;
  /** The option name aliases */
  std::vector<std::string> aliases;
  /** Whether the option was explicitly set by the user */
  bool setByUser;
  /** The option value information */
  std::variant<VoidInfo,
               ValueInfo<bool>,
               ValueInfo<std::string>,
               NumberInfo<int64_t>,
               NumberInfo<uint64_t>,
               NumberInfo<double>,
               ModeInfo>
      valueInfo;
  /** Obtain the current value as a bool. Asserts that valueInfo holds a bool.
   */
  bool boolValue() const;
  /** Obtain the current value as a string. Asserts that valueInfo holds a
   * string. */
  std::string stringValue() const;
  /** Obtain the current value as as int. Asserts that valueInfo holds an int.
   */
  int64_t intValue() const;
  /** Obtain the current value as a uint. Asserts that valueInfo holds a uint.
   */
  uint64_t uintValue() const;
  /** Obtain the current value as a double. Asserts that valueInfo holds a
   * double. */
  double doubleValue() const;
};

/**
 * Print a `OptionInfo` object to an ``std::ostream``.
 */
std::ostream& operator<<(std::ostream& os, const OptionInfo& oi) CVC5_EXPORT;

/* -------------------------------------------------------------------------- */
/* Statistics                                                                 */
/* -------------------------------------------------------------------------- */

/**
 * Represents a snapshot of a single statistic value.
 * A value can be of type `int64_t`, `double`, `std::string` or a histogram
 * (`std::map<std::string, uint64_t>`).
 * The value type can be queried (using `isInt()`, `isDouble()`, etc.) and
 * the stored value can be accessed (using `getInt()`, `getDouble()`, etc.).
 * It is possible to query whether this statistic is an expert statistic by
 * `isExpert()` and whether its value is the default value by `isDefault()`.
 */
class CVC5_EXPORT Stat
{
  struct StatData;

 public:
  friend class Statistics;
  friend std::ostream& operator<<(std::ostream& os, const Stat& sv);
  /** Representation of a histogram: maps names to frequencies. */
  using HistogramData = std::map<std::string, uint64_t>;
  /** Can only be obtained from a `Statistics` object. */
  Stat() = delete;
  /** Copy constructor */
  Stat(const Stat& s);
  /** Destructor */
  ~Stat();
  /** Copy assignment */
  Stat& operator=(const Stat& s);

  /**
   * Is this value intended for experts only?
   * @return Whether this is an expert statistic.
   */
  bool isExpert() const;
  /**
   * Does this value hold the default value?
   * @return Whether this is a defaulted statistic.
   */
  bool isDefault() const;

  /**
   * Is this value an integer?
   * @return Whether the value is an integer.
   */
  bool isInt() const;
  /**
   * Return the integer value.
   * @return The integer value.
   */
  int64_t getInt() const;
  /**
   * Is this value a double?
   * @return Whether the value is a double.
   */
  bool isDouble() const;
  /**
   * Return the double value.
   * @return The double value.
   */
  double getDouble() const;
  /**
   * Is this value a string?
   * @return Whether the value is a string.
   */
  bool isString() const;
  /**
   * Return the string value.
   * @return The string value.
   */
  const std::string& getString() const;
  /**
   * Is this value a histogram?
   * @return Whether the value is a histogram.
   */
  bool isHistogram() const;
  /**
   * Return the histogram value.
   * @return The histogram value.
   */
  const HistogramData& getHistogram() const;

 private:
  Stat(bool expert, bool def, StatData&& sd);
  /** Whether this statistic is only meant for experts */
  bool d_expert;
  /** Whether this statistic has the default value */
  bool d_default;
  std::unique_ptr<StatData> d_data;
};

/**
 * Print a `Stat` object to an ``std::ostream``.
 */
std::ostream& operator<<(std::ostream& os, const Stat& sv) CVC5_EXPORT;

/**
 * Represents a snapshot of the solver statistics.
 * Once obtained, an instance of this class is independent of the `Solver`
 * object: it will not change when the solvers internal statistics do, it
 * will not be invalidated if the solver is destroyed.
 * Iterating on this class (via `begin()` and `end()`) shows only public
 * statistics that have been changed. By passing appropriate flags to
 * `begin()`, statistics that are expert, defaulted, or both, can be
 * included as well. A single statistic value is represented as `Stat`.
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
             bool expert,
             bool defaulted);
    bool isVisible() const;
    BaseType::const_iterator d_it;
    const BaseType* d_base;
    bool d_showExpert = false;
    bool d_showDefault = false;
  };

  /**
   * Retrieve the statistic with the given name.
   * Asserts that a statistic with the given name actually exists and throws
   * a `CVC5ApiRecoverableException` if it does not.
   * @param name Name of the statistic.
   * @return The statistic with the given name.
   */
  const Stat& get(const std::string& name);
  /**
   * Begin iteration over the statistics values.
   * By default, only entries that are public (non-expert) and have been set
   * are visible while the others are skipped.
   * @param expert If set to true, expert statistics are shown as well.
   * @param defaulted If set to true, defaulted statistics are shown as well.
   */
  iterator begin(bool expert = false, bool defaulted = false) const;
  /** End iteration */
  iterator end() const;

 private:
  Statistics() = default;
  Statistics(const StatisticsRegistry& reg);
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
  friend class cvc5::Command;
  friend class cvc5::main::CommandExecutor;
  friend class Sort;
  friend class Term;

 private:
  /*
   * Constructs a solver with the given original options. This should only be
   * used internally when the Solver is reset.
   */
  Solver(std::unique_ptr<Options>&& original);

 public:
  /* .................................................................... */
  /* Constructors/Destructors                                             */
  /* .................................................................... */

  /**
   * Constructor.
   * @return the Solver
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
   * @return sort null
   */
  Sort getNullSort() const;

  /**
   * @return sort Boolean
   */
  Sort getBooleanSort() const;

  /**
   * @return sort Integer (in cvc5, Integer is a subtype of Real)
   */
  Sort getIntegerSort() const;

  /**
   * @return sort Real
   */
  Sort getRealSort() const;

  /**
   * @return sort RegExp
   */
  Sort getRegExpSort() const;

  /**
   * @return sort RoundingMode
   */
  Sort getRoundingModeSort() const;

  /**
   * @return sort String
   */
  Sort getStringSort() const;

  /**
   * Create an array sort.
   * @param indexSort the array index sort
   * @param elemSort the array element sort
   * @return the array sort
   */
  Sort mkArraySort(const Sort& indexSort, const Sort& elemSort) const;

  /**
   * Create a bit-vector sort.
   * @param size the bit-width of the bit-vector sort
   * @return the bit-vector sort
   */
  Sort mkBitVectorSort(uint32_t size) const;

  /**
   * Create a floating-point sort.
   * @param exp the bit-width of the exponent of the floating-point sort.
   * @param sig the bit-width of the significand of the floating-point sort.
   */
  Sort mkFloatingPointSort(uint32_t exp, uint32_t sig) const;

  /**
   * Create a datatype sort.
   * @param dtypedecl the datatype declaration from which the sort is created
   * @return the datatype sort
   */
  Sort mkDatatypeSort(const DatatypeDecl& dtypedecl) const;

  /**
   * Create a vector of datatype sorts. The names of the datatype declarations
   * must be distinct.
   *
   * @param dtypedecls the datatype declarations from which the sort is created
   * @return the datatype sorts
   */
  std::vector<Sort> mkDatatypeSorts(
      const std::vector<DatatypeDecl>& dtypedecls) const;

  /**
   * Create a vector of datatype sorts using unresolved sorts. The names of
   * the datatype declarations in dtypedecls must be distinct.
   *
   * This method is called when the DatatypeDecl objects dtypedecls have been
   * built using "unresolved" sorts.
   *
   * We associate each sort in unresolvedSorts with exactly one datatype from
   * dtypedecls. In particular, it must have the same name as exactly one
   * datatype declaration in dtypedecls.
   *
   * When constructing datatypes, unresolved sorts are replaced by the datatype
   * sort constructed for the datatype declaration it is associated with.
   *
   * @param dtypedecls the datatype declarations from which the sort is created
   * @param unresolvedSorts the list of unresolved sorts
   * @return the datatype sorts
   */
  std::vector<Sort> mkDatatypeSorts(
      const std::vector<DatatypeDecl>& dtypedecls,
      const std::set<Sort>& unresolvedSorts) const;

  /**
   * Create function sort.
   * @param domain the sort of the function argument
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  Sort mkFunctionSort(const Sort& domain, const Sort& codomain) const;

  /**
   * Create function sort.
   * @param sorts the sort of the function arguments
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  Sort mkFunctionSort(const std::vector<Sort>& sorts,
                      const Sort& codomain) const;

  /**
   * Create a sort parameter.
   * @param symbol the name of the sort
   * @return the sort parameter
   */
  Sort mkParamSort(const std::string& symbol) const;

  /**
   * Create a predicate sort.
   * @param sorts the list of sorts of the predicate
   * @return the predicate sort
   */
  Sort mkPredicateSort(const std::vector<Sort>& sorts) const;

  /**
   * Create a record sort
   * @param fields the list of fields of the record
   * @return the record sort
   */
  Sort mkRecordSort(
      const std::vector<std::pair<std::string, Sort>>& fields) const;

  /**
   * Create a set sort.
   * @param elemSort the sort of the set elements
   * @return the set sort
   */
  Sort mkSetSort(const Sort& elemSort) const;

  /**
   * Create a bag sort.
   * @param elemSort the sort of the bag elements
   * @return the bag sort
   */
  Sort mkBagSort(const Sort& elemSort) const;

  /**
   * Create a sequence sort.
   * @param elemSort the sort of the sequence elements
   * @return the sequence sort
   */
  Sort mkSequenceSort(const Sort& elemSort) const;

  /**
   * Create an uninterpreted sort.
   * @param symbol the name of the sort
   * @return the uninterpreted sort
   */
  Sort mkUninterpretedSort(const std::string& symbol) const;

  /**
   * Create a sort constructor sort.
   * @param symbol the symbol of the sort
   * @param arity the arity of the sort
   * @return the sort constructor sort
   */
  Sort mkSortConstructorSort(const std::string& symbol, size_t arity) const;

  /**
   * Create a tuple sort.
   * @param sorts of the elements of the tuple
   * @return the tuple sort
   */
  Sort mkTupleSort(const std::vector<Sort>& sorts) const;

  /* .................................................................... */
  /* Create Terms                                                         */
  /* .................................................................... */

  /**
   * Create 0-ary term of given kind.
   * @param kind the kind of the term
   * @return the Term
   */
  Term mkTerm(Kind kind) const;

  /**
   * Create a unary term of given kind.
   * @param kind the kind of the term
   * @param child the child of the term
   * @return the Term
   */
  Term mkTerm(Kind kind, const Term& child) const;

  /**
   * Create binary term of given kind.
   * @param kind the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @return the Term
   */
  Term mkTerm(Kind kind, const Term& child1, const Term& child2) const;

  /**
   * Create ternary term of given kind.
   * @param kind the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @param child3 the third child of the term
   * @return the Term
   */
  Term mkTerm(Kind kind,
              const Term& child1,
              const Term& child2,
              const Term& child3) const;

  /**
   * Create n-ary term of given kind.
   * @param kind the kind of the term
   * @param children the children of the term
   * @return the Term
   */
  Term mkTerm(Kind kind, const std::vector<Term>& children) const;

  /**
   * Create nullary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @return the Term
   */
  Term mkTerm(const Op& op) const;

  /**
   * Create unary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param child the child of the term
   * @return the Term
   */
  Term mkTerm(const Op& op, const Term& child) const;

  /**
   * Create binary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @return the Term
   */
  Term mkTerm(const Op& op, const Term& child1, const Term& child2) const;

  /**
   * Create ternary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @param child3 the third child of the term
   * @return the Term
   */
  Term mkTerm(const Op& op,
              const Term& child1,
              const Term& child2,
              const Term& child3) const;

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param children the children of the term
   * @return the Term
   */
  Term mkTerm(const Op& op, const std::vector<Term>& children) const;

  /**
   * Create a tuple term. Terms are automatically converted if sorts are
   * compatible.
   * @param sorts The sorts of the elements in the tuple
   * @param terms The elements in the tuple
   * @return the tuple Term
   */
  Term mkTuple(const std::vector<Sort>& sorts,
               const std::vector<Term>& terms) const;

  /* .................................................................... */
  /* Create Operators                                                     */
  /* .................................................................... */

  /**
   * Create an operator for a builtin Kind
   * The Kind may not be the Kind for an indexed operator
   *   (e.g. BITVECTOR_EXTRACT)
   * Note: in this case, the Op simply wraps the Kind.
   * The Kind can be used in mkTerm directly without
   *   creating an op first.
   * @param kind the kind to wrap
   */
  Op mkOp(Kind kind) const;

  /**
   * Create operator of kind:
   *   - DIVISIBLE (to support arbitrary precision integers)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg the string argument to this operator
   */
  Op mkOp(Kind kind, const std::string& arg) const;

  /**
   * Create operator of kind:
   *   - DIVISIBLE
   *   - BITVECTOR_REPEAT
   *   - BITVECTOR_ZERO_EXTEND
   *   - BITVECTOR_SIGN_EXTEND
   *   - BITVECTOR_ROTATE_LEFT
   *   - BITVECTOR_ROTATE_RIGHT
   *   - INT_TO_BITVECTOR
   *   - FLOATINGPOINT_TO_UBV
   *   - FLOATINGPOINT_TO_UBV_TOTAL
   *   - FLOATINGPOINT_TO_SBV
   *   - FLOATINGPOINT_TO_SBV_TOTAL
   *   - TUPLE_UPDATE
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg the uint32_t argument to this operator
   */
  Op mkOp(Kind kind, uint32_t arg) const;

  /**
   * Create operator of Kind:
   *   - BITVECTOR_EXTRACT
   *   - FLOATINGPOINT_TO_FP_IEEE_BITVECTOR
   *   - FLOATINGPOINT_TO_FP_FLOATINGPOINT
   *   - FLOATINGPOINT_TO_FP_REAL
   *   - FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR
   *   - FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR
   *   - FLOATINGPOINT_TO_FP_GENERIC
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg1 the first uint32_t argument to this operator
   * @param arg2 the second uint32_t argument to this operator
   */
  Op mkOp(Kind kind, uint32_t arg1, uint32_t arg2) const;

  /**
   * Create operator of Kind:
   *   - TUPLE_PROJECT
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param args the arguments (indices) of the operator
   */
  Op mkOp(Kind kind, const std::vector<uint32_t>& args) const;

  /* .................................................................... */
  /* Create Constants                                                     */
  /* .................................................................... */

  /**
   * Create a Boolean true constant.
   * @return the true constant
   */
  Term mkTrue() const;

  /**
   * Create a Boolean false constant.
   * @return the false constant
   */
  Term mkFalse() const;

  /**
   * Create a Boolean constant.
   * @return the Boolean constant
   * @param val the value of the constant
   */
  Term mkBoolean(bool val) const;

  /**
   * Create a constant representing the number Pi.
   * @return a constant representing Pi
   */
  Term mkPi() const;
  /**
   * Create an integer constant from a string.
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123").
   * @return a constant of sort Integer assuming 's' represents an integer)
   */
  Term mkInteger(const std::string& s) const;

  /**
   * Create an integer constant from a c++ int.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  Term mkInteger(int64_t val) const;

  /**
   * Create a real constant from a string.
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123") or real constant (e.g., "12.34" or "12/34").
   * @return a constant of sort Real
   */
  Term mkReal(const std::string& s) const;

  /**
   * Create a real constant from an integer.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  Term mkReal(int64_t val) const;

  /**
   * Create a real constant from a rational.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return a constant of sort Real
   */
  Term mkReal(int64_t num, int64_t den) const;

  /**
   * Create a regular expression all (re.all) term.
   * @return the all term
   */
  Term mkRegexpAll() const;

  /**
   * Create a regular expression allchar (re.allchar) term.
   * @return the allchar term
   */
  Term mkRegexpAllchar() const;

  /**
   * Create a regular expression none (re.none) term.
   * @return the none term
   */
  Term mkRegexpNone() const;

  /**
   * Create a constant representing an empty set of the given sort.
   * @param sort the sort of the set elements.
   * @return the empty set constant
   */
  Term mkEmptySet(const Sort& sort) const;

  /**
   * Create a constant representing an empty bag of the given sort.
   * @param sort the sort of the bag elements.
   * @return the empty bag constant
   */
  Term mkEmptyBag(const Sort& sort) const;

  /**
   * Create a separation logic empty term.
   * @return the separation logic empty term
   */
  Term mkSepEmp() const;

  /**
   * Create a separation logic nil term.
   * @param sort the sort of the nil term
   * @return the separation logic nil term
   */
  Term mkSepNil(const Sort& sort) const;

  /**
   * Create a String constant from a `std::string` which may contain SMT-LIB
   * compatible escape sequences like `\u1234` to encode unicode characters.
   * @param s the string this constant represents
   * @param useEscSequences determines whether escape sequences in `s` should
   * be converted to the corresponding unicode character
   * @return the String constant
   */
  Term mkString(const std::string& s, bool useEscSequences = false) const;

  /**
   * Create a String constant from a `std::wstring`.
   * This method does not support escape sequences as `std::wstring` already
   * supports unicode characters.
   * @param s the string this constant represents
   * @return the String constant
   */
  Term mkString(const std::wstring& s) const;

  /**
   * Create an empty sequence of the given element sort.
   * @param sort The element sort of the sequence.
   * @return the empty sequence with given element sort.
   */
  Term mkEmptySequence(const Sort& sort) const;

  /**
   * Create a universe set of the given sort.
   * @param sort the sort of the set elements
   * @return the universe set constant
   */
  Term mkUniverseSet(const Sort& sort) const;

  /**
   * Create a bit-vector constant of given size and value.
   *
   * Note: The given value must fit into a bit-vector of the given size.
   *
   * @param size the bit-width of the bit-vector sort
   * @param val the value of the constant
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size, uint64_t val = 0) const;

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   *
   * Note: The given value must fit into a bit-vector of the given size.
   *
   * @param size the bit-width of the constant
   * @param s the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size, const std::string& s, uint32_t base) const;

  /**
   * Create a constant array with the provided constant value stored at every
   * index
   * @param sort the sort of the constant array (must be an array sort)
   * @param val the constant value to store (must match the sort's element sort)
   * @return the constant array term
   */
  Term mkConstArray(const Sort& sort, const Term& val) const;

  /**
   * Create a positive infinity floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkPosInf(uint32_t exp, uint32_t sig) const;

  /**
   * Create a negative infinity floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNegInf(uint32_t exp, uint32_t sig) const;

  /**
   * Create a not-a-number (NaN) floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNaN(uint32_t exp, uint32_t sig) const;

  /**
   * Create a positive zero (+0.0) floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkPosZero(uint32_t exp, uint32_t sig) const;

  /**
   * Create a negative zero (-0.0) floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNegZero(uint32_t exp, uint32_t sig) const;

  /**
   * Create a roundingmode constant.
   * @param rm the floating point rounding mode this constant represents
   */
  Term mkRoundingMode(RoundingMode rm) const;

  /**
   * Create uninterpreted constant.
   * @param sort Sort of the constant
   * @param index Index of the constant
   */
  Term mkUninterpretedConst(const Sort& sort, int32_t index) const;

  /**
   * Create an abstract value constant.
   * The given index needs to be a positive integer in base 10.
   * @param index Index of the abstract value
   */
  Term mkAbstractValue(const std::string& index) const;

  /**
   * Create an abstract value constant.
   * The given index needs to be positive.
   * @param index Index of the abstract value
   */
  Term mkAbstractValue(uint64_t index) const;

  /**
   * Create a floating-point constant.
   * @param exp Size of the exponent
   * @param sig Size of the significand
   * @param val Value of the floating-point constant as a bit-vector term
   */
  Term mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const;

  /**
   * Create a cardinality constraint for an uninterpreted sort.
   * @param sort the sort the cardinality constraint is for
   * @param upperBound the upper bound on the cardinality of the sort
   * @return the cardinality constraint
   */
  Term mkCardinalityConstraint(const Sort& sort, uint32_t upperBound) const;

  /* .................................................................... */
  /* Create Variables                                                     */
  /* .................................................................... */

  /**
   * Create (first-order) constant (0-arity function symbol).
   * SMT-LIB:
   * \verbatim
   *   ( declare-const <symbol> <sort> )
   *   ( declare-fun <symbol> ( ) <sort> )
   * \endverbatim
   *
   * @param sort the sort of the constant
   * @param symbol the name of the constant
   * @return the first-order constant
   */
  Term mkConst(const Sort& sort, const std::string& symbol) const;
  /**
   * Create (first-order) constant (0-arity function symbol), with a default
   * symbol name.
   *
   * @param sort the sort of the constant
   * @return the first-order constant
   */
  Term mkConst(const Sort& sort) const;

  /**
   * Create a bound variable to be used in a binder (i.e. a quantifier, a
   * lambda, or a witness binder).
   * @param sort the sort of the variable
   * @param symbol the name of the variable
   * @return the variable
   */
  Term mkVar(const Sort& sort, const std::string& symbol = std::string()) const;

  /* .................................................................... */
  /* Create datatype constructor declarations                             */
  /* .................................................................... */

  DatatypeConstructorDecl mkDatatypeConstructorDecl(const std::string& name);

  /* .................................................................... */
  /* Create datatype declarations                                         */
  /* .................................................................... */

  /**
   * Create a datatype declaration.
   * @param name the name of the datatype
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl mkDatatypeDecl(const std::string& name,
                              bool isCoDatatype = false);

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param param the sort parameter
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl mkDatatypeDecl(const std::string& name,
                              Sort param,
                              bool isCoDatatype = false);

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param params a list of sort parameters
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl mkDatatypeDecl(const std::string& name,
                              const std::vector<Sort>& params,
                              bool isCoDatatype = false);

  /* .................................................................... */
  /* Formula Handling                                                     */
  /* .................................................................... */

  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   * @param t the formula to simplify
   * @return the simplified formula
   */
  Term simplify(const Term& t);

  /**
   * Assert a formula.
   * SMT-LIB:
   * \verbatim
   *   ( assert <term> )
   * \endverbatim
   * @param term the formula to assert
   */
  void assertFormula(const Term& term) const;

  /**
   * Check satisfiability.
   * SMT-LIB:
   * \verbatim
   *   ( check-sat )
   * \endverbatim
   * @return the result of the satisfiability check.
   */
  Result checkSat() const;

  /**
   * Check satisfiability assuming the given formula.
   * SMT-LIB:
   * \verbatim
   *   ( check-sat-assuming ( <prop_literal> ) )
   * \endverbatim
   * @param assumption the formula to assume
   * @return the result of the satisfiability check.
   */
  Result checkSatAssuming(const Term& assumption) const;

  /**
   * Check satisfiability assuming the given formulas.
   * SMT-LIB:
   * \verbatim
   *   ( check-sat-assuming ( <prop_literal>+ ) )
   * \endverbatim
   * @param assumptions the formulas to assume
   * @return the result of the satisfiability check.
   */
  Result checkSatAssuming(const std::vector<Term>& assumptions) const;

  /**
   * Check entailment of the given formula w.r.t. the current set of assertions.
   * @param term the formula to check entailment for
   * @return the result of the entailment check.
   */
  Result checkEntailed(const Term& term) const;

  /**
   * Check entailment of the given set of given formulas w.r.t. the current
   * set of assertions.
   * @param terms the terms to check entailment for
   * @return the result of the entailmentcheck.
   */
  Result checkEntailed(const std::vector<Term>& terms) const;

  /**
   * Create datatype sort.
   * SMT-LIB:
   * \verbatim
   *   ( declare-datatype <symbol> <datatype_decl> )
   * \endverbatim
   * @param symbol the name of the datatype sort
   * @param ctors the constructor declarations of the datatype sort
   * @return the datatype sort
   */
  Sort declareDatatype(const std::string& symbol,
                       const std::vector<DatatypeConstructorDecl>& ctors) const;

  /**
   * Declare n-ary function symbol.
   * SMT-LIB:
   * \verbatim
   *   ( declare-fun <symbol> ( <sort>* ) <sort> )
   * \endverbatim
   * @param symbol the name of the function
   * @param sorts the sorts of the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  Term declareFun(const std::string& symbol,
                  const std::vector<Sort>& sorts,
                  const Sort& sort) const;

  /**
   * Declare uninterpreted sort.
   * SMT-LIB:
   * \verbatim
   *   ( declare-sort <symbol> <numeral> )
   * \endverbatim
   * @param symbol the name of the sort
   * @param arity the arity of the sort
   * @return the sort
   */
  Sort declareSort(const std::string& symbol, uint32_t arity) const;

  /**
   * Define n-ary function.
   * SMT-LIB:
   * \verbatim
   *   ( define-fun <function_def> )
   * \endverbatim
   * @param symbol the name of the function
   * @param bound_vars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  Term defineFun(const std::string& symbol,
                 const std::vector<Term>& bound_vars,
                 const Sort& sort,
                 const Term& term,
                 bool global = false) const;

  /**
   * Define recursive function.
   * SMT-LIB:
   * \verbatim
   * ( define-fun-rec <function_def> )
   * \endverbatim
   * @param symbol the name of the function
   * @param bound_vars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  Term defineFunRec(const std::string& symbol,
                    const std::vector<Term>& bound_vars,
                    const Sort& sort,
                    const Term& term,
                    bool global = false) const;

  /**
   * Define recursive function.
   * SMT-LIB:
   * \verbatim
   * ( define-fun-rec <function_def> )
   * \endverbatim
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  Term defineFunRec(const Term& fun,
                    const std::vector<Term>& bound_vars,
                    const Term& term,
                    bool global = false) const;

  /**
   * Define recursive functions.
   * SMT-LIB:
   * \verbatim
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * \endverbatim
   * Create elements of parameter 'funs' with mkConst().
   * @param funs the sorted functions
   * @param bound_vars the list of parameters to the functions
   * @param terms the list of function bodies of the functions
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  void defineFunsRec(const std::vector<Term>& funs,
                     const std::vector<std::vector<Term>>& bound_vars,
                     const std::vector<Term>& terms,
                     bool global = false) const;

  /**
   * Echo a given string to the given output stream.
   * SMT-LIB:
   * \verbatim
   * ( echo <std::string> )
   * \endverbatim
   * @param out the output stream
   * @param str the string to echo
   */
  void echo(std::ostream& out, const std::string& str) const;

  /**
   * Get the list of asserted formulas.
   * SMT-LIB:
   * \verbatim
   * ( get-assertions )
   * \endverbatim
   * @return the list of asserted formulas
   */
  std::vector<Term> getAssertions() const;

  /**
   * Get info from the solver.
   * SMT-LIB: \verbatim( get-info <info_flag> )\endverbatim
   * @return the info
   */
  std::string getInfo(const std::string& flag) const;

  /**
   * Get the value of a given option.
   * SMT-LIB:
   * \verbatim
   * ( get-option <keyword> )
   * \endverbatim
   * @param option the option for which the value is queried
   * @return a string representation of the option value
   */
  std::string getOption(const std::string& option) const;

  /**
   * Get all option names that can be used with `setOption`, `getOption` and
   * `getOptionInfo`.
   * @return all option names
   */
  std::vector<std::string> getOptionNames() const;

  /**
   * Get some information about the given option. Check the `OptionInfo` class
   * for more details on which information is available.
   * @return information about the given option
   */
  OptionInfo getOptionInfo(const std::string& option) const;

  /**
   * Get the driver options, which provide access to options that can not be
   * communicated properly via getOption() and getOptionInfo().
   * @return a DriverOptions object.
   */
  DriverOptions getDriverOptions() const;

  /**
   * Get the set of unsat ("failed") assumptions.
   * SMT-LIB:
   * \verbatim
   * ( get-unsat-assumptions )
   * \endverbatim
   * Requires to enable option 'produce-unsat-assumptions'.
   * @return the set of unsat assumptions.
   */
  std::vector<Term> getUnsatAssumptions() const;

  /**
   * Get the unsatisfiable core.
   * SMT-LIB:
   * \verbatim
   * ( get-unsat-core )
   * \endverbatim
   * Requires to enable option 'produce-unsat-cores'.
   * @return a set of terms representing the unsatisfiable core
   */
  std::vector<Term> getUnsatCore() const;

  /**
   * Get a difficulty estimate for an asserted formula. This method is
   * intended to be called immediately after any response to a checkSat.
   *
   * @return a map from (a subset of) the input assertions to a real value that
   * is an estimate of how difficult each assertion was to solve. Unmentioned
   * assertions can be assumed to have zero difficulty.
   */
  std::map<Term, Term> getDifficulty() const;

  /**
   * Get the refutation proof
   * SMT-LIB:
   * \verbatim
   * ( get-proof )
   * \endverbatim
   * Requires to enable option 'produce-proofs'.
   * @return a string representing the proof, according to the value of
   * proof-format-mode.
   */
  std::string getProof() const;

  /**
   * Get the value of the given term in the current model.
   * SMT-LIB:
   * \verbatim
   * ( get-value ( <term> ) )
   * \endverbatim
   * @param term the term for which the value is queried
   * @return the value of the given term
   */
  Term getValue(const Term& term) const;

  /**
   * Get the values of the given terms in the current model.
   * SMT-LIB:
   * \verbatim
   * ( get-value ( <term>+ ) )
   * \endverbatim
   * @param terms the terms for which the value is queried
   * @return the values of the given terms
   */
  std::vector<Term> getValue(const std::vector<Term>& terms) const;

  /**
   * Get the domain elements of uninterpreted sort s in the current model. The
   * current model interprets s as the finite sort whose domain elements are
   * given in the return value of this method.
   *
   * @param s The uninterpreted sort in question
   * @return the domain elements of s in the current model
   */
  std::vector<Term> getModelDomainElements(const Sort& s) const;

  /**
   * This returns false if the model value of free constant v was not essential
   * for showing the satisfiability of the last call to checkSat using the
   * current model. This method will only return false (for any v) if
   * the model-cores option has been set.
   *
   * @param v The term in question
   * @return true if v is a model core symbol
   */
  bool isModelCoreSymbol(const Term& v) const;

  /**
   * Get the model
   * SMT-LIB:
   * \verbatim
   * ( get-model )
   * \endverbatim
   * Requires to enable option 'produce-models'.
   * @param sorts The list of uninterpreted sorts that should be printed in the
   * model.
   * @param vars The list of free constants that should be printed in the
   * model. A subset of these may be printed based on isModelCoreSymbol.
   * @return a string representing the model.
   */
  std::string getModel(const std::vector<Sort>& sorts,
                       const std::vector<Term>& vars) const;

  /**
   * Do quantifier elimination.
   * SMT-LIB:
   * \verbatim
   * ( get-qe <q> )
   * \endverbatim
   * Requires a logic that supports quantifier elimination. Currently, the only
   * logics supported by quantifier elimination is LRA and LIA.
   * @param q a quantified formula of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free formula
   * @return a formula ret such that, given the current set of formulas A
   * asserted to this solver:
   *   - ( A ^ q ) and ( A ^ ret ) are equivalent
   *   - ret is quantifier-free formula containing only free variables in
   *     y1...yn.
   */
  Term getQuantifierElimination(const Term& q) const;

  /**
   * Do partial quantifier elimination, which can be used for incrementally
   * computing the result of a quantifier elimination.
   * SMT-LIB:
   * \verbatim
   * ( get-qe-disjunct <q> )
   * \endverbatim
   * Requires a logic that supports quantifier elimination. Currently, the only
   * logics supported by quantifier elimination is LRA and LIA.
   * @param q a quantified formula of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free formula
   * @return a formula ret such that, given the current set of formulas A
   * asserted to this solver:
   *   - (A ^ q) => (A ^ ret) if Q is forall or (A ^ ret) => (A ^ q) if Q is
   *     exists,
   *   - ret is quantifier-free formula containing only free variables in
   *     y1...yn,
   *   - If Q is exists, let A^Q_n be the formula
   *       A ^ ~ret^Q_1 ^ ... ^ ~ret^Q_n
   *     where for each i=1,...n, formula ret^Q_i is the result of calling
   *     getQuantifierEliminationDisjunct for q with the set of assertions
   *     A^Q_{i-1}. Similarly, if Q is forall, then let A^Q_n be
   *       A ^ ret^Q_1 ^ ... ^ ret^Q_n
   *     where ret^Q_i is the same as above. In either case, we have
   *     that ret^Q_j will eventually be true or false, for some finite j.
   */
  Term getQuantifierEliminationDisjunct(const Term& q) const;

  /**
   * When using separation logic, this sets the location sort and the
   * datatype sort to the given ones. This method should be invoked exactly
   * once, before any separation logic constraints are provided.
   * @param locSort The location sort of the heap
   * @param dataSort The data sort of the heap
   */
  void declareSepHeap(const Sort& locSort, const Sort& dataSort) const;

  /**
   * When using separation logic, obtain the term for the heap.
   * @return The term for the heap
   */
  Term getValueSepHeap() const;

  /**
   * When using separation logic, obtain the term for nil.
   * @return The term for nil
   */
  Term getValueSepNil() const;

  /**
   * Declare a symbolic pool of terms with the given initial value.
   * SMT-LIB:
   * \verbatim
   * ( declare-pool <symbol> <sort> ( <term>* ) )
   * \endverbatim
   * @param symbol The name of the pool
   * @param sort The sort of the elements of the pool.
   * @param initValue The initial value of the pool
   */
  Term declarePool(const std::string& symbol,
                   const Sort& sort,
                   const std::vector<Term>& initValue) const;
  /**
   * Pop (a) level(s) from the assertion stack.
   * SMT-LIB:
   * \verbatim
   * ( pop <numeral> )
   * \endverbatim
   * @param nscopes the number of levels to pop
   */
  void pop(uint32_t nscopes = 1) const;

  /**
   * Get an interpolant
   * SMT-LIB:
   * \verbatim
   * ( get-interpol <conj> )
   * \endverbatim
   * Requires to enable option 'produce-interpols'.
   * @param conj the conjecture term
   * @param output a Term I such that A->I and I->B are valid, where A is the
   *        current set of assertions and B is given in the input by conj.
   * @return true if it gets I successfully, false otherwise.
   */
  bool getInterpolant(const Term& conj, Term& output) const;

  /**
   * Get an interpolant
   * SMT-LIB:
   * \verbatim
   * ( get-interpol <conj> <g> )
   * \endverbatim
   * Requires to enable option 'produce-interpols'.
   * @param conj the conjecture term
   * @param grammar the grammar for the interpolant I
   * @param output a Term I such that A->I and I->B are valid, where A is the
   *        current set of assertions and B is given in the input by conj.
   * @return true if it gets I successfully, false otherwise.
   */
  bool getInterpolant(const Term& conj, Grammar& grammar, Term& output) const;

  /**
   * Get an abduct.
   * SMT-LIB:
   * \verbatim
   * ( get-abduct <conj> )
   * \endverbatim
   * Requires enabling option 'produce-abducts'
   * @param conj the conjecture term
   * @param output a term C such that A^C is satisfiable, and A^~B^C is
   *        unsatisfiable, where A is the current set of assertions and B is
   *        given in the input by conj
   * @return true if it gets C successfully, false otherwise
   */
  bool getAbduct(const Term& conj, Term& output) const;

  /**
   * Get an abduct.
   * SMT-LIB:
   * \verbatim
   * ( get-abduct <conj> <g> )
   * \endverbatim
   * Requires enabling option 'produce-abducts'
   * @param conj the conjecture term
   * @param grammar the grammar for the abduct C
   * @param output a term C such that A^C is satisfiable, and A^~B^C is
   *        unsatisfiable, where A is the current set of assertions and B is
   *        given in the input by conj
   * @return true if it gets C successfully, false otherwise
   */
  bool getAbduct(const Term& conj, Grammar& grammar, Term& output) const;

  /**
   * Block the current model. Can be called only if immediately preceded by a
   * SAT or INVALID query.
   * SMT-LIB:
   * \verbatim
   * ( block-model )
   * \endverbatim
   * Requires enabling 'produce-models' option and setting 'block-models' option
   * to a mode other than "none".
   */
  void blockModel() const;

  /**
   * Block the current model values of (at least) the values in terms. Can be
   * called only if immediately preceded by a SAT or NOT_ENTAILED query.
   * SMT-LIB:
   * \verbatim
   * ( block-model-values ( <terms>+ ) )
   * \endverbatim
   * Requires enabling 'produce-models' option and setting 'block-models' option
   * to a mode other than "none".
   */
  void blockModelValues(const std::vector<Term>& terms) const;

  /**
   * Print all instantiations made by the quantifiers module.
   * @param out the output stream
   */
  void printInstantiations(std::ostream& out) const;

  /**
   * Push (a) level(s) to the assertion stack.
   * SMT-LIB:
   * \verbatim
   * ( push <numeral> )
   * \endverbatim
   * @param nscopes the number of levels to push
   */
  void push(uint32_t nscopes = 1) const;

  /**
   * Remove all assertions.
   * SMT-LIB:
   * \verbatim
   * ( reset-assertions )
   * \endverbatim
   */
  void resetAssertions() const;

  /**
   * Set info.
   * SMT-LIB:
   * \verbatim
   * ( set-info <attribute> )
   * \endverbatim
   * @param keyword the info flag
   * @param value the value of the info flag
   */
  void setInfo(const std::string& keyword, const std::string& value) const;

  /**
   * Set logic.
   * SMT-LIB:
   * \verbatim
   * ( set-logic <symbol> )
   * \endverbatim
   * @param logic the logic to set
   */
  void setLogic(const std::string& logic) const;

  /**
   * Set option.
   * SMT-LIB:
   * \verbatim
   *   ( set-option <option> )
   * \endverbatim
   * @param option the option name
   * @param value the option value
   */
  void setOption(const std::string& option, const std::string& value) const;

  /**
   * If needed, convert this term to a given sort. Note that the sort of the
   * term must be convertible into the target sort. Currently only Int to Real
   * conversions are supported.
   * @param t the term
   * @param s the target sort
   * @return the term wrapped into a sort conversion if needed
   */
  Term ensureTermSort(const Term& t, const Sort& s) const;

  /**
   * Append \p symbol to the current list of universal variables.
   * SyGuS v2:
   * \verbatim
   *   ( declare-var <symbol> <sort> )
   * \endverbatim
   * @param sort the sort of the universal variable
   * @param symbol the name of the universal variable
   * @return the universal variable
   */
  Term mkSygusVar(const Sort& sort,
                  const std::string& symbol = std::string()) const;

  /**
   * Create a Sygus grammar. The first non-terminal is treated as the starting
   * non-terminal, so the order of non-terminals matters.
   *
   * @param boundVars the parameters to corresponding synth-fun/synth-inv
   * @param ntSymbols the pre-declaration of the non-terminal symbols
   * @return the grammar
   */
  Grammar mkSygusGrammar(const std::vector<Term>& boundVars,
                         const std::vector<Term>& ntSymbols) const;

  /**
   * Synthesize n-ary function.
   * SyGuS v2:
   * \verbatim
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> )
   * \endverbatim
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  Term synthFun(const std::string& symbol,
                const std::vector<Term>& boundVars,
                const Sort& sort) const;

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   * SyGuS v2:
   * \verbatim
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )
   * \endverbatim
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param grammar the syntactic constraints
   * @return the function
   */
  Term synthFun(const std::string& symbol,
                const std::vector<Term>& boundVars,
                Sort sort,
                Grammar& grammar) const;

  /**
   * Synthesize invariant.
   * SyGuS v2:
   * \verbatim
   *   ( synth-inv <symbol> ( <boundVars>* ) )
   * \endverbatim
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @return the invariant
   */
  Term synthInv(const std::string& symbol,
                const std::vector<Term>& boundVars) const;

  /**
   * Synthesize invariant following specified syntactic constraints.
   * SyGuS v2:
   * \verbatim
   *   ( synth-inv <symbol> ( <boundVars>* ) <g> )
   * \endverbatim
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @param grammar the syntactic constraints
   * @return the invariant
   */
  Term synthInv(const std::string& symbol,
                const std::vector<Term>& boundVars,
                Grammar& grammar) const;

  /**
   * Add a forumla to the set of Sygus constraints.
   * SyGuS v2:
   * \verbatim
   *   ( constraint <term> )
   * \endverbatim
   * @param term the formula to add as a constraint
   */
  void addSygusConstraint(const Term& term) const;

  /**
   * Add a forumla to the set of Sygus assumptions.
   * SyGuS v2:
   * \verbatim
   *   ( assume <term> )
   * \endverbatim
   * @param term the formula to add as an assumption
   */
  void addSygusAssume(const Term& term) const;

  /**
   * Add a set of Sygus constraints to the current state that correspond to an
   * invariant synthesis problem.
   * SyGuS v2:
   * \verbatim
   *   ( inv-constraint <inv> <pre> <trans> <post> )
   * \endverbatim
   * @param inv the function-to-synthesize
   * @param pre the pre-condition
   * @param trans the transition relation
   * @param post the post-condition
   */
  void addSygusInvConstraint(Term inv, Term pre, Term trans, Term post) const;

  /**
   * Try to find a solution for the synthesis conjecture corresponding to the
   * current list of functions-to-synthesize, universal variables and
   * constraints.
   * SyGuS v2:
   * \verbatim
   *   ( check-synth )
   * \endverbatim
   * @return the result of the synthesis conjecture.
   */
  Result checkSynth() const;

  /**
   * Get the synthesis solution of the given term. This method should be called
   * immediately after the solver answers unsat for sygus input.
   * @param term the term for which the synthesis solution is queried
   * @return the synthesis solution of the given term
   */
  Term getSynthSolution(Term term) const;

  /**
   * Get the synthesis solutions of the given terms. This method should be
   * called immediately after the solver answers unsat for sygus input.
   * @param terms the terms for which the synthesis solutions is queried
   * @return the synthesis solutions of the given terms
   */
  std::vector<Term> getSynthSolutions(const std::vector<Term>& terms) const;

  /**
   * Returns a snapshot of the current state of the statistic values of this
   * solver. The returned object is completely decoupled from the solver and
   * will not change when the solver is used again.
   */
  Statistics getStatistics() const;

  /**
   * Whether the output stream for the given tag is enabled. Tags can be enabled
   * with the `output` option (and `-o <tag>` on the command line). Raises an
   * exception when an invalid tag is given.
   */
  bool isOutputOn(const std::string& tag) const;

  /**
   * Returns an output stream for the given tag. Tags can be enabled with the
   * `output` option (and `-o <tag>` on the command line). Raises an exception
   * when an invalid tag is given.
   */
  std::ostream& getOutput(const std::string& tag) const;

 private:
  /** @return the node manager of this solver */
  NodeManager* getNodeManager(void) const;
  /** Reset the API statistics */
  void resetStatistics();

  /**
   * Print the statistics to the given file descriptor, suitable for usage in
   * signal handlers.
   */
  void printStatisticsSafe(int fd) const;

  /** Helper to check for API misuse in mkOp functions. */
  void checkMkTerm(Kind kind, uint32_t nchildren) const;
  /** Helper for mk-functions that call d_nodeMgr->mkConst(). */
  template <typename T>
  Term mkValHelper(T t) const;
  /** Helper for making rational values. */
  Term mkRationalValHelper(const Rational& r) const;
  /** Helper for mkReal functions that take a string as argument. */
  Term mkRealFromStrHelper(const std::string& s) const;
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
   * Helper function that ensures that a given term is of sort real (as opposed
   * to being of sort integer).
   * @param t a term of sort integer or real
   * @return a term of sort real
   */
  Term ensureRealSort(const Term& t) const;

  /**
   * Create n-ary term of given kind. This handles the cases of left/right
   * associative operators, chainable operators, and cases when the number of
   * children exceeds the maximum arity for the kind.
   * @param kind the kind of the term
   * @param children the children of the term
   * @return the Term
   */
  Term mkTermHelper(Kind kind, const std::vector<Term>& children) const;

  /**
   * Create n-ary term of given kind from a given operator.
   * @param op the operator
   * @param children the children of the term
   * @return the Term
   */
  Term mkTermHelper(const Op& op, const std::vector<Term>& children) const;

  /**
   * Create a vector of datatype sorts, using unresolved sorts.
   * @param dtypedecls the datatype declarations from which the sort is created
   * @param unresolvedSorts the list of unresolved sorts
   * @return the datatype sorts
   */
  std::vector<Sort> mkDatatypeSortsInternal(
      const std::vector<DatatypeDecl>& dtypedecls,
      const std::set<Sort>& unresolvedSorts) const;

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   * SMT-LIB:
   * \verbatim
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> <g>? )
   * \endverbatim
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param isInv determines whether this is synth-fun or synth-inv
   * @param grammar the syntactic constraints
   * @return the function
   */
  Term synthFunHelper(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      const Sort& sort,
                      bool isInv = false,
                      Grammar* grammar = nullptr) const;

  /** Check whether string s is a valid decimal integer. */
  bool isValidInteger(const std::string& s) const;

  /** Increment the term stats counter. */
  void increment_term_stats(Kind kind) const;
  /** Increment the vars stats (if 'is_var') or consts stats counter. */
  void increment_vars_consts_stats(const Sort& sort, bool is_var) const;

  /** Keep a copy of the original option settings (for resets). */
  std::unique_ptr<Options> d_originalOptions;
  /** The node manager of this solver. */
  NodeManager* d_nodeMgr;
  /** The statistics collected on the Api level. */
  std::unique_ptr<APIStatistics> d_stats;
  /** The SMT engine of this solver. */
  std::unique_ptr<SolverEngine> d_slv;
  /** The random number generator of this solver. */
  std::unique_ptr<Random> d_rng;
};

}  // namespace cvc5::api

#endif
