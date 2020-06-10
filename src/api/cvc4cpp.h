/*********************                                                        */
/*! \file cvc4cpp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The CVC4 C++ API.
 **
 ** The CVC4 C++ API.
 **/

#include "cvc4_public.h"

#ifndef CVC4__API__CVC4CPP_H
#define CVC4__API__CVC4CPP_H

#include "api/cvc4cppkind.h"
// !!! Only temporarily public until the parser is fully migrated to the new
// API. !!!
#include "expr/kind.h"
// !!!

#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace CVC4 {

class Expr;
class Datatype;
class DatatypeConstructor;
class DatatypeConstructorArg;
class ExprManager;
class SmtEngine;
class Type;
class Options;
class Random;
class Result;

namespace api {

class Solver;

/* -------------------------------------------------------------------------- */
/* Exception                                                                  */
/* -------------------------------------------------------------------------- */

class CVC4_PUBLIC CVC4ApiException : public std::exception
{
 public:
  CVC4ApiException(const std::string& str) : d_msg(str) {}
  CVC4ApiException(const std::stringstream& stream) : d_msg(stream.str()) {}
  std::string getMessage() const { return d_msg; }
  const char* what() const noexcept override { return d_msg.c_str(); }

 private:
  std::string d_msg;
};

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * Encapsulation of a three-valued solver result, with explanations.
 */
class CVC4_PUBLIC Result
{
  friend class Solver;

 public:
  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor.
   * @param r the internal result that is to be wrapped by this result
   * @return the Result
   */
  Result(const CVC4::Result& r);

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
   * CVC4 was not able to determine (un)satisfiability.
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
   * Return true if query was a checkEntailed() () query and CVC4 was not able
   * to determine if it is entailed.
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
  std::string getUnknownExplanation() const;

  /**
   * @return a string representation of this result.
   */
  std::string toString() const;

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  CVC4::Result getResult(void) const;

 private:
  /**
   * The interal result wrapped by this result.
   * This is a shared_ptr rather than a unique_ptr since CVC4::Result is
   * not ref counted.
   */
  std::shared_ptr<CVC4::Result> d_result;
};

/**
 * Serialize a result to given stream.
 * @param out the output stream
 * @param r the result to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Result& r) CVC4_PUBLIC;

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

class Datatype;

/**
 * The sort of a CVC4 term.
 */
class CVC4_PUBLIC Sort
{
  friend class DatatypeConstructorDecl;
  friend class DatatypeDecl;
  friend class Op;
  friend class Solver;
  friend class Grammar;
  friend struct SortHashFunction;
  friend class Term;

 public:
  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param t the internal type that is to be wrapped by this sort
   * @return the Sort
   */
  Sort(const Solver* slv, const CVC4::Type& t);

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
   * @return true if the sort is a Boolean sort
   */
  bool isBoolean() const;

  /**
   * Is this a integer sort?
   * @return true if the sort is a integer sort
   */
  bool isInteger() const;

  /**
   * Is this a real sort?
   * @return true if the sort is a real sort
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
   * @return true if the sort is a array sort
   */
  bool isArray() const;

  /**
   * Is this a Set sort?
   * @return true if the sort is a Set sort
   */
  bool isSet() const;

  /**
   * Is this a sort kind?
   * @return true if this is a sort kind
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
   * (1) we handle equalities between terms of that type, and
   * (2) they are allowed to be parameters of parametric sorts (e.g. index or
   *     element sorts of arrays).
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
  bool isSubsortOf(Sort s) const;

  /**
   * Is this sort comparable to the given sort (i.e., do they share
   * a common ancestor in the subsort tree)?
   * @return true if this sort is comparable to s
   */
  bool isComparableTo(Sort s) const;

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
   * Output a string representation of this sort to a given stream.
   * @param out the output stream
   */
  void toStream(std::ostream& out) const;

  /**
   * @return a string representation of this sort
   */
  std::string toString() const;

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  CVC4::Type getType(void) const;

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
   * @return the array element sort of an array element sort
   */
  Sort getArrayElementSort() const;

  /* Set sort ------------------------------------------------------------ */

  /**
   * @return the element sort of a set sort
   */
  Sort getSetElementSort() const;

  /* Uninterpreted sort -------------------------------------------------- */

  /**
   * @return the name of an uninterpreted sort
   */
  std::string getUninterpretedSortName() const;

  /**
   * @return true if an uninterpreted sort is parameterezied
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
  uint32_t getBVSize() const;

  /* Floating-point sort ------------------------------------------------- */

  /**
   * @return the bit-width of the exponent of the floating-point sort
   */
  uint32_t getFPExponentSize() const;

  /**
   * @return the width of the significand of the floating-point sort
   */
  uint32_t getFPSignificandSize() const;

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
  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC4_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The interal type wrapped by this sort.
   * This is a shared_ptr rather than a unique_ptr to avoid overhead due to
   * memory allocation (CVC4::Type is already ref counted, so this could be
   * a unique_ptr instead).
   */
  std::shared_ptr<CVC4::Type> d_type;
};

/**
 * Serialize a sort to given stream.
 * @param out the output stream
 * @param s the sort to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Sort& s) CVC4_PUBLIC;

/**
 * Hash function for Sorts.
 */
struct CVC4_PUBLIC SortHashFunction
{
  size_t operator()(const Sort& s) const;
};

/* -------------------------------------------------------------------------- */
/* Op                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * A CVC4 operator.
 * An operator is a term that represents certain operators, instantiated
 * with its required parameters, e.g., a term of kind BITVECTOR_EXTRACT.
 */
class CVC4_PUBLIC Op
{
  friend class Solver;
  friend struct OpHashFunction;

 public:
  /**
   * Constructor.
   */
  Op();

  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor for a single kind (non-indexed operator).
   * @param slv the associated solver object
   * @param k the kind of this Op
   */
  Op(const Solver* slv, const Kind k);

  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param k the kind of this Op
   * @param e the internal expression that is to be wrapped by this term
   * @return the Term
   */
  Op(const Solver* slv, const Kind k, const CVC4::Expr& e);

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

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  CVC4::Expr getExpr(void) const;

 private:
  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC4_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * Note: An indexed operator has a non-null internal expr, d_expr
   * Note 2: We use a helper method to avoid having API functions call
   *         other API functions (we need to call this internally)
   * @return true iff this Op is indexed
   */
  bool isIndexedHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /* The kind of this operator. */
  Kind d_kind;

  /**
   * The internal expression wrapped by this operator.
   * This is a shared_ptr rather than a unique_ptr to avoid overhead due to
   * memory allocation (CVC4::Expr is already ref counted, so this could be
   * a unique_ptr instead).
   */
  std::shared_ptr<CVC4::Expr> d_expr;
};

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

/**
 * A CVC4 Term.
 */
class CVC4_PUBLIC Term
{
  friend class Datatype;
  friend class DatatypeConstructor;
  friend class Solver;
  friend class Grammar;
  friend struct TermHashFunction;

 public:
  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param e the internal expression that is to be wrapped by this term
   * @return the Term
   */
  Term(const Solver* slv, const CVC4::Expr& e);

  /**
   * Constructor.
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
   * Comparison for ordering on terms.
   * @param t the term to compare to
   * @return true if this term is less than t
   */
  bool operator<(const Term& t) const;

  /**
   * Comparison for ordering on terms.
   * @param t the term to compare to
   * @return true if this term is greater than t
   */
  bool operator>(const Term& t) const;

  /**
   * Comparison for ordering on terms.
   * @param t the term to compare to
   * @return true if this term is less than or equal to t
   */
  bool operator<=(const Term& t) const;

  /**
   * Comparison for ordering on terms.
   * @param t the term to compare to
   * @return true if this term is greater than or equal to t
   */
  bool operator>=(const Term& t) const;

  /**
   * Returns the number of children of this term.
   *
   * @return the number of term
   */
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
   * @return the result of replacing "e" by "replacement" in this term
   */
  Term substitute(Term e, Term replacement) const;

  /**
   * @return the result of simulatenously replacing "es" by "replacements" in
   * this term
   */
  Term substitute(const std::vector<Term> es,
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
   * @return true if this Term is a null term
   */
  bool isNull() const;

  /**
   * Check if this is a Term representing a constant.
   *
   * @return true if a constant Term
   */
  bool isConst() const;

  /**
   *  Return the base (element stored at all indices) of a constant array
   *  throws an exception if the kind is not CONST_ARRAY
   *  @return the base value
   */
  Term getConstArrayBase() const;

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
  class const_iterator : public std::iterator<std::input_iterator_tag, Term>
  {
    friend class Term;

   public:
    /**
     * Null Constructor.
     */
    const_iterator();

    /**
     * Constructor
     * @param slv the associated solver object
     * @param e a shared pointer to the expression that we're iterating over
     * @param p the position of the iterator (e.g. which child it's on)
     */
    const_iterator(const Solver* slv,
                   const std::shared_ptr<CVC4::Expr>& e,
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
    /* The original expression to be iterated over */
    std::shared_ptr<CVC4::Expr> d_orig_expr;
    /* Keeps track of the iteration position */
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

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  CVC4::Expr getExpr(void) const;

 protected:
  /**
   * The associated solver object.
   */
  const Solver* d_solver;

 private:
  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC4_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The internal expression wrapped by this term.
   * This is a shared_ptr rather than a unique_ptr to avoid overhead due to
   * memory allocation (CVC4::Expr is already ref counted, so this could be
   * a unique_ptr instead).
   */
  std::shared_ptr<CVC4::Expr> d_expr;
};

/**
 * Hash function for Terms.
 */
struct CVC4_PUBLIC TermHashFunction
{
  size_t operator()(const Term& t) const;
};

/**
 * Serialize a term to given stream.
 * @param out the output stream
 * @param t the term to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Term& t) CVC4_PUBLIC;

/**
 * Serialize a vector of terms to given stream.
 * @param out the output stream
 * @param vector the vector of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::vector<Term>& vector) CVC4_PUBLIC;

/**
 * Serialize a set of terms to the given stream.
 * @param out the output stream
 * @param set the set of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::set<Term>& set) CVC4_PUBLIC;

/**
 * Serialize an unordered_set of terms to the given stream.
 *
 * @param out the output stream
 * @param unordered_set the set of terms to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_set<Term, TermHashFunction>&
                             unordered_set) CVC4_PUBLIC;

/**
 * Serialize a map of terms to the given stream.
 *
 * @param out the output stream
 * @param map the map of terms to be serialized to the given stream
 * @return the output stream
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::map<Term, V>& map) CVC4_PUBLIC;

/**
 * Serialize an unordered_map of terms to the given stream.
 *
 * @param out the output stream
 * @param unordered_map the map of terms to be serialized to the given stream
 * @return the output stream
 */
template <typename V>
std::ostream& operator<<(std::ostream& out,
                         const std::unordered_map<Term, V, TermHashFunction>&
                             unordered_map) CVC4_PUBLIC;

/**
 * Serialize an operator to given stream.
 * @param out the output stream
 * @param t the operator to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Op& t) CVC4_PUBLIC;

/**
 * Hash function for Ops.
 */
struct CVC4_PUBLIC OpHashFunction
{
  size_t operator()(const Op& t) const;
};

/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

class DatatypeConstructorIterator;
class DatatypeIterator;

/**
 * A CVC4 datatype constructor declaration.
 */
class CVC4_PUBLIC DatatypeConstructorDecl
{
  friend class DatatypeDecl;
  friend class Solver;

 public:
  /**
   * Nullary constructor for Cython.
   */
  DatatypeConstructorDecl();

  /**
   * Add datatype selector declaration.
   * @param name the name of the datatype selector declaration to add
   * @param sort the range sort of the datatype selector declaration to add
   */
  void addSelector(const std::string& name, Sort sort);
  /**
   * Add datatype selector declaration whose range type is the datatype itself.
   * @param name the name of the datatype selector declaration to add
   */
  void addSelectorSelf(const std::string& name);

  /**
   * @return a string representation of this datatype constructor declaration
   */
  std::string toString() const;

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  const CVC4::DatatypeConstructor& getDatatypeConstructor(void) const;

 private:
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param name the name of the datatype constructor
   * @return the DatatypeConstructorDecl
   */
  DatatypeConstructorDecl(const Solver* slv, const std::string& name);

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal (intermediate) datatype constructor wrapped by this
   * datatype constructor declaration.
   * This is a shared_ptr rather than a unique_ptr since
   * CVC4::DatatypeConstructor is not ref counted.
   */
  std::shared_ptr<CVC4::DatatypeConstructor> d_ctor;
};

class Solver;
/**
 * A CVC4 datatype declaration.
 */
class CVC4_PUBLIC DatatypeDecl
{
  friend class DatatypeConstructorArg;
  friend class Solver;
  friend class Grammar;

 public:
  /**
   * Nullary constructor for Cython.
   */
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

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  CVC4::Datatype& getDatatype(void) const;

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
               Sort param,
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

  /**
   * Helper for isNull checks. This prevents calling an API function with
   * CVC4_API_CHECK_NOT_NULL
   */
  bool isNullHelper() const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /* The internal (intermediate) datatype wrapped by this datatype
   * declaration
   * This is a shared_ptr rather than a unique_ptr since CVC4::Datatype is
   * not ref counted.
   */
  std::shared_ptr<CVC4::Datatype> d_dtype;
};

/**
 * A CVC4 datatype selector.
 */
class CVC4_PUBLIC DatatypeSelector
{
  friend class DatatypeConstructor;
  friend class Solver;

 public:
  /**
   * Constructor.
   */
  DatatypeSelector();

  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor.
   * @param slv the associated solver object
   * @param stor the internal datatype selector to be wrapped
   * @return the DatatypeSelector
   */
  DatatypeSelector(const Solver* slv, const CVC4::DatatypeConstructorArg& stor);

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

  /** @return the range sort of this argument. */
  Sort getRangeSort() const;

  /**
   * @return a string representation of this datatype selector
   */
  std::string toString() const;

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  CVC4::DatatypeConstructorArg getDatatypeConstructorArg(void) const;

 private:
  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal datatype selector wrapped by this datatype selector.
   * This is a shared_ptr rather than a unique_ptr since CVC4::Datatype is
   * not ref counted.
   */
  std::shared_ptr<CVC4::DatatypeConstructorArg> d_stor;
};

/**
 * A CVC4 datatype constructor.
 */
class CVC4_PUBLIC DatatypeConstructor
{
  friend class Datatype;
  friend class Solver;

 public:
  /**
   * Constructor.
   */
  DatatypeConstructor();

  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor.
   * @param ctor the internal datatype constructor to be wrapped
   * @return the DatatypeConstructor
   */
  DatatypeConstructor(const Solver* slv, const CVC4::DatatypeConstructor& ctor);

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
   * @return a string representation of this datatype constructor
   */
  std::string toString() const;

  /**
   * Iterator for the selectors of a datatype constructor.
   */
  class const_iterator
      : public std::iterator<std::input_iterator_tag, DatatypeConstructor>
  {
    friend class DatatypeConstructor;  // to access constructor

   public:
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
     * @param true if this is a begin() iterator
     */
    const_iterator(const Solver* slv,
                   const CVC4::DatatypeConstructor& ctor,
                   bool begin);

    /**
     * The associated solver object.
     */
    const Solver* d_solver;

    /* A pointer to the list of selectors of the internal datatype
     * constructor to iterate over.
     * This pointer is maintained for operators == and != only. */
    const void* d_int_stors;

    /* The list of datatype selector (wrappers) to iterate over. */
    std::vector<DatatypeSelector> d_stors;

    /* The current index of the iterator. */
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

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  const CVC4::DatatypeConstructor& getDatatypeConstructor(void) const;

 private:
  /**
   * Return selector for name.
   * @param name The name of selector to find
   * @return the selector object for the name
   */
  DatatypeSelector getSelectorForName(const std::string& name) const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal datatype constructor wrapped by this datatype constructor.
   * This is a shared_ptr rather than a unique_ptr since CVC4::Datatype is
   * not ref counted.
   */
  std::shared_ptr<CVC4::DatatypeConstructor> d_ctor;
};

/*
 * A CVC4 datatype.
 */
class CVC4_PUBLIC Datatype
{
  friend class Solver;
  friend class Sort;

 public:
  // !!! This constructor is only temporarily public until the parser is fully
  // migrated to the new API. !!!
  /**
   * Constructor.
   * @param dtype the internal datatype to be wrapped
   * @return the Datatype
   */
  Datatype(const Solver* slv, const CVC4::Datatype& dtype);

  // Nullary constructor for Cython
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
   * @return a string representation of this datatype
   */
  std::string toString() const;

  /**
   * Iterator for the constructors of a datatype.
   */
  class const_iterator : public std::iterator<std::input_iterator_tag, Datatype>
  {
    friend class Datatype;  // to access constructor

   public:
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
     * @param true if this is a begin() iterator
     */
    const_iterator(const Solver* slv, const CVC4::Datatype& dtype, bool begin);

    /**
     * The associated solver object.
     */
    const Solver* d_solver;

    /* A pointer to the list of constructors of the internal datatype
     * to iterate over.
     * This pointer is maintained for operators == and != only. */
    const void* d_int_ctors;

    /* The list of datatype constructor (wrappers) to iterate over. */
    std::vector<DatatypeConstructor> d_ctors;

    /* The current index of the iterator. */
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

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  const CVC4::Datatype& getDatatype(void) const;

 private:
  /**
   * Return constructor for name.
   * @param name The name of constructor to find
   * @return the constructor object for the name
   */
  DatatypeConstructor getConstructorForName(const std::string& name) const;

  /**
   * The associated solver object.
   */
  const Solver* d_solver;

  /**
   * The internal datatype wrapped by this datatype.
   * This is a shared_ptr rather than a unique_ptr since CVC4::Datatype is
   * not ref counted.
   */
  std::shared_ptr<CVC4::Datatype> d_dtype;
};

/**
 * Serialize a datatype declaration to given stream.
 * @param out the output stream
 * @param dtdecl the datatype declaration to be serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeDecl& dtdecl) CVC4_PUBLIC;

/**
 * Serialize a datatype constructor declaration to given stream.
 * @param out the output stream
 * @param ctordecl the datatype constructor declaration to be serialized
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructorDecl& ctordecl) CVC4_PUBLIC;

/**
 * Serialize a vector of datatype constructor declarations to given stream.
 * @param out the output stream
 * @param vector the vector of datatype constructor declarations to be
 * serialized to the given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const std::vector<DatatypeConstructorDecl>& vector);

/**
 * Serialize a datatype to given stream.
 * @param out the output stream
 * @param dtdecl the datatype to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const Datatype& dtype) CVC4_PUBLIC;

/**
 * Serialize a datatype constructor to given stream.
 * @param out the output stream
 * @param ctor the datatype constructor to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructor& ctor) CVC4_PUBLIC;

/**
 * Serialize a datatype selector to given stream.
 * @param out the output stream
 * @param ctor the datatype selector to be serialized to given stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelector& stor) CVC4_PUBLIC;

/* -------------------------------------------------------------------------- */
/* Grammar                                                                    */
/* -------------------------------------------------------------------------- */

/**
 * A Sygus Grammar.
 */
class CVC4_PUBLIC Grammar
{
  friend class Solver;

 public:
  /**
   * Add <rule> to the set of rules corresponding to <ntSymbol>.
   * @param ntSymbol the non-terminal to which the rule is added
   * @param rule the rule to add
   */
  void addRule(Term ntSymbol, Term rule);

  /**
   * Allow <ntSymbol> to be an arbitrary constant.
   * @param ntSymbol the non-terminal allowed to be any constant
   */
  void addAnyConstant(Term ntSymbol);

  /**
   * Allow <ntSymbol> to be any input variable to corresponding
   * synth-fun/synth-inv with the same sort as <ntSymbol>.
   * @param ntSymbol the non-terminal allowed to be any input constant
   */
  void addAnyVariable(Term ntSymbol);

  /**
   * Add <rules> to the set of rules corresponding to <ntSymbol>.
   * @param ntSymbol the non-terminal to which the rules are added
   * @param rule the rules to add
   */
  void addRules(Term ntSymbol, std::vector<Term> rules);

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
   * Returns the resolved datatype of the Start symbol of the grammar.
   * @return the resolved datatype of the Start symbol of the grammar
   */
  Sort resolve();

  /**
   * Adds a constructor to sygus datatype <dt> whose sygus operator is <term>.
   *
   * <ntsToUnres> contains a mapping from non-terminal symbols to the
   * unresolved sorts they correspond to. This map indicates how the argument
   * <term> should be interpreted (instances of symbols from the domain of
   * <ntsToUnres> correspond to constructor arguments).
   *
   * The sygus operator that is actually added to <dt> corresponds to replacing
   * each occurrence of non-terminal symbols from the domain of <ntsToUnres>
   * with bound variables via purifySygusGTerm, and binding these variables
   * via a lambda.
   *
   * @param dt the non-terminal's datatype to which a constructor is added
   * @param term the sygus operator of the constructor
   * @param ntsToUnres mapping from non-terminals to their unresolved sorts
   */
  void addSygusConstructorTerm(
      DatatypeDecl& dt,
      Term term,
      const std::unordered_map<Term, Sort, TermHashFunction>& ntsToUnres) const;

  /** Purify sygus grammar term
   *
   * This returns a term where all occurrences of non-terminal symbols (those
   * in the domain of <ntsToUnres>) are replaced by fresh variables. For
   * each variable replaced in this way, we add the fresh variable it is
   * replaced with to <args>, and the unresolved sorts corresponding to the
   * non-terminal symbol to <cargs> (constructor args). In other words, <args>
   * contains the free variables in the term returned by this method (which
   * should be bound by a lambda), and <cargs> contains the sorts of the
   * arguments of the sygus constructor.
   *
   * @param term the term to purify
   * @param args the free variables in the term returned by this method
   * @param cargs the sorts of the arguments of the sygus constructor
   * @param ntsToUnres mapping from non-terminals to their unresolved sorts
   * @return the purfied term
   */
  Term purifySygusGTerm(
      Term term,
      std::vector<Term>& args,
      std::vector<Sort>& cargs,
      const std::unordered_map<Term, Sort, TermHashFunction>& ntsToUnres) const;

  /**
   * This adds constructors to <dt> for sygus variables in <d_sygusVars> whose
   * sort is argument <sort>. This method should be called when the sygus
   * grammar term (Variable sort) is encountered.
   *
   * @param dt the non-terminal's datatype to which the constructors are added
   * @param sort the sort of the sygus variables to add
   */
  void addSygusConstructorVariables(DatatypeDecl& dt, Sort sort) const;

  /** The solver that created this grammar. */
  const Solver* d_solver;
  /** Input variables to the corresponding function/invariant to synthesize.*/
  std::vector<Term> d_sygusVars;
  /** The non-terminal symbols of this grammar. */
  std::vector<Term> d_ntSyms;
  /** The mapping from non-terminal symbols to their production terms. */
  std::unordered_map<Term, std::vector<Term>, TermHashFunction> d_ntsToTerms;
  /** The set of non-terminals that can be arbitrary constants. */
  std::unordered_set<Term, TermHashFunction> d_allowConst;
  /** The set of non-terminals that can be sygus variables. */
  std::unordered_set<Term, TermHashFunction> d_allowVars;
  /** Did we call resolve() before? */
  bool d_isResolved;
};

/* -------------------------------------------------------------------------- */
/* Rounding Mode for Floating Points                                          */
/* -------------------------------------------------------------------------- */

/**
 * A CVC4 floating point rounding mode.
 */
enum CVC4_PUBLIC RoundingMode
{
  ROUND_NEAREST_TIES_TO_EVEN,
  ROUND_TOWARD_POSITIVE,
  ROUND_TOWARD_NEGATIVE,
  ROUND_TOWARD_ZERO,
  ROUND_NEAREST_TIES_TO_AWAY,
};

/**
 * Hash function for RoundingModes.
 */
struct CVC4_PUBLIC RoundingModeHashFunction
{
  inline size_t operator()(const RoundingMode& rm) const;
};

/* -------------------------------------------------------------------------- */
/* Solver                                                                     */
/* -------------------------------------------------------------------------- */

/*
 * A CVC4 solver.
 */
class CVC4_PUBLIC Solver
{
 public:
  /* .................................................................... */
  /* Constructors/Destructors                                             */
  /* .................................................................... */

  /**
   * Constructor.
   * @param opts a pointer to a solver options object (for parser only)
   * @return the Solver
   */
  Solver(Options* opts = nullptr);

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
   * @return sort Integer (in CVC4, Integer is a subtype of Real)
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
  Sort getRoundingmodeSort() const;

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
  Sort mkArraySort(Sort indexSort, Sort elemSort) const;

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
  Sort mkDatatypeSort(DatatypeDecl dtypedecl) const;

  /**
   * Create a vector of datatype sorts. The names of the datatype declarations
   * must be distinct.
   *
   * @param dtypedecls the datatype declarations from which the sort is created
   * @return the datatype sorts
   */
  std::vector<Sort> mkDatatypeSorts(
      std::vector<DatatypeDecl>& dtypedecls) const;

  /**
   * Create a vector of datatype sorts using unresolved sorts. The names of
   * the datatype declarations in dtypedecls must be distinct.
   *
   * This method is called when the DatatypeDecl objects dtypedecls have been
   * built using "unresolved" sorts.
   *
   * We associate each sort in unresolvedSorts with exacly one datatype from
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
  std::vector<Sort> mkDatatypeSorts(std::vector<DatatypeDecl>& dtypedecls,
                                    std::set<Sort>& unresolvedSorts) const;

  /**
   * Create function sort.
   * @param domain the sort of the fuction argument
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  Sort mkFunctionSort(Sort domain, Sort codomain) const;

  /**
   * Create function sort.
   * @param sorts the sort of the function arguments
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  Sort mkFunctionSort(const std::vector<Sort>& sorts, Sort codomain) const;

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
  Sort mkSetSort(Sort elemSort) const;

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
  Term mkTerm(Kind kind, Term child) const;

  /**
   * Create binary term of given kind.
   * @param kind the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @return the Term
   */
  Term mkTerm(Kind kind, Term child1, Term child2) const;

  /**
   * Create ternary term of given kind.
   * @param kind the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @param child3 the third child of the term
   * @return the Term
   */
  Term mkTerm(Kind kind, Term child1, Term child2, Term child3) const;

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
   * @param the operator
   * @return the Term
   */
  Term mkTerm(Op op) const;

  /**
   * Create unary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param the operator
   * @child the child of the term
   * @return the Term
   */
  Term mkTerm(Op op, Term child) const;

  /**
   * Create binary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param the operator
   * @child1 the first child of the term
   * @child2 the second child of the term
   * @return the Term
   */
  Term mkTerm(Op op, Term child1, Term child2) const;

  /**
   * Create ternary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param the operator
   * @child1 the first child of the term
   * @child2 the second child of the term
   * @child3 the third child of the term
   * @return the Term
   */
  Term mkTerm(Op op, Term child1, Term child2, Term child3) const;

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param kind the kind of the term
   * @param the operator
   * @children the children of the term
   * @return the Term
   */
  Term mkTerm(Op op, const std::vector<Term>& children) const;

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
   *   - RECORD_UPDATE
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
   * Create a real constant from a string.
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123") or real constant (e.g., "12.34" or "12/34").
   * @return a constant of sort Real or Integer (if 's' represents an integer)
   */
  Term mkReal(const char* s) const;

  /**
   * Create a real constant from a string.
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123") or real constant (e.g., "12.34" or "12/34").
   * @return a constant of sort Real or Integer (if 's' represents an integer)
   */
  Term mkReal(const std::string& s) const;

  /**
   * Create a real constant from an integer.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  Term mkReal(int32_t val) const;

  /**
   * Create a real constant from an integer.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  Term mkReal(int64_t val) const;

  /**
   * Create a real constant from an unsigned integer.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  Term mkReal(uint32_t val) const;

  /**
   * Create a real constant from an unsigned integer.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  Term mkReal(uint64_t val) const;

  /**
   * Create a real constant from a rational.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return a constant of sort Real or Integer (if 'num' is divisible by 'den')
   */
  Term mkReal(int32_t num, int32_t den) const;

  /**
   * Create a real constant from a rational.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return a constant of sort Real or Integer (if 'num' is divisible by 'den')
   */
  Term mkReal(int64_t num, int64_t den) const;

  /**
   * Create a real constant from a rational.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return a constant of sort Real or Integer (if 'num' is divisible by 'den')
   */
  Term mkReal(uint32_t num, uint32_t den) const;

  /**
   * Create a real constant from a rational.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return a constant of sort Real or Integer (if 'num' is divisible by 'den')
   */
  Term mkReal(uint64_t num, uint64_t den) const;

  /**
   * Create a regular expression empty term.
   * @return the empty term
   */
  Term mkRegexpEmpty() const;

  /**
   * Create a regular expression sigma term.
   * @return the sigma term
   */
  Term mkRegexpSigma() const;

  /**
   * Create a constant representing an empty set of the given sort.
   * @param s the sort of the set elements.
   * @return the empty set constant
   */
  Term mkEmptySet(Sort s) const;

  /**
   * Create a separation logic nil term.
   * @param sort the sort of the nil term
   * @return the separation logic nil term
   */
  Term mkSepNil(Sort sort) const;

  /**
   * Create a String constant.
   * @param s the string this constant represents
   * @param useEscSequences determines whether escape sequences in \p s should
   * be converted to the corresponding character
   * @return the String constant
   */
  Term mkString(const char* s, bool useEscSequences = false) const;

  /**
   * Create a String constant.
   * @param s the string this constant represents
   * @param useEscSequences determines whether escape sequences in \p s should
   * be converted to the corresponding character
   * @return the String constant
   */
  Term mkString(const std::string& s, bool useEscSequences = false) const;

  /**
   * Create a String constant.
   * @param c the character this constant represents
   * @return the String constant
   */
  Term mkString(const unsigned char c) const;

  /**
   * Create a String constant.
   * @param s a list of unsigned values this constant represents as string
   * @return the String constant
   */
  Term mkString(const std::vector<unsigned>& s) const;

  /**
   * Create a character constant from a given string.
   * @param s the string denoting the code point of the character (in base 16)
   * @return the character constant
   */
  Term mkChar(const std::string& s) const;

  /**
   * Create a character constant from a given string.
   * @param s the string denoting the code point of the character (in base 16)
   * @return the character constant
   */
  Term mkChar(const char* s) const;

  /**
   * Create a universe set of the given sort.
   * @param sort the sort of the set elements
   * @return the universe set constant
   */
  Term mkUniverseSet(Sort sort) const;

  /**
   * Create a bit-vector constant of given size and value.
   * @param size the bit-width of the bit-vector sort
   * @param val the value of the constant
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size, uint64_t val = 0) const;

  /**
   * Create a bit-vector constant from a given string.
   * @param s the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  Term mkBitVector(const char* s, uint32_t base = 2) const;

  /**
   * Create a bit-vector constant from a given string of base 2, 10 or 16.
   *
   * The size of resulting bit-vector is
   * - base  2: the size of the binary string
   * - base 10: the min. size required to represent the decimal as a bit-vector
   * - base 16: the max. size required to represent the hexadecimal as a
   *            bit-vector (4 * size of the given value string)
   *
   * @param s the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  Term mkBitVector(const std::string& s, uint32_t base = 2) const;

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   *
   * @param size the bit-width of the constant
   * @param s the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size, const char* s, uint32_t base) const;

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   * @param size the bit-width of the constant
   * @param s the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size, std::string& s, uint32_t base) const;

  /**
   * Create a constant array with the provided constant value stored at every
   * index
   * @param sort the sort of the constant array (must be an array sort)
   * @param val the constant value to store (must match the sort's element sort)
   * @return the constant array term
   */
  Term mkConstArray(Sort sort, Term val) const;

  /**
   * Create a positive infinity floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkPosInf(uint32_t exp, uint32_t sig) const;

  /**
   * Create a negative infinity floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNegInf(uint32_t exp, uint32_t sig) const;

  /**
   * Create a not-a-number (NaN) floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkNaN(uint32_t exp, uint32_t sig) const;

  /**
   * Create a positive zero (+0.0) floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  Term mkPosZero(uint32_t exp, uint32_t sig) const;

  /**
   * Create a negative zero (-0.0) floating-point constant. Requires CVC4 to be
   * compiled with SymFPU support.
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
   * @param arg1 Sort of the constant
   * @param arg2 Index of the constant
   */
  Term mkUninterpretedConst(Sort sort, int32_t index) const;

  /**
   * Create an abstract value constant.
   * @param index Index of the abstract value
   */
  Term mkAbstractValue(const std::string& index) const;

  /**
   * Create an abstract value constant.
   * @param index Index of the abstract value
   */
  Term mkAbstractValue(uint64_t index) const;

  /**
   * Create a floating-point constant (requires CVC4 to be compiled with symFPU
   * support).
   * @param exp Size of the exponent
   * @param sig Size of the significand
   * @param val Value of the floating-point constant as a bit-vector term
   */
  Term mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const;

  /* .................................................................... */
  /* Create Variables                                                     */
  /* .................................................................... */

  /**
   * Create (first-order) constant (0-arity function symbol).
   * SMT-LIB: ( declare-const <symbol> <sort> )
   * SMT-LIB: ( declare-fun <symbol> ( ) <sort> )
   *
   * @param sort the sort of the constant
   * @param symbol the name of the constant
   * @return the first-order constant
   */
  Term mkConst(Sort sort, const std::string& symbol = std::string()) const;

  /**
   * Create (bound) variable.
   * @param sort the sort of the variable
   * @param symbol the name of the variable
   * @return the variable
   */
  Term mkVar(Sort sort, const std::string& symbol = std::string()) const;

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
   * SMT-LIB: ( assert <term> )
   * @param term the formula to assert
   */
  void assertFormula(Term term) const;

  /**
   * Check satisfiability.
   * SMT-LIB: ( check-sat )
   * @return the result of the satisfiability check.
   */
  Result checkSat() const;

  /**
   * Check satisfiability assuming the given formula.
   * SMT-LIB: ( check-sat-assuming ( <prop_literal> ) )
   * @param assumption the formula to assume
   * @return the result of the satisfiability check.
   */
  Result checkSatAssuming(Term assumption) const;

  /**
   * Check satisfiability assuming the given formulas.
   * SMT-LIB: ( check-sat-assuming ( <prop_literal>+ ) )
   * @param assumptions the formulas to assume
   * @return the result of the satisfiability check.
   */
  Result checkSatAssuming(const std::vector<Term>& assumptions) const;

  /**
   * Check entailment of the given formula w.r.t. the current set of assertions.
   * @param term the formula to check entailment for
   * @return the result of the entailment check.
   */
  Result checkEntailed(Term term) const;

  /**
   * Check entailment of the given set of given formulas w.r.t. the current
   * set of assertions.
   * @param terms the terms to check entailment for
   * @return the result of the entailmentcheck.
   */
  Result checkEntailed(const std::vector<Term>& terms) const;

  /**
   * Create datatype sort.
   * SMT-LIB: ( declare-datatype <symbol> <datatype_decl> )
   * @param symbol the name of the datatype sort
   * @param ctors the constructor declarations of the datatype sort
   * @return the datatype sort
   */
  Sort declareDatatype(const std::string& symbol,
                       const std::vector<DatatypeConstructorDecl>& ctors) const;

  /**
   * Declare n-ary function symbol.
   * SMT-LIB: ( declare-fun <symbol> ( <sort>* ) <sort> )
   * @param symbol the name of the function
   * @param sorts the sorts of the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  Term declareFun(const std::string& symbol,
                  const std::vector<Sort>& sorts,
                  Sort sort) const;

  /**
   * Declare uninterpreted sort.
   * SMT-LIB: ( declare-sort <symbol> <numeral> )
   * @param symbol the name of the sort
   * @param arity the arity of the sort
   * @return the sort
   */
  Sort declareSort(const std::string& symbol, uint32_t arity) const;

  /**
   * Define n-ary function.
   * SMT-LIB: ( define-fun <function_def> )
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
                 Sort sort,
                 Term term,
                 bool global = false) const;
  /**
   * Define n-ary function.
   * SMT-LIB: ( define-fun <function_def> )
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  Term defineFun(Term fun,
                 const std::vector<Term>& bound_vars,
                 Term term,
                 bool global = false) const;

  /**
   * Define recursive function.
   * SMT-LIB: ( define-fun-rec <function_def> )
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
                    Sort sort,
                    Term term,
                    bool global = false) const;

  /**
   * Define recursive function.
   * SMT-LIB: ( define-fun-rec <function_def> )
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  Term defineFunRec(Term fun,
                    const std::vector<Term>& bound_vars,
                    Term term,
                    bool global = false) const;

  /**
   * Define recursive functions.
   * SMT-LIB: ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * Create elements of parameter 'funs' with mkConst().
   * @param funs the sorted functions
   * @param bound_vars the list of parameters to the functions
   * @param term the list of function bodies of the functions
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
   * SMT-LIB: ( echo <std::string> )
   * @param out the output stream
   * @param str the string to echo
   */
  void echo(std::ostream& out, const std::string& str) const;

  /**
   * Get the list of asserted formulas.
   * SMT-LIB: ( get-assertions )
   * @return the list of asserted formulas
   */
  std::vector<Term> getAssertions() const;

  /**
   * Get the assignment of asserted formulas.
   * SMT-LIB: ( get-assignment )
   * Requires to enable option 'produce-assignments'.
   * @return a list of formula-assignment pairs
   */
  std::vector<std::pair<Term, Term>> getAssignment() const;

  /**
   * Get info from the solver.
   * SMT-LIB: ( get-info <info_flag> )
   * @return the info
   */
  std::string getInfo(const std::string& flag) const;

  /**
   * Get the value of a given option.
   * SMT-LIB: ( get-option <keyword> )
   * @param option the option for which the value is queried
   * @return a string representation of the option value
   */
  std::string getOption(const std::string& option) const;

  /**
   * Get the set of unsat ("failed") assumptions.
   * SMT-LIB: ( get-unsat-assumptions )
   * Requires to enable option 'produce-unsat-assumptions'.
   * @return the set of unsat assumptions.
   */
  std::vector<Term> getUnsatAssumptions() const;

  /**
   * Get the unsatisfiable core.
   * SMT-LIB: ( get-unsat-core )
   * Requires to enable option 'produce-unsat-cores'.
   * @return a set of terms representing the unsatisfiable core
   */
  std::vector<Term> getUnsatCore() const;

  /**
   * Get the value of the given term.
   * SMT-LIB: ( get-value ( <term> ) )
   * @param term the term for which the value is queried
   * @return the value of the given term
   */
  Term getValue(Term term) const;
  /**
   * Get the values of the given terms.
   * SMT-LIB: ( get-value ( <term>+ ) )
   * @param terms the terms for which the value is queried
   * @return the values of the given terms
   */
  std::vector<Term> getValue(const std::vector<Term>& terms) const;

  /**
   * Pop (a) level(s) from the assertion stack.
   * SMT-LIB: ( pop <numeral> )
   * @param nscopes the number of levels to pop
   */
  void pop(uint32_t nscopes = 1) const;

  /**
   * Print the model of a satisfiable query to the given output stream.
   * Requires to enable option 'produce-models'.
   * @param out the output stream
   */
  void printModel(std::ostream& out) const;

  /**
   * Push (a) level(s) to the assertion stack.
   * SMT-LIB: ( push <numeral> )
   * @param nscopes the number of levels to push
   */
  void push(uint32_t nscopes = 1) const;

  /**
   * Remove all assertions.
   * SMT-LIB: ( reset-assertions )
   */
  void resetAssertions() const;

  /**
   * Set info.
   * SMT-LIB: ( set-info <attribute> )
   * @param keyword the info flag
   * @param value the value of the info flag
   */
  void setInfo(const std::string& keyword, const std::string& value) const;

  /**
   * Set logic.
   * SMT-LIB: ( set-logic <symbol> )
   * @param logic the logic to set
   */
  void setLogic(const std::string& logic) const;

  /**
   * Set option.
   * SMT-LIB: ( set-option <option> )
   * @param option the option name
   * @param value the option value
   */
  void setOption(const std::string& option, const std::string& value) const;

  /**
   * If needed, convert this term to a given sort. Note that the sort of the
   * term must be convertible into the target sort. Currently only Int to Real
   * conversions are supported.
   * @param s the target sort
   * @return the term wrapped into a sort conversion if needed
   */
  Term ensureTermSort(const Term& t, const Sort& s) const;

  /**
   * Append <symbol> to the current list of universal variables.
   * SyGuS v2: ( declare-var <symbol> <sort> )
   * @param sort the sort of the universal variable
   * @param symbol the name of the universal variable
   * @return the universal variable
   */
  Term mkSygusVar(Sort sort, const std::string& symbol = std::string()) const;

  /**
   * Create a Sygus grammar.
   * @param boundVars the parameters to corresponding synth-fun/synth-inv
   * @param ntSymbols the pre-declaration of the non-terminal symbols
   * @return the grammar
   */
  Grammar mkSygusGrammar(const std::vector<Term>& boundVars,
                         const std::vector<Term>& ntSymbols) const;

  /**
   * Synthesize n-ary function.
   * SyGuS v2: ( synth-fun <symbol> ( <boundVars>* ) <sort> )
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  Term synthFun(const std::string& symbol,
                const std::vector<Term>& boundVars,
                Sort sort) const;

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   * SyGuS v2: ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param g the syntactic constraints
   * @return the function
   */
  Term synthFun(const std::string& symbol,
                const std::vector<Term>& boundVars,
                Sort sort,
                Grammar& g) const;

  /**
   * Synthesize invariant.
   * SyGuS v2: ( synth-inv <symbol> ( <boundVars>* ) )
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @param sort the sort of the return value of this invariant
   * @return the invariant
   */
  Term synthInv(const std::string& symbol,
                const std::vector<Term>& boundVars) const;

  /**
   * Synthesize invariant following specified syntactic constraints.
   * SyGuS v2: ( synth-inv <symbol> ( <boundVars>* ) <g> )
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @param sort the sort of the return value of this invariant
   * @param g the syntactic constraints
   * @return the invariant
   */
  Term synthInv(const std::string& symbol,
                const std::vector<Term>& boundVars,
                Grammar& g) const;

  /**
   * Add a forumla to the set of Sygus constraints.
   * SyGuS v2: ( constraint <term> )
   * @param term the formula to add as a constraint
   */
  void addSygusConstraint(Term term) const;

  /**
   * Add a set of Sygus constraints to the current state that correspond to an
   * invariant synthesis problem.
   * SyGuS v2: ( inv-constraint <inv> <pre> <trans> <post> )
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
   * SyGuS v2: ( check-synth )
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
   * Print solution for synthesis conjecture to the given output stream.
   * @param out the output stream
   */
  void printSynthSolution(std::ostream& out) const;

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  ExprManager* getExprManager(void) const;

  // !!! This is only temporarily available until the parser is fully migrated
  // to the new API. !!!
  SmtEngine* getSmtEngine(void) const;

 private:
  /* Helper to convert a vector of internal types to sorts. */
  std::vector<Type> sortVectorToTypes(const std::vector<Sort>& vector) const;
  /* Helper to convert a vector of sorts to internal types. */
  std::vector<Expr> termVectorToExprs(const std::vector<Term>& vector) const;
  /* Helper to check for API misuse in mkOp functions. */
  void checkMkTerm(Kind kind, uint32_t nchildren) const;
  /* Helper for mk-functions that call d_exprMgr->mkConst(). */
  template <typename T>
  Term mkValHelper(T t) const;
  /* Helper for mkReal functions that take a string as argument. */
  Term mkRealFromStrHelper(const std::string& s) const;
  /* Helper for mkBitVector functions that take a string as argument. */
  Term mkBVFromStrHelper(const std::string& s, uint32_t base) const;
  /* Helper for mkBitVector functions that take a string and a size as
   * arguments. */
  Term mkBVFromStrHelper(uint32_t size,
                         const std::string& s,
                         uint32_t base) const;
  /* Helper for mkBitVector functions that take an integer as argument. */
  Term mkBVFromIntHelper(uint32_t size, uint64_t val) const;
  /* Helper for setLogic. */
  void setLogicHelper(const std::string& logic) const;
  /* Helper for mkTerm functions that create Term from a Kind */
  Term mkTermFromKind(Kind kind) const;
  /* Helper for mkChar functions that take a string as argument. */
  Term mkCharFromStrHelper(const std::string& s) const;

  /**
   * Helper function that ensures that a given term is of sort real (as opposed
   * to being of sort integer).
   * @param term a term of sort integer or real
   * @return a term of sort real
   */
  Term ensureRealSort(Term expr) const;

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
   * Create a vector of datatype sorts, using unresolved sorts.
   * @param dtypedecls the datatype declarations from which the sort is created
   * @param unresolvedSorts the list of unresolved sorts
   * @return the datatype sorts
   */
  std::vector<Sort> mkDatatypeSortsInternal(
      std::vector<DatatypeDecl>& dtypedecls,
      std::set<Sort>& unresolvedSorts) const;

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   * SMT-LIB: ( synth-fun <symbol> ( <boundVars>* ) <sort> <g>? )
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param isInv determines whether this is synth-fun or synth-inv
   * @param g the syntactic constraints
   * @return the function
   */
  Term synthFunHelper(const std::string& symbol,
                      const std::vector<Term>& boundVars,
                      const Sort& sort,
                      bool isInv = false,
                      Grammar* g = nullptr) const;

  /* The expression manager of this solver. */
  std::unique_ptr<ExprManager> d_exprMgr;
  /* The SMT engine of this solver. */
  std::unique_ptr<SmtEngine> d_smtEngine;
  /* The random number generator of this solver. */
  std::unique_ptr<Random> d_rng;
};

// !!! Only temporarily public until the parser is fully migrated to the
// new API. !!!
std::vector<Expr> termVectorToExprs(const std::vector<Term>& terms);
std::vector<Type> sortVectorToTypes(const std::vector<Sort>& sorts);
std::set<Type> sortSetToTypes(const std::set<Sort>& sorts);
std::vector<Term> exprVectorToTerms(const Solver* slv,
                                    const std::vector<Expr>& terms);
std::vector<Sort> typeVectorToSorts(const Solver* slv,
                                    const std::vector<Type>& sorts);

}  // namespace api

// !!! Only temporarily public until the parser is fully migrated to the
// new API. !!!
CVC4::api::Kind intToExtKind(CVC4::Kind k);
CVC4::Kind extToIntKind(CVC4::api::Kind k);

}  // namespace CVC4
#endif
