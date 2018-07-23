/*********************                                                        */
/*! \file cvc4cpp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The CVC4 C++ API.
 **
 ** The CVC4 C++ API.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__API__CVC4CPP_H
#define __CVC4__API__CVC4CPP_H

#include "cvc4cppkind.h"

#include <map>
#include <memory>
#include <set>
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
   * Return true if corresponding query was a valid checkValid() or
   * checkValidAssuming() query.
   */
  bool isValid() const;

  /**
   * Return true if corresponding query was an invalid checkValid() or
   * checkValidAssuming() query.
   */
  bool isInvalid() const;

  /**
   * Return true if query was a checkValid() or checkValidAssuming() query
   * and CVC4 was not able to determine (in)validity.
   */
  bool isValidUnknown() const;

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

 private:
  /**
   * Constructor.
   * @param r the internal result that is to be wrapped by this result
   * @return the Result
   */
  Result(const CVC4::Result& r);

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
  friend class DatatypeSelectorDecl;
  friend class OpTerm;
  friend class Solver;
  friend struct SortHashFunction;
  friend class Term;

 public:
  /**
   * Destructor.
   */
  ~Sort();

  /**
   * Assignment operator.
   * @param s the sort to assign to this sort
   * @return this sort after assignment
   */
  Sort& operator=(const Sort& s);

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

 private:
  /**
   * Constructor.
   * @param t the internal type that is to be wrapped by this sort
   * @return the Sort
   */
  Sort(const CVC4::Type& t);

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
  friend struct TermHashFunction;

 public:
  /**
   * Constructor.
   */
  Term();

  /**
   * Destructor.
   */
  ~Term();

  /**
   * Assignment operator, makes a copy of the given term.
   * Both terms must belong to the same solver object.
   * @param t the term to assign
   * @return the reference to this term after assignment
   */
  Term& operator=(const Term& t);

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
   * @return the kind of this term
   */
  Kind getKind() const;

  /**
   * @return the sort of this term
   */
  Sort getSort() const;

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
   * Boolean if-and-only-if.
   * @param t a Boolean term
   * @return the Boolean equivalence of this term and the given term
   */
  Term iffTerm(const Term& t) const;

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
   */
  class const_iterator : public std::iterator<std::input_iterator_tag, Term>
  {
    friend class Term;

   public:
    /**
     * Constructor.
     */
    const_iterator();

    /**
     * Copy constructor.
     */
    const_iterator(const const_iterator& it);

    /**
     * Destructor.
     */
    ~const_iterator();

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
    /* The internal expression iterator wrapped by this iterator. */
    void* d_iterator;
    /* Constructor. */
    explicit const_iterator(void*);
  };

  /**
   * @return an iterator to the first child of this Term
   */
  const_iterator begin() const;

  /**
   * @return an iterator to one-off-the-last child of this Term
   */
  const_iterator end() const;

 private:
  /**
   * Constructor.
   * @param e the internal expression that is to be wrapped by this term
   * @return the Term
   */
  Term(const CVC4::Expr& e);

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

/* -------------------------------------------------------------------------- */
/* OpTerm                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * A CVC4 operator term.
 * An operator term is a term that represents certain operators, instantiated
 * with its required parameters, e.g., a term of kind BITVECTOR_EXTRACT.
 */
class CVC4_PUBLIC OpTerm
{
  friend class Solver;
  friend struct OpTermHashFunction;

 public:
  /**
   * Constructor.
   */
  OpTerm();

  /**
   * Destructor.
   */
  ~OpTerm();

  /**
   * Assignment operator, makes a copy of the given operator term.
   * Both terms must belong to the same solver object.
   * @param t the term to assign
   * @return the reference to this operator term after assignment
   */
  OpTerm& operator=(const OpTerm& t);

  /**
   * Syntactic equality operator.
   * Return true if both operator terms are syntactically identical.
   * Both operator terms must belong to the same solver object.
   * @param t the operator term to compare to for equality
   * @return true if the operator terms are equal
   */
  bool operator==(const OpTerm& t) const;

  /**
   * Syntactic disequality operator.
   * Return true if both operator terms differ syntactically.
   * Both terms must belong to the same solver object.
   * @param t the operator term to compare to for disequality
   * @return true if operator terms are disequal
   */
  bool operator!=(const OpTerm& t) const;

  /**
   * @return the kind of this operator term
   */
  Kind getKind() const;

  /**
   * @return the sort of this operator term
   */
  Sort getSort() const;

  /**
   * @return true if this operator term is a null term
   */
  bool isNull() const;

  /**
   * @return a string representation of this operator term
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param e the internal expression that is to be wrapped by this term
   * @return the Term
   */
  OpTerm(const CVC4::Expr& e);

  /**
   * The internal expression wrapped by this operator term.
   * This is a shared_ptr rather than a unique_ptr to avoid overhead due to
   * memory allocation (CVC4::Expr is already ref counted, so this could be
   * a unique_ptr instead).
   */
  std::shared_ptr<CVC4::Expr> d_expr;
};

/**
 * Serialize an operator term to given stream.
 * @param out the output stream
 * @param t the operator term to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, const OpTerm& t) CVC4_PUBLIC;

/**
 * Hash function for OpTerms.
 */
struct CVC4_PUBLIC OpTermHashFunction
{
  size_t operator()(const OpTerm& t) const;
};

/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

class DatatypeConstructorIterator;
class DatatypeIterator;

/**
 * A place-holder sort to allow a DatatypeDecl to refer to itself.
 * Self-sorted fields of DatatypeDecls will be properly sorted when a Sort is
 * created for the DatatypeDecl.
 */
class CVC4_PUBLIC DatatypeDeclSelfSort
{
};

/**
 * A CVC4 datatype selector declaration.
 */
class CVC4_PUBLIC DatatypeSelectorDecl
{
  friend class DatatypeConstructorDecl;

 public:
  /**
   * Constructor.
   * @param name the name of the datatype selector
   * @param sort the sort of the datatype selector
   * @return the DatatypeSelectorDecl
   */
  DatatypeSelectorDecl(const std::string& name, Sort sort);

  /**
   * Constructor.
   * @param name the name of the datatype selector
   * @param sort the sort of the datatype selector
   * @return the DAtatypeSelectorDecl
   */
  DatatypeSelectorDecl(const std::string& name, DatatypeDeclSelfSort sort);

  /**
   * @return a string representation of this datatype selector
   */
  std::string toString() const;

 private:
  /* The name of the datatype selector. */
  std::string d_name;
  /* The sort of the datatype selector. */
  Sort d_sort;
};

/**
 * A CVC4 datatype constructor declaration.
 */
class CVC4_PUBLIC DatatypeConstructorDecl
{
  friend class DatatypeDecl;

 public:
  /**
   * Constructor.
   * @param name the name of the datatype constructor
   * @return the DatatypeConstructorDecl
   */
  DatatypeConstructorDecl(const std::string& name);

  /**
   * Add datatype selector declaration.
   * @param stor the datatype selector declaration to add
   */
  void addSelector(const DatatypeSelectorDecl& stor);

  /**
   * @return a string representation of this datatype constructor declaration
   */
  std::string toString() const;

 private:
  /**
   * The internal (intermediate) datatype constructor wrapped by this
   * datatype constructor declaration.
   * This is a shared_ptr rather than a unique_ptr since
   * CVC4::DatatypeConstructor is not ref counted.
   */
  std::shared_ptr<CVC4::DatatypeConstructor> d_ctor;
};

/**
 * A CVC4 datatype declaration.
 */
class CVC4_PUBLIC DatatypeDecl
{
  friend class DatatypeConstructorArg;
  friend class Solver;

 public:
  /**
   * Constructor.
   * @param name the name of the datatype
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  DatatypeDecl(const std::string& name, bool isCoDatatype = false);

  /**
   * Constructor for parameterized datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param param the sort parameter
   * @param isCoDatatype true if a codatatype is to be constructed
   */
  DatatypeDecl(const std::string& name, Sort param, bool isCoDatatype = false);

  /**
   * Constructor for parameterized datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param params a list of sort parameters
   * @param isCoDatatype true if a codatatype is to be constructed
   */
  DatatypeDecl(const std::string& name,
               const std::vector<Sort>& params,
               bool isCoDatatype = false);

  /**
   * Destructor.
   */
  ~DatatypeDecl();

  /**
   * Add datatype constructor declaration.
   * @param ctor the datatype constructor declaration to add
   */
  void addConstructor(const DatatypeConstructorDecl& ctor);

  /**
   * @return a string representation of this datatype declaration
   */
  std::string toString() const;

 private:
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

  /**
   * Destructor.
   */
  ~DatatypeSelector();

  /**
   * @return a string representation of this datatype selector
   */
  std::string toString() const;

 private:
  /**
   * Constructor.
   * @param stor the internal datatype selector to be wrapped
   * @return the DatatypeSelector
   */
  DatatypeSelector(const CVC4::DatatypeConstructorArg& stor);

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

  /**
   * Destructor.
   */
  ~DatatypeConstructor();

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
     * @param ctor the internal datatype constructor to iterate over
     * @param true if this is a begin() iterator
     */
    const_iterator(const CVC4::DatatypeConstructor& ctor, bool begin);
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

 private:
  /**
   * Constructor.
   * @param ctor the internal datatype constructor to be wrapped
   * @return thte DatatypeConstructor
   */
  DatatypeConstructor(const CVC4::DatatypeConstructor& ctor);

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
  /**
   * Destructor.
   */
  ~Datatype();

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
     * @param dtype the internal datatype to iterate over
     * @param true if this is a begin() iterator
     */
    const_iterator(const CVC4::Datatype& dtype, bool begin);
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

 private:
  /**
   * Constructor.
   * @param dtype the internal datatype to be wrapped
   * @return the Datatype
   */
  Datatype(const CVC4::Datatype& dtype);

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
 * Serialize a datatype selector declaration to given stream.
 * @param out the output stream
 * @param stordecl the datatype selector declaration to be serialized
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelectorDecl& stordecl) CVC4_PUBLIC;

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
  Solver(const Solver&) CVC4_UNDEFINED;
  Solver& operator=(const Solver&) CVC4_UNDEFINED;

  /* .................................................................... */
  /* Sorts Handling                                                       */
  /* .................................................................... */

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
   * Create a datatype sort.
   * @param dtypedecl the datatype declaration from which the sort is created
   * @return the datatype sort
   */
  Sort mkDatatypeSort(DatatypeDecl dtypedecl) const;

  /**
   * Create function sort.
   * @param domain the sort of the fuction argument
   * @param range the sort of the function return value
   * @return the function sort
   */
  Sort mkFunctionSort(Sort domain, Sort range) const;

  /**
   * Create function sort.
   * @param argSorts the sort of the function arguments
   * @param range the sort of the function return value
   * @return the function sort
   */
  Sort mkFunctionSort(const std::vector<Sort>& argSorts, Sort range) const;

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
   * Create 0-ary term of given kind and sort.
   * @param kind the kind of the term
   * @param sort the sort argument to this kind
   * @return the Term
   */
  Term mkTerm(Kind kind, Sort sort) const;

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
   * Create term with no children from a given operator term.
   * Create operator terms with mkOpTerm().
   * @param the operator term
   * @return the Term
   */
  Term mkTerm(OpTerm opTerm) const;

  /**
   * Create unary term from a given operator term.
   * Create operator terms with mkOpTerm().
   * @param the operator term
   * @child the child of the term
   * @return the Term
   */
  Term mkTerm(OpTerm opTerm, Term child) const;

  /**
   * Create binary term from a given operator term.
   * Create operator terms with mkOpTerm().
   * @param the operator term
   * @child1 the first child of the term
   * @child2 the second child of the term
   * @return the Term
   */
  Term mkTerm(OpTerm opTerm, Term child1, Term child2) const;

  /**
   * Create ternary term from a given operator term.
   * Create operator terms with mkOpTerm().
   * @param the operator term
   * @child1 the first child of the term
   * @child2 the second child of the term
   * @child3 the third child of the term
   * @return the Term
   */
  Term mkTerm(OpTerm opTerm, Term child1, Term child2, Term child3) const;

  /**
   * Create n-ary term from a given operator term.
   * Create operator terms with mkOpTerm().
   * @param the operator term
   * @children the children of the term
   * @return the Term
   */
  Term mkTerm(OpTerm opTerm, const std::vector<Term>& children) const;

  /* .................................................................... */
  /* Create Operator Terms                                                */
  /* .................................................................... */

  /**
   * Create operator term of kind:
   *   - CHAIN_OP
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param k the kind argument to this operator
   */
  OpTerm mkOpTerm(Kind kind, Kind k);

  /**
   * Create operator of kind:
   *   - RECORD_UPDATE_OP
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg the string argument to this operator
   */
  OpTerm mkOpTerm(Kind kind, const std::string& arg);

  /**
   * Create operator of kind:
   *   - DIVISIBLE_OP
   *   - BITVECTOR_REPEAT_OP
   *   - BITVECTOR_ZERO_EXTEND_OP
   *   - BITVECTOR_SIGN_EXTEND_OP
   *   - BITVECTOR_ROTATE_LEFT_OP
   *   - BITVECTOR_ROTATE_RIGHT_OP
   *   - INT_TO_BITVECTOR_OP
   *   - FLOATINGPOINT_TO_UBV_OP
   *   - FLOATINGPOINT_TO_UBV_TOTAL_OP
   *   - FLOATINGPOINT_TO_SBV_OP
   *   - FLOATINGPOINT_TO_SBV_TOTAL_OP
   *   - TUPLE_UPDATE_OP
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg the uint32_t argument to this operator
   */
  OpTerm mkOpTerm(Kind kind, uint32_t arg);

  /**
   * Create operator of Kind:
   *   - BITVECTOR_EXTRACT_OP
   *   - FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP
   *   - FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP
   *   - FLOATINGPOINT_TO_FP_REAL_OP
   *   - FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP
   *   - FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP
   *   - FLOATINGPOINT_TO_FP_GENERIC_OP
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg1 the first uint32_t argument to this operator
   * @param arg2 the second uint32_t argument to this operator
   */
  OpTerm mkOpTerm(Kind kind, uint32_t arg1, uint32_t arg2);

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
   * Create an Integer constant.
   * @param s the string represetntation of the constant
   * @param base the base of the string representation
   * @return the Integer constant
   */
  Term mkInteger(const char* s, uint32_t base = 10) const;

  /**
   * Create an Integer constant.
   * @param s the string represetntation of the constant
   * @param base the base of the string representation
   * @return the Integer constant
   */
  Term mkInteger(const std::string& s, uint32_t base = 10) const;

  /**
   * Create an Integer constant.
   * @param val the value of the constant
   * @return the Integer constant
   */
  Term mkInteger(int32_t val) const;

  /**
   * Create an Integer constant.
   * @param val the value of the constant
   * @return the Integer constant
   */
  Term mkInteger(uint32_t val) const;

  /**
   * Create an Integer constant.
   * @param val the value of the constant
   * @return the Integer constant
   */
  Term mkInteger(int64_t val) const;

  /**
   * Create an Integer constant.
   * @param val the value of the constant
   * @return the Integer constant
   */
  Term mkInteger(uint64_t val) const;

  /**
   * Create a constant representing the number Pi.
   * @return a constant representing Pi
   */
  Term mkPi() const;

  /**
   * Create an Real constant.
   * @param s the string represetntation of the constant
   * @param base the base of the string representation
   * @return the Real constant
   */
  Term mkReal(const char* s, uint32_t base = 10) const;

  /**
   * Create an Real constant.
   * @param s the string represetntation of the constant
   * @param base the base of the string representation
   * @return the Real constant
   */
  Term mkReal(const std::string& s, uint32_t base = 10) const;

  /**
   * Create an Real constant.
   * @param val the value of the constant
   * @return the Real constant
   */
  Term mkReal(int32_t val) const;

  /**
   * Create an Real constant.
   * @param val the value of the constant
   * @return the Real constant
   */
  Term mkReal(int64_t val) const;

  /**
   * Create an Real constant.
   * @param val the value of the constant
   * @return the Real constant
   */
  Term mkReal(uint32_t val) const;

  /**
   * Create an Real constant.
   * @param val the value of the constant
   * @return the Real constant
   */
  Term mkReal(uint64_t val) const;

  /**
   * Create an Rational constant.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return the Rational constant
   */
  Term mkReal(int32_t num, int32_t den) const;

  /**
   * Create an Rational constant.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return the Rational constant
   */
  Term mkReal(int64_t num, int64_t den) const;

  /**
   * Create an Rational constant.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return the Rational constant
   */
  Term mkReal(uint32_t num, uint32_t den) const;

  /**
   * Create an Rational constant.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return the Rational constant
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
   * @return the String constant
   */
  Term mkString(const char* s) const;

  /**
   * Create a String constant.
   * @param s the string this constant represents
   * @return the String constant
   */
  Term mkString(const std::string& s) const;

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
   * Create a universe set of the given sort.
   * @param sort the sort of the set elements
   * @return the universe set constant
   */
  Term mkUniverseSet(Sort sort) const;

  /**
   * Create a bit-vector constant of given size with value 0.
   * @param size the bit-width of the bit-vector sort
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size) const;

  /**
   * Create a bit-vector constant of given size and value.
   * @param size the bit-width of the bit-vector sort
   * @param val the value of the constant
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size, uint32_t val) const;

  /**
   * Create a bit-vector constant of given size and value.
   * @param size the bit-width of the bit-vector sort
   * @param val the value of the constant
   * @return the bit-vector constant
   */
  Term mkBitVector(uint32_t size, uint64_t val) const;

  /**
   * Create a bit-vector constant from a given string.
   * @param s the string represetntation of the constant
   * @param base the base of the string representation
   * @return the bit-vector constant
   */
  Term mkBitVector(const char* s, uint32_t base = 2) const;

  /**
   * Create a bit-vector constant from a given string.
   * @param s the string represetntation of the constant
   * @param base the base of the string representation
   * @return the bit-vector constant
   */
  Term mkBitVector(std::string& s, uint32_t base = 2) const;

  /**
   * Create constant of kind:
   *   - CONST_ROUNDINGMODE
   * @param rm the floating point rounding mode this constant represents
   */
  Term mkConst(RoundingMode rm) const;

  /*
   * Create constant of kind:
   *   - EMPTYSET
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, Sort arg) const;

  /**
   * Create constant of kind:
   *   - UNINTERPRETED_CONSTANT
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, Sort arg1, int32_t arg2) const;

  /**
   * Create constant of kind:
   *   - BOOLEAN
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, bool arg) const;

  /**
   * Create constant of kind:
   *   - CONST_STRING
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, const char* arg) const;

  /**
   * Create constant of kind:
   *   - CONST_STRING
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, const std::string& arg) const;

  /**
   * Create constant of kind:
   *   - ABSTRACT_VALUE
   *   - CONST_RATIONAL (for integers, reals)
   *   - CONST_BITVECTOR
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, const char* arg1, uint32_t arg2 = 10) const;

  /**
   * Create constant of kind:
   *   - ABSTRACT_VALUE
   *   - CONST_RATIONAL (for integers, reals)
   *   - CONST_BITVECTOR
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, const std::string& arg1, uint32_t arg2 = 10) const;

  /**
   * Create constant of kind:
   *   - ABSTRACT_VALUE
   *   - CONST_RATIONAL (for integers, reals)
   *   - CONST_BITVECTOR
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, uint32_t arg) const;

  /**
   * Create constant of kind:
   *   - ABSTRACT_VALUE
   *   - CONST_RATIONAL (for integers, reals)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, int32_t arg) const;

  /**
   * Create constant of kind:
   *   - ABSTRACT_VALUE
   *   - CONST_RATIONAL (for integers, reals)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, int64_t arg) const;

  /**
   * Create constant of kind:
   *   - ABSTRACT_VALUE
   *   - CONST_RATIONAL (for integers, reals)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg the argument to this kind
   */
  Term mkConst(Kind kind, uint64_t arg) const;

  /**
   * Create constant of kind:
   *   - CONST_RATIONAL (for rationals)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, int32_t arg1, int32_t arg2) const;

  /**
   * Create constant of kind:
   *   - CONST_RATIONAL (for rationals)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, int64_t arg1, int64_t arg2) const;

  /**
   * Create constant of kind:
   *   - CONST_RATIONAL (for rationals)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, uint32_t arg1, uint32_t arg2) const;

  /**
   * Create constant of kind:
   *   - CONST_RATIONAL (for rationals)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, uint64_t arg1, uint64_t arg2) const;

  /**
   * Create constant of kind:
   *   - CONST_BITVECTOR
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   */
  Term mkConst(Kind kind, uint32_t arg1, uint64_t arg2) const;

  /**
   * Create constant of kind:
   *   - CONST_FLOATINGPOINT
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the constant
   * @param arg1 the first argument to this kind
   * @param arg2 the second argument to this kind
   * @param arg3 the third argument to this kind
   */
  Term mkConst(Kind kind, uint32_t arg1, uint32_t arg2, Term arg3) const;

  /* .................................................................... */
  /* Create Variables                                                     */
  /* .................................................................... */

  /**
   * Create variable.
   * @param symbol the name of the variable
   * @param sort the sort of the variable
   * @return the variable
   */
  Term mkVar(const std::string& symbol, Sort sort) const;

  /**
   * Create variable.
   * @param sort the sort of the variable
   * @return the variable
   */
  Term mkVar(Sort sort) const;

  /**
   * Create bound variable.
   * @param symbol the name of the variable
   * @param sort the sort of the variable
   * @return the variable
   */
  Term mkBoundVar(const std::string& symbol, Sort sort) const;

  /**
   * Create bound variable.
   * @param sort the sort of the variable
   * @return the variable
   */
  Term mkBoundVar(Sort sort) const;

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
   * Check validity.
   * @return the result of the validity check.
   */
  Result checkValid() const;

  /**
   * Check validity assuming the given formula.
   * @param assumption the formula to assume
   * @return the result of the validity check.
   */
  Result checkValidAssuming(Term assumption) const;

  /**
   * Check validity assuming the given formulas.
   * @param assumptions the formulas to assume
   * @return the result of the validity check.
   */
  Result checkValidAssuming(const std::vector<Term>& assumptions) const;

  /**
   * Declare first-order constant (0-arity function symbol).
   * SMT-LIB: ( declare-const <symbol> <sort> )
   * SMT-LIB: ( declare-fun <symbol> ( ) <sort> )
   * This command corresponds to mkVar().
   * @param symbol the name of the first-order constant
   * @param sort the sort of the first-order constant
   * @return the first-order constant
   */
  Term declareConst(const std::string& symbol, Sort sort) const;

  /**
   * Create datatype sort.
   * SMT-LIB: ( declare-datatype <symbol> <datatype_decl> )
   * @param symbol the name of the datatype sort
   * @param ctors the constructor declarations of the datatype sort
   * @return the datatype sort
   */
  Sort declareDatatype(
      const std::string& symbol,
      const std::vector<DatatypeConstructorDecl>& ctors) const;

  /**
   * Declare 0-arity function symbol.
   * SMT-LIB: ( declare-fun <symbol> ( ) <sort> )
   * @param symbol the name of the function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  Term declareFun(const std::string& symbol, Sort sort) const;

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
   * @return the function
   */
  Term defineFun(const std::string& symbol,
                 const std::vector<Term>& bound_vars,
                 Sort sort,
                 Term term) const;
  /**
   * Define n-ary function.
   * SMT-LIB: ( define-fun <function_def> )
   * Create parameter 'fun' with mkVar().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @return the function
   */
  Term defineFun(Term fun,
                 const std::vector<Term>& bound_vars,
                 Term term) const;

  /**
   * Define recursive function.
   * SMT-LIB: ( define-fun-rec <function_def> )
   * @param symbol the name of the function
   * @param bound_vars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @return the function
   */
  Term defineFunRec(const std::string& symbol,
                    const std::vector<Term>& bound_vars,
                    Sort sort,
                    Term term) const;

  /**
   * Define recursive function.
   * SMT-LIB: ( define-fun-rec <function_def> )
   * Create parameter 'fun' with mkVar().
   * @param fun the sorted function
   * @param bound_vars the parameters to this function
   * @param term the function body
   * @return the function
   */
  Term defineFunRec(Term fun,
                    const std::vector<Term>& bound_vars,
                    Term term) const;

  /**
   * Define recursive functions.
   * SMT-LIB: ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * Create elements of parameter 'funs' with mkVar().
   * @param funs the sorted functions
   * @param bound_vars the list of parameters to the functions
   * @param term the list of function bodies of the functions
   * @return the function
   */
  void defineFunsRec(const std::vector<Term>& funs,
                     const std::vector<std::vector<Term>>& bound_vars,
                     const std::vector<Term>& terms) const;

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
   * Reset the solver.
   * SMT-LIB: ( reset )
   */
  void reset() const;

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

 private:
  /* Helper to convert a vector of internal types to sorts. */
  std::vector<Type> sortVectorToTypes(const std::vector<Sort>& vector) const;
  /* Helper to convert a vector of sorts to internal types. */
  std::vector<Expr> termVectorToExprs(const std::vector<Term>& vector) const;

  /* The options of this solver. */
  std::unique_ptr<Options> d_opts;
  /* The expression manager of this solver. */
  std::unique_ptr<ExprManager> d_exprMgr;
  /* The SMT engine of this solver. */
  std::unique_ptr<SmtEngine> d_smtEngine;
  /* The random number generator of this solver. */
  std::unique_ptr<Random> d_rng;
};

}  // namespace api
}  // namespace CVC4
#endif
