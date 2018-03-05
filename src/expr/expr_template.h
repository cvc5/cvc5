/*********************                                                        */
/*! \file expr_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public-facing expression interface.
 **
 ** Public-facing expression interface.
 **/

#include "cvc4_public.h"

// putting the constant-payload #includes up here allows circularity
// (some of them may require a completely-defined Expr type).  This
// way, those #includes can forward-declare some stuff to get Expr's
// getConst<> template instantiations correct, and then #include
// "expr.h" safely, then go on to completely declare their own stuff.
${includes}

#ifndef __CVC4__EXPR_H
#define __CVC4__EXPR_H

#include <stdint.h>
#include <iosfwd>
#include <iterator>
#include <string>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>

#include "base/exception.h"
#include "options/language.h"
#include "util/hash.h"

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 44 "${template}"

namespace CVC4 {

// The internal expression representation
template <bool ref_count>
class NodeTemplate;

class NodeManager;

class Expr;
class ExprManager;
class SmtEngine;
class Type;
class TypeCheckingException;
class TypeCheckingExceptionPrivate;

namespace expr {
  namespace pickle {
    class Pickler;
  }/* CVC4::expr::pickle namespace */
}/* CVC4::expr namespace */

namespace prop {
  class TheoryProxy;
}/* CVC4::prop namespace */

struct ExprManagerMapCollection;

struct ExprHashFunction;

namespace smt {
  class SmtEnginePrivate;
}/* CVC4::smt namespace */

namespace expr {
  class ExportPrivate;
}/* CVC4::expr namespace */

/**
 * Exception thrown in the case of type-checking errors.
 */
class CVC4_PUBLIC TypeCheckingException : public Exception {
 private:
  friend class SmtEngine;
  friend class smt::SmtEnginePrivate;

  /** The expression responsible for the error */
  Expr* d_expr;

 protected:
  TypeCheckingException() : Exception() {}
  TypeCheckingException(ExprManager* em,
                        const TypeCheckingExceptionPrivate* exc);

 public:
  TypeCheckingException(const Expr& expr, std::string message);

  /** Copy constructor */
  TypeCheckingException(const TypeCheckingException& t);

  /** Destructor */
  ~TypeCheckingException() override;

  /**
   * Get the Expr that caused the type-checking to fail.
   *
   * @return the expr
   */
  Expr getExpression() const;

  /**
   * Returns the message corresponding to the type-checking failure.
   * We prefer toStream() to toString() because that keeps the expr-depth
   * and expr-language settings present in the stream.
   */
  void toStream(std::ostream& out) const override;

  friend class ExprManager;
};/* class TypeCheckingException */

/**
 * Exception thrown in case of failure to export
 */
class CVC4_PUBLIC ExportUnsupportedException : public Exception {
 public:
  ExportUnsupportedException() : Exception("export unsupported") {}
  ExportUnsupportedException(const char* msg) : Exception(msg) {}
};/* class DatatypeExportUnsupportedException */

std::ostream& operator<<(std::ostream& out,
                         const TypeCheckingException& e) CVC4_PUBLIC;

/**
 * Output operator for expressions
 * @param out the stream to output to
 * @param e the expression to output
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Expr& e) CVC4_PUBLIC;

/**
 * Serialize a vector of expressions to given stream.
 *
 * @param out the output stream to use
 * @param container the vector of expressions to output to the stream
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const std::vector<Expr>& container);

/**
 * Serialize a set of expressions to the given stream.
 *
 * @param out the output stream to use
 * @param container the set of expressions to output to the stream
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const std::set<Expr>& container);

/**
 * Serialize an unordered_set of expressions to the given stream.
 *
 * @param out the output stream to use
 * @param container the unordered_set of expressions to output to the stream
 * @return the stream
 */
std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_set<Expr, ExprHashFunction>& container);

/**
 * Serialize a map of expressions to the given stream.
 *
 * @param out the output stream to use
 * @param container the map of expressions to output to the stream
 * @return the stream
 */
template <typename V>
std::ostream& operator<<(std::ostream& out, const std::map<Expr, V>& container);

/**
 * Serialize an unordered_map of expressions to the given stream.
 *
 * @param out the output stream to use
 * @param container the unordered_map of expressions to output to the stream
 * @return the stream
 */
template <typename V>
std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_map<Expr, V, ExprHashFunction>& container);

// for hash_maps, hash_sets..
struct ExprHashFunction {
  size_t operator()(CVC4::Expr e) const;
};/* struct ExprHashFunction */

/**
 * Class encapsulating CVC4 expressions and methods for constructing new
 * expressions.
 */
class CVC4_PUBLIC Expr {

  /** The internal expression representation */
  NodeTemplate<true>* d_node;

  /** The responsible expression manager */
  ExprManager* d_exprManager;

  /**
   * Constructor for internal purposes.
   *
   * @param em the expression manager that handles this expression
   * @param node the actual expression node pointer
   */
  Expr(ExprManager* em, NodeTemplate<true>* node);

public:

  /** Default constructor, makes a null expression. */
  Expr();

  /**
   * Copy constructor, makes a copy of a given expression
   *
   * @param e the expression to copy
   */
  Expr(const Expr& e);

  /** Destructor */
  ~Expr();

  /**
   * Assignment operator, makes a copy of the given expression. If the
   * expression managers of the two expressions differ, the expression of
   * the given expression will be used.
   *
   * @param e the expression to assign
   * @return the reference to this expression after assignment
   */
  Expr& operator=(const Expr& e);

  /**
   * Syntactic comparison operator. Returns true if expressions belong to the
   * same expression manager and are syntactically identical.
   *
   * @param e the expression to compare to
   * @return true if expressions are syntactically the same, false otherwise
   */
  bool operator==(const Expr& e) const;

  /**
   * Syntactic disequality operator.
   *
   * @param e the expression to compare to
   * @return true if expressions differ syntactically, false otherwise
   */
  bool operator!=(const Expr& e) const;

  /**
   * Order comparison operator. The only invariant on the order of expressions
   * is that the expressions that were created sooner will be smaller in the
   * ordering than all the expressions created later. Null expression is the
   * smallest element of the ordering. The behavior of the operator is
   * undefined if the expressions come from two different expression managers.
   *
   * @param e the expression to compare to
   * @return true if this expression is smaller than the given one
   */
  bool operator<(const Expr& e) const;

  /**
   * Order comparison operator. The only invariant on the order of expressions
   * is that the expressions that were created sooner will be smaller in the
   * ordering than all the expressions created later. Null expression is the
   * smallest element of the ordering. The behavior of the operator is
   * undefined if the expressions come from two different expression managers.
   *
   * @param e the expression to compare to
   * @return true if this expression is greater than the given one
   */
  bool operator>(const Expr& e) const;

  /**
   * Order comparison operator. The only invariant on the order of expressions
   * is that the expressions that were created sooner will be smaller in the
   * ordering than all the expressions created later. Null expression is the
   * smallest element of the ordering. The behavior of the operator is
   * undefined if the expressions come from two different expression managers.
   *
   * @param e the expression to compare to
   * @return true if this expression is smaller or equal to the given one
   */
  bool operator<=(const Expr& e) const { return !(*this > e); }

  /**
   * Order comparison operator. The only invariant on the order of expressions
   * is that the expressions that were created sooner will be smaller in the
   * ordering than all the expressions created later. Null expression is the
   * smallest element of the ordering. The behavior of the operator is
   * undefined if the expressions come from two different expression managers.
   *
   * @param e the expression to compare to
   * @return true if this expression is greater or equal to the given one
   */
  bool operator>=(const Expr& e) const { return !(*this < e); }

  /**
   * Get the ID of this expression (used for the comparison operators).
   *
   * @return an identifier uniquely identifying the value this
   * expression holds.
   */
  unsigned long getId() const;

  /**
   * Returns the kind of the expression (AND, PLUS ...).
   *
   * @return the kind of the expression
   */
  Kind getKind() const;

  /**
   * Returns the number of children of this expression.
   *
   * @return the number of children
   */
  size_t getNumChildren() const;

  /**
   * Returns the i'th child of this expression.
   *
   * @param i the index of the child to retrieve
   * @return the child
   */
  Expr operator[](unsigned i) const;

  /**
   * Returns the children of this Expr.
   */
  std::vector<Expr> getChildren() const {
    return std::vector<Expr>(begin(), end());
  }

  /**
   * Returns the Boolean negation of this Expr.
   */
  Expr notExpr() const;

  /**
   * Returns the conjunction of this expression and
   * the given expression.
   */
  Expr andExpr(const Expr& e) const;

  /**
   * Returns the disjunction of this expression and
   * the given expression.
   */
  Expr orExpr(const Expr& e) const;

  /**
   * Returns the exclusive disjunction of this expression and
   * the given expression.
   */
  Expr xorExpr(const Expr& e) const;

  /**
   * Returns the Boolean equivalence of this expression and
   * the given expression.
   */
  Expr iffExpr(const Expr& e) const;

  /**
   * Returns the implication of this expression and
   * the given expression.
   */
  Expr impExpr(const Expr& e) const;

  /**
   * Returns the if-then-else expression with this expression
   * as the Boolean condition and the given expressions as
   * the "then" and "else" expressions.
   */
  Expr iteExpr(const Expr& then_e, const Expr& else_e) const;

  /**
   * Iterator type for the children of an Expr.
   */
  class const_iterator : public std::iterator<std::input_iterator_tag, Expr> {
    ExprManager* d_exprManager;
    void* d_iterator;

    explicit const_iterator(ExprManager*, void*);

    friend class Expr;// to access void* constructor

  public:
    const_iterator();
    const_iterator(const const_iterator& it);
    const_iterator& operator=(const const_iterator& it);
    ~const_iterator();
    bool operator==(const const_iterator& it) const;
    bool operator!=(const const_iterator& it) const {
      return !(*this == it);
    }
    const_iterator& operator++();
    const_iterator operator++(int);
    Expr operator*() const;
  };/* class Expr::const_iterator */

  /**
   * Returns an iterator to the first child of this Expr.
   */
  const_iterator begin() const;

  /**
   * Returns an iterator to one-off-the-last child of this Expr.
   */
  const_iterator end() const;

  /**
   * Check if this is an expression that has an operator.
   *
   * @return true if this expression has an operator
   */
  bool hasOperator() const;

  /**
   * Get the operator of this expression.
   *
   * @throws IllegalArgumentException if it has no operator
   * @return the operator of this expression
   */
  Expr getOperator() const;

  /**
   * Get the type for this Expr and optionally do type checking.
   *
   * Initial type computation will be near-constant time if
   * type checking is not requested. Results are memoized, so that
   * subsequent calls to getType() without type checking will be
   * constant time.
   *
   * Initial type checking is linear in the size of the expression.
   * Again, the results are memoized, so that subsequent calls to
   * getType(), with or without type checking, will be constant
   * time.
   *
   * NOTE: A TypeCheckingException can be thrown even when type
   * checking is not requested. getType() will always return a
   * valid and correct type and, thus, an exception will be thrown
   * when no valid or correct type can be computed (e.g., if the
   * arguments to a bit-vector operation aren't bit-vectors). When
   * type checking is not requested, getType() will do the minimum
   * amount of checking required to return a valid result.
   *
   * @param check whether we should check the type as we compute it
   * (default: false)
   */
  Type getType(bool check = false) const;

  /**
   * Substitute "replacement" in for "e".
   */
  Expr substitute(Expr e, Expr replacement) const;

  /**
   * Substitute "replacements" in for "exes".
   */
  Expr substitute(const std::vector<Expr> exes,
                  const std::vector<Expr>& replacements) const;

  /**
   * Substitute pairs of (ex,replacement) from the given map.
   */
  Expr substitute(const std::unordered_map<Expr, Expr, ExprHashFunction> map) const;

  /**
   * Returns the string representation of the expression.
   * @return a string representation of the expression
   */
  std::string toString() const;

  /**
   * Outputs the string representation of the expression to the stream.
   *
   * @param out the stream to serialize this expression to
   * @param toDepth the depth to which to print this expression, or -1
   * to print it fully
   * @param types set to true to ascribe types to the output
   * expressions (might break language compliance, but good for
   * debugging expressions)
   * @param dag the dagification threshold to use (0 == off)
   * @param language the language in which to output
   */
  void toStream(std::ostream& out, int toDepth = -1, bool types = false, size_t dag = 1,
                OutputLanguage language = language::output::LANG_AUTO) const;

  /**
   * Check if this is a null expression.
   *
   * @return true if a null expression
   */
  bool isNull() const;

  /**
   * Check if this is an expression representing a variable.
   *
   * @return true if a variable expression
   */
  bool isVariable() const;

  /**
   * Check if this is an expression representing a constant.
   *
   * @return true if a constant expression
   */
  bool isConst() const;

  /* A note on isAtomic() and isAtomicFormula() (in CVC3 parlance)..
   *
   * It has been decided for now to hold off on implementations of
   * these functions, as they may only be needed in CNF conversion,
   * where it's pointless to do a lazy isAtomic determination by
   * searching through the DAG, and storing it, since the result will
   * only be used once.  For more details see the 4/27/2010 CVC4
   * developer's meeting notes at:
   *
   * http://goedel.cims.nyu.edu/wiki/Meeting_Minutes_-_April_27,_2010#isAtomic.28.29_and_isAtomicFormula.28.29
   */
  // bool containsDecision(); // is "atomic"
  // bool properlyContainsDecision(); // maybe not atomic but all children are

  /** Extract a constant of type T */
  template <class T>
  const T& getConst() const;

  /**
   * Returns the expression reponsible for this expression.
   */
  ExprManager* getExprManager() const;

  /**
   * Maps this Expr into one for a different ExprManager, using
   * variableMap for the translation and extending it with any new
   * mappings.
   */
  Expr exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap, uint32_t flags = 0) const;

  /**
   * Very basic pretty printer for Expr.
   * This is equivalent to calling e.getNode().printAst(...)
   * @param out output stream to print to.
   * @param indent number of spaces to indent the formula by.
   */
  void printAst(std::ostream& out, int indent = 0) const;

private:

  /**
   * Pretty printer for use within gdb
   * This is not intended to be used outside of gdb.
   * This writes to the ostream Warning() and immediately flushes
   * the ostream.
   */
  void debugPrint();

  /**
   * Returns the actual internal node.
   * @return the internal node
   */
  NodeTemplate<true> getNode() const;

  /**
   * Returns the actual internal node as a TNode.
   * @return the internal node
   */
  NodeTemplate<false> getTNode() const;

  // Friend to access the actual internal expr information and private methods
  friend class SmtEngine;
  friend class smt::SmtEnginePrivate;
  friend class ExprManager;
  friend class NodeManager;
  friend class TypeCheckingException;
  friend class expr::pickle::Pickler;
  friend class prop::TheoryProxy;
  friend class expr::ExportPrivate;
  friend std::ostream& CVC4::operator<<(std::ostream& out, const Expr& e);
  template <bool ref_count> friend class NodeTemplate;

};/* class Expr */

${getConst_instantiations}

#line 549 "${template}"

inline size_t ExprHashFunction::operator()(CVC4::Expr e) const {
  return (size_t) e.getId();
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_H */
