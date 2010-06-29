/*********************                                                        */
/*! \file expr_template.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): cconway, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-facing expression interface.
 **
 ** Public-facing expression interface.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__EXPR_H
#define __CVC4__EXPR_H

#include "expr/type.h"
#include <string>
#include <iostream>
#include <stdint.h>

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 33 "${template}"

namespace CVC4 {

// The internal expression representation
template <bool ref_count>
class NodeTemplate;

class Expr;

namespace expr {
  class NodeSetDepth;
}/* CVC4::expr namespace */

/**
 * Exception thrown in the case of type-checking errors.
 */
class CVC4_PUBLIC TypeCheckingException : public Exception {

private:

  /** The expression responsible for the error */
  Expr* d_expr;

protected:

  TypeCheckingException(): Exception() {}
  TypeCheckingException(const Expr& expr, std::string message);

public:

  /** Copy constructor */
  TypeCheckingException(const TypeCheckingException& t);

  /** Destructor */
  ~TypeCheckingException() throw ();

  /**
   * Get the Node that caused the type-checking to fail.
   * @return the node
   */
  Expr getExpression() const;

  /** Returns the message corresponding to the type-checking failure */
  std::string toString() const;

  friend class ExprManager;
};

/**
 * Class encapsulating CVC4 expressions and methods for constructing new
 * expressions.
 */
class CVC4_PUBLIC Expr {
protected:

  /** The internal expression representation */
  NodeTemplate<true>* d_node;

  /** The responsible expression manager */
  ExprManager* d_exprManager;

  /**
   * Constructor for internal purposes.
   * @param em the expression manager that handles this expression
   * @param node the actual expression node pointer
   */
  Expr(ExprManager* em, NodeTemplate<true>* node);

public:

  /** Default constructor, makes a null expression. */
  Expr();

  /**
   * Copy constructor, makes a copy of a given expression
   * @param e the expression to copy
   */
  Expr(const Expr& e);

  /**
   * Initialize from an integer. Fails if the integer is not 0.
   * NOTE: This is here purely to support the auto-initialization
   * behavior of the ANTLR3 C backend. Should be removed if future
   * versions of ANTLR fix the problem.
   */
  Expr(uintptr_t n);

  /** Destructor */
  ~Expr();

  /**
   * Assignment operator, makes a copy of the given expression. If the
   * expression managers of the two expressions differ, the expression of
   * the given expression will be used.
   * @param e the expression to assign
   * @return the reference to this expression after assignment
   */
  Expr& operator=(const Expr& e);

  /**
   * Syntactic comparison operator. Returns true if expressions belong to the
   * same expression manager and are syntactically identical.
   * @param e the expression to compare to
   * @return true if expressions are syntactically the same, false otherwise
   */
  bool operator==(const Expr& e) const;

  /**
   * Syntactic dis-equality operator.
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
   * @param e the expression to compare to
   * @return true if this expression is smaller than the given one
   */
  bool operator<(const Expr& e) const;

  /**
   * Returns the kind of the expression (AND, PLUS ...).
   * @return the kind of the expression
   */
  Kind getKind() const;

  /**
   * Returns the number of children of this expression.
   * @return the number of children
   */
  size_t getNumChildren() const;

  /**
   * Returns the i'th child of this expression.
   * @param i the index of the child to retrieve
   * @return the child
   */
  Expr getChild(unsigned int i) const;

  /**
   * Check if this is an expression that has an operator.
   * @return true if this expression has an operator
   */
  bool hasOperator() const;

  /**
   * Get the operator of this expression.
   * @throws IllegalArgumentException if it has no operator
   * @return the operator of this expression
   */
  Expr getOperator() const;

  /** Returns the type of the expression, if it has been computed.
   * Returns NULL if the type of the expression is not known.
   */
  Type getType() const throw (TypeCheckingException);

  /**
   * Returns the string representation of the expression.
   * @return a string representation of the expression
   */
  std::string toString() const;

  /**
   * Outputs the string representation of the expression to the stream.
   * @param out the output stream
   */
  void toStream(std::ostream& out) const;

  /**
   * Check if this is a null expression.
   * @return true if a null expression
   */
  bool isNull() const;

  /**
   * Check if this is a null expression.
   * @return true if NOT a null expression
   */
  operator bool() const;

  /**
   * Check if this is an expression representing a constant.
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
   * IOStream manipulator to set the maximum depth of Nodes when
   * pretty-printing.  -1 means print to any depth.  E.g.:
   *
   *   // let a, b, c, and d be VARIABLEs
   *   Node n = nm->mkNode(OR, a, b, nm->mkNode(AND, c, nm->mkNode(NOT, d)))
   *   out << setdepth(3) << n;
   *
   * gives "(OR a b (AND c (NOT d)))", but
   *
   *   out << setdepth(1) << [same node as above]
   *
   * gives "(OR a b (...))"
   */
  typedef expr::NodeSetDepth setdepth;

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

protected:

  /**
   * Returns the actual internal node.
   * @return the internal node
   */
  NodeTemplate<true> getNode() const;

  // Friend to access the actual internal node information and private methods
  friend class SmtEngine;
  friend class ExprManager;
};

/**
 * Output operator for expressions
 * @param out the stream to output to
 * @param e the expression to output
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Expr& e) CVC4_PUBLIC;

/**
 * Extending the expression with the capability to construct Boolean
 * expressions.
 */
class CVC4_PUBLIC BoolExpr : public Expr {

public:

  /** Default constructor, makes a null expression */
  BoolExpr();

  /**
   * Convert an expression to a Boolean expression
   */
  BoolExpr(const Expr& e);

  /**
   * Negate this expression.
   * @return the logical negation of this expression.
   */
  BoolExpr notExpr() const;

  /**
   * Conjunct the given expression to this expression.
   * @param e the expression to conjunct
   * @return the conjunction of this expression and e
   */
  BoolExpr andExpr(const BoolExpr& e) const;

  /**
   * Disjunct the given expression to this expression.
   * @param e the expression to disjunct
   * @return the disjunction of this expression and e
   */
  BoolExpr orExpr(const BoolExpr& e) const;

  /**
   * Make an exclusive or expression out of this expression and the given
   * expression.
   * @param e the right side of the xor
   * @return the xor of this expression and e
   */
  BoolExpr xorExpr(const BoolExpr& e) const;

  /**
   * Make an equivalence expression out of this expression and the given
   * expression.
   * @param e the right side of the equivalence
   * @return the equivalence expression
   */
  BoolExpr iffExpr(const BoolExpr& e) const;

  /**
   * Make an implication expression out of this expression and the given
   * expression.
   * @param e the right side of the equivalence
   * @return the equivalence expression
   */
  BoolExpr impExpr(const BoolExpr& e) const;

  /**
   * Make a Boolean if-then-else expression using this expression as the
   * condition, and given the then and else parts
   * @param then_e the then branch expression
   * @param else_e the else branch expression
   * @return the if-then-else expression
   */
  BoolExpr iteExpr(const BoolExpr& then_e, const BoolExpr& else_e) const;

  /**
   * Make a term if-then-else expression using this expression as the
   * condition, and given the then and else parts
   * @param then_e the then branch expression
   * @param else_e the else branch expression
   * @return the if-then-else expression
   */
  Expr iteExpr(const Expr& then_e, const Expr& else_e) const;
};

${getConst_instantiations}

namespace expr {

/**
 * IOStream manipulator to set the maximum depth of Nodes when
 * pretty-printing.  -1 means print to any depth.  E.g.:
 *
 *   // let a, b, c, and d be VARIABLEs
 *   Node n = nm->mkNode(OR, a, b, nm->mkNode(AND, c, nm->mkNode(NOT, d)))
 *   out << setdepth(3) << n;
 *
 * gives "(OR a b (AND c (NOT d)))", but
 *
 *   out << setdepth(1) << [same node as above]
 *
 * gives "(OR a b (...))".
 *
 * The implementation of this class serves two purposes; it holds
 * information about the depth setting (such as the index of the
 * allocated word in ios_base), and serves also as the manipulator
 * itself (as above).
 */
class NodeSetDepth {
  /**
   * The allocated index in ios_base for our depth setting.
   */
  static const int s_iosIndex;

  /**
   * The default depth to print, for ostreams that haven't yet had a
   * setdepth() applied to them.
   */
  static const int s_defaultPrintDepth = 3;

  /**
   * When this manipulator is 
   */
  long d_depth;

public:
  /**
   * Construct a NodeSetDepth with the given depth.
   */
  NodeSetDepth(long depth) : d_depth(depth) {}

  inline void applyDepth(std::ostream& out) {
    out.iword(s_iosIndex) = d_depth;
  }

  static inline long getDepth(std::ostream& out) {
    long& l = out.iword(s_iosIndex);
    if(l == 0) {
      // set the default print depth on this ostream
      l = s_defaultPrintDepth;
    }
    return l;
  }

  static inline void setDepth(std::ostream& out, long depth) {
    out.iword(s_iosIndex) = depth;
  }
};

/**
 * Sets the default depth when pretty-printing a Node to an ostream.
 * Use like this:
 *
 *   // let out be an ostream, n a Node
 *   out << Node::setdepth(n) << n << endl;
 *
 * The depth stays permanently (until set again) with the stream.
 */
inline std::ostream& operator<<(std::ostream& out, NodeSetDepth sd) {
  sd.applyDepth(out);
  return out;
}

}/* CVC4::expr namespace */

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_H */
