/*********************                                                        */
/*! \file expr_template.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Liana Hadarean, Kshitij Bansal, Tim King, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

#include <string>
#include <iostream>
#include <iterator>
#include <stdint.h>

#include "util/exception.h"
#include "util/language.h"
#include "util/hash.h"
#include "expr/options.h"

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
  class CVC4_PUBLIC ExprSetDepth;
  class CVC4_PUBLIC ExprPrintTypes;
  class CVC4_PUBLIC ExprDag;
  class CVC4_PUBLIC ExprSetLanguage;

  class ExportPrivate;
}/* CVC4::expr namespace */

/**
 * Exception thrown in the case of type-checking errors.
 */
class CVC4_PUBLIC TypeCheckingException : public Exception {

  friend class SmtEngine;
  friend class smt::SmtEnginePrivate;

private:

  /** The expression responsible for the error */
  Expr* d_expr;

protected:

  TypeCheckingException() throw() : Exception() {}
  TypeCheckingException(ExprManager* em,
                        const TypeCheckingExceptionPrivate* exc) throw();

public:

  TypeCheckingException(const Expr& expr, std::string message) throw();

  /** Copy constructor */
  TypeCheckingException(const TypeCheckingException& t) throw();

  /** Destructor */
  ~TypeCheckingException() throw();

  /**
   * Get the Expr that caused the type-checking to fail.
   *
   * @return the expr
   */
  Expr getExpression() const throw();

  /**
   * Returns the message corresponding to the type-checking failure.
   * We prefer toStream() to toString() because that keeps the expr-depth
   * and expr-language settings present in the stream.
   */
  void toStream(std::ostream& out) const throw();

  friend class ExprManager;
};/* class TypeCheckingException */

/**
 * Exception thrown in case of failure to export
 */
class CVC4_PUBLIC ExportUnsupportedException : public Exception {
public:
  ExportUnsupportedException() throw():
    Exception("export unsupported") {
  }
  ExportUnsupportedException(const char* msg) throw():
    Exception(msg) {
  }
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
  Type getType(bool check = false) const throw (TypeCheckingException);

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
  Expr substitute(const std::hash_map<Expr, Expr, ExprHashFunction> map) const;

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
                OutputLanguage language = language::output::LANG_AST) const;

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
   * IOStream manipulator to set the maximum depth of Exprs when
   * pretty-printing.  -1 means print to any depth.  E.g.:
   *
   *   // let a, b, c, and d be VARIABLEs
   *   Expr e = em->mkExpr(OR, a, b, em->mkExpr(AND, c, em->mkExpr(NOT, d)))
   *   out << setdepth(3) << e;
   *
   * gives "(OR a b (AND c (NOT d)))", but
   *
   *   out << setdepth(1) << [same expr as above]
   *
   * gives "(OR a b (...))"
   */
  typedef expr::ExprSetDepth setdepth;

  /**
   * IOStream manipulator to print type ascriptions or not.
   *
   *   // let a, b, c, and d be variables of sort U
   *   Expr e = em->mkExpr(OR, a, b, em->mkExpr(AND, c, em->mkExpr(NOT, d)))
   *   out << printtypes(true) << e;
   *
   * gives "(OR a:U b:U (AND c:U (NOT d:U)))", but
   *
   *   out << printtypes(false) << [same expr as above]
   *
   * gives "(OR a b (AND c (NOT d)))"
   */
  typedef expr::ExprPrintTypes printtypes;

  /**
   * IOStream manipulator to print expressions as a DAG (or not).
   */
  typedef expr::ExprDag dag;

  /**
   * IOStream manipulator to set the output language for Exprs.
   */
  typedef expr::ExprSetLanguage setlanguage;

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
  NodeTemplate<true> getNode() const throw();

  /**
   * Returns the actual internal node as a TNode.
   * @return the internal node
   */
  NodeTemplate<false> getTNode() const throw();

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

namespace expr {

/**
 * IOStream manipulator to set the maximum depth of Exprs when
 * pretty-printing.  -1 means print to any depth.  E.g.:
 *
 *   // let a, b, c, and d be VARIABLEs
 *   Expr e = em->mkExpr(OR, a, b, em->mkExpr(AND, c, em->mkExpr(NOT, d)))
 *   out << setdepth(3) << e;
 *
 * gives "(OR a b (AND c (NOT d)))", but
 *
 *   out << setdepth(1) << [same expr as above]
 *
 * gives "(OR a b (...))".
 *
 * The implementation of this class serves two purposes; it holds
 * information about the depth setting (such as the index of the
 * allocated word in ios_base), and serves also as the manipulator
 * itself (as above).
 */
class CVC4_PUBLIC ExprSetDepth {
  /**
   * The allocated index in ios_base for our depth setting.
   */
  static const int s_iosIndex;

  /**
   * The default depth to print, for ostreams that haven't yet had a
   * setdepth() applied to them.
   */
  static const int s_defaultPrintDepth = -1;

  /**
   * When this manipulator is used, the depth is stored here.
   */
  long d_depth;

public:
  /**
   * Construct a ExprSetDepth with the given depth.
   */
  ExprSetDepth(long depth) : d_depth(depth) {}

  inline void applyDepth(std::ostream& out) {
    out.iword(s_iosIndex) = d_depth;
  }

  static inline long getDepth(std::ostream& out) {
    long& l = out.iword(s_iosIndex);
    if(l == 0) {
      // set the default print depth on this ostream
      if(&Options::current() != NULL) {
        l = options::defaultExprDepth();
      }
      if(l == 0) {
        // if called from outside the library, we may not have options
        // available to us at this point (or perhaps the output language
        // is not set in Options).  Default to something reasonable, but
        // don't set "l" since that would make it "sticky" for this
        // stream.
        return s_defaultPrintDepth;
      }
    }
    return l;
  }

  static inline void setDepth(std::ostream& out, long depth) {
    out.iword(s_iosIndex) = depth;
  }

  /**
   * Set the expression depth on the output stream for the current
   * stack scope.  This makes sure the old depth is reset on the stream
   * after normal OR exceptional exit from the scope, using the RAII
   * C++ idiom.
   */
  class Scope {
    std::ostream& d_out;
    long d_oldDepth;

  public:

    inline Scope(std::ostream& out, long depth) :
      d_out(out),
      d_oldDepth(ExprSetDepth::getDepth(out)) {
      ExprSetDepth::setDepth(out, depth);
    }

    inline ~Scope() {
      ExprSetDepth::setDepth(d_out, d_oldDepth);
    }

  };/* class ExprSetDepth::Scope */

};/* class ExprSetDepth */

/**
 * IOStream manipulator to print type ascriptions or not.
 *
 *   // let a, b, c, and d be variables of sort U
 *   Expr e = em->mkExpr(OR, a, b, em->mkExpr(AND, c, em->mkExpr(NOT, d)))
 *   out << e;
 *
 * gives "(OR a:U b:U (AND c:U (NOT d:U)))", but
 */
class CVC4_PUBLIC ExprPrintTypes {
  /**
   * The allocated index in ios_base for our setting.
   */
  static const int s_iosIndex;

  /**
   * When this manipulator is used, the setting is stored here.
   */
  bool d_printTypes;

public:
  /**
   * Construct a ExprPrintTypes with the given setting.
   */
  ExprPrintTypes(bool printTypes) : d_printTypes(printTypes) {}

  inline void applyPrintTypes(std::ostream& out) {
    out.iword(s_iosIndex) = d_printTypes;
  }

  static inline bool getPrintTypes(std::ostream& out) {
    return out.iword(s_iosIndex);
  }

  static inline void setPrintTypes(std::ostream& out, bool printTypes) {
    out.iword(s_iosIndex) = printTypes;
  }

  /**
   * Set the print-types state on the output stream for the current
   * stack scope.  This makes sure the old state is reset on the
   * stream after normal OR exceptional exit from the scope, using the
   * RAII C++ idiom.
   */
  class Scope {
    std::ostream& d_out;
    bool d_oldPrintTypes;

  public:

    inline Scope(std::ostream& out, bool printTypes) :
      d_out(out),
      d_oldPrintTypes(ExprPrintTypes::getPrintTypes(out)) {
      ExprPrintTypes::setPrintTypes(out, printTypes);
    }

    inline ~Scope() {
      ExprPrintTypes::setPrintTypes(d_out, d_oldPrintTypes);
    }

  };/* class ExprPrintTypes::Scope */

};/* class ExprPrintTypes */

/**
 * IOStream manipulator to print expressions as a dag (or not).
 */
class CVC4_PUBLIC ExprDag {
  /**
   * The allocated index in ios_base for our setting.
   */
  static const int s_iosIndex;

  /**
   * The default setting, for ostreams that haven't yet had a
   * dag() applied to them.
   */
  static const size_t s_defaultDag = 1;

  /**
   * When this manipulator is used, the setting is stored here.
   */
  size_t d_dag;

public:
  /**
   * Construct a ExprDag with the given setting (dagification on or off).
   */
  explicit ExprDag(bool dag) : d_dag(dag ? 1 : 0) {}

  /**
   * Construct a ExprDag with the given setting (letify only common
   * subexpressions that appear more than 'dag' times).  dag <= 0 means
   * don't dagify.
   */
  explicit ExprDag(int dag) : d_dag(dag < 0 ? 0 : dag) {}

  inline void applyDag(std::ostream& out) {
    // (offset by one to detect whether default has been set yet)
    out.iword(s_iosIndex) = static_cast<long>(d_dag) + 1;
  }

  static inline size_t getDag(std::ostream& out) {
    long& l = out.iword(s_iosIndex);
    if(l == 0) {
      // set the default dag setting on this ostream
      // (offset by one to detect whether default has been set yet)
      if(&Options::current() != NULL) {
        l = options::defaultDagThresh() + 1;
      }
      if(l == 0) {
        // if called from outside the library, we may not have options
        // available to us at this point (or perhaps the output language
        // is not set in Options).  Default to something reasonable, but
        // don't set "l" since that would make it "sticky" for this
        // stream.
        return s_defaultDag + 1;
      }
    }
    return static_cast<size_t>(l - 1);
  }

  static inline void setDag(std::ostream& out, size_t dag) {
    // (offset by one to detect whether default has been set yet)
    out.iword(s_iosIndex) = static_cast<long>(dag) + 1;
  }

  /**
   * Set the dag state on the output stream for the current
   * stack scope.  This makes sure the old state is reset on the
   * stream after normal OR exceptional exit from the scope, using the
   * RAII C++ idiom.
   */
  class Scope {
    std::ostream& d_out;
    size_t d_oldDag;

  public:

    inline Scope(std::ostream& out, size_t dag) :
      d_out(out),
      d_oldDag(ExprDag::getDag(out)) {
      ExprDag::setDag(out, dag);
    }

    inline ~Scope() {
      ExprDag::setDag(d_out, d_oldDag);
    }

  };/* class ExprDag::Scope */

};/* class ExprDag */

/**
 * IOStream manipulator to set the output language for Exprs.
 */
class CVC4_PUBLIC ExprSetLanguage {
  /**
   * The allocated index in ios_base for our depth setting.
   */
  static const int s_iosIndex;

  /**
   * The default language to use, for ostreams that haven't yet had a
   * setlanguage() applied to them and where the current Options
   * information isn't available.
   */
  static const int s_defaultOutputLanguage = language::output::LANG_AST;

  /**
   * When this manipulator is used, the setting is stored here.
   */
  OutputLanguage d_language;

public:
  /**
   * Construct a ExprSetLanguage with the given setting.
   */
  ExprSetLanguage(OutputLanguage l) : d_language(l) {}

  inline void applyLanguage(std::ostream& out) {
    // (offset by one to detect whether default has been set yet)
    out.iword(s_iosIndex) = int(d_language) + 1;
  }

  static inline OutputLanguage getLanguage(std::ostream& out) {
    long& l = out.iword(s_iosIndex);
    if(l == 0) {
      // set the default language on this ostream
      // (offset by one to detect whether default has been set yet)
      if(&Options::current() != NULL) {
        l = options::outputLanguage() + 1;
      }
      if(l <= 0 || l > language::output::LANG_MAX) {
        // if called from outside the library, we may not have options
        // available to us at this point (or perhaps the output language
        // is not set in Options).  Default to something reasonable, but
        // don't set "l" since that would make it "sticky" for this
        // stream.
        return OutputLanguage(s_defaultOutputLanguage);
      }
    }
    return OutputLanguage(l - 1);
  }

  static inline void setLanguage(std::ostream& out, OutputLanguage l) {
    // (offset by one to detect whether default has been set yet)
    out.iword(s_iosIndex) = int(l) + 1;
  }

  /**
   * Set a language on the output stream for the current stack scope.
   * This makes sure the old language is reset on the stream after
   * normal OR exceptional exit from the scope, using the RAII C++
   * idiom.
   */
  class Scope {
    std::ostream& d_out;
    OutputLanguage d_oldLanguage;

  public:

    inline Scope(std::ostream& out, OutputLanguage language) :
      d_out(out),
      d_oldLanguage(ExprSetLanguage::getLanguage(out)) {
      ExprSetLanguage::setLanguage(out, language);
    }

    inline ~Scope() {
      ExprSetLanguage::setLanguage(d_out, d_oldLanguage);
    }

  };/* class ExprSetLanguage::Scope */

};/* class ExprSetLanguage */

}/* CVC4::expr namespace */

${getConst_instantiations}

#line 939 "${template}"

namespace expr {

/**
 * Sets the default depth when pretty-printing a Expr to an ostream.
 * Use like this:
 *
 *   // let out be an ostream, e an Expr
 *   out << Expr::setdepth(n) << e << endl;
 *
 * The depth stays permanently (until set again) with the stream.
 */
inline std::ostream& operator<<(std::ostream& out, ExprSetDepth sd) {
  sd.applyDepth(out);
  return out;
}

/**
 * Sets the default print-types setting when pretty-printing an Expr
 * to an ostream.  Use like this:
 *
 *   // let out be an ostream, e an Expr
 *   out << Expr::printtypes(true) << e << endl;
 *
 * The setting stays permanently (until set again) with the stream.
 */
inline std::ostream& operator<<(std::ostream& out, ExprPrintTypes pt) {
  pt.applyPrintTypes(out);
  return out;
}

/**
 * Sets the default dag setting when pretty-printing a Expr to an ostream.
 * Use like this:
 *
 *   // let out be an ostream, e an Expr
 *   out << Expr::dag(true) << e << endl;
 *
 * The setting stays permanently (until set again) with the stream.
 */
inline std::ostream& operator<<(std::ostream& out, ExprDag d) {
  d.applyDag(out);
  return out;
}

/**
 * Sets the output language when pretty-printing a Expr to an ostream.
 * Use like this:
 *
 *   // let out be an ostream, e an Expr
 *   out << Expr::setlanguage(LANG_SMTLIB_V2) << e << endl;
 *
 * The setting stays permanently (until set again) with the stream.
 */
inline std::ostream& operator<<(std::ostream& out, ExprSetLanguage l) {
  l.applyLanguage(out);
  return out;
}

}/* CVC4::expr namespace */

inline size_t ExprHashFunction::operator()(CVC4::Expr e) const {
  return (size_t) e.getId();
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_H */
