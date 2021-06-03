/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Expr IO manipulation classes.
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__EXPR_IOMANIP_H
#define CVC5__EXPR__EXPR_IOMANIP_H

#include <iosfwd>

namespace cvc5 {
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
class ExprSetDepth
{
 public:
  /**
   * Construct a ExprSetDepth with the given depth.
   */
  ExprSetDepth(long depth);

  void applyDepth(std::ostream& out);

  static long getDepth(std::ostream& out);

  static void setDepth(std::ostream& out, long depth);

  /**
   * Set the expression depth on the output stream for the current
   * stack scope.  This makes sure the old depth is reset on the stream
   * after normal OR exceptional exit from the scope, using the RAII
   * C++ idiom.
   */
  class Scope {
  public:
    Scope(std::ostream& out, long depth);
    ~Scope();

  private:
    std::ostream& d_out;
    long d_oldDepth;
  };/* class ExprSetDepth::Scope */

 private:
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
}; /* class ExprSetDepth */

/**
 * IOStream manipulator to print expressions as a dag (or not).
 */
class ExprDag
{
 public:
  /**
   * Construct a ExprDag with the given setting (dagification on or off).
   */
  explicit ExprDag(bool dag);

  /**
   * Construct a ExprDag with the given setting (letify only common
   * subexpressions that appear more than 'dag' times).  dag <= 0 means
   * don't dagify.
   */
  explicit ExprDag(int dag);

  void applyDag(std::ostream& out);

  static size_t getDag(std::ostream& out);

  static void setDag(std::ostream& out, size_t dag);

  /**
   * Set the dag state on the output stream for the current
   * stack scope.  This makes sure the old state is reset on the
   * stream after normal OR exceptional exit from the scope, using the
   * RAII C++ idiom.
   */
  class Scope {
  public:
    Scope(std::ostream& out, size_t dag);
    ~Scope();

  private:
    std::ostream& d_out;
    size_t d_oldDag;
  };/* class ExprDag::Scope */

 private:
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
}; /* class ExprDag */

/**
 * Sets the default dag setting when pretty-printing a Expr to an ostream.
 * Use like this:
 *
 *   // let out be an ostream, e an Expr
 *   out << Expr::dag(true) << e << endl;
 *
 * The setting stays permanently (until set again) with the stream.
 */
std::ostream& operator<<(std::ostream& out, ExprDag d);

/**
 * Sets the default depth when pretty-printing a Expr to an ostream.
 * Use like this:
 *
 *   // let out be an ostream, e an Expr
 *   out << Expr::setdepth(n) << e << endl;
 *
 * The depth stays permanently (until set again) with the stream.
 */
std::ostream& operator<<(std::ostream& out, ExprSetDepth sd);

}  // namespace expr

}  // namespace cvc5

#endif /* CVC5__EXPR__EXPR_IOMANIP_H */
