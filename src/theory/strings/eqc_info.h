/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Equivalence class info for the theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__EQC_INFO_H
#define CVC5__THEORY__STRINGS__EQC_INFO_H

#include <map>

#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * SAT-context-dependent information about an equivalence class. This
 * information is updated eagerly as assertions are processed by the theory of
 * strings at standard effort.
 */
class EqcInfo
{
 public:
  EqcInfo(context::Context* c);
  ~EqcInfo() {}
  /** add prefix constant
   *
   * This informs this equivalence class info that a term t in its
   * equivalence class has a constant prefix (if isSuf=true) or suffix
   * (if isSuf=false). The constant c (if non-null) is the value of that
   * constant, if it has been computed already.
   *
   * If this method returns a non-null node ret, then ret is a conjunction
   * corresponding to a conflict that holds in the current context.
   */
  Node addEndpointConst(Node t, Node c, bool isSuf);
  /**
   * If non-null, this is a term x from this eq class such that str.len( x )
   * occurs as a term in this SAT context.
   */
  context::CDO<Node> d_lengthTerm;
  /**
   * If non-null, this is a term x from this eq class such that str.code( x )
   * occurs as a term in this SAT context.
   */
  context::CDO<Node> d_codeTerm;
  context::CDO<unsigned> d_cardinalityLemK;
  context::CDO<Node> d_normalizedLength;
  /**
   * If this is a string equivalence class, this is
   * a node that explains the longest constant prefix known of this
   * equivalence class. This can either be:
   * (1) A term from this equivalence class, including a constant "ABC" or
   * concatenation term (str.++ "ABC" ...), or
   * (2) A membership of the form (str.in.re x R) where x is in this
   * equivalence class and R is a regular expression of the form
   * (str.to.re "ABC") or (re.++ (str.to.re "ABC") ...).
   *
   * If this is an integer equivalence class, this is the lower bound
   * of the value of this equivalence class.
   */
  context::CDO<Node> d_firstBound;
  /** same as above, for suffix and integer upper bounds. */
  context::CDO<Node> d_secondBound;
  /**
   * Make merge conflict. Let "bound term" refer to a term that is set
   * as the data member of this class for d_firstBound or d_secondBound.
   * This method is called when this implies that two terms occur in an
   * equivalence class that have conflicting properties. For example,
   * t may be (str.in_re x (re.++ (str.to_re "A") R2)) and prev may be
   * (str.++ "B" y), where the equivalence class of x has merged into
   * the equivalence class of (str.++ "B" y). This method would return
   * the conflict:
   *   (and (= x (str.++ "B" y)) (str.in_re x (re.++ (str.to_re "A") R2)))
   * for this input.
   *
   * @param t The first bound term
   * @param prev The second bound term
   * @param isArith Whether this is an arithmetic conflict. This impacts
   * whether (str.in_re x R) is processed as x or (str.len x).
   * @return The node corresponding to the conflict.
   */
  static Node mkMergeConflict(Node t, Node prev, bool isArith);
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__EQC_INFO_H */
