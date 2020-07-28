/*********************                                                        */
/*! \file eqc_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Equivalence class info for the theory of strings
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__EQC_INFO_H
#define CVC4__THEORY__STRINGS__EQC_INFO_H

#include <map>

#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"

namespace CVC4 {
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
   * A node that explains the longest constant prefix known of this
   * equivalence class. This can either be:
   * (1) A term from this equivalence class, including a constant "ABC" or
   * concatenation term (str.++ "ABC" ...), or
   * (2) A membership of the form (str.in.re x R) where x is in this
   * equivalence class and R is a regular expression of the form
   * (str.to.re "ABC") or (re.++ (str.to.re "ABC") ...).
   */
  context::CDO<Node> d_prefixC;
  /** same as above, for suffix. */
  context::CDO<Node> d_suffixC;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__EQC_INFO_H */
