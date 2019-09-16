/*********************                                                        */
/*! \file vts_term_cache.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Virtual term substitution term cache.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEGQI__VTS_TERM_CACHE_H
#define CVC4__THEORY__QUANTIFIERS__CEGQI__VTS_TERM_CACHE_H

#include <map>
#include "expr/attribute.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

/** Attribute to mark Skolems as virtual terms */
struct VirtualTermSkolemAttributeId
{
};
typedef expr::Attribute<VirtualTermSkolemAttributeId, bool>
    VirtualTermSkolemAttribute;

namespace quantifiers {

/** Virtual term substitution term cache
 *
 * This class stores skolems corresponding to virtual terms (e.g. delta and
 * infinity) and has methods for performing virtual term substitution.
 *
 * In detail, there are three kinds of virtual terms:
 * (1) delta, of Real type, representing a infinitesimally small real value,
 * (2) infinity, of Real type, representing an infinitely large real value,
 * (3) infinity, of Int type, representing an infinitely large integer value.
 *
 * For each of the above three virtual terms, we have 2 variants.
 *
 * The first variant we simply call "virtual terms". These terms are intended
 * to never appear in assertions and are simply used by algorithms e.g. CEGQI
 * for specifying instantiations. They are eliminated by the standard rules of
 * virtual term substitution, e.g.:
 *   t < s + delta ---> t <=s
 *   t <= s + delta ---> t <= s
 *   t < s - delta ----> t < s
 *   t <= s - delta -----> t < s
 *   t <= s + inf ----> true
 *   t <= s - inf ----> false
 *
 * The second variant we call "free virtual terms". These terms are intended
 * to appear in assertions and are constrained to have the semantics of the
 * above virtual terms, e.g.:
 *   0 < delta_free
 *   forall x. x < inf_free
 * We use free virtual terms for some instantiation strategies, e.g. those
 * that combine instantiating quantified formulas with nested quantifiers
 * with terms containing virtual terms.
 */
class VtsTermCache
{
 public:
  VtsTermCache(QuantifiersEngine* qe);
  ~VtsTermCache() {}
  /**
   * Get vts delta. The argument isFree indicates if we are getting the
   * free variant of delta. If create is false, this method returns Node::null
   * if the requested delta has not already been created.
   */
  Node getVtsDelta(bool isFree = false, bool create = true);
  /**
   * Get vts infinity of type tn, where tn should be Int or Real.
   * The argument isFree indicates if we are getting the free variant of
   * infinity. If create is false, this method returns Node::null if the
   * requested infinity has not already been created.
   */
  Node getVtsInfinity(TypeNode tn, bool isFree = false, bool create = true);
  /**
   * Get all vts terms and add them to vector t.
   * If the argument isFree is true, we return the free variant of all virtual
   * terms. If create is false, we do not add virtual terms that have not
   * already been created. If inc_delta is false, we do not include delta.
   */
  void getVtsTerms(std::vector<Node>& t,
                   bool isFree = false,
                   bool create = true,
                   bool inc_delta = true);
  /**
   * Rewrite virtual terms in node n. This returns the rewritten form of n
   * after virtual term substitution.
   *
   * This method ensures that the returned node is equivalent to n and does
   * not contain free occurrences of the virtual terms.
   */
  Node rewriteVtsSymbols(Node n);
  /**
   * This method returns true iff n contains a virtual term. If isFree is true,
   * if returns true iff n contains a free virtual term.
   */
  bool containsVtsTerm(Node n, bool isFree = false);
  /**
   * This method returns true iff any term in vector n contains a virtual term.
   * If isFree is true, if returns true iff any term in vector n contains a
   * free virtual term.
   */
  bool containsVtsTerm(std::vector<Node>& n, bool isFree = false);
  /**
   * This method returns true iff n contains an occurence of the virtual term
   * infinity. If isFree is true, if returns true iff n contains the free
   * virtual term infinity.
   */
  bool containsVtsInfinity(Node n, bool isFree = false);

 private:
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** constants */
  Node d_zero;
  /** The virtual term substitution delta */
  Node d_vts_delta;
  /** The virtual term substitution "free delta" */
  Node d_vts_delta_free;
  /** The virtual term substitution infinities for int/real types */
  std::map<TypeNode, Node> d_vts_inf;
  /** The virtual term substitution "free infinities" for int/real types */
  std::map<TypeNode, Node> d_vts_inf_free;
  /** substitute vts terms with their corresponding vts free terms */
  Node substituteVtsFreeTerms(Node n);
}; /* class TermUtil */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__CEGQI__VTS_TERM_CACHE_H */
