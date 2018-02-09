/*********************                                                        */
/*! \file extended_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief extended rewriting class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H
#define __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H

#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Extended rewriter
 *
 * This class is used for all rewriting that is not necessarily
 * helpful for quantifier-free solving, but is helpful
 * in other use cases. An example of this is SyGuS, where rewriting
 * can be used for generalizing refinement lemmas, and hence
 * should be highly aggressive.
 *
 * This class extended the standard techniques for rewriting
 * with techniques, including but not limited to:
 * - ITE branch merging,
 * - ITE conditional variable elimination,
 * - ITE condition subsumption, and
 * - Aggressive rewriting for string equalities.
 */
class ExtendedRewriter
{
 public:
  ExtendedRewriter();
  ~ExtendedRewriter() {}
  /** return the extended rewritten form of n */
  Node extendedRewrite(Node n);

 private:
  /** true and false nodes */
  Node d_true;
  Node d_false;
  /** cache for extendedRewrite */
  std::unordered_map<Node, Node, NodeHashFunction> d_ext_rewrite_cache;
  /** pull ITE
   * Do simple ITE pulling, e.g.:
   *   C2 --->^E false
   * implies:
   *  ite( C, C1, C2 ) --->^E  C ^ C1
   * where ---->^E denotes extended rewriting.
   */
  Node extendedRewritePullIte(Node n);
  /** bitvector subsume 
   * 
   * Returns true if a's 1 bits are a superset of b's 1 bits.
   * That is, if this function returns true, then 
   *   (bvand (bvnot a) b) = 0.
   * If strict is true, then it must be the case that at least one bit of a
   * is 1 that is 0 in bit, that is:
   *   (bvand a (bvnot b)) != 0.
   */
  bool bitVectorSubsume( Node a, Node b, bool strict=false );
  /** bitvector arithmetic compare 
   * 
   * Returns true if bvugt( a, b ) is entailed, or bvuge( a, b ) if strict is
   * false.
   */
  bool bitVectorArithComp( Node a, Node b, bool strict=false );
  /** bitvector disjoint
   * 
   * Returns true if there are no bits where a and b are both 1.
   * That is, if this function returns true, then
   *   (bvand a b) = 0.
   */
  bool bitvectorDisjoint( Node a, Node b );
  /** extended rewrite 
   * 
   * Prints debug information, indicating the rewrite n ---> ret was found.
   */
  void debugExtendedRewrite( Node n, Node ret, const char * c );
  /** decompose chain */
  Node decomposeChain( Kind k, Node n, std::vector< Node >& children );
  /** chain */
  Node mkChain( Kind k, Node base, std::vector< Node >& children );
  /** mk const as the same type as n, 0 if !isNot, 1s if isNot */
  Node mkConstBv( Node n, bool isNot );
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H */
