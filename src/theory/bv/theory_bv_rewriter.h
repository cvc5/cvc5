/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_REWRITER_H
#define CVC5__THEORY__BV__THEORY_BV_REWRITER_H

#include "theory/theory_rewriter.h"

namespace cvc5 {
namespace theory {
namespace bv {

typedef RewriteResponse (*RewriteFunction) (TNode, bool);

class TheoryBVRewriter : public TheoryRewriter
{
 public:
  /**
   * Temporary hack for devision-by-zero until we refactor theory code from
   * smt engine.
   *
   * @param node
   *
   * @return
   */
  static Node eliminateBVSDiv(TNode node);

  TheoryBVRewriter();

  RewriteResponse postRewrite(TNode node) override;
  RewriteResponse preRewrite(TNode node) override;

  TrustNode expandDefinition(Node node) override;

 private:
  static RewriteResponse IdentityRewrite(TNode node, bool prerewrite = false);
  static RewriteResponse UndefinedRewrite(TNode node, bool prerewrite = false);

  static RewriteResponse RewriteBitOf(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteEqual(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUlt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUltBv(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSlt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSltBv(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUle(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSle(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUgt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSgt(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUge(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSge(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteITEBv(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNot(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteConcat(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteAnd(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteOr(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteXnor(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteXor(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNand(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNor(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteComp(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteMult(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteAdd(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSub(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteNeg(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUdiv(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUrem(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUdivTotal(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteUremTotal(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSmod(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSdiv(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSrem(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteShl(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteLshr(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteAshr(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteExtract(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRepeat(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteZeroExtend(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteSignExtend(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRotateRight(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRotateLeft(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRedor(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteRedand(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteEagerAtom(TNode node, bool prerewrite = false);

  static RewriteResponse RewriteBVToNat(TNode node, bool prerewrite = false);
  static RewriteResponse RewriteIntToBV(TNode node, bool prerewrite = false);

  void initializeRewrites();

  RewriteFunction d_rewriteTable[kind::LAST_KIND];
}; /* class TheoryBVRewriter */

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BV__THEORY_BV_REWRITER_H */
