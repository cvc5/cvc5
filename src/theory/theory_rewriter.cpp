/*********************                                                        */
/*! \file theory_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The TheoryRewriter class
 **
 ** The TheoryRewriter class is the interface that theory rewriters implement.
 **/

#include "theory/theory_rewriter.h"

namespace CVC4 {
namespace theory {

TrustRewriteResponse::TrustRewriteResponse(RewriteStatus status,
                                           Node n,
                                           Node nr,
                                           ProofGenerator* pg)
    : d_status(status)
{
  d_node = TrustNode::mkTrustRewrite(n, nr, pg);
}

TrustRewriteResponse TheoryRewriter::postRewriteWithProof(TNode node)
{
  RewriteResponse response = postRewrite(node);
  // TODO
  // by default, we return a trust rewrite response with no proof generator
  return TrustRewriteResponse(
      response.d_status, node, response.d_node, nullptr);
}

TrustRewriteResponse TheoryRewriter::preRewriteWithProof(TNode node)
{
  RewriteResponse response = preRewrite(node);
  // TODO
  // by default, we return a trust rewrite response with no proof generator
  return TrustRewriteResponse(
      response.d_status, node, response.d_node, nullptr);
}

}  // namespace theory
}  // namespace CVC4
