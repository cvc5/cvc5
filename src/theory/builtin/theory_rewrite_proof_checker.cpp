/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Builtin proof checker utility for THEORY_REWRITE.
 */

#include "theory/builtin/theory_rewrite_proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

TheoryRewriteProofChecker::TheoryRewriteProofChecker(NodeManager* nm) : d_nm(nm){}

Node TheoryRewriteProofChecker::checkRewrite(ProofRewriteRule id, const Node& lhs)
{
  Trace("theory-rewrite-pc") << "Check " << id << " " << lhs << std::endl;
  switch (id)
  {
    case ProofRewriteRule::EXISTS_ELIM:
    {
      if (lhs.getKind() != Kind::EXISTS)
      {
        return Node::null();
      }
      std::vector<Node> fchildren;
      fchildren.push_back(lhs[0]);
      fchildren.push_back(lhs[1].negate());
      if (lhs.getNumChildren() == 3)
      {
        fchildren.push_back(lhs[2]);
      }
      return d_nm->mkNode(Kind::NOT, d_nm->mkNode(Kind::FORALL, fchildren));
    }
    break;
    default:
      break;
  }
  return Node::null();
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

