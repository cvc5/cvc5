/*********************                                                        */
/*! \file theory_rewrite_rcons.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for reconstructing proofs of THEORY_REWRITE steps.
 **/

#include "cvc5_private.h"

#ifndef CVC4__SMT__THEORY_REWRITE_RCONS_H
#define CVC4__SMT__THEORY_REWRITE_RCONS_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/proof.h"
#include "expr/proof_node_manager.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5 {
namespace smt {

/**
 */
class TheoryRewriteRCons
{
 public:
  TheoryRewriteRCons(ProofNodeManager* pnm);
  ~TheoryRewriteRCons() {}
  /**
   * Reconstruct
   */
  bool reconstruct(CDProof* cdp,
                   Node eq,
                   theory::TheoryId tid,
                   theory::MethodId mid);

 private:
  /** Try rule */
  bool tryRule(CDProof* cdp, Node eq, PfRule r, const std::vector<Node>& args);
  /** Proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace smt
}  // namespace cvc5

#endif
