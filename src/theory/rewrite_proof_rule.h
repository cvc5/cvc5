/*********************                                                        */
/*! \file rewrite_proof_rule.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite proof rule data structure
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__REWRITE_PROOF_RULE__H
#define CVC4__THEORY__REWRITE_PROOF_RULE__H

#include <string>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

/**
 * The definition of a (conditional) rewrite rule.
 */
class RewritePfRule
{
 public:
  /** The name of the rule */
  std::string d_name;
  /** The conditions of the rule */
  std::vector<Node> d_cond;
  /** The conclusion of the rule (an equality) */
  Node d_eq;
  /** initialize this rule */
  void init(const std::string& name, const std::vector<Node>& cond, Node eq);

 private:
  /** the ordered list of free variables */
  std::vector<Node> d_fvs;
  /** number of free variables */
  size_t d_numFv;
  /**
   * The free variables that do not occur in the conditions. These cannot be
   * "holes" in a proof.
   */
  std::map<Node, bool> d_noOccVars;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__REWRITE_PROOF_RULE__H */
