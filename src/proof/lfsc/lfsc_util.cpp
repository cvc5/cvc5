/*********************                                                        */
/*! \file lfsc_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "proof/lfsc/lfsc_util.h"

#include "expr/proof_checker.h"

namespace cvc5 {
namespace proof {

const char* toString(LfscRule id)
{
  switch (id)
  {
    case LfscRule::SCOPE: return "scope";
    case LfscRule::NEG_SYMM: return "neg_symm";
    case LfscRule::CONG: return "cong";
    case LfscRule::AND_ELIM1: return "and_elim1";
    case LfscRule::AND_ELIM2: return "and_elim2";
    case LfscRule::AND_INTRO1: return "and_intro1";
    case LfscRule::AND_INTRO2: return "and_intro2";
    case LfscRule::NOT_AND_REV: return "not_and_rev";
    case LfscRule::PROCESS_SCOPE: return "process_scope";
    case LfscRule::ARITH_SUM_UB: return "arith_sum_ub";
    case LfscRule::INSTANTIATE: return "instantiate";
    case LfscRule::SKOLEMIZE: return "skolemize";
    case LfscRule::LAMBDA: return "\\";
    case LfscRule::PLET: return "plet";
    default: return "?";
  }
}
std::ostream& operator<<(std::ostream& out, LfscRule id)
{
  out << toString(id);
  return out;
}

bool getLfscRule(Node n, LfscRule& lr)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    lr = static_cast<LfscRule>(id);
    return true;
  }
  return false;
}

LfscRule getLfscRule(Node n)
{
  LfscRule lr = LfscRule::UNKNOWN;
  getLfscRule(n, lr);
  return lr;
}

Node mkLfscRuleNode(LfscRule r)
{
  return NodeManager::currentNM()->mkConst(Rational(static_cast<uint32_t>(r)));
}

bool LfscProofLetifyTraverseCallback::shouldTraverse(const ProofNode* pn)
{
  if (pn->getRule() == PfRule::SCOPE)
  {
    // this may not be necessary?
    return false;
  }
  if (pn->getRule() != PfRule::LFSC_RULE)
  {
    return true;
  }
  // do not traverse under LFSC scope
  LfscRule lr = getLfscRule(pn->getArguments()[0]);
  return lr != LfscRule::LAMBDA;
}

}  // namespace proof
}  // namespace cvc5
