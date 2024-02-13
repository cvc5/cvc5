/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for converting proof nodes.
 */

#include "proof/subtype_elim_proof_converter.h"

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

SubtypeElimConverterCallback::SubtypeElimConverterCallback(Env& env)
    : EnvObj(env)
{
  d_pc = d_env.getProofNodeManager()->getChecker();
}

Node SubtypeElimConverterCallback::convert(Node res,
                                           ProofRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args,
                                           CDProof* cdp)
{
  std::vector<Node> cargs;
  for (const Node& a : args)
  {
    cargs.push_back(d_nconv.convert(a));
  }
  // Node resc = d_nconv.convert(res);
  //  see if proof rule still works
  Node resc = d_nconv.convert(res);
  Node newRes;
  // if either failed or succeeded outright
  if (tryWith(id, children, cargs, resc, newRes, cdp))
  {
    if (newRes.isNull())
    {
      Trace("ajr-temp") << "Failed to convert subtyping " << id << std::endl;
      Trace("ajr-temp") << "Premises: " << children << std::endl;
      Trace("ajr-temp") << "Args: " << cargs << std::endl;
      AlwaysAssert(false) << "Failed to convert subtyping " << id;
    }
    return newRes;
  }
  Trace("ajr-temp") << "Introduction of subtyping via rule " << id << std::endl;
  Trace("ajr-temp") << "Premises: " << children << std::endl;
  Trace("ajr-temp") << "Args: " << cargs << std::endl;
  Trace("ajr-temp") << "...gives " << newRes << std::endl;
  Trace("ajr-temp") << "...wants " << resc << std::endl;
  bool success = false;
  switch (id)
  {
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    {
      success = true;
      Node lhs = resc[0];
      Node rhs = resc[1];
      NodeManager* nm = NodeManager::currentNM();
      for (size_t i = 0, nchild = lhs.getNumChildren(); i < nchild; i++)
      {
        Node eqOld = newRes[0][i].eqNode(newRes[1][i]);
        Node eqNew = lhs[i].eqNode(rhs[i]);
        if (eqOld == eqNew)
        {
          continue;
        }
        // e.g. t=t becomes (to_real t)=(to_real t) or 0=0 becomes 0.0=0.0?
        if (lhs[i] == rhs[i])
        {
          cdp->addStep(eqNew, ProofRule::REFL, {}, {lhs[i]});
          continue;
        }
        // maybe t=s becomes (to_real t)=(to_real s), or t=0 becomes
        // (to_real t)=0.0?
        Node newR[2];
        Node newREq[2];
        bool needsTrans = false;
        for (size_t j = 0; j < 2; j++)
        {
          newR[j] = nm->mkNode(Kind::TO_REAL, newRes[j][i]);
          if (newR[j] != resc[j][i])
          {
            // if e.g. (to_real 0) = 0.0, prove by evaluate
            Node eq = j == 1 ? newR[j].eqNode(resc[j][i])
                             : resc[j][i].eqNode(newR[j]);
            Node peq = d_pc->checkDebug(ProofRule::EVALUATE, {}, {newR[j]});
            if (!CDProof::isSame(eq, peq))
            {
              success = false;
              break;
            }
            newREq[j] = eq;
            needsTrans = true;
          }
        }
        if (success)
        {
          Node nk = ProofRuleChecker::mkKindNode(Kind::TO_REAL);
          Node ceq = newR[0].eqNode(newR[1]);
          cdp->addStep(ceq, ProofRule::CONG, {children[i]}, {nk});
          Trace("ajr-temp") << "...via " << ceq << std::endl;
          if (needsTrans)
          {
            std::vector<Node> tchildren;
            if (!newREq[0].isNull())
            {
              tchildren.push_back(newREq[0]);
            }
            tchildren.push_back(ceq);
            if (!newREq[1].isNull())
            {
              tchildren.push_back(newREq[1]);
            }
            cdp->addStep(eqNew, ProofRule::TRANS, tchildren, {});
            Trace("ajr-temp") << "...via trans " << tchildren << std::endl;
          }
          continue;
        }
        break;
      }
      if (success)
      {
        newRes = resc;
      }
    }
    break;
    case ProofRule::ARITH_MULT_POS:
    case ProofRule::ARITH_MULT_NEG:
    {
      NodeManager* nm = NodeManager::currentNM();
      std::vector<Node> typedArgs;
      typedArgs.push_back(nm->mkConstRealOrInt(args[1][0].getType(),
                                               args[0].getConst<Rational>()));
      typedArgs.push_back(args[1]);
      if (tryWith(id, children, typedArgs, resc, newRes, cdp))
      {
        success = !newRes.isNull();
      }
    }
    break;
    case ProofRule::MACRO_ARITH_SCALE_SUM_UB:
    {
      NodeManager* nm = NodeManager::currentNM();
      std::vector<Node> typedArgs;
      for (size_t i = 0, nargs = args.size(); i < nargs; i++)
      {
        typedArgs.push_back(nm->mkConstRealOrInt(children[i][0].getType(),
                                                 args[i].getConst<Rational>()));
      }
      if (tryWith(id, children, typedArgs, resc, newRes, cdp))
      {
        success = !newRes.isNull();
      }
    }
    break;
    case ProofRule::MACRO_SR_EQ_INTRO:
    case ProofRule::SKOLEM_INTRO: break;
    case ProofRule::TRUST_THEORY_REWRITE: break;
    default: break;
  }
  if (success)
  {
    return newRes;
  }
  AlwaysAssert(false) << "Introduction of subtyping via rule " << id;
  return Node::null();
}

bool SubtypeElimConverterCallback::tryWith(ProofRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args,
                                           Node resc,
                                           Node& newRes,
                                           CDProof* cdp)
{
  newRes = d_pc->checkDebug(id, children, args);
  if (!newRes.isNull())
  {
    // check if the new result has subtyping
    if (resc == newRes)
    {
      cdp->addStep(newRes, id, children, args);
      return true;
    }
    return false;
  }
  return true;
}

}  // namespace cvc5::internal
