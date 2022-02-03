/*********************                                                        */
/*! \file lfsc_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the Lfsc post proccessor
 **/

#include "proof/lfsc/lfsc_post_processor.h"

#include "options/proof_options.h"
#include "proof/lazy_proof.h"
#include "proof/lfsc/lfsc_printer.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_node_updater.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace proof {

LfscProofPostprocessCallback::LfscProofPostprocessCallback(
    LfscNodeConverter& ltp, ProofNodeManager* pnm)
    : d_pnm(pnm), d_pc(pnm->getChecker()), d_tproc(ltp), d_firstTime(false)
{
}

void LfscProofPostprocessCallback::initializeUpdate() { d_firstTime = true; }

bool LfscProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                const std::vector<Node>& fa,
                                                bool& continueUpdate)
{
  return pn->getRule() != PfRule::LFSC_RULE;
}

bool LfscProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  Trace("lfsc-pp") << "LfscProofPostprocessCallback::update: " << id
                   << std::endl;
  Trace("lfsc-pp-debug") << "...proves " << res << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Assert(id != PfRule::LFSC_RULE);
  bool isFirstTime = d_firstTime;
  // On the first call to update, the proof node is the outermost scope of the
  // proof. This scope should not be printed in the LFSC proof. Instead, the
  // LFSC proof printer will print the proper scope around the proof, which
  // e.g. involves an LFSC "check" command.
  d_firstTime = false;

  switch (id)
  {
    case PfRule::SCOPE:
    {
      if (isFirstTime)
      {
        // Note that we do not want to modify the top-most SCOPE
        return false;
      }
      Assert(children.size() == 1);
      // (SCOPE P :args (F1 ... Fn))
      // becomes
      // (scope _ _ (\ X1 ... (scope _ _ (\ Xn P)) ... ))
      Node curr = children[0];
      for (size_t i = 0, nargs = args.size(); i < nargs; i++)
      {
        size_t ii = (nargs - 1) - i;
        // Use a dummy conclusion for what LAMBDA proves, since there is no
        // FOL representation for its type.
        Node fconc = mkDummyPredicate();
        addLfscRule(cdp, fconc, {curr}, LfscRule::LAMBDA, {args[ii]});
        // we use a chained implication (=> F1 ... (=> Fn C)) which avoids
        // aliasing.
        Node next = nm->mkNode(OR, args[ii].notNode(), curr);
        addLfscRule(cdp, next, {fconc}, LfscRule::SCOPE, {args[ii]});
        curr = next;
      }
      // In LFSC, we have now proved:
      //  (or (not F1) (or (not F2) ... (or (not Fn) C) ... ))
      // We now must convert this to one of two cases
      if (res.getKind() == NOT)
      {
        // we have C = false,
        // convert to (not (and F1 (and F2 ... (and Fn true) ... )))
        // this also handles the case where the conclusion is simply F1,
        // when n=1.
        addLfscRule(cdp, res, {curr}, LfscRule::NOT_AND_REV, {});
      }
      else
      {
        // we have that C != false
        // convert to (=> (and F1 (and F2 ... (and Fn true) ... )) C)
        addLfscRule(cdp, res, {curr}, LfscRule::PROCESS_SCOPE, {children[0]});
      }
    }
    break;
    case PfRule::CHAIN_RESOLUTION:
    {
      // turn into binary resolution
      Node cur = children[0];
      for (size_t i = 1, size = children.size(); i < size; i++)
      {
        std::vector<Node> newChildren{cur, children[i]};
        std::vector<Node> newArgs{args[(i - 1) * 2], args[(i - 1) * 2 + 1]};
        cur = d_pc->checkDebug(PfRule::RESOLUTION, newChildren, newArgs);
        cdp->addStep(cur, PfRule::RESOLUTION, newChildren, newArgs);
      }
    }
    break;
    case PfRule::SYMM:
    {
      if (res.getKind() != NOT)
      {
        // no need to convert (positive) equality symmetry
        return false;
      }
      // must use alternate SYMM rule for disequality
      addLfscRule(cdp, res, {children[0]}, LfscRule::NEG_SYMM, {});
    }
    break;
    case PfRule::TRANS:
    {
      if (children.size() <= 2)
      {
        // no need to change
        return false;
      }
      // turn into binary
      Node cur = children[0];
      std::unordered_set<Node> processed;
      processed.insert(children.begin(), children.end());
      for (size_t i = 1, size = children.size(); i < size; i++)
      {
        std::vector<Node> newChildren{cur, children[i]};
        cur = d_pc->checkDebug(PfRule::TRANS, newChildren, {});
        if (processed.find(cur) != processed.end())
        {
          continue;
        }
        processed.insert(cur);
        cdp->addStep(cur, PfRule::TRANS, newChildren, {});
      }
    }
    break;
    case PfRule::CONG:
    {
      Assert(res.getKind() == EQUAL);
      Assert(res[0].getOperator() == res[1].getOperator());
      Trace("lfsc-pp-cong") << "Processing congruence for " << res << " "
                            << res[0].getKind() << std::endl;
      // different for closures
      if (res[0].isClosure())
      {
        if (res[0][0] != res[1][0])
        {
          // cannot convert congruence with different variables currently
          return false;
        }
        Node cop = d_tproc.getOperatorOfClosure(res[0]);
        Trace("lfsc-pp-qcong") << "Operator for closure " << cop << std::endl;
        // start with base case body = body'
        Node curL = children[1][0];
        Node curR = children[1][1];
        Node currEq = children[1];
        Trace("lfsc-pp-qcong") << "Base congruence " << currEq << std::endl;
        for (size_t i = 0, nvars = res[0][0].getNumChildren(); i < nvars; i++)
        {
          Trace("lfsc-pp-qcong") << "Process child " << i << std::endl;
          // CONG rules for each variable
          Node v = res[0][0][nvars - 1 - i];
          Node vop = d_tproc.getOperatorOfBoundVar(cop, v);
          Node vopEq = vop.eqNode(vop);
          cdp->addStep(vopEq, PfRule::REFL, {}, {vop});
          Node nextEq;
          if (i + 1 == nvars)
          {
            // if we are at the end, we prove the final equality
            nextEq = res;
          }
          else
          {
            curL = nm->mkNode(HO_APPLY, vop, curL);
            curR = nm->mkNode(HO_APPLY, vop, curR);
            nextEq = curL.eqNode(curR);
          }
          addLfscRule(cdp, nextEq, {vopEq, currEq}, LfscRule::CONG, {});
          currEq = nextEq;
        }
        return true;
      }
      Kind k = res[0].getKind();
      if (k == HO_APPLY)
      {
        // HO_APPLY congruence is a single application of LFSC congruence
        addLfscRule(cdp, res, children, LfscRule::CONG, {});
        return true;
      }
      // We are proving f(t1, ..., tn) = f(s1, ..., sn), nested.
      // First, get the operator, which will be used for printing the base
      // REFL step. Notice this may be for interpreted or uninterpreted
      // function symbols.
      Node op = d_tproc.getOperatorOfTerm(res[0]);
      Trace("lfsc-pp-cong") << "Processing cong for op " << op << " "
                            << op.getType() << std::endl;
      Assert(!op.isNull());
      // initial base step is REFL
      Node opEq = op.eqNode(op);
      cdp->addStep(opEq, PfRule::REFL, {}, {op});
      size_t nchildren = children.size();
      Node nullTerm = d_tproc.getNullTerminator(k, res[0].getType());
      // Are we doing congruence of an n-ary operator? If so, notice that op
      // is a binary operator and we must apply congruence in a special way.
      // Note we use the first block of code if we have more than 2 children,
      // or if we have a null terminator.
      // special case: constructors and apply uf are not treated as n-ary; these
      // symbols have function types that expect n arguments.
      bool isNary = NodeManager::isNAryKind(k) && k != kind::APPLY_CONSTRUCTOR
                    && k != kind::APPLY_UF;
      if (isNary && (nchildren > 2 || !nullTerm.isNull()))
      {
        // get the null terminator for the kind, which may mean we are doing
        // a special kind of congruence for n-ary kinds whose base is a REFL
        // step for the null terminator.
        Node currEq;
        if (!nullTerm.isNull())
        {
          currEq = nullTerm.eqNode(nullTerm);
          // if we have a null terminator, we do a final REFL step to add
          // the null terminator to both sides.
          cdp->addStep(currEq, PfRule::REFL, {}, {nullTerm});
        }
        else
        {
          // Otherwise, start with the last argument.
          currEq = children[nchildren - 1];
        }
        for (size_t i = 0; i < nchildren; i++)
        {
          size_t ii = (nchildren - 1) - i;
          Node uop = op;
          // special case: each bv concat in the chain has a different type,
          // so remake the operator here.
          if (k == kind::BITVECTOR_CONCAT)
          {
            // we get the operator of the next argument concatenated with the
            // current accumulated remainder.
            Node currApp =
                nm->mkNode(kind::BITVECTOR_CONCAT, children[ii][0], currEq[0]);
            uop = d_tproc.getOperatorOfTerm(currApp);
          }
          Node argAppEq =
              nm->mkNode(HO_APPLY, uop, children[ii][0])
                  .eqNode(nm->mkNode(HO_APPLY, uop, children[ii][1]));
          addLfscRule(cdp, argAppEq, {opEq, children[ii]}, LfscRule::CONG, {});
          // now, congruence to the current equality
          Node nextEq;
          if (ii == 0)
          {
            // use final conclusion
            nextEq = res;
          }
          else
          {
            // otherwise continue to apply
            nextEq = nm->mkNode(HO_APPLY, argAppEq[0], currEq[0])
                         .eqNode(nm->mkNode(HO_APPLY, argAppEq[1], currEq[1]));
          }
          addLfscRule(cdp, nextEq, {argAppEq, currEq}, LfscRule::CONG, {});
          currEq = nextEq;
        }
      }
      else
      {
        // non n-ary kinds do not have null terminators
        Assert(nullTerm.isNull());
        Node curL = op;
        Node curR = op;
        Node currEq = opEq;
        for (size_t i = 0; i < nchildren; i++)
        {
          // CONG rules for each child
          Node nextEq;
          if (i + 1 == nchildren)
          {
            // if we are at the end, we prove the final equality
            nextEq = res;
          }
          else
          {
            curL = nm->mkNode(HO_APPLY, curL, children[i][0]);
            curR = nm->mkNode(HO_APPLY, curR, children[i][1]);
            nextEq = curL.eqNode(curR);
          }
          addLfscRule(cdp, nextEq, {currEq, children[i]}, LfscRule::CONG, {});
          currEq = nextEq;
        }
      }
    }
    break;
    case PfRule::AND_INTRO:
    {
      Node cur = d_tproc.getNullTerminator(AND);
      size_t nchildren = children.size();
      for (size_t j = 0; j < nchildren; j++)
      {
        size_t jj = (nchildren - 1) - j;
        // conclude the final conclusion if we are finished
        Node next = jj == 0 ? res : nm->mkNode(AND, children[jj], cur);
        if (j == 0)
        {
          addLfscRule(cdp, next, {children[jj]}, LfscRule::AND_INTRO1, {});
        }
        else
        {
          addLfscRule(cdp, next, {children[jj], cur}, LfscRule::AND_INTRO2, {});
        }
        cur = next;
      }
    }
    break;
    case PfRule::ARITH_SUM_UB:
    {
      // proof of null terminator base 0 = 0
      Node zero = d_tproc.getNullTerminator(ADD);
      Node cur = zero.eqNode(zero);
      cdp->addStep(cur, PfRule::REFL, {}, {zero});
      for (size_t i = 0, size = children.size(); i < size; i++)
      {
        size_t ii = (children.size() - 1) - i;
        std::vector<Node> newChildren{children[ii], cur};
        if (ii == 0)
        {
          // final rule must be the real conclusion
          addLfscRule(cdp, res, newChildren, LfscRule::ARITH_SUM_UB, {});
        }
        else
        {
          // rules build an n-ary chain of + on both sides
          cur = d_pc->checkDebug(PfRule::ARITH_SUM_UB, newChildren, {});
          addLfscRule(cdp, cur, newChildren, LfscRule::ARITH_SUM_UB, {});
        }
      }
    }
    break;
    default: return false; break;
  }
  AlwaysAssert(cdp->getProofFor(res)->getRule() != PfRule::ASSUME);
  return true;
}

void LfscProofPostprocessCallback::addLfscRule(
    CDProof* cdp,
    Node conc,
    const std::vector<Node>& children,
    LfscRule lr,
    const std::vector<Node>& args)
{
  std::vector<Node> largs;
  largs.push_back(mkLfscRuleNode(lr));
  largs.push_back(conc);
  largs.insert(largs.end(), args.begin(), args.end());
  cdp->addStep(conc, PfRule::LFSC_RULE, children, largs);
}

Node LfscProofPostprocessCallback::mkChain(Kind k,
                                           const std::vector<Node>& children)
{
  Assert(!children.empty());
  NodeManager* nm = NodeManager::currentNM();
  size_t nchildren = children.size();
  size_t i = 0;
  // do we have a null terminator? If so, we start with it.
  Node ret = d_tproc.getNullTerminator(k, children[0].getType());
  if (ret.isNull())
  {
    ret = children[nchildren - 1];
    i = 1;
  }
  while (i < nchildren)
  {
    ret = nm->mkNode(k, children[(nchildren - 1) - i], ret);
    i++;
  }
  return ret;
}

Node LfscProofPostprocessCallback::mkDummyPredicate()
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkBoundVar(nm->booleanType());
}

LfscProofPostprocess::LfscProofPostprocess(LfscNodeConverter& ltp,
                                           ProofNodeManager* pnm)
    : d_cb(new proof::LfscProofPostprocessCallback(ltp, pnm)), d_pnm(pnm)
{
}

void LfscProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  d_cb->initializeUpdate();
  // do not automatically add symmetry steps, since this leads to
  // non-termination for example on policy_variable.smt2
  ProofNodeUpdater updater(d_pnm, *(d_cb.get()), false, false);
  updater.process(pf);
}

}  // namespace proof
}  // namespace cvc5
