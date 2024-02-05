/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The post processor for the AletheLF format.
 */

#include "proof/alf/alf_post_processor.h"

#include <vector>

#include "expr/skolem_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/builtin/generic_op.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace proof {

AlfProofPostprocessCallback::AlfProofPostprocessCallback(ProofNodeManager* pnm,
                                                         AlfNodeConverter& ltp)
    : d_pnm(pnm), d_tproc(ltp), d_numIgnoredScopes(0)
{
}

AlfProofPostprocess::AlfProofPostprocess(Env& env, AlfNodeConverter& ltp)
    : EnvObj(env),
      d_cb(new proof::AlfProofPostprocessCallback(env.getProofNodeManager(),
                                                  ltp))
{
}

bool AlfProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                               const std::vector<Node>& fa,
                                               bool& continueUpdate)
{
  switch (pn->getRule())
  {
    case ProofRule::CONG:
    case ProofRule::CONCAT_CONFLICT:
    case ProofRule::SKOLEM_INTRO: return true;
    default: return false;
  }
}

bool AlfProofPostprocessCallback::addAlfStep(AlfRule rule,
                                             Node conclusion,
                                             const std::vector<Node>& children,
                                             const std::vector<Node>& args,
                                             CDProof& cdp)
{
  std::vector<Node> newArgs;
  NodeManager* nm = NodeManager::currentNM();
  newArgs.push_back(nm->mkConstInt(Rational(static_cast<uint32_t>(rule))));
  newArgs.push_back(conclusion);
  for (const Node& arg : args)
  {
    newArgs.push_back(arg);
  }
  Trace("alf-proof") << "... add alf step " << conclusion << " " << rule
                          << " " << children << " / " << newArgs << std::endl;
  return cdp.addStep(conclusion, ProofRule::ALF_RULE, children, newArgs);
}

void AlfProofPostprocessCallback::addReflStep(const Node& n, CDProof& cdp)
{
  // share REFL
  std::map<Node, std::shared_ptr<ProofNode> >::iterator it = d_refl.find(n);
  if (it == d_refl.end())
  {
    d_refl[n] = d_pnm->mkNode(ProofRule::REFL, {}, {n});
    it = d_refl.find(n);
  }
  cdp.addProof(it->second);
}

bool AlfProofPostprocessCallback::update(Node res,
                                         ProofRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args,
                                         CDProof* cdp,
                                         bool& continueUpdate)
{
  Trace("alf-proof") << "...Alf pre-update " << res << " " << id << " "
                     << children << " / " << args << std::endl;

  switch (id)
  {
    case ProofRule::CONG:
    {
      Assert(res.getKind() == Kind::EQUAL);
      Assert(res[0].getOperator() == res[1].getOperator());
      Trace("alf-proof") << "Processing congruence for " << res << " "
                         << res[0].getKind() << std::endl;

      Kind k = res[0].getKind();
      if (k == Kind::HO_APPLY)
      {
        // HO_APPLY congruence is a single application of HO_CONG
        cdp->addStep(res, ProofRule::HO_CONG, children, {});
        return true;
      }
      // NOTE: as optimization can collect REFL steps. This would subsume
      // the ordinary closure handling

      // get the operator
      Node op = d_tproc.getOperatorOfTerm(res[0]);
      Trace("alf-proof") << "Processing cong for op " << op << " "
                         << op.getType() << std::endl;
      if (res[0].isClosure())
      {
        Assert(children.size() >= 2);
        // variable lists should be equal
        Assert(res[0][0] == res[1][0]);
        std::vector<Node> vars;
        for (const Node& v : res[0][0])
        {
          vars.push_back(d_tproc.convert(v));
        }
        // can use ordinary cong
        Node vl = d_tproc.mkList(vars);
        Node opc = d_tproc.mkInternalApp(
            printer::smt2::Smt2Printer::smtKindString(k), {vl}, vl.getType());
        std::vector<Node> newChildren(
            children.begin() + 1,
            children.begin() + d_tproc.getNumChildrenToProcessForClosure(k));
        addAlfStep(AlfRule::CONG, res, newChildren, {opc}, *cdp);
        return true;
      }
      // Note that indexed operators are "collected" at the base of ordinary
      // cong rule applications and don't need special treatment here.
      Assert(!op.isNull());
      // Are we doing congruence of an n-ary operator? If so, notice that op
      // is a binary operator and we must apply congruence in a special way.
      // Note we use the first block of code if we have more than 2 children.
      // special case: constructors and apply uf are not treated as n-ary; these
      // symbols have function types that expect n arguments.
      bool isNary = false;
      Node nullt;
      if (NodeManager::isNAryKind(k))
      {
        nullt = d_tproc.getNullTerminator(k, res[0].getType());
        isNary = !nullt.isNull();
      }
      if (isNary)
      {
        // use n-ary rule
        addAlfStep(AlfRule::NARY_CONG, res, children, {op}, *cdp);
      }
      else
      {
        // use ordinary rule
        addAlfStep(AlfRule::CONG, res, children, {op}, *cdp);
      }
    }
    break;
    default: return false;
  }
  return true;
}

void AlfProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_env, *(d_cb.get()));
  updater.process(pf);
};

}  // namespace proof
}  // namespace cvc5::internal
