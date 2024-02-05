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
    case ProofRule::SCOPE:
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
  NodeManager* nm = NodeManager::currentNM();

  switch (id)
  {
    case ProofRule::SCOPE:
    {
      // On the first two calls to update, the proof nodes are the outermost
      // scopes of the proof. These scopes should not be printed in the AletheLF
      // proof. Instead, the AletheLF proof printer will print the proper scopes
      // around the proof, which e.g. involves an AletheLF "check" command.
      if (d_numIgnoredScopes < 2)
      {
        d_numIgnoredScopes++;
        // Note that we do not want to modify the top-most SCOPEs.
        return false;
      }
      Node curr = children[0];
      for (size_t i = 0, nargs = args.size(); i < nargs; i++)
      {
        size_t ii = (nargs - 1) - i;
        Node next = nm->mkNode(Kind::IMPLIES, args[ii], curr);
        addAlfStep(AlfRule::SCOPE, next, {curr}, {args[ii]}, *cdp);
        curr = next;
      }
      // convert (=> F1 (=> ... (=> Fn C)...)) to (=> (and F1 ... Fn) C) or
      // (not (and F1 ... Fn))
      addAlfStep(AlfRule::PROCESS_SCOPE, res, {curr}, {children[0]}, *cdp);
    }
    break;
    case ProofRule::CONG:
    {
      Assert(res.getKind() == Kind::EQUAL);
      Assert(res[0].getOperator() == res[1].getOperator());
      Trace("alf-proof") << "Processing congruence for " << res << " "
                         << res[0].getKind() << std::endl;

      Kind k = res[0].getKind();
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
      return false;
    }
    break;
    case ProofRule::CONCAT_CONFLICT:
    {
      if (children.size() == 1)
      {
        // no need to change
        return false;
      }
      Assert(children.size() == 2);
      Assert(children[0].getKind() == Kind::EQUAL);
      Assert(children[0][0].getType().isSequence());
      // must use the sequences version of the rule
      addAlfStep(AlfRule::CONCAT_CONFLICT_DEQ, res, children, args, *cdp);
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
