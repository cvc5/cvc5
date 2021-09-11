/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into Alethe proof nodes
 */

#include "proof/alethe/alethe_post_processor.h"

#include "expr/node_algorithm.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "util/rational.h"

namespace cvc5 {

namespace proof {

// This function removes all attributes contained in a given list of attributes
// from a Node res while only recursively updating the node further if
// continueRemoval is true.
static Node removeAttributes(Node res,
                             const std::vector<Kind>& attributes,
                             bool (*continueRemoval)(Node))
{
  if (res.getNumChildren() != 0)
  {
    std::vector<Node> new_children;
    if (res.hasOperator())
    {
      new_children.push_back(res.getOperator());
    }
    for (Node r : res)
    {
      if (std::find(attributes.begin(), attributes.end(), r.getKind())
          == attributes.end())
      {
        new_children.push_back(
            proof::removeAttributes(r, attributes, continueRemoval));
      }
    }
    return NodeManager::currentNM()->mkNode(res.getKind(), new_children);
  }
  return res;
}

AletheProofPostprocessCallback::AletheProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_nm(NodeManager::currentNM())
{
  d_cl = d_nm->mkBoundVar("cl", d_nm->stringType());
}

bool AletheProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 const std::vector<Node>& fa,
                                                 bool& continueUpdate)
{
  if (pn->getRule() == PfRule::ALETHE_RULE)
  {
    return false;
  }
  return true;
}

bool AletheProofPostprocessCallback::addAletheStep(
    Node res,
    AletheRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  return addAletheStep(res, rule, res, children, args, cdp);
}

bool AletheProofPostprocessCallback::addAletheStep(
    Node res,
    AletheRule rule,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  // delete attributes
  Node sanitized_conclusion = conclusion;
  if (expr::hasClosure(conclusion))
  {
    sanitized_conclusion = removeAttributes(
        conclusion, {kind::INST_PATTERN, kind::INST_PATTERN_LIST}, [](Node n) {
          return expr::hasClosure(n);
        });
  }

  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(rule)));
  new_args.push_back(res);
  new_args.push_back(sanitized_conclusion);
  new_args.insert(new_args.end(), args.begin(), args.end());
  Trace("alethe-proof") << "... add Alethe step " << res << " / " << conclusion
                       << " " << rule << " " << children << " / " << new_args
                       << std::endl;
  return cdp.addStep(res, PfRule::ALETHE_RULE, children, new_args);
}

// Replace a node (or F1 ... Fn) by (cl F1 ... Fn)
bool AletheProofPostprocessCallback::addAletheStepFromOr(
    Node res,
    AletheRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> subterms = {d_cl};
  subterms.insert(subterms.end(), res.begin(), res.end());
  Node conclusion = d_nm->mkNode(kind::SEXPR, subterms);
  return addAletheStep(res, rule, conclusion, children, args, cdp);
}

}  // namespace proof

}  // namespace cvc5
