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

// This function removes all attributes contained in the list of attributes from
// a Node res while only recursively updating the node further if
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
    for (int i = 0; i < res.end() - res.begin(); i++)
    {
      if (std::find(attributes.begin(), attributes.end(), res[i].getKind())
          == attributes.end())
      {
        new_children.push_back(
            proof::removeAttributes(res[i], attributes, continueRemoval));
      }
    }
    return NodeManager::currentNM()->mkNode(res.getKind(), new_children);
  }
  return res;
}

AletheProofPostprocessCallback::AletheProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  NodeManager* nm = NodeManager::currentNM();
  d_cl = nm->mkBoundVar("cl", nm->stringType());
}

bool AletheProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 const std::vector<Node>& fa,
                                                 bool& continueUpdate)
{
  return pn->getRule() != PfRule::ALETHE_RULE;
}

bool AletheProofPostprocessCallback::update(Node res,
                                            PfRule id,
                                            const std::vector<Node>& children,
                                            const std::vector<Node>& args,
                                            CDProof* cdp,
                                            bool& continueUpdate)
{
  Trace("alethe-proof") << "- Alethe post process callback " << res << " " << id
                        << " " << children << " / " << args << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> new_args = std::vector<Node>();

  switch (id)
  {
    default:
    {
      std::cout << "Not implemented yet " << id << std::endl;
      return addAletheStep(AletheRule::UNDEFINED,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           args,
                           *cdp);
    }
  }
}

bool AletheProofPostprocessCallback::addAletheStep(
    AletheRule rule,
    Node res,
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
  new_args.push_back(
      NodeManager::currentNM()->mkConst<Rational>(static_cast<unsigned>(rule)));
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
  Node conclusion = NodeManager::currentNM()->mkNode(kind::SEXPR, subterms);
  return addAletheStep(rule, res, conclusion, children, args, cdp);
}

}  // namespace proof

}  // namespace cvc5
