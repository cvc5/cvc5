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
    //================================================= Core rules
    //======================== Assume and Scope
    // ======== Assumption (a leaf)
    // Children: none
    // Arguments: (F)
    // --------------
    // Conclusion: F
    //
    // proof rule: assume
    // proof node: (VP:F)
    // proof term: F
    // premises: ()
    // args: ()
    case PfRule::ASSUME:
    {
      return addAletheStep(AletheRule::ASSUME, res, res, children, {}, *cdp);
    }
    // ======== Scope (a binder for assumptions)
    // Children: (P:F)
    // Arguments: (F1, ..., Fn)
    // --------------
    // Conclusion: (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) if F is false
    //
    // proof rule: anchor
    // proof node: (VP1:(cl (not F1) ... (not Fn) F))
    // proof term: (cl (not F1) ... (not Fn) F)
    // premises: P
    // args: (F1, ..., Fn)
    //
    // Repeat the following two step for i=1 to n:
    //
    // proof rule: and_pos
    // proof node: (VP2_i:(cl (not (and F1 ... Fn)) Fi))
    // proof term: (cl (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    //
    // Let (not (and F1 ... Fn))^i denote the repetition of (not (and F1 ...
    // Fn)) for i times
    //
    // proof rule: resolution
    // proof node: (VP2a:(cl F (not (and F1 ... Fn))^n))
    // proof term: (cl F (not (and F1 ... Fn))^n)
    // premises: VP1, VP2_i for all i in {1..n},
    // args: ()
    //
    // proof rule: reorder
    // proof node: (VP2b:(cl (not (and F1 ... Fn))^n F))
    // proof term: (cl (not (and F1 ... Fn))^n F)
    // premises: VP2a
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (VP3:(cl (not (and F1 ... Fn)) F))
    // proof term: (cl (not (and F1 ... Fn)) F)
    // premises: VP2a or VP2b
    // args: ()
    //
    // proof rule: implies_neg1
    // proof node: (VP4:(cl (=> (and F1 ... Fn) F) (and F1 ... Fn)))
    // proof term: (cl (=> (and F1 ... Fn) F) (and F1 ... Fn))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP5:(cl (=> (and F1 ... Fn) F) F))
    // proof term: (cl (=> (and F1 ... Fn) F) F)
    // premises: VP4 VP3
    // args: ()
    //
    // proof rule: implies_neg2
    // proof node: (VP6:(cl (=> (and F1 ... Fn) F) (not F)))
    // proof term: (cl (=> (and F1 ... Fn) F) (not F))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP7:(cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F)))
    // proof term: (cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F))
    // premises: VP5 VP6
    // args: ()
    //
    // If F = false:
    //
    // proof rule: duplicated_literals
    // proof node: (VP8:(cl (=> (and F1 ... Fn) F)))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: VP7
    // args: ()
    //
    // proof rule: implies_simplify
    // proof node:
    //   (VP9:(cl (= (=> (and F1 ... Fn) false) (not (and F1 ...Fn)))))
    // proof term:
    //   (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node:
    //   (VP10:(cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn))))
    // proof term:
    //   (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn)))
    // premises: VP9
    // args: ()
    //
    // proof rule: resolution
    // proof node: (or (not (and F1 ... Fn)))
    // proof term: (cl (not (and F1 ... Fn)))
    // premises: VP8 VP10
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: duplicated_literals
    // proof node: (or (=> (and F1 ... Fn) F))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: VP7
    // args: ()
    case PfRule::SCOPE:
    {
      bool success = true;

      // Build vp1
      std::vector<Node> negNode;
      std::vector<Node> sanitized_args;
      for (Node arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
        sanitized_args.push_back(removeAttributes(
            arg, {kind::INST_PATTERN, kind::INST_PATTERN_LIST}, [](Node n) {
              return expr::hasClosure(n);
            }));
      }
      negNode.push_back(children[0]);         // (not F1) ... (not Fn) F
      negNode.insert(negNode.begin(), d_cl);  // (cl (not F1) ... (not F) F)
      Node vp1 = nm->mkNode(kind::SEXPR, negNode);
      success &= addAletheStep(AletheRule::ANCHOR_SUBPROOF,
                               vp1,
                               vp1,
                               children,
                               sanitized_args,
                               *cdp);

      // Build vp2i
      Node andNode;
      if (args.size() != 1)
      {
        andNode = nm->mkNode(kind::AND, args);  // (and F1 ... Fn)
      }
      else
      {
        andNode = args[0];  // F1
      }
      std::vector<Node> premisesVP2 = {vp1};
      std::vector<Node> notAnd = {d_cl, children[0]};  // cl F
      Node vp2_i;
      for (long unsigned int i = 0; i < args.size(); i++)
      {
        vp2_i = nm->mkNode(kind::SEXPR,
                           d_cl,
                           andNode.notNode(),
                           args[i]);  // (cl (not (and F1 ... Fn)) Fi)
        success &=
            addAletheStep(AletheRule::AND_POS, vp2_i, vp2_i, {}, {}, *cdp);
        premisesVP2.push_back(vp2_i);
        notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
      }

      Node vp2a =
          nm->mkNode(kind::SEXPR, notAnd);  // (cl F (not (and F1 ... Fn))^n)
      success &= addAletheStep(
          AletheRule::RESOLUTION, vp2a, vp2a, premisesVP2, {}, *cdp);

      notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n F)
      notAnd.push_back(children[0]);     //(cl (not (and F1 ... Fn))^n F)
      Node vp2b = nm->mkNode(kind::SEXPR, notAnd);
      success &=
          addAletheStep(AletheRule::REORDER, vp2b, vp2b, {vp2a}, {}, *cdp);

      Node vp3 = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
      success &= addAletheStep(
          AletheRule::DUPLICATED_LITERALS, vp3, vp3, {vp2b}, {}, *cdp);

      Node vp8 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::IMPLIES, andNode, children[0]));

      Node vp4 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], andNode);
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG1, vp4, vp4, {}, {}, *cdp);

      Node vp5 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0]);
      success &=
          addAletheStep(AletheRule::RESOLUTION, vp5, vp5, {vp4, vp3}, {}, *cdp);

      Node vp6 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0].notNode());
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG2, vp6, vp6, {}, {}, *cdp);

      Node vp7 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], vp8[1]);
      success &=
          addAletheStep(AletheRule::RESOLUTION, vp7, vp7, {vp5, vp6}, {}, *cdp);

      if (children[0] != nm->mkConst(false))
      {
        success &= addAletheStep(
            AletheRule::DUPLICATED_LITERALS, res, vp8, {vp7}, {}, *cdp);
      }
      else
      {
        success &= addAletheStep(
            AletheRule::DUPLICATED_LITERALS, vp8, vp8, {vp7}, {}, *cdp);

        Node vp9 =
            nm->mkNode(kind::SEXPR,
                       d_cl,
                       nm->mkNode(kind::EQUAL, vp8[1], andNode.notNode()));

        success &=
            addAletheStep(AletheRule::IMPLIES_SIMPLIFY, vp9, vp9, {}, {}, *cdp);

        Node vp10 =
            nm->mkNode(kind::SEXPR, d_cl, vp8[1].notNode(), andNode.notNode());
        success &=
            addAletheStep(AletheRule::EQUIV1, vp10, vp10, {vp9}, {}, *cdp);

        success &= addAletheStep(AletheRule::RESOLUTION,
                                 res,
                                 nm->mkNode(kind::SEXPR, d_cl, res),
                                 {vp8, vp10},
                                 {},
                                 *cdp);
      }

      return success;
    }
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
