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

AletheProofPostprocessCallback::AletheProofPostprocessCallback(
    ProofNodeManager* pnm, AletheNodeConverter& anc)
    : d_pnm(pnm), d_anc(anc)
{
  NodeManager* nm = NodeManager::currentNM();
  d_cl = nm->mkBoundVar("cl", nm->sExprType());
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
    case PfRule::ASSUME:
    {
      return addAletheStep(AletheRule::ASSUME, res, res, children, {}, *cdp);
    }
    // See proof_rule.h for documentation on the SCOPE rule. This comment uses
    // variable names as introduced there. Instead of (not (and F1 ... Fn))
    // (cl (not (and F1 ... Fn))) is printed and instead of (=> (and F1 ... Fn)
    // F) the term (cl (=> (and F1 ... Fn))) is printed while the proof node
    // remains the same.
    //
    // Let (not (and F1 ... Fn))^i denote the repetition of (not (and F1 ...
    // Fn)) for i times.
    //
    // T1:
    //
    //   P
    // ----- ANCHOR    ------- ... ------- AND_POS
    //  VP1             VP2_1  ...  VP2_n
    // ------------------------------------ RESOLUTION
    //               VP2a
    // ------------------------------------ REORDER
    //  VP2b
    // ------ DUPLICATED_LITERALS   ------- IMPLIES_NEG1
    //   VP3                          VP4
    // ------------------------------------  RESOLUTION    ------- IMPLIES_NEG2
    //    VP5                                                VP6
    // ----------------------------------------------------------- RESOLUTION
    //                               VP7
    //
    // VP1: (cl (not F1) ... (not Fn) F)
    // VP2_i: (cl (not (and F1 ... Fn)) Fi), for i = 1 to n
    // VP2a: (cl F (not (and F1 ... Fn))^n)
    // VP2b: (cl (not (and F1 ... Fn))^n F)
    // VP3: (cl (not (and F1 ... Fn)) F)
    // VP4: (cl (=> (and F1 ... Fn) F) (and F1 ... Fn)))
    // VP5: (cl (=> (and F1 ... Fn) F) F)
    // VP6: (cl (=> (and F1 ... Fn) F) (not F))
    // VP7: (cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F))
    //
    // The reorder step is not necessary if n = 1, because in that case VP2a is
    // (cl (not F1 F) which is the same as VP2b.
    //
    //
    // If F = false:
    //
    //                                    --------- IMPLIES_SIMPLIFY
    //    T1                                 VP9
    // --------- DUPLICATED_LITERALS      --------- EQUIV_1
    //    VP8                                VP10
    // -------------------------------------------- RESOLUTION
    //          (cl (not (and F1 ... Fn)))*
    //
    // VP8: (cl (=> (and F1 ... Fn))) (cl (not (=> (and F1 ... Fn) false))
    //      (not (and F1 ... Fn)))
    // VP9: (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
    //
    //
    // Otherwise,
    //                T1
    //  ------------------------------ DUPLICATED_LITERALS
    //   (cl (=> (and F1 ... Fn) F))**
    //
    //
    // *  the corresponding proof node is (not (and F1 ... Fn))
    // ** the corresponding proof node is (=> (and F1 ... Fn) F)
    case PfRule::SCOPE:
    {
      bool success = true;

      // Build vp1
      std::vector<Node> negNode{d_cl};
      std::vector<Node> sanitized_args;
      for (Node arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
        sanitized_args.push_back(d_anc.convert(arg));
      }
      negNode.push_back(children[0]);         // (cl (not F1) ... (not Fn) F)
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
        vp2_i = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), args[i]);
        success &=
            addAletheStep(AletheRule::AND_POS, vp2_i, vp2_i, {}, {}, *cdp);
        premisesVP2.push_back(vp2_i);
        notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
      }

      Node vp2a = nm->mkNode(kind::SEXPR, notAnd);
      success &= addAletheStep(
          AletheRule::RESOLUTION, vp2a, vp2a, premisesVP2, {}, *cdp);

      notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n)
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
    sanitized_conclusion = d_anc.convert(conclusion);
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
