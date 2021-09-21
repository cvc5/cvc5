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
    case PfRule::SCOPE:
    {
      bool success = true;

      // Build vp1
      std::vector<Node> negNode;
      std::vector<Node> sanitized_args;
      for (Node arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
        sanitized_args.push_back(d_anc.convert(arg));
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
    // The rule is translated according to the theory id tid and the outermost
    // connective of the conclusion F. This is not an exact translation but
    // should work in most cases.
    //
    // E.g. if the F: (= (* 0 d) 0) and tid = THEORY_ARITH, then prod_simplify
    // is correctly guessed as the rule.
    case PfRule::THEORY_REWRITE:
    {
      AletheRule vrule = AletheRule::UNDEFINED;
      Node t = res[0];

      switch (static_cast<theory::TheoryId>(std::stoul(args[1].toString())))
      {
        case theory::TheoryId::THEORY_BUILTIN:
        {
          switch (t.getKind())
          {
            case kind::ITE:
            {
              vrule = AletheRule::ITE_SIMPLIFY;
              break;
            }
            case kind::EQUAL:
            {
              vrule = AletheRule::EQ_SIMPLIFY;
              break;
            }
            case kind::AND:
            {
              vrule = AletheRule::AND_SIMPLIFY;
              break;
            }
            case kind::OR:
            {
              vrule = AletheRule::OR_SIMPLIFY;
              break;
            }
            case kind::NOT:
            {
              vrule = AletheRule::NOT_SIMPLIFY;
              break;
            }
            case kind::IMPLIES:
            {
              vrule = AletheRule::IMPLIES_SIMPLIFY;
              break;
            }
            case kind::WITNESS:
            {
              vrule = AletheRule::QNT_SIMPLIFY;
              break;
            }
            default:
            {
              // In this case the rule is undefined
            }
          }
          break;
        }
        case theory::TheoryId::THEORY_BOOL:
        {
          vrule = AletheRule::BOOL_SIMPLIFY;
          break;
        }
        case theory::TheoryId::THEORY_UF:
        {
          if (t.getKind() == kind::EQUAL)
          {
            // A lot of these seem to be symmetry rules but not all...
            vrule = AletheRule::EQUIV_SIMPLIFY;
          }
          break;
        }
        case theory::TheoryId::THEORY_ARITH:
        {
          switch (t.getKind())
          {
            case kind::DIVISION:
            {
              vrule = AletheRule::DIV_SIMPLIFY;
              break;
            }
            case kind::PRODUCT:
            {
              vrule = AletheRule::PROD_SIMPLIFY;
              break;
            }
            case kind::MINUS:
            {
              vrule = AletheRule::MINUS_SIMPLIFY;
              break;
            }
            case kind::UMINUS:
            {
              vrule = AletheRule::UNARY_MINUS_SIMPLIFY;
              break;
            }
            case kind::PLUS:
            {
              vrule = AletheRule::SUM_SIMPLIFY;
              break;
            }
            case kind::MULT:
            {
              vrule = AletheRule::PROD_SIMPLIFY;
              break;
            }
            case kind::EQUAL:
            {
              vrule = AletheRule::EQUIV_SIMPLIFY;
              break;
            }
            case kind::LT:
            {
              [[fallthrough]];
            }
            case kind::GT:
            {
              [[fallthrough]];
            }
            case kind::GEQ:
            {
              [[fallthrough]];
            }
            case kind::LEQ:
            {
              vrule = AletheRule::COMP_SIMPLIFY;
              break;
            }
            case kind::CAST_TO_REAL:
            {
              return addAletheStep(AletheRule::LA_GENERIC,
                                   res,
                                   nm->mkNode(kind::SEXPR, d_cl, res),
                                   children,
                                   {nm->mkConst(Rational(1))},
                                   *cdp);
            }
            default:
            {
              // In this case the rule is undefined
            }
          }
          break;
        }
        case theory::TheoryId::THEORY_QUANTIFIERS:
        {
          vrule = AletheRule::QUANTIFIER_SIMPLIFY;
          break;
        }
        default:
        {
          // In this case the rule is undefined
        };
      }
      return addAletheStep(
          vrule, res, nm->mkNode(kind::SEXPR, d_cl, res), children, {}, *cdp);
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
