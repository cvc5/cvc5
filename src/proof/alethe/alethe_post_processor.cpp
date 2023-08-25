/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into Alethe proof nodes
 */

#include "proof/alethe/alethe_post_processor.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/resolution_proofs_util.h"
#include "smt/env.h"
#include "theory/builtin/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

namespace proof {

std::unordered_map<Kind, AletheRule> s_bvKindToAletheRule = {
  {kind::BITVECTOR_ULT, AletheRule::BV_BITBLAST_STEP_BVULT},
  {kind::VARIABLE, AletheRule::BV_BITBLAST_STEP_VAR},
  {kind::BITVECTOR_AND, AletheRule::BV_BITBLAST_STEP_BVAND},
  {kind::BITVECTOR_OR, AletheRule::BV_BITBLAST_STEP_BVOR},
  {kind::BITVECTOR_XOR, AletheRule::BV_BITBLAST_STEP_BVXOR},
  {kind::BITVECTOR_XNOR, AletheRule::BV_BITBLAST_STEP_BVXNOR},
  {kind::BITVECTOR_NOT, AletheRule::BV_BITBLAST_STEP_BVNOT},
  {kind::BITVECTOR_ADD, AletheRule::BV_BITBLAST_STEP_BVADD},
  {kind::BITVECTOR_NEG, AletheRule::BV_BITBLAST_STEP_BVNEG},
  {kind::BITVECTOR_MULT, AletheRule::BV_BITBLAST_STEP_BVMULT},
  {kind::BITVECTOR_CONCAT, AletheRule::BV_BITBLAST_STEP_CONCAT},
  {kind::CONST_BITVECTOR, AletheRule::BV_BITBLAST_STEP_CONST},
  {kind::BITVECTOR_EXTRACT, AletheRule::BV_BITBLAST_STEP_EXTRACT},
  {kind::EQUAL, AletheRule::BV_BITBLAST_STEP_BVEQUAL},
};

AletheProofPostprocessCallback::AletheProofPostprocessCallback(
    Env& env, AletheNodeConverter& anc, bool resPivots)
    : EnvObj(env), d_anc(anc), d_resPivots(resPivots)
{
  NodeManager* nm = NodeManager::currentNM();
  d_cl = nm->mkBoundVar("cl", nm->sExprType());
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool AletheProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                  const std::vector<Node>& fa,
                                                  bool& continueUpdate)
{
  return pn->getRule() != PfRule::ALETHE_RULE;
}

bool AletheProofPostprocessCallback::shouldUpdatePost(
    std::shared_ptr<ProofNode> pn, const std::vector<Node>& fa)
{
  Assert(!pn->getArguments().empty());
  AletheRule rule = getAletheRule(pn->getArguments()[0]);
  return rule == AletheRule::RESOLUTION_OR || rule == AletheRule::REORDERING
         || rule == AletheRule::CONTRACTION;
}

bool AletheProofPostprocessCallback::update(Node res,
                                            PfRule id,
                                            const std::vector<Node>& children,
                                            const std::vector<Node>& args,
                                            CDProof* cdp,
                                            bool& continueUpdate)
{
  Trace("alethe-proof") << "...Alethe pre-update " << res << " " << id << " "
                        << children << " / " << args << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> new_args = std::vector<Node>();

  switch (id)
  {
    // To keep the original shape of the proof node it is necessary to rederive
    // the original conclusion. However, the term that should be printed might
    // be different from that conclusion. Thus, it is stored as an additional
    // argument in the proof node. Usually, the only difference is an additional
    // cl operator or the outmost or operator being replaced by a cl operator.
    //
    // When steps are added to the proof that have not been there previously,
    // it is unwise to add them in the same manner. To illustrate this the
    // following counterexample shows the pitfalls of this approach:
    //
    //  (or a (or b c))   (not a)
    // --------------------------- RESOLUTION
    //  (or b c)
    //
    //  is converted into an Alethe proof that should be printed as
    //
    //  (cl a (or b c))   (cl (not a))
    // -------------------------------- RESOLUTION
    //  (cl (or b c))
    // --------------- OR
    //  (cl b c)
    //
    // Here, (cl (or b c)) and (cl b c) cannot correspond to the same proof node
    // (or b c). Thus, we build a new proof node using the kind SEXPR
    // that is then printed as (cl (or b c)). We denote this wrapping of a proof
    // node by using an extra pair of parenthesis, i.e. ((or b c)) is the proof
    // node printed as (cl (or b c)).
    //
    // Adding an OR node to a premises will take place in the finalize function
    // where in the case that a step is printed as (cl (or F1 ... Fn)) but used
    // as (cl F1 ... Fn) an OR step is added to transform it to this very thing.
    // This is necessary for rules that work on clauses, i.e. RESOLUTION,
    // CHAIN_RESOLUTION, REORDERING and FACTORING.
    //
    //
    // Some proof rules have a close correspondence in Alethe. There are two
    // very frequent patterns that, to avoid repetition, are described here and
    // referred to in the comments on the specific proof rules below.
    //
    // The first pattern, which will be called singleton pattern in the
    // following, adds the original proof node F with the corresponding rule R'
    // of the Alethe calculus and uses the same premises as the original proof
    // node (P1:F1) ... (Pn:Fn). However, the conclusion is printed as (cl F).
    //
    // This means a cvc5 rule R that looks as follows:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R
    //  F
    //
    // is transformed into:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R'
    //  (cl F)*
    //
    // * the corresponding proof node is F
    //
    // The second pattern, which will be called clause pattern in the following,
    // has a disjunction (or G1 ... Gn) as conclusion. It also adds the orignal
    // proof node (or G1 ... Gn) with the corresponding rule R' of the Alethe
    // calculus and uses the same premises as the original proof node (P1:F1)
    // ... (Pn:Fn). However, the conclusion is printed as (cl G1 ... Gn), i.e.
    // the or is replaced by the cl operator.
    //
    // This means a cvc5 rule R that looks as follows:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R
    //  (or G1 ... Gn)
    //
    // Is transformed into:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R'
    //  (cl G1 ... Gn)*
    //
    // * the corresponding proof node is (or G1 ... Gn)
    //
    //================================================= Core rules
    //======================== Assume and Scope
    case PfRule::ASSUME:
    {
      return addAletheStep(AletheRule::ASSUME, res, res, children, {}, *cdp);
    }
    // See proof_rule.h for documentation on the SCOPE rule. This comment uses
    // variable names as introduced there. Since the SCOPE rule originally
    // concludes
    // (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) but the ANCHOR rule
    // concludes (cl (not F1) ... (not Fn) F), to keep the original shape of the
    // proof node it is necessary to rederive the original conclusion. The
    // transformation is described below, depending on the form of SCOPE's
    // conclusion.
    //
    // Note that after the original conclusion is rederived the new proof node
    // will actually have to be printed, respectively, (cl (=> (and F1 ... Fn)
    // F)) or (cl (not (and F1 ... Fn))).
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
    // ------------------------------------ REORDERING
    //  VP2b
    // ------ CONTRACTION           ------- IMPLIES_NEG1
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
    // Note that if n = 1, then the ANCHOR step yields (cl (not F1) F), which is
    // the same as VP3. Since VP1 = VP3, the steps for that transformation are
    // not generated.
    //
    //
    // If F = false:
    //
    //                                    --------- IMPLIES_SIMPLIFY
    //    T1                                 VP9
    // --------- CONTRACTION              --------- EQUIV_1
    //    VP8                                VP10
    // -------------------------------------------- RESOLUTION
    //          (cl (not (and F1 ... Fn)))*
    //
    // VP8: (cl (=> (and F1 ... Fn) false))
    // VP9: (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
    // VP10: (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn)))
    //
    // Otherwise,
    //                T1
    //  ------------------------------ CONTRACTION
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
      for (const Node& arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
        sanitized_args.push_back(d_anc.convert(arg));
      }
      negNode.push_back(children[0]);  // (cl (not F1) ... (not Fn) F)
      Node vp1 = nm->mkNode(kind::SEXPR, negNode);
      success &= addAletheStep(AletheRule::ANCHOR_SUBPROOF,
                               vp1,
                               vp1,
                               children,
                               sanitized_args,
                               *cdp);

      Node andNode, vp3;
      if (args.size() == 1)
      {
        vp3 = vp1;
        andNode = args[0];  // F1
      }
      else
      {
        // Build vp2i
        andNode = nm->mkNode(kind::AND, args);  // (and F1 ... Fn)
        std::vector<Node> premisesVP2 = {vp1};
        std::vector<Node> notAnd = {d_cl, children[0]};  // cl F
        Node vp2_i;
        for (size_t i = 0, size = args.size(); i < size; i++)
        {
          vp2_i = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), args[i]);
          success &=
              addAletheStep(AletheRule::AND_POS, vp2_i, vp2_i, {}, {}, *cdp);
          premisesVP2.push_back(vp2_i);
          notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
        }

        Node vp2a = nm->mkNode(kind::SEXPR, notAnd);
        if (d_resPivots)
        {
          std::vector<Node> newArgs;
          for (const Node& arg : args)
          {
            newArgs.push_back(arg);
            newArgs.push_back(d_false);
          }
          success &= addAletheStep(
              AletheRule::RESOLUTION, vp2a, vp2a, premisesVP2, newArgs, *cdp);
        }
        else
        {
          success &= addAletheStep(AletheRule::RESOLUTION,
                                   vp2a,
                                   vp2a,
                                   premisesVP2,
                                   std::vector<Node>(),
                                   *cdp);
        }

        notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n)
        notAnd.push_back(children[0]);     //(cl (not (and F1 ... Fn))^n F)
        Node vp2b = nm->mkNode(kind::SEXPR, notAnd);
        success &=
            addAletheStep(AletheRule::REORDERING, vp2b, vp2b, {vp2a}, {}, *cdp);

        vp3 = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
        success &=
            addAletheStep(AletheRule::CONTRACTION, vp3, vp3, {vp2b}, {}, *cdp);
      }

      Node vp8 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::IMPLIES, andNode, children[0]));

      Node vp4 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], andNode);
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG1, vp4, vp4, {}, {}, *cdp);

      Node vp5 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0]);
      success &= addAletheStep(AletheRule::RESOLUTION,
                               vp5,
                               vp5,
                               {vp4, vp3},
                               d_resPivots ? std::vector<Node>{andNode, d_true}
                                           : std::vector<Node>(),
                               *cdp);

      Node vp6 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0].notNode());
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG2, vp6, vp6, {}, {}, *cdp);

      Node vp7 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], vp8[1]);
      success &=
          addAletheStep(AletheRule::RESOLUTION,
                        vp7,
                        vp7,
                        {vp5, vp6},
                        d_resPivots ? std::vector<Node>{children[0], d_true}
                                    : std::vector<Node>(),
                        *cdp);

      if (children[0] != d_false)
      {
        success &=
            addAletheStep(AletheRule::CONTRACTION, res, vp8, {vp7}, {}, *cdp);
      }
      else
      {
        success &=
            addAletheStep(AletheRule::CONTRACTION, vp8, vp8, {vp7}, {}, *cdp);

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
                                 d_resPivots ? std::vector<Node>{vp8[1], d_true}
                                             : std::vector<Node>(),
                                 *cdp);
      }

      return success;
    }
    case PfRule::THEORY_REWRITE:
    {
      return addAletheStep(AletheRule::ALL_SIMPLIFY,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Resolution and N-ary Resolution
    // See proof_rule.h for documentation on the RESOLUTION and CHAIN_RESOLUTION
    // rule. This comment uses variable names as introduced there.
    //
    // Because the RESOLUTION rule is merely a special case of CHAIN_RESOLUTION,
    // the same translation can be used for both.
    //
    // The main complication for the translation of the rule is that in the case
    // that the conclusion C is (or G1 ... Gn), the result is ambigous. E.g.,
    //
    // (cl F1 (or F2 F3))    (cl (not F1))
    // -------------------------------------- RESOLUTION
    // (cl (or F2 F3))
    //
    // (cl F1 F2 F3)         (cl (not F1))
    // -------------------------------------- RESOLUTION
    // (cl F2 F3)
    //
    // both (cl (or F2 F3)) and (cl F2 F3) correspond to the same proof node (or
    // F2 F3). Thus, it has to be checked if C is a singleton clause or not.
    //
    // If C = (or F1 ... Fn) is a non-singleton clause, then:
    //
    //   VP1 ... VPn
    // ------------------ RESOLUTION
    //  (cl F1 ... Fn)*
    //
    // Else if, C = false:
    //
    //   VP1 ... VPn
    // ------------------ RESOLUTION
    //       (cl)*
    //
    // Otherwise:
    //
    //   VP1 ... VPn
    // ------------------ RESOLUTION
    //      (cl C)*
    //
    //  * the corresponding proof node is C
    case PfRule::RESOLUTION:
    case PfRule::CHAIN_RESOLUTION:
    {
      std::vector<Node> newArgs;
      // checker expects opposite order. We always keep the pivots because we
      // need them to compute in updatePost whether we will add OR steps. If
      // d_resPivots is off we will remove the pivots after that.
      for (size_t i = 0, size = args.size(); i < size; i = i + 2)
      {
        newArgs.push_back(args[i + 1]);
        newArgs.push_back(args[i]);
      }
      if (!isSingletonClause(res, children, args))
      {
        return addAletheStepFromOr(
            AletheRule::RESOLUTION_OR, res, children, newArgs, *cdp);
      }
      return addAletheStep(AletheRule::RESOLUTION_OR,
                           res,
                           res == d_false ? nm->mkNode(kind::SEXPR, d_cl)
                                          : nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           newArgs,
                           *cdp);
    }
    // ======== Factoring
    // See proof_rule.h for documentation on the FACTORING rule. This comment
    // uses variable names as introduced there.
    //
    // If C2 = (or F1 ... Fn) but C1 != (or C2 ... C2), then VC2 = (cl F1 ...
    // Fn) Otherwise, VC2 = (cl C2).
    //
    //    P
    // ------- CONTRACTION
    //   VC2*
    //
    // * the corresponding proof node is C2
    case PfRule::FACTORING:
    {
      if (res.getKind() == kind::OR)
      {
        for (const Node& child : children[0])
        {
          if (child != res)
          {
            return addAletheStepFromOr(
                AletheRule::CONTRACTION, res, children, {}, *cdp);
          }
        }
      }
      return addAletheStep(AletheRule::CONTRACTION,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Reordering
    // This rule is translated according to the clauses pattern.
    case PfRule::REORDERING:
    {
      return addAletheStepFromOr(
          AletheRule::REORDERING, res, children, {}, *cdp);
    }
    // ======== Split
    // See proof_rule.h for documentation on the SPLIT rule. This comment
    // uses variable names as introduced there.
    //
    // --------- NOT_NOT      --------- NOT_NOT
    //    VP1                    VP2
    // -------------------------------- RESOLUTION
    //          (cl F (not F))*
    //
    // VP1: (cl (not (not (not F))) F)
    // VP2: (cl (not (not (not (not F)))) (not F))
    //
    // * the corresponding proof node is (or F (not F))
    case PfRule::SPLIT:
    {
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, args[0].notNode().notNode().notNode(), args[0]);
      Node vp2 = nm->mkNode(kind::SEXPR,
                            d_cl,
                            args[0].notNode().notNode().notNode().notNode(),
                            args[0].notNode());
      return addAletheStep(AletheRule::NOT_NOT, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(AletheRule::NOT_NOT, vp1, vp1, {}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::RESOLUTION,
                 res,
                 {vp1, vp2},
                 d_resPivots
                     ? std::vector<Node>{args[0].notNode().notNode().notNode(),
                                         d_true}
                     : std::vector<Node>(),
                 *cdp);
    }
    // ======== Equality resolution
    // See proof_rule.h for documentation on the EQ_RESOLVE rule. This
    // comment uses variable names as introduced there.
    //
    // If F1 = (or G1 ... Gn), then P1 will be printed as (cl G1 ... Gn) but
    // needs to be printed as (cl (or G1 ... Gn)). The only exception to this
    // are ASSUME steps that are always printed as (cl (or G1 ... Gn)) and
    // EQ_RESOLVE steps themselves.
    //
    //           ------  ...  ------ OR_NEG
    //   P1       VP21   ...   VP2n
    //  ---------------------------- RESOLUTION
    //              VP3
    //  ---------------------------- CONTRACTION
    //              VP4
    //
    //  for i=1 to n, VP2i: (cl (or G1 ... Gn) (not Gi))
    //  VP3: (cl (or G1 ... Gn)^n)
    //  VP4: (cl (or (G1 ... Gn))
    //
    //  Let child1 = VP4.
    //
    //
    // Otherwise, child1 = P1.
    //
    //
    // Then, if F2 = false:
    //
    //  ------ EQUIV_POS2
    //   VP1                P2    child1
    //  --------------------------------- RESOLUTION
    //                (cl)*
    //
    // Otherwise:
    //
    //  ------ EQUIV_POS2
    //   VP1                P2    child1
    //  --------------------------------- RESOLUTION
    //              (cl F2)*
    //
    // VP1: (cl (not (= F1 F2)) (not F1) F2)
    //
    // * the corresponding proof node is F2
    case PfRule::EQ_RESOLVE:
    {
      bool success = true;
      Node vp1 =
          nm->mkNode(kind::SEXPR,
                     {d_cl, children[1].notNode(), children[0].notNode(), res});
      Node child1 = children[0];

      // Transform (cl F1 ... Fn) into (cl (or F1 ... Fn))
      if (children[0].notNode() != children[1].notNode()
          && children[0].getKind() == kind::OR)
      {
        PfRule pr = cdp->getProofFor(child1)->getRule();
        if (pr != PfRule::ASSUME && pr != PfRule::EQ_RESOLVE)
        {
          std::vector<Node> clauses{d_cl};
          clauses.insert(clauses.end(),
                         children[0].begin(),
                         children[0].end());  //(cl G1 ... Gn)

          std::vector<Node> vp2Nodes{children[0]};
          std::vector<Node> resNodes{d_cl};
          std::vector<Node> newArgs;
          for (size_t i = 0, size = children[0].getNumChildren(); i < size; i++)
          {
            Node vp2i = nm->mkNode(
                kind::SEXPR,
                d_cl,
                children[0],
                children[0][i].notNode());  //(cl (or G1 ... Gn) (not Gi))
            success &=
                addAletheStep(AletheRule::OR_NEG, vp2i, vp2i, {}, {}, *cdp);
            vp2Nodes.push_back(vp2i);
            resNodes.push_back(children[0]);
            if (d_resPivots)
            {
              newArgs.push_back(children[0][i]);
              newArgs.push_back(d_true);
            }
          }
          Node vp3 = nm->mkNode(kind::SEXPR, resNodes);
          success &= addAletheStep(
              AletheRule::RESOLUTION, vp3, vp3, vp2Nodes, newArgs, *cdp);

          Node vp4 = nm->mkNode(kind::SEXPR, d_cl, children[0]);
          success &=
              addAletheStep(AletheRule::CONTRACTION, vp4, vp4, {vp3}, {}, *cdp);
          child1 = vp4;
        }
      }

      success &= addAletheStep(AletheRule::EQUIV_POS2, vp1, vp1, {}, {}, *cdp);

      return success &=
             addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           {vp1, children[1], child1},
                           d_resPivots ? std::vector<Node>{children[1],
                                                           d_false,
                                                           children[0],
                                                           d_false}
                                       : std::vector<Node>(),
                           *cdp);
    }
    // ======== Modus ponens
    // See proof_rule.h for documentation on the MODUS_PONENS rule. This comment
    // uses variable names as introduced there.
    //
    //     (P2:(=> F1 F2))
    // ------------------------ IMPLIES
    //  (VP1:(cl (not F1) F2))             (P1:F1)
    // -------------------------------------------- RESOLUTION
    //                   (cl F2)*
    //
    // * the corresponding proof node is F2
    case PfRule::MODUS_PONENS:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(
                 AletheRule::IMPLIES, vp1, vp1, {children[1]}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Double negation elimination
    // See proof_rule.h for documentation on the NOT_NOT_ELIM rule. This comment
    // uses variable names as introduced there.
    //
    // ---------------------------------- NOT_NOT
    //  (VP1:(cl (not (not (not F))) F))           (P:(not (not F)))
    // ------------------------------------------------------------- RESOLUTION
    //                            (cl F)*
    //
    // * the corresponding proof node is F
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(AletheRule::NOT_NOT, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Contradiction
    // See proof_rule.h for documentation on the CONTRA rule. This
    // comment uses variable names as introduced there.
    //
    //  P1   P2
    // --------- RESOLUTION
    //   (cl)*
    //
    // * the corresponding proof node is false
    case PfRule::CONTRA:
    {
      return addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl),
                           children,
                           d_resPivots ? std::vector<Node>{children[0], d_true}
                                       : std::vector<Node>(),
                           *cdp);
    }
    // ======== And elimination
    // This rule is translated according to the singleton pattern.
    case PfRule::AND_ELIM:
    {
      return addAletheStep(AletheRule::AND,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== And introduction
    // See proof_rule.h for documentation on the AND_INTRO rule. This
    // comment uses variable names as introduced there.
    //
    //
    // ----- AND_NEG
    //  VP1            P1 ... Pn
    // -------------------------- RESOLUTION
    //   (cl (and F1 ... Fn))*
    //
    // VP1:(cl (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // * the corresponding proof node is (and F1 ... Fn)
    case PfRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes = {d_cl, res};
      for (size_t i = 0, size = children.size(); i < size; i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = nm->mkNode(kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children = {vp1};
      new_children.insert(new_children.end(), children.begin(), children.end());
      std::vector<Node> newArgs;
      if (d_resPivots)
      {
        for (const Node& child : children)
        {
          newArgs.push_back(child);
          newArgs.push_back(d_false);
        }
      }
      return addAletheStep(AletheRule::AND_NEG, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
                              newArgs,
                              *cdp);
    }
    // ======== Not Or elimination
    // This rule is translated according to the singleton pattern.
    case PfRule::NOT_OR_ELIM:
    {
      return addAletheStep(AletheRule::NOT_OR,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Implication elimination
    // This rule is translated according to the clause pattern.
    case PfRule::IMPLIES_ELIM:
    {
      return addAletheStepFromOr(AletheRule::IMPLIES, res, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 1
    // This rule is translated according to the singleton pattern.
    case PfRule::NOT_IMPLIES_ELIM1:
    {
      return addAletheStep(AletheRule::NOT_IMPLIES1,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Not Implication elimination version 2
    // This rule is translated according to the singleton pattern.
    case PfRule::NOT_IMPLIES_ELIM2:
    {
      return addAletheStep(AletheRule::NOT_IMPLIES2,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Various elimination rules
    // The following rules are all translated according to the clause pattern.
    case PfRule::EQUIV_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::EQUIV1, res, children, {}, *cdp);
    }
    case PfRule::EQUIV_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::EQUIV2, res, children, {}, *cdp);
    }
    case PfRule::NOT_EQUIV_ELIM1:
    {
      return addAletheStepFromOr(
          AletheRule::NOT_EQUIV1, res, children, {}, *cdp);
    }
    case PfRule::NOT_EQUIV_ELIM2:
    {
      return addAletheStepFromOr(
          AletheRule::NOT_EQUIV2, res, children, {}, *cdp);
    }
    case PfRule::XOR_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::XOR1, res, children, {}, *cdp);
    }
    case PfRule::XOR_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::XOR2, res, children, {}, *cdp);
    }
    case PfRule::NOT_XOR_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::NOT_XOR1, res, children, {}, *cdp);
    }
    case PfRule::NOT_XOR_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::NOT_XOR2, res, children, {}, *cdp);
    }
    case PfRule::ITE_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::ITE2, res, children, {}, *cdp);
    }
    case PfRule::ITE_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::ITE1, res, children, {}, *cdp);
    }
    case PfRule::NOT_ITE_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::NOT_ITE2, res, children, {}, *cdp);
    }
    case PfRule::NOT_ITE_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::NOT_ITE1, res, children, {}, *cdp);
    }
    //================================================= De Morgan rules
    // ======== Not And
    // This rule is translated according to the clause pattern.
    case PfRule::NOT_AND:
    {
      return addAletheStepFromOr(AletheRule::NOT_AND, res, children, {}, *cdp);
    }

    //================================================= CNF rules
    // The following rules are all translated according to the clause pattern.
    case PfRule::CNF_AND_POS:
    {
      return addAletheStepFromOr(AletheRule::AND_POS, res, children, {}, *cdp);
    }
    case PfRule::CNF_AND_NEG:
    {
      return addAletheStepFromOr(AletheRule::AND_NEG, res, children, {}, *cdp);
    }
    case PfRule::CNF_OR_POS:
    {
      return addAletheStepFromOr(AletheRule::OR_POS, res, children, {}, *cdp);
    }
    case PfRule::CNF_OR_NEG:
    {
      return addAletheStepFromOr(AletheRule::OR_NEG, res, children, {}, *cdp);
    }
    case PfRule::CNF_IMPLIES_POS:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_POS, res, children, {}, *cdp);
    }
    case PfRule::CNF_IMPLIES_NEG1:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_NEG1, res, children, {}, *cdp);
    }
    case PfRule::CNF_IMPLIES_NEG2:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_POS1:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_POS2, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_POS2:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_POS1, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_NEG1:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_NEG2:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_NEG1, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_POS1:
    {
      return addAletheStepFromOr(AletheRule::XOR_POS1, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_POS2:
    {
      return addAletheStepFromOr(AletheRule::XOR_POS2, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_NEG1:
    {
      return addAletheStepFromOr(AletheRule::XOR_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_NEG2:
    {
      return addAletheStepFromOr(AletheRule::XOR_NEG1, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_POS1:
    {
      return addAletheStepFromOr(AletheRule::ITE_POS2, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_POS2:
    {
      return addAletheStepFromOr(AletheRule::ITE_POS1, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_NEG1:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_NEG2:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG1, res, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 3
    //
    // ----- ITE_POS1            ----- ITE_POS2
    //  VP1                       VP2
    // ------------------------------- RESOLUTION
    //             VP3
    // ------------------------------- REORDERING
    //             VP4
    // ------------------------------- CONTRACTION
    //  (cl (not (ite C F1 F2)) F1 F2)
    //
    // VP1: (cl (not (ite C F1 F2)) C F2)
    // VP2: (cl (not (ite C F1 F2)) (not C) F1)
    // VP3: (cl (not (ite C F1 F2)) F2 (not (ite C F1 F2)) F1)
    // VP4: (cl (not (ite C F1 F2)) (not (ite C F1 F2)) F1 F2)
    //
    // * the corresponding proof node is (or (not (ite C F1 F2)) F1 F2)
    case PfRule::CNF_ITE_POS3:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0], res[2]});
      Node vp2 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0].notNode(), res[1]});
      Node vp3 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[2], res[0], res[1]});
      Node vp4 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[0], res[1], res[2]});

      return addAletheStep(AletheRule::ITE_POS1, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::ITE_POS2, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              vp3,
                              vp3,
                              {vp1, vp2},
                              d_resPivots
                                  ? std::vector<Node>{args[0][0], d_true}
                                  : std::vector<Node>(),
                              *cdp)
             && addAletheStep(AletheRule::REORDERING, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::CONTRACTION, res, {vp4}, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    //
    // ----- ITE_NEG1            ----- ITE_NEG2
    //  VP1                       VP2
    // ------------------------------- RESOLUTION
    //             VP3
    // ------------------------------- REORDERING
    //             VP4
    // ------------------------------- CONTRACTION
    //  (cl (ite C F1 F2) C (not F2))
    //
    // VP1: (cl (ite C F1 F2) C (not F2))
    // VP2: (cl (ite C F1 F2) (not C) (not F1))
    // VP3: (cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1))
    // VP4: (cl (ite C F1 F2) (ite C F1 F2) (not F1) (not F2))
    //
    // * the corresponding proof node is (or (ite C F1 F2) C (not F2))
    case PfRule::CNF_ITE_NEG3:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0], res[2]});
      Node vp2 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0].notNode(), res[1]});
      Node vp3 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[2], res[0], res[1]});
      Node vp4 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[0], res[1], res[2]});

      return addAletheStep(AletheRule::ITE_NEG1, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::ITE_NEG2, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              vp3,
                              vp3,
                              {vp1, vp2},
                              d_resPivots
                                  ? std::vector<Node>{args[0][0], d_true}
                                  : std::vector<Node>(),
                              *cdp)
             && addAletheStep(AletheRule::REORDERING, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::CONTRACTION, res, {vp4}, {}, *cdp);
    }
    //================================================= Equality rules
    // The following rules are all translated according to the singleton
    // pattern.
    case PfRule::REFL:
    {
      return addAletheStep(AletheRule::REFL,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    case PfRule::SYMM:
    {
      return addAletheStep(
          res.getKind() == kind::NOT ? AletheRule::NOT_SYMM : AletheRule::SYMM,
          res,
          nm->mkNode(kind::SEXPR, d_cl, res),
          children,
          {},
          *cdp);
    }
    case PfRule::TRANS:
    {
      return addAletheStep(AletheRule::TRANS,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Congruence
    // In the case that the kind of the function symbol f? is FORALL or
    // EXISTS, the cong rule needs to be converted into a bind rule. The first
    // n children will be refl rules, e.g. (= (v0 Int) (v0 Int)).
    //
    //  Let t1 = (BOUND_VARIABLE LIST (v1 A1) ... (vn An)) and s1 =
    //  (BOUND_VARIABLE LIST (v1 A1) ... (vn vn)).
    //
    //  ----- REFL ... ----- REFL
    //   VP1            VPn             P2
    //  --------------------------------------- bind,
    //                                          ((:= (v1 A1) v1) ...
    //                                          (:= (vn An) vn))
    //   (cl (= (forall ((v1 A1)...(vn An)) t2)
    //   (forall ((v1 B1)...(vn Bn)) s2)))**
    //
    //  VPi: (cl (= vi vi))*
    //
    //  * the corresponding proof node is (or (= vi vi))
    //
    // Otherwise, the rule follows the singleton pattern, i.e.:
    //
    //    P1 ... Pn
    //  -------------------------------------------------------- cong
    //   (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))**
    //
    // ** the corresponding proof node is (= (<kind> f? t1 ... tn) (<kind> f?
    // s1 ... sn))
    case PfRule::CONG:
    {
      if (res[0].isClosure())
      {
        std::vector<Node> vpis;
        bool success = true;
        for (size_t i = 0, size = children[0][0].getNumChildren(); i < size;
             i++)
        {
          Node vpi = children[0][0][i].eqNode(children[0][1][i]);
          new_args.push_back(vpi);
          vpi = nm->mkNode(kind::SEXPR, d_cl, vpi);
          vpis.push_back(vpi);
          success &= addAletheStep(AletheRule::REFL, vpi, vpi, {}, {}, *cdp);
        }
        vpis.push_back(children[1]);
        return success
               && addAletheStep(AletheRule::ANCHOR_BIND,
                                res,
                                nm->mkNode(kind::SEXPR, d_cl, res),
                                vpis,
                                new_args,
                                *cdp);
      }
      return addAletheStep(AletheRule::CONG,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== True intro
    //
    // ------------------------------- EQUIV_SIMPLIFY
    //  (VP1:(cl (= (= F true) F)))
    // ------------------------------- EQUIV2
    //  (VP2:(cl (= F true) (not F)))           P
    // -------------------------------------------- RESOLUTION
    //  (cl (= F true))*
    //
    // * the corresponding proof node is (= F true)
    case PfRule::TRUE_INTRO:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, res.eqNode(children[0]));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV2, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== True elim
    //
    // ------------------------------- EQUIV_SIMPLIFY
    //  (VP1:(cl (= (= F true) F)))
    // ------------------------------- EQUIV1
    //  (VP2:(cl (not (= F true)) F))           P
    // -------------------------------------------- RESOLUTION
    //  (cl F)*
    //
    // * the corresponding proof node is F
    case PfRule::TRUE_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].eqNode(res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV1, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== False intro
    //
    // ----- EQUIV_SIMPLIFY
    //  VP1
    // ----- EQUIV2     ----- NOT_NOT
    //  VP2              VP3
    // ---------------------- RESOLUTION
    //          VP4                        P
    // -------------------------------------- RESOLUTION
    //          (cl (= F false))*
    //
    // VP1: (cl (= (= F false) (not F)))
    // VP2: (cl (= F false) (not (not F)))
    // VP3: (cl (not (not (not F))) F)
    // VP4: (cl (= F false) F)
    //
    // * the corresponding proof node is (= F false)
    case PfRule::FALSE_INTRO:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, res.eqNode(children[0]));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      Node vp3 = nm->mkNode(
          kind::SEXPR, d_cl, children[0].notNode().notNode(), children[0][0]);
      Node vp4 = nm->mkNode(kind::SEXPR, d_cl, res, children[0][0]);

      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV2, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::NOT_NOT, vp3, vp3, {}, {}, *cdp)
             && addAletheStep(
                 AletheRule::RESOLUTION,
                 vp4,
                 vp4,
                 {vp2, vp3},
                 d_resPivots ? std::vector<Node>{children[0].notNode(), d_true}
                             : std::vector<Node>(),
                 *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp4, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0][0], d_true}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== False elim
    //
    // ----- EQUIV_SIMPLIFY
    //  VP1
    // ----- EQUIV1
    //  VP2                P
    // ---------------------- RESOLUTION
    //     (cl (not F))*
    //
    // VP1: (cl (= (= F false) (not F)))
    // VP2: (cl (not (= F false)) (not F))
    // VP3: (cl (not (not (not F))) F)
    // VP4: (cl (= F false) F)
    //
    // * the corresponding proof node is (not F)
    case PfRule::FALSE_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].eqNode(res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV1, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    //================================================= Skolems rules
    // ======== Skolem intro
    // Since this rule just equates a term to its purification skolem, whose
    // conversion is the term itself, the converted conclusion is an equality
    // between the same terms.
    case PfRule::SKOLEM_INTRO:
    {
      return addAletheStep(AletheRule::REFL,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           {},
                           {},
                           *cdp);
    }
    // ======== Replace term by its axiom definition
    // For now this introduces a hole. The processing in the future should
    // generate corresponding Alethe steps for each particular axiom for term
    // removal (for example for the ITE case).
    case PfRule::REMOVE_TERM_FORMULA_AXIOM:
    {
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           {},
                           {},
                           *cdp);
    }
    // ======== Skolemize
    // See proof_rule.h for documentation on the SKOLEMIZE rule. This
    // comment uses variable names as introduced there.
    //
    // Either a positive existential or a negative forall is skolemized. First
    // step is to build the Alethe skolemization step which introduces a valid
    // equality:
    //
    //                      ---------------- REFL
    //                       (= F F*sigma')
    //  ----------------------------------------------- ANCHOR_SKO_EX, sigma_n
    //          (= (exists ((xn Tn)) F) F*sigma')
    // -----------------------------------------------
    //                       ...
    //  ----------------------------------------------- ANCHOR_SKO_EX, sigma_2
    //   (= (exists ((x2 T1) ... (xn Tn)) F) F*sigma')
    //  ----------------------------------------------- ANCHOR_SKO_EX, sigma_1
    //   (= (exists ((x1 T1) ... (xn Tn)) F) F*sigma')
    //
    // where sigma' is the cumulative substitution built from sigma1...sigma_n,
    // and each sigma_i replaces xi by the choice term (epsilon ((xi Ti))
    // (exists ((xi+1 Ti+1) ... (xn+1 Tn+1)) F)).
    //
    // Then, we apply the equivalence elimination reasoning to obtain F*sigma
    // from the premise:
    //
    //  ---------------- EQUIV_POS2
    //     VP1              (= (exists (...) F) F*sigma')       (exists (...) F)
    //  ------------------------------------------------------------- RESOLUTION
    //                           F*sigma'
    //
    // VP1 :
    //  (cl (not (= (exists (...) F) F*sigma')) (not (exists (...) F)) F*sigma')
    //
    // Note that F*sigma' is equivalent to F*sigma once its skolem terms are
    // lifted to choice terms by the node converter.
    //
    // The case for negative forall is analagous except the rules are
    // ANCHOR_SKO_FORALL and the one concluding the desired equivalence is
    // followed by a congruence step to wrap the equality terms under a
    // negation, i.e., (not ...).
    case PfRule::SKOLEMIZE:
    {
      AletheRule skoRule;
      bool isExists;
      Node quant, skolemized;
      Kind quantKind;
      if (children[0].getKind() == kind::EXISTS)
      {
        isExists = true;
        skoRule = AletheRule::ANCHOR_SKO_EX;
        quant = children[0];
        skolemized = res;
        quantKind = kind::EXISTS;
      }
      else
      {
        isExists = false;
        skoRule = AletheRule::ANCHOR_SKO_FORALL;
        quant = children[0][0];
        skolemized = res[0];
        quantKind = kind::FORALL;
      }
      // add rfl step for final replacement
      Node curPremise = nm->mkNode(
          kind::SEXPR, d_cl, d_anc.convert(quant[1].eqNode(skolemized)));
      addAletheStep(AletheRule::REFL, curPremise, curPremise, {}, {}, *cdp);
      std::vector<Node> bVars{quant[0].begin(), quant[0].end()};
      for (size_t size = quant[0].getNumChildren(), i = size; i > 0; --i)
      {
        // build i-th anchor step, whose argument will be the i-th variable
        // mapped to a choice term for that variable over the quantifier over
        // i+1-th to n-th variable over the quant body.
        Node ithBVars = nm->mkNode(
            kind::BOUND_VAR_LIST,
            std::vector<Node>{bVars.begin() + (size - i), bVars.end()});
        // What we are currently skolemizing is the quantifier (i-1)-th
        // variable. So we must take the suffix of variables from that one (note
        // that when i == 1 the suffix is all the variables)
        Node curSkolemizing =
            i == 1 ? quant
                   : nm->mkNode(quantKind,
                                nm->mkNode(kind::BOUND_VAR_LIST, ithBVars),
                                quant[1]);
        // The choice term is for the (i-1)-th variable defined as the
        // quantifier with the suffix from the i-th variable. This is the same
        // as the term we skolemized in the previous iteration. Note that for
        // the last variable in the suffix this is what was used in the REFL
        // step. In either case, this is always the lhs of the equality in
        // curPremise (under the cl). Remember that when doing SKO_FORALL the
        // body of the choice is negated.
        Node ithChoice = nm->mkNode(
            kind::WITNESS,
            nm->mkNode(kind::BOUND_VAR_LIST, quant[0][i - 1]),
            isExists ? curPremise[1][0] : curPremise[1][0].notNode());
        Node conclusion =
            nm->mkNode(kind::SEXPR,
                       d_cl,
                       d_anc.convert(curSkolemizing.eqNode(skolemized)));
        addAletheStep(skoRule,
                      conclusion,
                      conclusion,
                      {curPremise},
                      {d_anc.convert(quant[0][i - 1].eqNode(ithChoice))},
                      *cdp);
        // update premise
        curPremise = conclusion;
      }
      // add congruence step with NOT for the forall case
      if (!isExists)
      {
        Node conclusion = nm->mkNode(
            kind::SEXPR,
            d_cl,
            (curPremise[1][0].notNode()).eqNode(curPremise[1][1].notNode()));
        addAletheStep(
            AletheRule::CONG, conclusion, conclusion, {curPremise}, {}, *cdp);
        curPremise = conclusion;
      }
      // now equality resolution reasoning
      Node vp1 = nm->mkNode(
          kind::SEXPR,
          {d_cl, curPremise[1].notNode(), children[0].notNode(), res});
      addAletheStep(AletheRule::EQUIV_POS2, vp1, vp1, {}, {}, *cdp);
      addAletheStep(
          AletheRule::RESOLUTION,
          res,
          nm->mkNode(kind::SEXPR, d_cl, res),
          {vp1, curPremise, children[0]},
          d_resPivots
              ? std::vector<Node>{curPremise[1], d_false, children[0], d_false}
              : std::vector<Node>(),
          *cdp);
      return true;
    }
    // ======== Bitvector
    //
    // ------------------------ BV_BITBLAST_STEP_BV<KIND>
    //  (cl (= t bitblast(t)))
    case PfRule::BV_BITBLAST_STEP:
    {
      Assert(s_bvKindToAletheRule.find(res[0].getKind())
             != s_bvKindToAletheRule.end())
          << "Bit-blasted kind not supported in Alethe post-processing.";
      return addAletheStep(s_bvKindToAletheRule.at(res[0].getKind()),
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    //================================================= Quantifiers rules
    // ======== Instantiate
    // See proof_rule.h for documentation on the INSTANTIATE rule. This
    // comment uses variable names as introduced there.
    //
    // ----- FORALL_INST, (= x1 t1) ... (= xn tn)
    //  VP1
    // ----- OR
    //  VP2              P
    // -------------------- RESOLUTION
    //     (cl F*sigma)^
    //
    // VP1: (cl (or (not (forall ((x1 T1) ... (xn Tn)) F*sigma)
    // VP2: (cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma)
    //
    // ^ the corresponding proof node is F*sigma
    case PfRule::INSTANTIATE:
    {
      for (size_t i = 0, size = children[0][0].getNumChildren(); i < size; i++)
      {
        new_args.push_back(children[0][0][i].eqNode(args[i]));
      }
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::OR, children[0].notNode(), res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      return addAletheStep(
                 AletheRule::FORALL_INST, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::OR, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    //================================================= Arithmetic rules
    // ======== Adding Scaled Inequalities
    //
    // -------------------------------------- LA_GENERIC
    // (cl (not P1) ... (not Pn) (>< t1 t2))              P1 ... Pn
    // ------------------------------------------------------------- RESOLUTION
    //  (cl (>< t1 t2))*
    //
    // * the corresponding proof node is (>< t1 t2)
    case PfRule::ARITH_SUM_UB:
    {
      // if the conclusion were an equality we'd need to phrase LA_GENERIC in
      // terms of disequalities, but ARITH_SUM_UB does not have equalities as
      // conclusions
      Assert(res.getKind() != kind::EQUAL);
      Node one = nm->mkConstInt(Rational(1));
      Node minusOne = nm->mkConstInt(Rational(-1));
      std::vector<Node> resArgs;
      std::vector<Node> resChildren;
      std::vector<Node> lits{d_cl};
      for (const Node& child : children)
      {
        lits.push_back(child.notNode());
        // equalities are multiplied by minus 1 rather than 1
        new_args.push_back(child.getKind() == kind::EQUAL ? minusOne : one);
        resArgs.push_back(child);
        resArgs.push_back(d_false);
      }
      lits.push_back(res);
      new_args.push_back(one);
      Node laGen = nm->mkNode(kind::SEXPR, lits);
      addAletheStep(AletheRule::LA_GENERIC, laGen, laGen, {}, new_args, *cdp);
      resChildren.push_back(laGen);
      resChildren.insert(resChildren.end(), children.begin(), children.end());
      return addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           resChildren,
                           d_resPivots ? resArgs : std::vector<Node>(),
                           *cdp);
    }
    // Direct translation
    case PfRule::ARITH_MULT_POS:
    case PfRule::ARITH_MULT_NEG:
    {
      // We require the multiplicative factor to be a value
      Assert(args[0].isConst());
      return addAletheStep(id == PfRule::ARITH_MULT_POS
                               ? AletheRule::LA_MULT_POS
                               : AletheRule::LA_MULT_NEG,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Tightening Strict Integer Upper Bounds
    //
    // ----- LA_GENERIC, 1
    //  VP1                      P
    // ------------------------------------- RESOLUTION
    //  (cl (<= i greatestIntLessThan(c)))*
    //
    // VP1: (cl (not (< i c)) (<= i greatestIntLessThan(c)))
    //
    // * the corresponding proof node is (<= i greatestIntLessThan(c))
    case PfRule::INT_TIGHT_UB:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      std::vector<Node> new_children = {vp1, children[0]};
      new_args.push_back(nm->mkConstInt(Rational(1)));
      new_args.push_back(nm->mkConstInt(Rational(1)));
      return addAletheStep(AletheRule::LA_GENERIC, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Tightening Strict Integer Lower Bounds
    //
    // ----- LA_GENERIC, 1
    //  VP1                      P
    // ------------------------------------- RESOLUTION
    //  (cl (>= i leastIntGreaterThan(c)))*
    //
    // VP1: (cl (not (> i c)) (>= i leastIntGreaterThan(c)))
    //
    // * the corresponding proof node is (>= i leastIntGreaterThan(c))
    case PfRule::INT_TIGHT_LB:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      std::vector<Node> new_children = {vp1, children[0]};
      new_args.push_back(nm->mkConstInt(Rational(1)));
      new_args.push_back(nm->mkConstInt(Rational(1)));
      return addAletheStep(AletheRule::LA_GENERIC, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Trichotomy of the reals
    // See proof_rule.h for documentation on the ARITH_TRICHOTOMY rule. This
    // comment uses variable names as introduced there.
    //
    // If C = (= x c) or C = (> x c) pre-processing has to transform (>= x c)
    // into (<= c x)
    //
    // ------------------------------------------------------ LA_DISEQUALITY
    //  (VP1: (cl (or (= x c) (not (<= x c)) (not (<= c x)))))
    // -------------------------------------------------------- OR
    //  (VP2: (cl (= x c) (not (<= x c)) (not (<= c x))))
    //
    // If C = (> x c) or C = (< x c) post-processing has to be added. In these
    // cases resolution on VP2 A B yields (not (<=x c)) or (not (<= c x)) and
    // comp_simplify is used to transform it into C. Otherwise,
    //
    //  VP2   A   B
    // ---------------- RESOLUTION
    //  (cl C)*
    //
    // * the corresponding proof node is C
    case PfRule::ARITH_TRICHOTOMY:
    {
      bool success = true;
      Node equal, lesser, greater;

      Kind k = res.getKind();
      if (k == kind::EQUAL)
      {
        equal = res;
        if (children[0].getKind() == kind::LEQ)
        {
          greater = children[0];
          lesser = children[1];
        }
        else
        {
          greater = children[1];
          lesser = children[0];
        }
      }
      // Add case where res is not =
      else if (res.getKind() == kind::GT)
      {
        greater = res;
        if (children[0].getKind() == kind::NOT)
        {
          equal = children[0];
          lesser = children[1];
        }
        else
        {
          equal = children[1];
          lesser = children[0];
        }
      }
      else
      {
        lesser = res;
        if (children[0].getKind() == kind::NOT)
        {
          equal = children[0];
          greater = children[1];
        }
        else
        {
          equal = children[1];
          greater = children[0];
        }
      }

      Node x, c;
      if (equal.getKind() == kind::NOT)
      {
        x = equal[0][0];
        c = equal[0][1];
      }
      else
      {
        x = equal[0];
        c = equal[1];
      }
      Node vp_child1 = children[0], vp_child2 = children[1];

      // Preprocessing
      if (res == equal || res == greater)
      {  // C = (= x c) or C = (> x c)
        // lesser = (>= x c)
        Node vpc2 = nm->mkNode(
            kind::SEXPR,
            d_cl,
            nm->mkNode(kind::GEQ, x, c).eqNode(nm->mkNode(kind::LEQ, c, x)));
        // (cl (= (>= x c) (<= c x)))
        Node vpc1 = nm->mkNode(kind::SEXPR,
                               {d_cl,
                                vpc2[1].notNode(),
                                nm->mkNode(kind::GEQ, x, c).notNode(),
                                nm->mkNode(kind::LEQ, c, x)});
        // (cl (not(= (>= x c) (<= c x))) (not (>= x c)) (<= c x))
        vp_child1 = nm->mkNode(
            kind::SEXPR, d_cl, nm->mkNode(kind::LEQ, c, x));  // (cl (<= c x))

        success &=
            addAletheStep(AletheRule::EQUIV_POS2, vpc1, vpc1, {}, {}, *cdp)
            && addAletheStep(
                AletheRule::COMP_SIMPLIFY, vpc2, vpc2, {}, {}, *cdp)
            && addAletheStep(
                AletheRule::RESOLUTION,
                vp_child1,
                vp_child1,
                {vpc1, vpc2, lesser},
                d_resPivots
                    ? std::vector<Node>{vpc2[1], d_false, lesser, d_false}
                    : std::vector<Node>(),
                *cdp);
        // greater = (<= x c) or greater = (not (= x c)) -> no preprocessing
        // necessary
        vp_child2 = res == equal ? greater : equal;
      }

      // Process
      Node vp1 = nm->mkNode(kind::SEXPR,
                            d_cl,
                            nm->mkNode(kind::OR,
                                       nm->mkNode(kind::EQUAL, x, c),
                                       nm->mkNode(kind::LEQ, x, c).notNode(),
                                       nm->mkNode(kind::LEQ, c, x).notNode()));
      // (cl (or (= x c) (not (<= x c)) (not (<= c x))))
      Node vp2 = nm->mkNode(kind::SEXPR,
                            {d_cl,
                             nm->mkNode(kind::EQUAL, x, c),
                             nm->mkNode(kind::LEQ, x, c).notNode(),
                             nm->mkNode(kind::LEQ, c, x).notNode()});
      // (cl (= x c) (not (<= x c)) (not (<= c x)))
      success &=
          addAletheStep(AletheRule::LA_DISEQUALITY, vp1, vp1, {}, {}, *cdp)
          && addAletheStep(AletheRule::OR, vp2, vp2, {vp1}, {}, *cdp);

      // Postprocessing
      if (res == equal)
      {  // no postprocessing necessary
        return success
               && addAletheStep(
                   AletheRule::RESOLUTION,
                   res,
                   nm->mkNode(kind::SEXPR, d_cl, res),
                   {vp2, vp_child1, vp_child2},
                   d_resPivots
                       ? std::vector<Node>{vp_child1[1],
                                           d_false,
                                           // note that vp_child2 is not a
                                           // clause, so it is itself the pivot
                                           vp_child2,
                                           d_false}
                       : std::vector<Node>(),
                   *cdp);
      }
      if (res == greater)
      {  // have (not (<= x c)) but result should be (> x c)
        Node vp3 = nm->mkNode(
            kind::SEXPR,
            d_cl,
            nm->mkNode(kind::LEQ, x, c).notNode());  // (cl (not (<= x c)))
        Node vp4 = nm->mkNode(
            kind::SEXPR,
            {d_cl,
             nm->mkNode(kind::EQUAL,
                        nm->mkNode(kind::GT, x, c),
                        nm->mkNode(kind::LEQ, x, c).notNode())
                 .notNode(),
             nm->mkNode(kind::GT, x, c),
             nm->mkNode(kind::LEQ, x, c)
                 .notNode()
                 .notNode()});  // (cl (not(= (> x c) (not (<= x c)))) (> x c)
                                // (not (not (<= x c))))
        Node vp5 =
            nm->mkNode(kind::SEXPR,
                       d_cl,
                       nm->mkNode(kind::GT, x, c)
                           .eqNode(nm->mkNode(kind::LEQ, x, c).notNode()));
        // (cl (= (> x c) (not (<= x c))))

        return success
               && addAletheStep(AletheRule::RESOLUTION,
                                vp3,
                                vp3,
                                {vp2, vp_child1, vp_child2},
                                d_resPivots ? std::vector<Node>{vp_child1[1],
                                                                d_false,
                                                                vp_child2[0],
                                                                d_true}
                                            : std::vector<Node>(),
                                *cdp)
               && addAletheStep(AletheRule::EQUIV_POS1, vp4, vp4, {}, {}, *cdp)
               && addAletheStep(
                   AletheRule::COMP_SIMPLIFY, vp5, vp5, {}, {}, *cdp)
               && addAletheStep(
                   AletheRule::RESOLUTION,
                   res,
                   nm->mkNode(kind::SEXPR, d_cl, res),
                   {vp3, vp4, vp5},
                   d_resPivots
                       ? std::vector<Node>{vp3[1], d_true, vp5[1], d_false}
                       : std::vector<Node>(),
                   *cdp);
      }
      // have (not (<= c x)) but result should be (< x c)
      Node vp3 = nm->mkNode(
          kind::SEXPR,
          d_cl,
          nm->mkNode(kind::LEQ, c, x).notNode());  // (cl (not (<= c x)))
      Node vp4 =
          nm->mkNode(kind::SEXPR,
                     {d_cl,
                      nm->mkNode(kind::LT, x, c)
                          .eqNode(nm->mkNode(kind::LEQ, c, x).notNode())
                          .notNode(),
                      nm->mkNode(kind::LT, x, c),
                      nm->mkNode(kind::LEQ, c, x)
                          .notNode()
                          .notNode()});  // (cl (not(= (< x c) (not (<= c x))))
                                         // (< x c) (not (not (<= c x))))
      Node vp5 = nm->mkNode(
          kind::SEXPR,
          d_cl,
          nm->mkNode(kind::LT, x, c)
              .eqNode(nm->mkNode(kind::LEQ, c, x)
                          .notNode()));  // (cl (= (< x c) (not (<= c x))))
      return success
             && addAletheStep(AletheRule::RESOLUTION,
                              vp3,
                              vp3,
                              {vp2, vp_child1, vp_child2},
                              d_resPivots ? std::vector<Node>{vp_child1,
                                                              d_false,
                                                              vp_child2[0],
                                                              d_true}
                                          : std::vector<Node>(),
                              *cdp)
             && addAletheStep(AletheRule::EQUIV_POS1, vp4, vp4, {}, {}, *cdp)
             && addAletheStep(AletheRule::COMP_SIMPLIFY, vp5, vp5, {}, {}, *cdp)
             && addAletheStep(
                 AletheRule::RESOLUTION,
                 res,
                 nm->mkNode(kind::SEXPR, d_cl, res),
                 {vp3, vp4, vp5},
                 d_resPivots
                     ? std::vector<Node>{vp3[1], d_true, vp5[1], d_false}
                     : std::vector<Node>(),
                 *cdp);
    }
    default:
    {
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           args,
                           *cdp);
    }
  }
}

bool AletheProofPostprocessCallback::maybeReplacePremiseProof(Node premise,
                                                              CDProof* cdp)
{
  // This method is called only when the premise is used as a singleton
  // clause. If its proof however concludes a non-singleton clause it'll fail
  // the test below and we must change its proof.
  std::shared_ptr<ProofNode> premisePf = cdp->getProofFor(premise);
  Node premisePfConclusion = premisePf->getArguments()[2];
  if (premisePfConclusion.getNumChildren() <= 2
      || premisePfConclusion[0] != d_cl)
  {
    return false;
  }
  // If this resolution child is used as a singleton OR but the rule
  // justifying it concludes a clause, then we are necessarily in this
  // scenario:
  //
  // (or t1 ... tn)
  // -------------- OR
  // (cl t1 ... tn)
  // ---------------- FACTORING/REORDERING
  // (cl t1' ... tn')
  //
  // where what is used in the resolution is actually (or t1' ... tn').
  //
  // This happens when (or t1' ... tn') has been added to the SAT solver as
  // a literal as well, and its node clashed with the conclusion of the
  // FACTORING/REORDERING step.
  //
  // The solution is to *not* use FACTORING/REORDERING (which in Alethe
  // operate on clauses) but generate a proof to obtain (via rewriting) the
  // expected node (or t1' ... tn') from the original node (or t1 ... tn).
  NodeManager* nm = NodeManager::currentNM();
  Trace("alethe-proof") << "\n";
  CVC5_UNUSED AletheRule premisePfRule =
      getAletheRule(premisePf->getArguments()[0]);
  CVC5_UNUSED AletheRule premiseChildPfRule =
      getAletheRule(premisePf->getChildren()[0]->getArguments()[0]);
  Assert((premisePfRule == AletheRule::CONTRACTION
          || premisePfRule == AletheRule::REORDERING)
         && premiseChildPfRule == AletheRule::OR);
  // get great grand child
  std::shared_ptr<ProofNode> premiseChildPf =
      premisePf->getChildren()[0]->getChildren()[0];
  Node premiseChildConclusion = premiseChildPf->getResult();
  // Note that we need to add this proof node explicitly (i.e., as an ASSUME
  // step) to cdp because cdp does not have a step for
  // premiseChildConclusion. Rather it is only present in cdp as a descendant of
  // premisePf (which is in cdp), so if premisePf is to be lost, then so will
  // premiseChildPf. By adding the ASSUME step for premiseChildConclusion, a
  // step will be present in cdp connecting premiseChildConclusion to
  // premiseChildPf (since by default adding an ASSUME step will not rewrite an
  // existing proof for a node).
  addAletheStep(AletheRule::ASSUME,
                premiseChildConclusion,
                premiseChildConclusion,
                {},
                {},
                *cdp);
  // equate it to what we expect, use equiv elim and resolution to
  // obtain a proof the expected
  Node equiv = premiseChildConclusion.eqNode(premise);
  addAletheStep(AletheRule::ALL_SIMPLIFY,
                equiv,
                nm->mkNode(kind::SEXPR, d_cl, equiv),
                {},
                {},
                *cdp);
  Node equivElim = nm->mkNode(
      kind::SEXPR,
      {d_cl, equiv.notNode(), premiseChildConclusion.notNode(), premise});
  addAletheStep(AletheRule::EQUIV_POS2, equivElim, equivElim, {}, {}, *cdp);
  Node newPremise = nm->mkNode(kind::SEXPR, d_cl, premise);
  addAletheStep(
      AletheRule::RESOLUTION,
      newPremise,
      newPremise,
      {equivElim, equiv, premiseChildConclusion},
      d_resPivots
          ? std::vector<Node>{equiv, d_false, premiseChildConclusion, d_false}
          : std::vector<Node>(),
      *cdp);
  Trace("alethe-proof") << "Reverted handling as a clause for converting "
                        << premiseChildConclusion << " into " << premise
                        << std::endl;
  return true;
}

// Adds an OR rule to the premises of a step if the premise is not a clause and
// should not be a singleton. Since CONTRACTION and REORDERING always take
// non-singletons, this function adds an OR step to their premise if it was
// formerly printed as (cl (or F1 ... Fn)). For resolution, it is necessary to
// check all children to find out whether they're singleton before determining
// if they are already printed correctly.
bool AletheProofPostprocessCallback::updatePost(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  AletheRule rule = getAletheRule(args[0]);
  Trace("alethe-proof") << "...Alethe post-update " << rule << " / " << res
                        << " / args: " << args << std::endl;
  switch (rule)
  {
    // In the case of a resolution rule the rule might originally have been a
    // cvc5 RESOLUTION or CHAIN_RESOLUTION rule, it is possible
    // that one of the children was printed as (cl (or F1 ... Fn)) but used as
    // (cl F1 ... Fn). However, from the pivot of the
    // resolution step for the child we can determine an additional OR step is
    // necessary to convert (cl (or ...)) to (cl ...).
    case AletheRule::RESOLUTION_OR:
    {
      // if we do not have pivots, we can't compute easily, so we do not try.
      // This should only be the case if this proof node was previously updated
      // and we are not printing pivots.
      if (args.size() < 4)
      {
        return false;
      }
      std::vector<Node> newChildren = children;
      bool hasUpdated = false;

      // Note that we will have inverted the order of polarity/pivot.
      size_t polIdx, pivIdx;
      polIdx = 4;
      pivIdx = 3;
      // The first child is used as a non-singleton clause if it is not equal
      // to its pivot L_1. Since it's the first clause in the resolution it can
      // only be equal to the pivot in the case the polarity is true.
      if (children[0].getKind() == kind::OR
          && (args[polIdx] != d_true || args[pivIdx] != children[0]))
      {
        std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
        Node childConclusion = childPf->getArguments()[2];
        AletheRule childRule = getAletheRule(childPf->getArguments()[0]);
        // if child conclusion is of the form (sexpr cl (or ...)), then we need
        // to add an OR step, since this child must not be a singleton
        if ((childConclusion.getNumChildren() == 2 && childConclusion[0] == d_cl
             && childConclusion[1].getKind() == kind::OR)
            || (childRule == AletheRule::ASSUME
                && childConclusion.getKind() == kind::OR))
        {
          hasUpdated = true;
          // Add or step
          std::vector<Node> subterms{d_cl};
          if (childRule == AletheRule::ASSUME)
          {
            subterms.insert(
                subterms.end(), childConclusion.begin(), childConclusion.end());
          }
          else
          {
            subterms.insert(subterms.end(),
                            childConclusion[1].begin(),
                            childConclusion[1].end());
          }
          Node newConclusion = nm->mkNode(kind::SEXPR, subterms);
          addAletheStep(AletheRule::OR,
                        newConclusion,
                        newConclusion,
                        {children[0]},
                        {},
                        *cdp);
          newChildren[0] = newConclusion;
          Trace("alethe-proof") << "Added OR step for " << childConclusion
                                << " / " << newConclusion << std::endl;
        }
      }
      // The premise is used a singleton clause. We must guarantee that its
      // proof indeed concludes a singleton clause.
      else if (children[0].getKind() == kind::OR)
      {
        Assert(args[polIdx] == d_true && args[pivIdx] == children[0]);
        if (maybeReplacePremiseProof(children[0], cdp))
        {
          hasUpdated = true;
          newChildren[0] = nm->mkNode(kind::SEXPR, d_cl, children[0]);
        }
      }
      // For all other children C_i the procedure is similar. There is however a
      // key difference in the choice of the pivot element which is now the
      // L_{i-1}, i.e. the pivot of the child with the result of the i-1
      // resolution steps between the children before it. Therefore, if the
      // policy id_{i-1} is true, the pivot has to appear negated in the child
      // in which case it should not be a (cl (or F1 ... Fn)) node. The same is
      // true if it isn't the pivot element.
      for (std::size_t i = 1, size = children.size(); i < size; ++i)
      {
        polIdx = 2 * (i - 1) + 3 + 1;
        pivIdx = 2 * (i - 1) + 3;
        if (children[i].getKind() == kind::OR
            && (args[polIdx] != d_false || args[pivIdx] != children[i]))
        {
          // the arguments will have been converted to witness form already, so
          // we also check whether after conversion the child is still not the
          // same (in the case where we'd need to have them different)
          if (args[polIdx] == d_false
              && args[pivIdx] == d_anc.convert(children[i]))
          {
            continue;
          }
          std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
          Node childConclusion = childPf->getArguments()[2];
          AletheRule childRule = getAletheRule(childPf->getArguments()[0]);
          // Add or step
          if ((childConclusion.getNumChildren() == 2
               && childConclusion[0] == d_cl
               && childConclusion[1].getKind() == kind::OR)
              || (childRule == AletheRule::ASSUME
                  && childConclusion.getKind() == kind::OR))
          {
            hasUpdated = true;
            std::vector<Node> lits{d_cl};
            if (childRule == AletheRule::ASSUME)
            {
              lits.insert(
                  lits.end(), childConclusion.begin(), childConclusion.end());
            }
            else
            {
              lits.insert(lits.end(),
                          childConclusion[1].begin(),
                          childConclusion[1].end());
            }
            Node conclusion = nm->mkNode(kind::SEXPR, lits);
            addAletheStep(AletheRule::OR,
                          conclusion,
                          conclusion,
                          {children[i]},
                          {},
                          *cdp);
            newChildren[i] = conclusion;
            Trace("alethe-proof") << "Added OR step for " << childConclusion
                                  << " / " << conclusion << std::endl;
          }
        }
        // As for the first premise, we need to handle the case in which the
        // premise is a singleton but the rule concluding it yields a clause.
        else if (children[i].getKind() == kind::OR)
        {
          Assert(args[polIdx] == d_false && args[pivIdx] == children[i]);
          if (maybeReplacePremiseProof(children[i], cdp))
          {
            hasUpdated = true;
            newChildren[i] = nm->mkNode(kind::SEXPR, d_cl, children[i]);
          }
        }
      }
      if (hasUpdated || !d_resPivots)
      {
        Trace("alethe-proof")
            << "... update alethe step in finalizer " << res << " "
            << newChildren << " / " << args << std::endl;
        cdp->addStep(res,
                     PfRule::ALETHE_RULE,
                     newChildren,
                     d_resPivots
                         ? args
                         : std::vector<Node>{args.begin(), args.begin() + 3});
        return true;
      }
      Trace("alethe-proof") << "... no update\n";
      return false;
    }
    // A application of the FACTORING rule:
    //
    // (or a a b)
    // ---------- FACTORING
    //  (or a b)
    //
    // might be translated during pre-visit (update) to:
    //
    // (or (cl a a b))*
    // ---------------- CONTRACTION
    //  (cl a b)**
    //
    // In this post-visit an additional OR step is added in that case:
    //
    // (cl (or a a b))*
    // ---------------- OR
    // (cl a a b)
    // ---------------- CONTRACTION
    // (cl a b)**
    //
    // * the corresponding proof node is (or a a b)
    // ** the corresponding proof node is (or a b)
    //
    // The process is analogous for REORDERING.
    case AletheRule::REORDERING:
    case AletheRule::CONTRACTION:
    {
      std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
      Node childConclusion = childPf->getArguments()[2];
      AletheRule childRule = getAletheRule(childPf->getArguments()[0]);
      if ((childConclusion.getNumChildren() == 2 && childConclusion[0] == d_cl
           && childConclusion[1].getKind() == kind::OR)
          || (childRule == AletheRule::ASSUME
              && childConclusion.getKind() == kind::OR))
      {
        // Add or step for child
        std::vector<Node> subterms{d_cl};
        if (getAletheRule(childPf->getArguments()[0]) == AletheRule::ASSUME)
        {
          subterms.insert(
              subterms.end(), childConclusion.begin(), childConclusion.end());
        }
        else
        {
          subterms.insert(subterms.end(),
                          childConclusion[1].begin(),
                          childConclusion[1].end());
        }
        Node newChild = nm->mkNode(kind::SEXPR, subterms);
        addAletheStep(
            AletheRule::OR, newChild, newChild, {children[0]}, {}, *cdp);
        Trace("alethe-proof")
            << "Added OR step in finalizer to child " << childConclusion
            << " / " << newChild << std::endl;
        // update res step
        cdp->addStep(res, PfRule::ALETHE_RULE, {newChild}, args);
        return true;
      }
      Trace("alethe-proof") << "... no update\n";
      return false;
    }
    default:
    {
      Trace("alethe-proof") << "... no update\n";
      return false;
    }
  }
  Trace("alethe-proof") << "... no update\n";
  return false;
}

// If the second-last step of the proof was:
//
// Children:  (P1:C1) ... (Pn:Cn)
// Arguments: (AletheRule::VRULE,false,(cl false))
// ---------------------
// Conclusion: (false)
//
// In Alethe:
//
//  P1 ... Pn
// ------------------- VRULE   ---------------------- FALSE
//  (VP1:(cl false))*           (VP2:(cl (not true)))
// -------------------------------------------------- RESOLUTION
//                       (cl)**
//
// *  the corresponding proof node is ((false))
// ** the corresponding proof node is (false)
//
// This method also handles the case where the internal proof is "empty", i.e.,
// it consists only of "false" as an assumption.
bool AletheProofPostprocessCallback::finalStep(Node res,
                                               PfRule id,
                                               std::vector<Node>& children,
                                               const std::vector<Node>& args,
                                               CDProof* cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);

  // convert inner proof, i.e., children[0], if its conclusion is (cl false) or
  // if it's a false assumption
  if (childPf->getRule() == PfRule::ALETHE_RULE
      && ((childPf->getArguments()[2].getNumChildren() == 2
           && childPf->getArguments()[2][1] == d_false)
          || childPf->getArguments()[2] == d_false))
  {
    Node notFalse =
        nm->mkNode(kind::SEXPR, d_cl, d_false.notNode());  // (cl (not false))
    Node newChild = nm->mkNode(kind::SEXPR, d_cl);  // (cl)

    addAletheStep(AletheRule::FALSE, notFalse, notFalse, {}, {}, *cdp);
    addAletheStep(
        AletheRule::RESOLUTION,
        newChild,
        newChild,
        {children[0], notFalse},
        d_resPivots ? std::vector<Node>{d_false, d_true} : std::vector<Node>(),
        *cdp);
    children[0] = newChild;
  }

  // Sanitize original assumptions and create a placeholder proof step to hold
  // them.
  Assert(id == PfRule::SCOPE);
  std::vector<Node> sanitizedArgs{
      nm->mkConstInt(static_cast<uint32_t>(AletheRule::UNDEFINED)), res, res};
  for (const Node& arg : args)
  {
    sanitizedArgs.push_back(d_anc.convert(arg, false));
  }
  return cdp->addStep(res, PfRule::ALETHE_RULE, children, sanitizedArgs);
}

bool AletheProofPostprocessCallback::addAletheStep(
    AletheRule rule,
    Node res,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> newArgs{NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(rule)))};
  newArgs.push_back(res);
  newArgs.push_back(d_anc.convert(conclusion));
  for (const Node& arg : args)
  {
    newArgs.push_back(d_anc.convert(arg));
  }
  Trace("alethe-proof") << "... add alethe step " << res << " / " << conclusion
                        << " " << rule << " " << children << " / " << newArgs
                        << std::endl;
  return cdp.addStep(res, PfRule::ALETHE_RULE, children, newArgs);
}

bool AletheProofPostprocessCallback::addAletheStepFromOr(
    AletheRule rule,
    Node res,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> subterms = {d_cl};
  subterms.insert(subterms.end(), res.begin(), res.end());
  Node conclusion = NodeManager::currentNM()->mkNode(kind::SEXPR, subterms);
  return addAletheStep(rule, res, conclusion, children, args, cdp);
}

AletheProofPostprocess::AletheProofPostprocess(Env& env,
                                               AletheNodeConverter& anc,
                                               bool resPivots)
    : EnvObj(env), d_cb(env, anc, resPivots)
{
}

AletheProofPostprocess::~AletheProofPostprocess() {}

void AletheProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  // first two nodes are scopes for definitions and other assumptions. We
  // process only the internal proof node. And we merge these two scopes
  Assert(pf->getRule() == PfRule::SCOPE
         && pf->getChildren()[0]->getRule() == PfRule::SCOPE);
  std::shared_ptr<ProofNode> definitionsScope = pf;
  std::shared_ptr<ProofNode> assumptionsScope = pf->getChildren()[0];
  std::shared_ptr<ProofNode> internalProof = assumptionsScope->getChildren()[0];
  // Translate proof node
  ProofNodeUpdater updater(d_env, d_cb, false, false);
  updater.process(internalProof);

  // In the Alethe proof format the final step has to be (cl). However, after
  // the translation it might be (cl false). In that case additional steps are
  // required.
  // The function has the additional purpose of sanitizing the attributes of the
  // outer SCOPEs
  CDProof cpf(
      d_env, nullptr, "AletheProofPostProcess::finalStep::CDProof", true);
  std::vector<Node> ccn{internalProof->getResult()};
  cpf.addProof(internalProof);
  std::vector<Node> args{definitionsScope->getArguments().begin(),
                         definitionsScope->getArguments().end()};
  args.insert(args.end(),
              assumptionsScope->getArguments().begin(),
              assumptionsScope->getArguments().end());
  if (d_cb.finalStep(
          definitionsScope->getResult(), PfRule::SCOPE, ccn, args, &cpf))
  {
    std::shared_ptr<ProofNode> npn =
        cpf.getProofFor(definitionsScope->getResult());

    // then, update the original proof node based on this one
    Trace("pf-process-debug") << "Update node..." << std::endl;
    d_env.getProofNodeManager()->updateNode(pf.get(), npn.get());
    Trace("pf-process-debug") << "...update node finished." << std::endl;
  }
}

}  // namespace proof

}  // namespace cvc5::internal
