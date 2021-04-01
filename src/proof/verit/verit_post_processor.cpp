/*********************                                                        */
/*! \file verit_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into veriT proof nodes
 **/

#include "proof/verit/verit_post_processor.h"

#include <cstdlib>
#include <functional>
#include <memory>
#include <vector>

#include "expr/proof.h"
#include "expr/proof_ensure_closed.h"
#include "expr/proof_node_algorithm.h"
#include "expr/proof_node_manager.h"

namespace cvc5 {

namespace proof {

VeritProofPostprocessCallback::VeritProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  d_nm = NodeManager::currentNM();
}

void VeritProofPostprocessCallback::initializeUpdate() {}

bool VeritProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 bool& continueUpdate)
{
  switch (pn->getRule())
  {
    case PfRule::VERIT_RULE: return false;
    default: return true;
  }
}

bool VeritProofPostprocessCallback::addVeritStep(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(rule)));
  new_args.push_back(res);
  new_args.insert(new_args.end(), args.begin(), args.end());
  return cdp.addStep(res, PfRule::VERIT_RULE, children, new_args);
}

bool VeritProofPostprocessCallback::update(Node res,
                                           PfRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args,
                                           CDProof* cdp,
                                           bool& continueUpdate)
{
  std::vector<Node> new_args = std::vector<Node>();
  // Test print
  std::cout << id << std::endl;

  // TODO: add SEXPR to solve or and cl issue

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
    // proof term: (F)
    // premises: ()
    // args: ()
    case PfRule::ASSUME:
    {
      // TODO Assumes should only be printed once in the end
      return addVeritStep(res, VeritRule::ASSUME, children, {}, *cdp);
    }
    // ======== Scope (a binder for assumptions)
    // Children: (P:F)
    // Arguments: (F1, ..., Fn)
    // --------------
    // Conclusion: (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) if F is false
    //
    // proof rule: anchor
    // proof term:
    // premises:
    // args: (F1, ..., Fn)
    case PfRule::SCOPE: { return true;
    }
    //================================================= Boolean rules
    // ======== Resolution
    // Children:
    //  (P1:(or F_1 ... F_i-1 F_i F_i+1 ... F_n),
    //   P2:(or G_1 ... G_j-1 G_j G_j+1 ... G_m))
    //
    // Arguments: (F_i)
    // ---------------------
    // Conclusion: (or F_1 ... F_i-1 F_i+1 ... F_n G_1 ... G_j-1 G_j+1 ... G_m)
    // where
    //   G_j = (not F_i)
    //
    // proof rule: resolution
    // proof term: (or F_1 ... F_i-1 F_i+1 ... F_n G_1 ... G_j-1 G_j+1 ... G_m)
    // premises: (P1:(or F_1 ... F_i-1 F_i F_i+1 ... F_n),
    //            P2:(or G_1 ... G_j-1 G_j G_j+1 ... G_m))
    // args: ()
    case PfRule::RESOLUTION:
    {
      if (res == d_nm->mkConst(false))
      {
        new_args.push_back(d_nm->mkConst<Rational>(
            static_cast<unsigned>(VeritRule::RESOLUTION)));
        new_args.push_back(res);
        // Note: This will not print correctly. Before Node::null() was pushed
        // but because of the move of the check of the VERIT_RULE to
        // theory/builtin/proof_checker.cpp res has to be equal to args[1].
        // However, this issue is resolved in a later version so it is not
        // changed here.
        return cdp->addStep(res, PfRule::VERIT_RULE, children, new_args);
      }
      return addVeritStep(res, VeritRule::RESOLUTION, children, {}, *cdp);
    }
    // ======== Chain Resolution
    // Children: (P1:(or F_{1,1} ... F_{1,n1}), ..., Pm:(or F_{m,1} ...
    // F_{m,nm})) Arguments: (L_1, ..., L_{m-1})
    // ---------------------
    // Conclusion: C_m'
    // where
    //   let "C_1 <>_l C_2" represent the resolution of C_1 with C_2 with pivot
    //   l, let C_1' = C_1 (from P_1), for each i > 1, C_i' = C_i <>_L_i
    //   C_{i-1}'
    //
    // proof rule: resolution
    // proof term: (C_m')
    // premises: (P1:(or F_{1,1} ... F_{1,n1}), ..., Pm:(or F_{m,1} ...
    // F_{m,nm})) args: ()
    case PfRule::CHAIN_RESOLUTION:
    {
      return addVeritStep(res, VeritRule::RESOLUTION, children, {}, *cdp);
    }
    // ======== Factoring
    // Children: (P:C1)
    // Arguments: ()
    // ---------------------
    // Conclusion: C2
    // where
    //  Set representations of C1 and C2 is the same and the number of literals
    //  in C2 is smaller than that of C1
    //
    //  proof rule: duplicate_literals
    //  proof term: (C2)
    //  premises: (P:C1)
    //  args: ()
    case PfRule::FACTORING:
    {
      return addVeritStep(
          res, VeritRule::DUPLICATE_LITERALS, children, {}, *cdp);
    }
    // ======== Reordering
    // Children: (P:C1)
    // Arguments: (C2)
    // ---------------------
    // Conclusion: C2
    // where
    //  Set representations of C1 and C2 is the same but the number of literals
    //  in C2 is the same of that of C1
    //
    // proof rule:
    // proof term:
    // premises:
    // args:
    case PfRule::REORDERING: { return true;
    }
    // ======== Split
    // Children: none
    // Arguments: (F)
    // ---------------------
    // Conclusion: (or F (not F))
    //
    // proof rule: not_not
    // proof term: (VP1:(or (not (not (not F))) F))
    // premises: ()
    // args: ()
    //
    // proof rule: not_not
    // proof term: (VP2:(or (not (not (not (not F)))) (not F))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (or F (not F))
    // premises: VP1 VP2
    // args: ()
    case PfRule::SPLIT:
    {
      Node vp1 = d_nm->mkNode(
          kind::OR, args[0].notNode().notNode().notNode(), args[0]);
      Node vp2 = d_nm->mkNode(kind::OR,
                              args[0].notNode().notNode().notNode().notNode(),
                              args[0].notNode());

      return addVeritStep(vp2, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(res, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp);
    }
    // ======== Equality resolution
    // Children: (P1:F1, P2:(= F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    // proof rule: equiv_pos2
    // proof term: (VP1:(or (not (= F1 F2)) (not F1) (F2)))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (F2)
    // premises: (VP1:(or (not (= F1 F2)) (not F1) (F2))) (P1:F1) (P2:(= F1 F2))
    // args: ()
    case PfRule::EQ_RESOLVE:
    {
      Node vp1 =
          d_nm->mkNode(kind::OR, d_nm->mkNode(kind::NOT, children[1]), res);

      return addVeritStep(vp1, VeritRule::EQUIV_POS2, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             {vp1, children[0], children[1]},
                             {},
                             *cdp);
    }
    // ======== Modus ponens
    // Children: (P1:F1, P2:(=> F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    // proof rule: implies
    // proof term: (VP:(or (not F1) F2))
    // premises: (P2:(=> F1 F2))
    // args: ()
    //
    // proof rule: resolution
    // proof term: (F2)
    // premises: (P1:F1) (VP:(or (not F1) F2))
    // args: ()
    case PfRule::MODUS_PONENS:
    {
      Node vp =
          d_nm->mkNode(kind::OR, d_nm->mkNode(kind::NOT, children[0]), res);
      return addVeritStep(vp, VeritRule::IMPLIES, {children[1]}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::RESOLUTION, {vp, children[0]}, {}, *cdp);
    }
    // ======== Double negation elimination
    // Children: (P:(not (not F)))
    // Arguments: none
    // ---------------------
    // Conclusion: (F)
    //
    // proof rule: not_not
    // proof term: (VP:(or (not (not (not F))) F))
    // premises:
    // args: ()
    //
    // proof rule: resolution
    // proof term: (F)
    // premises: (VP:(or (not (not (not F))) F)) (P:(not (not F)))
    // args: ()
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp =
          d_nm->mkNode(kind::OR, d_nm->mkNode(kind::NOT, children[0]), res);
      return addVeritStep(vp, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::RESOLUTION, {children[0], vp}, {}, *cdp);
    }
    // ======== Contradiction
    // Children: (P1:F P2:(not F))
    // Arguments: ()
    // ---------------------
    // Conclusion: false
    //
    // proof rule: resolution
    // proof term: ()
    // premises: (P1:F) (P2:(not F))
    // args: ()
    case PfRule::CONTRA:
    {
      new_args.push_back(d_nm->mkConst<Rational>(
          static_cast<unsigned>(VeritRule::RESOLUTION)));
      new_args.push_back(res);
      // Note: This will not print correctly. Before Node::null() was pushed but
      // because of the move of the check of the VERIT_RULE to
      // theory/builtin/proof_checker.cpp res has to be equal to args[1].
      // However, this issue is resolved in a later version so it is not changed
      // here.
      return cdp->addStep(res, PfRule::VERIT_RULE, children, new_args);
    }
    // ======== And elimination
    // Children: (P:(and F1 ... Fn))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (Fi)
    //
    // proof rule: and
    // proof term: (Fi)
    // premises: (P:(and F1 ... Fn))
    // args: ()
    case PfRule::AND_ELIM:
    {
      return addVeritStep(res, VeritRule::AND, children, {}, *cdp);
    }
    // ======== And introduction
    // Children: (P1:F1 ... Pn:Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (and P1 ... Pn)
    //
    // proof rule: and_neg
    // proof term: (VP1:(or (and F1 ... Fn) (not F1) ... (not Fn)))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (and P1 ... Pn)
    // premises: (P1:F1 ... Pn:Fn) (VP1:(or (and F1 ... Fn) (not F1) ... (not
    // Fn))) args: ()
    case PfRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes;
      neg_Nodes.push_back(d_nm->mkNode(kind::AND, children));
      for (size_t i = 0; i < children.size(); i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }

      Node vp1 = d_nm->mkNode(kind::OR, neg_Nodes);
      std::vector<Node> new_children;
      new_children.insert(new_children.end(), children.begin(), children.end());
      new_children.push_back(vp1);

      return addVeritStep(vp1, VeritRule::AND_NEG, {}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::RESOLUTION, new_children, {}, *cdp);
    }
    // ======== Not Or elimination
    // Children: (P:(not (or F1 ... Fn)))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (not Fi)
    //
    // proof rule: not_or
    // proof term: (not Fi)
    // premises: (P:(not (or F1 ... Fn)))
    // args: ()
    case PfRule::NOT_OR_ELIM:
    {
      return addVeritStep(res, VeritRule::NOT_OR, children, {}, *cdp);
    }
    // ======== Implication elimination
    // Children: (P:(=> F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: implies
    // proof term: (or (not F1) F2)
    // premises: (P:(=> F1 F2))
    // args: ()
    case PfRule::IMPLIES_ELIM:
    {
      return addVeritStep(res, VeritRule::IMPLIES, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 1
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (F1)
    //
    // proof rule: not_implies1
    // proof term: (F1)
    // premises: (P:(not (=> F1 F2)))
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM1:
    {
      return addVeritStep(res, VeritRule::NOT_IMPLIES1, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 2
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (not F2)
    //
    // proof rule: not_implies2
    // proof term: (not F2)
    // premises: (P:(not (=> F1 F2)))
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM2:
    {
      return addVeritStep(res, VeritRule::NOT_IMPLIES2, children, {}, *cdp);
    }
    // ======== Equivalence elimination version 1
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: equiv1
    // proof term: (or (not F1) F2)
    // premises: (P:(= F1 F2))
    // args: ()
    case PfRule::EQUIV_ELIM1:
    {
      return addVeritStep(res, VeritRule::EQUIV1, children, {}, *cdp);
    }
    // ======== Equivalence elimination version 2
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: equiv2
    // proof term: (or F1 (not F2))
    // premises: (P:(= F1 F2))
    // args: ()
    case PfRule::EQUIV_ELIM2:
    {
      return addVeritStep(res, VeritRule::EQUIV2, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 1
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: not_equiv1
    // proof term: (or F1 F2)
    // premises: (P:(not (= F1 F2)))
    // args: ()
    case PfRule::NOT_EQUIV_ELIM1:
    {
      return addVeritStep(res, VeritRule::NOT_EQUIV1, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 2
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) (not F2))
    //
    // proof rule: not_equiv2
    // proof term: (or (not F1) (not F2))
    // premises: (P:(not (= F1 F2)))
    // args: ()
    case PfRule::NOT_EQUIV_ELIM2:
    {
      return addVeritStep(res, VeritRule::NOT_EQUIV2, children, {}, *cdp);
    }
    // ======== XOR elimination version 1
    // Children: (P:(xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: XOR1
    // proof term: (or F1 F2)
    // premises: (P:(xor F1 F2))
    // args: ()
    case PfRule::XOR_ELIM1:
    {
      return addVeritStep(res, VeritRule::XOR1, children, {}, *cdp);
    }
    // ======== XOR elimination version 2
    // Children: (P:(not (xor F1 F2))))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: XOR2
    // proof term: (or F1 (not F2))
    // premises: (P:(not (xor F1 F2)))
    // args: ()
    case PfRule::XOR_ELIM2:
    {
      return addVeritStep(res, VeritRule::XOR2, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 1
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: NOT_XOR1
    // proof term: (or F1 (not F2))
    // premises: (P:(not (xor F1 F2)))
    // args: ()
    case PfRule::NOT_XOR_ELIM1:
    {
      return addVeritStep(res, VeritRule::NOT_XOR1, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 2
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: NOT_XOR1
    // proof term: (or (not F1) F2)
    // premises: (P:(not (xor F1 F2)))
    // args: ()
    case PfRule::NOT_XOR_ELIM2:
    {
      return addVeritStep(res, VeritRule::NOT_XOR2, children, {}, *cdp);
    }
    // ======== ITE elimination version 1
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) F1)
    //
    // proof rule: ite2
    // proof term: (or (not C) F1)
    // premises: (P:(ite C F1 F2))
    // args: ()
    case PfRule::ITE_ELIM1:
    {
      return addVeritStep(res, VeritRule::ITE2, children, {}, *cdp);
    }
    // ======== ITE elimination version 2
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C F2)
    //
    // proof rule: ite1
    // proof term: (or C F2)
    // premises: (P:(ite C F1 F2))
    // args: ()
    case PfRule::ITE_ELIM2:
    {
      return addVeritStep(res, VeritRule::ITE1, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) (not F1))
    //
    // proof rule: not_ite2
    // proof term: (or (not C) (not F1))
    // premises: (P:(not (ite C F1 F2)))
    // args: ()
    case PfRule::NOT_ITE_ELIM1:
    {
      return addVeritStep(res, VeritRule::NOT_ITE2, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C (not F2))
    //
    // proof rule: not_ite1
    // proof term: (or C (not F2))
    // premises: (P:(not (ite C F1 F2)))
    // args: ()
    case PfRule::NOT_ITE_ELIM2:
    {
      return addVeritStep(res, VeritRule::NOT_ITE1, children, {}, *cdp);
    }

    //================================================= De Morgan rules
    // ======== Not And
    // Children: (P:(not (and F1 ... Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) ... (not Fn))
    //
    // proof rule: not_and
    // proof term: (or (not F1) ... (not Fn))
    // premises: (P:(not (and F1 ... Fn))
    // args: ()
    case PfRule::NOT_AND:
    {
      return addVeritStep(res, VeritRule::NOT_AND, children, {}, *cdp);
    }

    //================================================= CNF rules
    // ======== CNF And Pos
    // Children: ()
    // Arguments: ((and F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (not (and F1 ... Fn)) Fi)
    //
    // proof rule: and_pos
    // proof term: (or (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_POS:
    {
      return addVeritStep(res, VeritRule::AND_POS, children, {}, *cdp);
    }
    // ======== CNF And Neg
    // Children: ()
    // Arguments: ((and F1 ... Fn))
    // ---------------------
    // Conclusion: (or (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // proof rule: and_neg
    // proof term: (or (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_NEG:
    {
      return addVeritStep(res, VeritRule::AND_NEG, children, {}, *cdp);
    }
    // ======== CNF Or Pos
    // Children: ()
    // Arguments: ((or F1 ... Fn))
    // ---------------------
    // Conclusion: (or (not (or F1 ... Fn)) F1 ... Fn)
    //
    // proof rule: or_pos
    // proof term: (or (not (or F1 ... Fn)) F1 ... Fn)
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_POS:
    {
      return addVeritStep(res, VeritRule::OR_POS, children, {}, *cdp);
    }
    // ======== CNF Or Neg
    // Children: ()
    // Arguments: ((or F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (or F1 ... Fn) (not Fi))
    //
    // proof rule: or_neg
    // proof term: (or (or F1 ... Fn) (not Fi))
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_NEG:
    {
      return addVeritStep(res, VeritRule::OR_NEG, children, {}, *cdp);
    }
    // ======== CNF Implies Pos
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (not (implies F1 F2)) (not F1) F2)
    //
    // proof rule: implies_pos
    // proof term: (or (not (implies F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_POS:
    {
      return addVeritStep(res, VeritRule::IMPLIES_POS, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 1
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) F1)
    //
    // proof rule: implies_neg1
    // proof term: (or (implies F1 F2) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG1:
    {
      return addVeritStep(res, VeritRule::IMPLIES_NEG1, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 2
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) (not F2))
    //
    // proof rule: implies_neg2
    // proof term: (or (implies F1 F2) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG2:
    {
      return addVeritStep(res, VeritRule::IMPLIES_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) (not F1) F2)
    //
    // proof rule: equiv_pos2
    // proof term: (or (not (= F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS1:
    {
      return addVeritStep(res, VeritRule::EQUIV_POS2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) F1 (not F2))
    //
    // proof rule: equiv_pos1
    // proof term: (or (not (= F1 F2)) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS2:
    {
      return addVeritStep(res, VeritRule::EQUIV_POS1, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) F1 F2)
    //
    // proof rule: equiv_neg2
    // proof term: (or (= F1 F2) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG1:
    {
      return addVeritStep(res, VeritRule::EQUIV_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) (not F1) (not F2))
    //
    // proof rule: equiv_neg1
    // proof term: (or (= F1 F2) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG2:
    {
      return addVeritStep(res, VeritRule::EQUIV_NEG1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) F1 F2)
    //
    // proof rule: xor_pos1
    // proof term: (or (not (xor F1 F2)) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS1:
    {
      return addVeritStep(res, VeritRule::XOR_POS1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) (not F1) (not F2))
    //
    // proof rule: xor_pos2
    // proof term: (or (not (xor F1 F2)) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS2:
    {
      return addVeritStep(res, VeritRule::XOR_POS2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) (not F1) F2)
    //
    // proof rule: xor_neg2
    // proof term: (or (xor F1 F2) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG1:
    {
      return addVeritStep(res, VeritRule::XOR_NEG2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) F1 (not F2))
    //
    // proof rule: xor_neg1
    // proof term: (or (xor F1 F2) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG2:
    {
      return addVeritStep(res, VeritRule::XOR_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) (not C) F1)
    //
    // proof rule: ite_pos2
    // proof term: (or (not (ite C F1 F2)) (not C) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS1:
    {
      return addVeritStep(res, VeritRule::ITE_POS2, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) C F2)
    //
    // proof rule: ite_pos1
    // proof term: (or (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS2:
    {
      return addVeritStep(res, VeritRule::ITE_POS1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) F1 F2)
    //
    // proof rule: ite_pos1
    // proof term: (VP1:(or (not (ite C F1 F2)) C F2))
    // premises: ()
    // args: ()
    //
    // proof rule: ite_pos2
    // proof term: (VP2:(or (not (ite C F1 F2)) (not C) F1))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (VP3:(or (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
    // premises: (VP1:(or (not (ite C F1 F2)) C F2)) (VP2:(or (not (ite C F1
    // F2)) (not C) F1)) args: ()
    //
    // proof rule: duplicate_literals
    // proof term: (or (not (ite C F1 F2)) F1 F2)
    // premises: (VP3:(or (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
    // args: ()
    case PfRule::CNF_ITE_POS3:
    {
      Node vp1 = d_nm->mkNode(kind::OR, res[0], args[0][0], res[2]);
      Node vp2 = d_nm->mkNode(
          kind::OR, res[0], d_nm->mkNode(kind::NOT, args[0][0]), res[1]);
      Node vp3 = d_nm->mkNode(kind::OR, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_POS1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_POS2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::DUPLICATE_LITERALS, {vp3}, {}, *cdp);
    }
    // ======== CNF ITE Neg version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not C) (not F1))
    //
    // proof rule: ite_neg2
    // proof term: (or (ite C F1 F2) (not C) (not F1))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG1:
    {
      return addVeritStep(res, VeritRule::ITE_NEG2, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) C (not F2))
    //
    // proof rule: ite_neg1
    // proof term: (or (ite C F1 F2) C (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG2:
    {
      return addVeritStep(res, VeritRule::ITE_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not F1) (not F2))
    //
    // proof rule: ite_neg1
    // proof term: (VP1:(or (ite C F1 F2) C (not F2)))
    // premises: ()
    // args: ()
    //
    // proof rule: ite_neg2
    // proof term: (VP2:(or (ite C F1 F2) (not C) (not F1)))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (VP3:(or (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
    // premises: ((VP1:(or (ite C F1 F2) C (not F2))) (VP2:(or (ite C F1 F2)
    // (not C) (not F1)))) args: ()
    //
    // proof rule: duplicate_literals
    // proof term: (or (ite C F1 F2) C (not F2))
    // premises: (VP3:(or (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
    // args: ()
    case PfRule::CNF_ITE_NEG3:
    {
      Node vp1 = d_nm->mkNode(kind::OR, res[0], args[0][0], res[2]);
      Node vp2 = d_nm->mkNode(
          kind::OR, res[0], d_nm->mkNode(kind::NOT, args[0][0]), res[1]);
      Node vp3 = d_nm->mkNode(kind::OR, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_NEG1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_NEG2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::DUPLICATE_LITERALS, {vp3}, {}, *cdp);
    }

    //================================================= Equality rules
    // ======== Reflexive
    // Children: none
    // Arguments: (t)
    // ---------------------
    // Conclusion: (= t t)
    //
    // proof rule: refl
    // proof term: (= t t)
    // premises: ()
    // args: ()
    case PfRule::REFL:
    {
      return addVeritStep(res, VeritRule::REFL, children, {}, *cdp);
    }
    // ======== Symmetric
    // Children: (P:(= t1 t2)) or (P:(not (= t1 t2)))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t2 t1) or (not (= t2 t1))
    //
    // proof rule:
    // proof term:
    // premises:
    // args:
    case PfRule::SYMM:
    {
      // TODO: veriT implicitly reorders equalities, without generating steps
      // However, it might not be okay to just delete these nodes.
      return true;
    }
    // ======== Transitivity
    // Children: (P1:(= t1 t2), ..., Pn:(= t{n-1} tn))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t1 tn)
    //
    // proof rule: trans
    // proof term: (= t1 tn)
    // premises: (P1:(= t1 t2), ..., Pn:(= t{n-1} tn))
    // args: ()
    case PfRule::TRANS:
    {
      return addVeritStep(res, VeritRule::TRANS, children, {}, *cdp);
    }
    // ======== Congruence
    // Children: (P1:(= t1 s1), ..., Pn:(= tn sn))
    // Arguments: (<kind> f?)
    // ---------------------------------------------
    // Conclusion: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    // Notice that f must be provided iff <kind> is a parameterized kind, e.g.
    // APPLY_UF. The actual node for <kind> is constructible via
    // ProofRuleChecker::mkKindNode.
    //
    // proof rule: cong
    // proof term: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    // premises: (P1:(= t1 s1), ..., Pn:(= tn sn))
    // args: ()
    case PfRule::CONG:
    {
      return addVeritStep(res, VeritRule::CONG, children, {}, *cdp);
    }
    // ======== True intro
    // Children: (P:F)
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F true)
    //
    // proof rule: equiv_simplify
    // proof term: (VP1:(= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof term: (VP2:(or (= F true) (not F)))
    // premises: (VP1:(= (= F true) F))
    // args: ()
    //
    // proof rule: resolution
    // proof term: (= F true)
    // premises: (P:F) (VP2:(or (= F true) (not F)))
    // args: ()
    case PfRule::TRUE_INTRO:
    {
      Node vp1 = d_nm->mkNode(kind::EQUAL, res, children[0]);
      Node vp2 =
          d_nm->mkNode(kind::OR, res, d_nm->mkNode(kind::NOT, children[0]));
      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::RESOLUTION, {vp2, children[0]}, {}, *cdp);
    }
    // ======== True elim
    // Children: (P:(= F true))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: F
    //
    // proof rule: equiv_simplify
    // proof term: (VP1:(= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof term: (VP2:(or (not (= F true)) F))
    // premises: (VP1:(= (= F true) F))
    // args: ()
    //
    // proof rule: resolution
    // proof term: (F)
    // premises: (VP2:(or (not (= F true)) F)) (P:(= F true))
    // args: ()
    case PfRule::TRUE_ELIM:
    {
      Node vp1 = d_nm->mkNode(kind::EQUAL, children[0], res);
      Node vp2 =
          d_nm->mkNode(kind::OR, d_nm->mkNode(kind::NOT, children[0]), res);
      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::RESOLUTION, {vp2, children[0]}, {}, *cdp);
    }
    // ======== False intro
    // Children: (P:(not F))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F false)
    //
    // proof rule: equiv_simplify
    // proof term: (VP1:(= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof term: (VP2:(or (= F false) (not (not F))))
    // premises: (VP1:(= (= F false) (not F)))
    // args: ()
    //
    // proof rule: not_not
    // proof term: (VP3:(or (not (not (not F))) F))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof term: (VP4:(or (= F false) F))
    // premises: (VP2:(or (= F false) (not (not F)))) (VP3:(or (not (not (not
    // F))) F)) args: ()
    //
    // proof rule: resolution
    // proof term: (= F false)
    // premises: (VP4:(or (= F false) F)) (P:(not F))
    // args: ()
    case PfRule::FALSE_INTRO:
    {
      Node vp1 = d_nm->mkNode(kind::EQUAL, res, children[0]);
      Node vp2 =
          d_nm->mkNode(kind::OR, res, d_nm->mkNode(kind::NOT, children[0]));
      Node vp3 = d_nm->mkNode(
          kind::OR,
          d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::NOT, children[0])),
          children[0][0]);
      Node vp4 = d_nm->mkNode(kind::OR, res, children[0][0]);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp4, VeritRule::RESOLUTION, {vp2, vp3}, {}, *cdp)
             && addVeritStep(res, VeritRule::RESOLUTION, {vp4}, {}, *cdp);
    }
    // ======== False elim
    // Children: (P:(= F false))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (not F)
    //
    // proof rule: equiv_simplify
    // proof term: (VP1:(= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof term: (VP2:(or (not (= F false)) (not F)))
    // premises: (VP1:(= (= F false) (not F)))
    // args: ()
    //
    // proof rule: resolution
    // proof term: (not F)
    // premises: (VP1:(= (= F false) (not F))) (P:(= F false))
    // args: ()
    case PfRule::FALSE_ELIM:
    {
      Node vp1 = d_nm->mkNode(kind::EQUAL, children[0], res);
      Node vp2 =
          d_nm->mkNode(kind::OR, d_nm->mkNode(kind::NOT, children[0]), res);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp)
             && addVeritStep(
                    res, VeritRule::RESOLUTION, {vp1, children[0]}, {}, *cdp);
    }
      // ======== HO trust
      // Children: none
      // Arguments: (t)
      // ---------------------
      // Conclusion: (= t TheoryUfRewriter::getHoApplyForApplyUf(t))
      // For example, this rule concludes (f x y) = (HO_APPLY (HO_APPLY f x) y)
      //
      // proof rule:
      // proof term:
      // premises:
      // args:
      // case PfRule::HO_APP_ENCODE:
      //{
      // TODO
      //}
      // ======== Congruence
      // Children: (P1:(= f g), P2:(= t1 s1), ..., Pn+1:(= tn sn))
      // Arguments: ()
      // ---------------------------------------------
      // Conclusion: (= (f t1 ... tn) (g s1 ... sn))
      // Notice that this rule is only used when the application kinds are
      // APPLY_UF.
      //
      // proof rule:
      // proof term:
      // premises:
      // args:
      // case PfRule::HO_CONG:
      //{
      // TODO
      //}

    default:
      return addVeritStep(res, VeritRule::UNDEFINED, children, args, *cdp);
  }
  return true;
}

VeritProofPostprocess::VeritProofPostprocess(ProofNodeManager* pnm)
    : d_pnm(pnm), d_cb(new VeritProofPostprocessCallback(pnm))
{
  d_debugFreeAssumps = false;
}

VeritProofPostprocess::~VeritProofPostprocess() {}

// TODO: This process function is copied from ProofNodeUpdater. It should be
// adapted to this specific proof post processor at some point.
void VeritProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  if (d_debugFreeAssumps)
  {
    if (Trace.isOn("pfnu-debug"))
    {
      Trace("pfnu-debug2") << "Initial proof: " << *pf.get() << std::endl;
      Trace("pfnu-debug") << "ProofNodeUpdater::process" << std::endl;
      Trace("pfnu-debug") << "Expected free assumptions: " << std::endl;
      for (const Node& fa : d_freeAssumps)
      {
        Trace("pfnu-debug") << "- " << fa << std::endl;
      }
      std::vector<Node> assump;
      expr::getFreeAssumptions(pf.get(), assump);
      Trace("pfnu-debug") << "Current free assumptions: " << std::endl;
      for (const Node& fa : assump)
      {
        Trace("pfnu-debug") << "- " << fa << std::endl;
      }
    }
  }
  processInternal(pf, d_freeAssumps);
}

void VeritProofPostprocess::processInternal(std::shared_ptr<ProofNode> pf,
                                            const std::vector<Node>& fa)
{
  Trace("pf-process") << "ProofNodeUpdater::process" << std::endl;
  std::unordered_map<std::shared_ptr<ProofNode>, bool> visited;
  std::unordered_map<std::shared_ptr<ProofNode>, bool>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pf);
  std::map<Node, std::shared_ptr<ProofNode>>::iterator itc;
  // A cache from formulas to proof nodes that are in the current scope.
  // Notice that we make a fresh recursive call to process if the current
  // rule is SCOPE below.
  std::map<Node, std::shared_ptr<ProofNode>> resCache;
  Node res;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    res = cur->getResult();
    if (it == visited.end())
    {
      itc = resCache.find(res);
      if (itc != resCache.end())
      {
        // already have a proof
        visited[cur] = true;
        d_pnm->updateNode(cur.get(), itc->second.get());
      }
      else
      {
        visited[cur] = false;
        // run update to a fixed point
        bool continueUpdate = true;
        while (runUpdate(cur, fa, continueUpdate) && continueUpdate)
        {
          Trace("pf-process-debug") << "...updated proof." << std::endl;
        }
        if (!continueUpdate)
        {
          // no further changes should be made to cur according to the callback
          Trace("pf-process-debug")
              << "...marked to not continue update." << std::endl;
          continue;
        }
        visit.push_back(cur);
        // If we are not the top-level proof, we were a scope, or became a
        // scope after updating, we need to make a separate recursive call to
        // this method.
        if (cur->getRule() == PfRule::SCOPE && cur != pf)
        {
          std::vector<Node> nfa;
          // if we are debugging free assumptions, update the set
          if (d_debugFreeAssumps)
          {
            nfa.insert(nfa.end(), fa.begin(), fa.end());
            const std::vector<Node>& args = cur->getArguments();
            nfa.insert(nfa.end(), args.begin(), args.end());
            Trace("pfnu-debug2")
                << "Process new scope with " << args << std::endl;
          }
          // Process in new call separately, since we should not cache
          // the results of proofs that have a different scope.
          processInternal(cur, nfa);
          continue;
        }
        const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
        // now, process children
        for (const std::shared_ptr<ProofNode>& cp : ccp)
        {
          visit.push_back(cp);
        }
      }
    }
    else if (!it->second)
    {
      visited[cur] = true;
      // cache result
      resCache[res] = cur;
      if (d_debugFreeAssumps)
      {
        // We have that npn is a node we occurring the final updated version of
        // the proof. We can now debug based on the expected set of free
        // assumptions.
        Trace("pfnu-debug") << "Ensure update closed..." << std::endl;
        pfnEnsureClosedWrt(
            cur.get(), fa, "pfnu-debug", "ProofNodeUpdater:finalize");
      }
    }
  } while (!visit.empty());
  Trace("pf-process") << "ProofNodeUpdater::process: finished" << std::endl;
}

bool VeritProofPostprocess::runUpdate(std::shared_ptr<ProofNode> cur,
                                      const std::vector<Node>& fa,
                                      bool& continueUpdate)
{
  // should it be updated?
  if (!d_cb->shouldUpdate(cur, continueUpdate))
  {
    return false;
  }
  PfRule id = cur->getRule();
  // use CDProof to open a scope for which the callback updates
  CDProof cpf(d_pnm);
  const std::vector<std::shared_ptr<ProofNode>>& cc = cur->getChildren();
  std::vector<Node> ccn;
  for (const std::shared_ptr<ProofNode>& cp : cc)
  {
    Node cpres = cp->getResult();
    ccn.push_back(cpres);
    // store in the proof
    cpf.addProof(cp);
  }
  Trace("pf-process-debug")
      << "Updating (" << cur->getRule() << ")..." << std::endl;
  Node res = cur->getResult();
  // only if the callback updated the node
  if (d_cb->update(res, id, ccn, cur->getArguments(), &cpf, continueUpdate))
  {
    std::shared_ptr<ProofNode> npn = cpf.getProofFor(res);
    std::vector<Node> fullFa;
    if (d_debugFreeAssumps)
    {
      expr::getFreeAssumptions(cur.get(), fullFa);
      Trace("pfnu-debug") << "Original proof : " << *cur << std::endl;
    }
    // then, update the original proof node based on this one
    Trace("pf-process-debug") << "Update node..." << std::endl;
    d_pnm->updateNode(cur.get(), npn.get());
    Trace("pf-process-debug") << "...update node finished." << std::endl;
    if (d_debugFreeAssumps)
    {
      fullFa.insert(fullFa.end(), fa.begin(), fa.end());
      // We have that npn is a node we occurring the final updated version of
      // the proof. We can now debug based on the expected set of free
      // assumptions.
      Trace("pfnu-debug") << "Ensure update closed..." << std::endl;
      pfnEnsureClosedWrt(
          npn.get(), fullFa, "pfnu-debug", "ProofNodeUpdater:postupdate");
    }
    Trace("pf-process-debug") << "..finished" << std::endl;
    return true;
  }
  Trace("pf-process-debug") << "..finished" << std::endl;
  return false;
}

}  // namespace proof

}  // namespace cvc5
