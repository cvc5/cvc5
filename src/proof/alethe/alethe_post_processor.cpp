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
#include "theory/builtin/proof_checker.h"
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
    // Note that if n = 1, then the ANCHOR step yields (cl (not F1) F), which is
    // the same as VP3. Since VP1 = VP3, the steps for that transformation are
    // not generated.
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
        success &= addAletheStep(
            AletheRule::RESOLUTION, vp2a, vp2a, premisesVP2, {}, *cdp);

        notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n)
        notAnd.push_back(children[0]);     //(cl (not (and F1 ... Fn))^n F)
        Node vp2b = nm->mkNode(kind::SEXPR, notAnd);
        success &=
            addAletheStep(AletheRule::REORDER, vp2b, vp2b, {vp2a}, {}, *cdp);

        vp3 = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
        success &= addAletheStep(
            AletheRule::DUPLICATED_LITERALS, vp3, vp3, {vp2b}, {}, *cdp);
      }

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
    // connective of the first term in the conclusion F, since F always has the
    // form (= t1 t2) where t1 is the term being rewritten. This is not an exact
    // translation but should work in most cases.
    //
    // E.g. if F is (= (* 0 d) 0) and tid = THEORY_ARITH, then prod_simplify
    // is correctly guessed as the rule.
    case PfRule::THEORY_REWRITE:
    {
      AletheRule vrule = AletheRule::UNDEFINED;
      Node t = res[0];

      theory::TheoryId tid;
      if (!theory::builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid))
      {
        return addAletheStep(
            vrule, res, nm->mkNode(kind::SEXPR, d_cl, res), children, {}, *cdp);
      }
      switch (tid)
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
    //================================================= Boolean rules
    // ======== Resolution
    // See proof_rule.h for documentation on the RESOLUTION rule. This comment
    // uses variable names as introduced there.
    //
    // In the case that C = (or G1 ... Gn) the result is ambigous. E.g.,
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
    // F2 F3). Therefore, the translation has to keep track of the current
    // resolvent that is then compared to the result. E.g. in the first case
    // current_resolvent = {(or F2 F3)} indicates that the result is a singleton
    // clause, in the second current_resolvent = {F2,F3} that it is an or node.
    //
    // It is always clear what clauses to add to the current_resolvent, except
    // for when a child is an assumption or the result of an equality resolution
    // step. In these cases it might be necessary to add an additional or step.
    //
    //
    // If rule(C1) = ASSUME or rule(C1) = EQ_RESOLVE:
    //
    //  If C1 = (or F1 ... Fn) and C2 != (not (or F1 ... Fn)):
    //
    //            P1
    //  ---------------------
    //   VP1: (cl F1 ... Fn)
    //
    //  Otherwise, VP1 = P1
    //
    // If rule(C2) = ASSUME or rule(C2) = EQ_RESOLVE:
    //
    //  If C2 = (or F1 ... Fn) and C1 != (not (or F1 ... Fn)):
    //
    //            P2
    //  ---------------------
    //   VP2: (cl F1 ... Fn)
    //
    //  Otherwise, VP2 = P2
    //
    //
    // If C = (or G1 ... Gn) and C is not a singleton:
    //
    //    VP1           VP2
    //  ---------------------
    //     (cl G1 ... Gn)*
    //
    // Otherwise, if C = false
    //
    //    VP1           VP2
    //  ---------------------
    //     (cl)**
    //
    // Otherwise,
    //
    //    VP1           VP2
    //  ---------------------
    //     (cl C)***
    //
    //  *   the corresponding proof node is (not (and F1 ... Fn))
    //  **  the corresponding proof node is False
    //  *** the corresponding proof node is C
    case PfRule::RESOLUTION:
    {
      bool success = true;
      std::vector<Node> vps = children;

      // Needed to determine if (cl C) or (cl G1 ... Gn) should be added in the
      // end.
      std::vector<Node> current_resolvent;

      // If the rule of a child is ASSUME or EQ_RESOLUTION an application of the
      // or rule might be needed.
      for (unsigned long int i = 0; i < 2; i++)
      {
        if (cdp->getProofFor(children[i])->getRule() == PfRule::ASSUME
            || cdp->getProofFor(children[i])->getRule() == PfRule::EQ_RESOLVE)
        {
          // The current child is not a singleton if its the negation of the
          // other child. Then, they will resolve to (cl). In this case, an
          // additional or step is necessary to.
          Node child2 = children[1 - i];

          if (children[i].getKind() == kind::OR
              && children[i] != child2.notNode())
          {
            std::vector<Node> clauses;
            clauses.push_back(d_cl);
            clauses.insert(
                clauses.end(), children[i].begin(), children[i].end());
            vps[i] = nm->mkNode(kind::SEXPR, clauses);
            success &=
                addAletheStep(AletheRule::OR, vps[i], vps[i], {children[i]}, {}, *cdp);
            // If this is the case the literals in C1 are added to the
            // current_resolvent.
            current_resolvent.insert(current_resolvent.end(),
                                     children[i].begin(),
                                     children[i].end());
          }
          else
          {
            // Otherwise, the whole clause is added.
            current_resolvent.push_back(children[i]);
          }
        }
        // For all other rules it is easy to determine if the whole clause or
        // the literals in the clause should be added. If the node is an or node
        // add literals otherwise the whole clause.
        else
        {
          if (children[i].getKind() == kind::OR)
          {
            current_resolvent.insert(current_resolvent.end(),
                                     children[i].begin(),
                                     children[i].end());
          }
          else
          {
            current_resolvent.push_back(children[i]);
          }
        }
      }

      // The pivot and its negation are deleted from the current_resolvent
      current_resolvent.erase(std::find(
          current_resolvent.begin(), current_resolvent.end(), args[1]));
      current_resolvent.erase(std::find(current_resolvent.begin(),
                                        current_resolvent.end(),
                                        args[1].notNode()));
      // If there is only one element left in current_resolvent C should be
      // printed as (cl C), otherwise as (cl G1 ... Gn)
      if (res.getKind() == kind::OR && current_resolvent.size() != 1)
      {
        return success &= addAletheStepFromOr(AletheRule::RESOLUTION,
                                              res,
                                              vps,
                                              {},
                                              *cdp);  //(cl G1 ... Gn)
      }
      else if (res == nm->mkConst(false))
      {
        return success &= addAletheStep(AletheRule::RESOLUTION,
        			        res,
                                        nm->mkNode(kind::SEXPR, d_cl),
                                        vps,
                                        {},
                                        *cdp);  //(cl)
      }
      return success &= addAletheStep(AletheRule::RESOLUTION,
                                      res,
                                      nm->mkNode(kind::SEXPR, d_cl, res),
                                      vps,
                                      {},
                                      *cdp);  //(cl C)
    }
    // ======== N-ary Resolution
    // See proof_rule.h for documentation on the CHAIN_RESOLUTION rule. This
    // comment uses variable names as introduced there.
    //
    // If for any Ci, rule(Ci) = ASSUME or rule(Ci) = EQ_RESOLVE and Ci = (or F1
    // ... Fn) and Ci != L_{i-1} (for C1, C1 != L_1) then:
    //
    //       P1 ... Pm
    // ---------------------- OR
    //  (VPi:(cl F1 ... Fn))
    //
    // Otherwise VPi = Ci.
    //
    // It is necessary to determine whether C is a singleton clause or not (see
    // RESOLUTION for more details). However, in contrast to the RESOLUTION rule
    // it is not necessary to calculate the complete current resolvent. Instead
    // it suffices to find the last introduction of the conclusion as a subterm
    // of a child and then check if it is eliminated by a later resolution step.
    // If the conclusion was not introduced as a subterm it has to be a
    // non-singleton clause. If it was introduced but not eliminated, it follows
    // that it is indeed a singleton clause and should be printed as (cl F1 ...
    // Fn) instead of (cl (or F1 ... Fn)).
    //
    // This procedure is possible since the proof is already structured in a
    // certain way. It can never contain a second occurrance of a literal when
    // the first occurrence we found was eliminated from the proof. E.g., note
    // that constellations as for example:
    //
    // (cl (not (or a b)))   (cl (or a b) (or a b))
    // ---------------------------------------------
    //                 (cl (or a b))
    //
    // are not possible by design of the proof generation.
    //
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
    case PfRule::CHAIN_RESOLUTION:
    {
      Node trueNode = nm->mkConst(true);
      Node falseNode = nm->mkConst(false);
      std::vector<Node> new_children = children;

      // If a child F = (or F1 ... Fn) is the result of a ASSUME or
      // EQ_RESOLUTION it might be necessary to add an additional step with the
      // Alethe or rule since otherwise it will be used as (cl (or F1 ... Fn)).

      // The first child is used as a OR non-singleton clause if it is not equal
      // to its pivot L_1. Since it's the first clause in the resolution it can
      // only be equal to the pivot in the case the polarity is true.
      if (children[0].getKind() == kind::OR
          && (args[0] != trueNode || children[0] != args[1]))
      {
        std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
        if (childPf->getRule() == PfRule::ASSUME
            || childPf->getRule() == PfRule::EQ_RESOLVE)
        {
          // Add or step
          std::vector<Node> subterms{d_cl};
          subterms.insert(
              subterms.end(), children[0].begin(), children[0].end());
          Node conclusion = nm->mkNode(kind::SEXPR, subterms);
          addAletheStep(
              AletheRule::OR, conclusion, conclusion, {children[0]}, {}, *cdp);
          new_children[0] = conclusion;
        }
      }

      // For all other children C_i the procedure is simliar. There is however a
      // key difference in the choice of the pivot element which is now the
      // L_{i-1}, i.e. the pivot of the child with the result of the i-1
      // resolution steps between the children before it. Therefore, if the
      // policy id_{i-1} is true, the pivot has to appear negated in the child
      // in which case it should not be a (cl (or F1 ... Fn)) node. The same is
      // true if it isn't the pivot element.
      for (std::size_t i = 1, size = children.size(); i < size; ++i)
      {
        if (children[i].getKind() == kind::OR
            && (args[2 * (i - 1)] != falseNode
                || args[2 * (i - 1) + 1] != children[i]))
        {
          std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
          if (childPf->getRule() == PfRule::ASSUME
              || childPf->getRule() == PfRule::EQ_RESOLVE)
          {
            // Add or step
            std::vector<Node> lits{d_cl};
            lits.insert(lits.end(), children[i].begin(), children[i].end());
            Node conclusion = nm->mkNode(kind::SEXPR, lits);
            addAletheStep(AletheRule::OR,
                          conclusion,
                          conclusion,
                          {children[i]},
                          {},
                          *cdp);
            new_children[i] = conclusion;
          }
        }
      }

      // If res is not an or node, then it's necessarily a singleton clause.
      bool isSingletonClause = res.getKind() != kind::OR;
      // Otherwise, we need to determine if res if it's of the form (or t1 ...
      // tn), corresponds to the clause (cl t1 ... tn) or to (cl (OR t1 ...
      // tn)). The only way in which the latter can happen is if res occurs as a
      // child in one of the premises, and is not eliminated afterwards. So we
      // search for res as a subterm of some children, which would mark its last
      // insertion into the resolution result. If res does not occur as the
      // pivot to be eliminated in a subsequent premise, then, and only then, it
      // is a singleton clause.
      if (!isSingletonClause)
      {
        size_t i;
        // Find out which child introduced res. There can be at most one by
        // design of the proof production. After the loop finishes i is the
        // index of the child C_i that introduced res. If i=0 none of the
        // children introduced res as a subterm and therefore it cannot be a
        // singleton clause.
        for (i = children.size(); i > 0; --i)
        {
          // only non-singleton clauses may be introducing
          // res, so we only care about non-singleton or nodes. We check then
          // against the kind and whether the whole or node occurs as a pivot of
          // the respective resolution
          if (children[i - 1].getKind() != kind::OR)
          {
            continue;
          }
          size_t pivotIndex = (i != 1) ? 2 * (i - 1) - 1 : 1;
          if (args[pivotIndex] == children[i - 1]
              || args[pivotIndex].notNode() == children[i - 1])
          {
            continue;
          }
          // if res occurs as a subterm of a non-singleton premise
          if (std::find(children[i - 1].begin(), children[i - 1].end(), res)
              != children[i - 1].end())
          {
            break;
          }
        }

        // If res is a subterm of one of the children we still need to check if
        // that subterm is eliminated
        if (i > 0)
        {
          bool posFirst = (i == 1) ? (args[0] == trueNode)
                                   : (args[(2 * (i - 1)) - 2] == trueNode);
          Node pivot = (i == 1) ? args[1] : args[(2 * (i - 1)) - 1];

          // Check if it is eliminated by the previous resolution step
          if ((res == pivot && !posFirst)
              || (res.notNode() == pivot && posFirst)
              || (pivot.notNode() == res && posFirst))
          {
            // We decrease i by one such that isSingletonClause is set to false
            --i;
          }
          else
          {
            // Otherwise check if any subsequent premise eliminates it
            for (; i < children.size(); ++i)
            {
              posFirst = args[(2 * i) - 2] == trueNode;
              pivot = args[(2 * i) - 1];
              // To eliminate res, the clause must contain it with opposite
              // polarity. There are three successful cases, according to the
              // pivot and its sign
              //
              // - res is the same as the pivot and posFirst is true, which
              // means that the clause contains its negation and eliminates it
              //
              // - res is the negation of the pivot and posFirst is false, so
              // the clause contains the node whose negation is res. Note that
              // this case may either be res.notNode() == pivot or res ==
              // pivot.notNode().
              if ((res == pivot && posFirst)
                  || (res.notNode() == pivot && !posFirst)
                  || (pivot.notNode() == res && !posFirst))
              {
                break;
              }
            }
          }
        }
        // if not eliminated (loop went to the end), then it's a singleton
        // clause
        isSingletonClause = i == children.size();
      }
      if (!isSingletonClause)
      {
        return addAletheStepFromOr(
            AletheRule::RESOLUTION, res, new_children, {}, *cdp);
      }
      if (res == falseNode)
      {
        return addAletheStep(AletheRule::RESOLUTION,
                             res,
                             nm->mkNode(kind::SEXPR, d_cl),
                             new_children,
                             {},
                             *cdp);
      }
      return addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           new_children,
                           {},
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
    // ------- DUPLICATED_LITERALS
    //   VC2*
    //
    // * the corresponding proof node is C2
    case PfRule::FACTORING:
    {
      if (res.getKind() == kind::OR)
      {
        for (auto child : children[0])
        {
          if (child != res)
          {
            return addAletheStepFromOr(
                AletheRule::DUPLICATED_LITERALS, res, children, {}, *cdp);
          }
        }
      }
      return addAletheStep(AletheRule::DUPLICATED_LITERALS,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
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
          && addAletheStepFromOr(AletheRule::RESOLUTION, res, {vp1, vp2}, {}, *cdp);
    }
    // ======== Equality resolution
    // See proof_rule.h for documentation on the EQ_RESOLVE rule. This
    // comment uses variable names as introduced there.
    //
    // If F1 = (or G1 ... Gn), then P1 will be printed as (cl G1 ... Gn) but
    // needs to be printed as (cl (or G1 ... Gn)). The only exception to this
    // are ASSUME steps that are always printed as (cl (or G1 ... Gn)) and
    // EQ_RESOLVE steps itself.
    //
    //           ------  ...  ------ OR_NEG
    //   P1       VP21   ...   VP2n
    //  ---------------------------- RESOLUTION
    //              VP3
    //  ---------------------------- DUPLICATED_LITERALS
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
    // * the corresponding proof node is F2
    case PfRule::EQ_RESOLVE:
    {
      bool success = true;
      Node vp1 =
          nm->mkNode(kind::SEXPR,
                     {d_cl, children[1].notNode(), children[0].notNode(), res});
      Node child1 = children[0];

      // Transform (cl F1 ... Fn) into (cl (or F1 ... Fn))
      if (children[0].notNode() != vp1[1] && children[0].getKind() == kind::OR)
      {
        PfRule pr = cdp->getProofFor(child1)->getRule();
        if (pr != PfRule::ASSUME && pr != PfRule::EQ_RESOLVE)
        {
          std::vector<Node> clauses;
          clauses.push_back(d_cl);  // cl
          clauses.insert(clauses.end(),
                         children[0].begin(),
                         children[0].end());  //(cl G1 ... Gn)

          std::vector<Node> vp2Nodes = {children[0]};
          std::vector<Node> resNodes = {d_cl};
          for (int i = 0; i < children[0].end() - children[0].begin(); i++)
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
          }
          Node vp3 = nm->mkNode(kind::SEXPR, resNodes);
          success &= addAletheStep(
              AletheRule::RESOLUTION, vp3, vp3, vp2Nodes, {}, *cdp);

          Node vp4 = nm->mkNode(kind::SEXPR, d_cl, children[0]);
          success &= addAletheStep(
              AletheRule::DUPLICATED_LITERALS, vp4, vp4, {vp3}, {}, *cdp);
          child1 = vp4;
        }
      }

      success &= addAletheStep(AletheRule::EQUIV_POS2, vp1, vp1, {}, {}, *cdp);

      if (res == nm->mkConst(false))
      {
        return success &= addAletheStep(AletheRule::RESOLUTION,
                                        res,
                                        nm->mkNode(kind::SEXPR, d_cl),
                                        {vp1, children[1], child1},
                                        {},
                                        *cdp);
      }

      return success &= addAletheStep(AletheRule::RESOLUTION,
                                      res,
                                      nm->mkNode(kind::SEXPR, d_cl, res),
                                      {vp1, children[1], child1},
                                      {},
                                      *cdp);
    }
    // ======== Modus ponens
    // See proof_rule.h for documentation on the MODUS_PONENS rule. This comment
    // uses variable names as introduced there.
    //
    //    (P2:(=> F1 F2))
    // --------------------- IMPLIES
    // (VP1:(cl (not F1) F2))             (P1:F1)
    // ------------------------------------------- RESOLUTION
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
                              {},
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
    // * the corresponding proof node is F2
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(AletheRule::NOT_NOT, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
                              {},
                              *cdp);
    }
    // ======== Contradiction
    // See proof_rule.h for documentation on the CONTRADICTION rule. This
    // comment uses variable names as introduced there.
    //
    //  P1   P2
    // --------- RESOLUTION
    //  (cl)*
    //
    // * the corresponding proof node is false
    case PfRule::CONTRA:
    {
      return addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl),
                           children,
                           {},
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
      std::vector<Node> neg_Nodes = {d_cl,res};
      for (size_t i = 0, size = children.size(); i < size; i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = nm->mkNode(kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children = {vp1};
      new_children.insert(new_children.end(), children.begin(), children.end());

      return addAletheStep(AletheRule::AND_NEG, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
                              {},
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
    // ======== CNF ITE Pos version 3
    //
    // ----- ITE_POS1            ----- ITE_POS2
    //  VP1                       VP2
    // ------------------------------- RESOLUTION
    //             VP3
    // ------------------------------- REORDER
    //             VP4
    // ------------------------------- DUPLICATED_LITERALS
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
             && addAletheStep(
                 AletheRule::RESOLUTION, vp3, vp3, {vp1, vp2}, {}, *cdp)
             && addAletheStep(AletheRule::REORDER, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::DUPLICATED_LITERALS, res, {vp4}, {}, *cdp);
    }
    // The following rules are all translated according to the clause pattern.
    case PfRule::CNF_ITE_NEG1:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_NEG2:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG1, res, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    //
    // ----- ITE_NEG1            ----- ITE_NEG2
    //  VP1                       VP2
    // ------------------------------- RESOLUTION
    //             VP3
    // ------------------------------- REORDER
    //             VP4
    // ------------------------------- DUPLICATED_LITERALS
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
             && addAletheStep(
                 AletheRule::RESOLUTION, vp3, vp3, {vp1, vp2}, {}, *cdp)
             && addAletheStep(AletheRule::REORDER, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::DUPLICATED_LITERALS, res, {vp4}, {}, *cdp);
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
    // In the case that the kind of the function symbol ?f is forall, the cong
    // rule needs to be converted into a bind rule. The first child will be a
    // refl rule that can be omitted.
    //
    //  let t1 = (BOUND_VARIABLE LIST (v1 A1) ... (vn An)) and s1 =
    //  (BOUND_VARIABLE LIST (w1 B1) ... (wn Bn))
    //
    //    P2
    //  ----------------------------------------------- bind, args: ((:= v1 w1)
    //  ... (:= vn wn)) (cl (= (forall ((v1 A1)...(vn An)) t2) (forall
    //  ((w1 B1)...(wn Bn)) s2)))*
    //
    // Otherwise, the rule follows the singleton pattern, i.e.:
    //
    //    P1 ... Pn
    //  ------------------------------------------------------ cong
    //   (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))*
    //
    // * the corresponding proof node is (= (<kind> f? t1 ... tn) (<kind> f? s1
    // ... sn))
    case PfRule::CONG:
    {
      if (args[0] == ProofRuleChecker::mkKindNode(kind::FORALL))
      {
        std::vector<Node> new_children;
        std::vector<Node> sanitized_args;
        for (size_t i = 0,
                    size = (children[0][0].end() - children[0][0].begin());
             i < size;
             i++)
        {
          sanitized_args.push_back(d_anc.convert(
              nm->mkNode(kind::EQUAL, children[0][0][i], children[0][1][i])));
        }
        return addAletheStep(AletheRule::ANCHOR_BIND,
                             res,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {children[1]},
                             sanitized_args,
                             *cdp);
      }
      return addAletheStep(AletheRule::CONG,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
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

AletheProofPostprocessFinalCallback::AletheProofPostprocessFinalCallback(
    ProofNodeManager* pnm, AletheNodeConverter& anc)
    : d_pnm(pnm), d_anc(anc)
{
  NodeManager* nm = NodeManager::currentNM();
  d_cl = nm->mkBoundVar("cl", nm->sExprType());
}

bool AletheProofPostprocessFinalCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn,
    const std::vector<Node>& fa,
    bool& continueUpdate)
{
  return false;
}

bool AletheProofPostprocessFinalCallback::update(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp,
    bool& continueUpdate)
{
  return true;
}

AletheProofPostprocess::AletheProofPostprocess(ProofNodeManager* pnm,
                                               AletheNodeConverter& anc)
    : d_pnm(pnm), d_cb(d_pnm, anc), d_fcb(d_pnm, anc)
{
}

AletheProofPostprocess::~AletheProofPostprocess() {}

void AletheProofPostprocess::process(std::shared_ptr<ProofNode> pf) {}

}  // namespace proof

}  // namespace cvc5
