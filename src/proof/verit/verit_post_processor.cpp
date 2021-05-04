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
 * The module for processing proof nodes into veriT proof nodes
 */

#include "proof/verit/verit_post_processor.h"

#include "expr/proof.h"
#include "expr/proof_checker.h"

namespace cvc5 {

namespace proof {

VeritProofPostprocessCallback::VeritProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_nm(NodeManager::currentNM())
{
  d_cl = d_nm->mkBoundVar("cl", d_nm->stringType());
}

bool VeritProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 const std::vector<Node>& fa,
                                                 bool& continueUpdate)
{
  if (pn->getRule() == PfRule::VERIT_RULE)
  {
    return false;
  }
  return true;
}

bool VeritProofPostprocessCallback::update(Node res,
                                           PfRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args,
                                           CDProof* cdp,
                                           bool& continueUpdate)
{
  Trace("verit-proof") << "- veriT post process callback " << res << " " << id
                       << " " << children << " / " << args << std::endl;

  d_nm = NodeManager::currentNM();
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
      return addVeritStep(res, VeritRule::ASSUME, children, {}, *cdp);
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
      for (Node arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
      }
      negNode.push_back(children[0]);         // (not F1) ... (not Fn) F
      negNode.insert(negNode.begin(), d_cl);  // (cl (not F1) ... (not F) F)
      Node vp1 = d_nm->mkNode(kind::SEXPR, negNode);
      success &=
          addVeritStep(vp1, VeritRule::ANCHOR_SUBPROOF, children, args, *cdp);

      // Build vp2i
      Node andNode;
      if (args.size() != 1)
      {
        andNode = d_nm->mkNode(kind::AND, args);  // (and F1 ... Fn)
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
        vp2_i = d_nm->mkNode(kind::SEXPR,
                             d_cl,
                             andNode.notNode(),
                             args[i]);  // (cl (not (and F1 ... Fn)) Fi)
        success &= addVeritStep(vp2_i, VeritRule::AND_POS, {}, {}, *cdp);
        premisesVP2.push_back(vp2_i);
        notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
      }

      Node vp2a =
          d_nm->mkNode(kind::SEXPR, notAnd);  // (cl F (not (and F1 ... Fn))^n)
      success &=
          addVeritStep(vp2a, VeritRule::RESOLUTION, premisesVP2, {}, *cdp);

      notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n F)
      notAnd.push_back(children[0]);     //(cl (not (and F1 ... Fn))^n F)
      Node vp2b = d_nm->mkNode(kind::SEXPR, notAnd);
      success &= addVeritStep(vp2b, VeritRule::REORDER, {vp2a}, {}, *cdp);

      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
      success &=
          addVeritStep(vp3, VeritRule::DUPLICATED_LITERALS, {vp2b}, {}, *cdp);

      Node vp8 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::IMPLIES, andNode, children[0]));

      Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], andNode);
      success &= addVeritStep(vp4, VeritRule::IMPLIES_NEG1, {}, {}, *cdp);

      Node vp5 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0]);
      success &= addVeritStep(vp5, VeritRule::RESOLUTION, {vp4, vp3}, {}, *cdp);

      Node vp6 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0].notNode());
      success &= addVeritStep(vp6, VeritRule::IMPLIES_NEG2, {}, {}, *cdp);

      Node vp7 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], vp8[1]);
      success &= addVeritStep(vp7, VeritRule::RESOLUTION, {vp5, vp6}, {}, *cdp);

      if (children[0] != d_nm->mkConst(false))
      {
        success &= addVeritStep(
            res, VeritRule::DUPLICATED_LITERALS, vp8, {vp7}, {}, *cdp);
      }
      else
      {
        success &=
            addVeritStep(vp8, VeritRule::DUPLICATED_LITERALS, {vp7}, {}, *cdp);

        Node vp9 =
            d_nm->mkNode(kind::SEXPR,
                         d_cl,
                         d_nm->mkNode(kind::EQUAL, vp8[1], andNode.notNode()));
        success &= addVeritStep(vp9, VeritRule::IMPLIES_SIMPLIFY, {}, {}, *cdp);

        Node vp10 = d_nm->mkNode(
            kind::SEXPR, d_cl, vp8[1].notNode(), andNode.notNode());
        success &= addVeritStep(vp10, VeritRule::EQUIV1, {vp9}, {}, *cdp);

        success &= addVeritStep(res,
                                VeritRule::RESOLUTION,
                                d_nm->mkNode(kind::SEXPR, d_cl, res),
                                {vp8, vp10},
                                {},
                                *cdp);
      }

      return success;
    }
    // ======== Theory Rewrite
    // Children: none
    // Arguments: (F, tid, rid)
    // ----------------------------------------
    // Conclusion: F
    // where F is an equality of the form (= t t') where t' is obtained by
    // applying the kind of rewriting given by the method identifier rid, which
    // is one of:
    //  { RW_REWRITE_THEORY_PRE, RW_REWRITE_THEORY_POST, RW_REWRITE_EQ_EXT }
    // Notice that the checker for this rule does not replay the rewrite to
    // ensure correctness, since theory rewriter methods are not static. For
    // example, the quantifiers rewriter involves constructing new bound
    // variables that are not guaranteed to be consistent on each call.
    //
    //
    // The rule is translated according to tid and the outermost connective of
    // t. This is not an exact translation but should work in most cases.
    //
    // E.g. if the F: (= (* 0 d) 0) and tid = THEORY_ARITH, then prod_simplify
    // is correctly guessed as the rule.
    case PfRule::THEORY_REWRITE:
    {
      theory::TheoryId tid =
          static_cast<theory::TheoryId>(std::stoul(args[1].toString()));
      VeritRule vrule = VeritRule::UNDEFINED;
      Node t = res[0];

      switch (tid)
      {
        case theory::TheoryId::THEORY_BUILTIN:
        {
          switch (t.getKind())
          {
            case kind::ITE:
            {
              vrule = VeritRule::ITE_SIMPLIFY;
              break;
            }
            case kind::EQUAL:
            {
              vrule = VeritRule::EQ_SIMPLIFY;
              break;
            }
            case kind::AND:
            {
              vrule = VeritRule::AND_SIMPLIFY;
              break;
            }
            case kind::OR:
            {
              vrule = VeritRule::OR_SIMPLIFY;
              break;
            }
            case kind::NOT:
            {
              vrule = VeritRule::NOT_SIMPLIFY;
              break;
            }
            case kind::IMPLIES:
            {
              vrule = VeritRule::IMPLIES_SIMPLIFY;
              break;
            }
            case kind::WITNESS:
            {
              vrule = VeritRule::QNT_SIMPLIFY;
              break;
            }
            default:
            {
              // In this case the rule is undefined
              // Should this be BOOL_SIMPLIFY?
            }
          }
          break;
        }
        case theory::TheoryId::THEORY_BOOL:
        {
          vrule = VeritRule::BOOL_SIMPLIFY;
          break;
        }
        case theory::TheoryId::THEORY_UF:
        {
          switch (t.getKind())
          {
            case kind::EQUAL:
            {  // A lot of these seem to be symmetry rules but not all....
              vrule = VeritRule::EQUIV_SIMPLIFY;
              break;
            }
            default:
            {
              // In this case the rule is undefined
            }
          }
          break;
        }
        case theory::TheoryId::THEORY_ARITH:
        {
          switch (t.getKind())
          {
            case kind::DIVISION:
            {
              vrule = VeritRule::DIV_SIMPLIFY;
              break;
            }
            case kind::PRODUCT:
            {
              vrule = VeritRule::PROD_SIMPLIFY;
              break;
            }
            case kind::MINUS:
            {
              vrule = VeritRule::MINUS_SIMPLIFY;
              break;
            }
            case kind::UMINUS:
            {
              vrule = VeritRule::UNARY_MINUS_SIMPLIFY;
              break;
            }
            case kind::PLUS:
            {
              vrule = VeritRule::SUM_SIMPLIFY;
              break;
            }
            case kind::MULT:
            {
              vrule = VeritRule::PROD_SIMPLIFY;
              break;
            }
            case kind::EQUAL:
            {
              vrule = VeritRule::EQUIV_SIMPLIFY;
              break;
            }
            case kind::LT: { [[fallthrough]];
            }
            case kind::GT: { [[fallthrough]];
            }
            case kind::GEQ: { [[fallthrough]];
            }
            case kind::LEQ:
            {
              vrule = VeritRule::COMP_SIMPLIFY;
              break;
            }
            case kind::CAST_TO_REAL:
            {
              return addVeritStep(res,
                                  VeritRule::LA_GENERIC,
                                  d_nm->mkNode(kind::SEXPR, d_cl, res),
                                  children,
                                  {d_nm->mkConst(Rational(1))},
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
          vrule = VeritRule::QUANTIFIER_SIMPLIFY;
          break;
        }
        default: {
        };
      }
      return addVeritStep(
          res, vrule, d_nm->mkNode(kind::SEXPR, d_cl, res), children, {}, *cdp);
    }

    //================================================= Boolean rules
    // ======== Resolution
    // Children:
    //  (P1:C1, P2:C2)
    // Arguments: (id, L)
    // ---------------------
    // Conclusion: C
    // where
    //   - C1 and C2 are nodes viewed as clauses, i.e., either an OR node with
    //     each children viewed as a literal or a node viewed as a literal. Note
    //     that an OR node could also be a literal.
    //   - id is either true or false
    //   - L is the pivot of the resolution, which occurs as is (resp. under a
    //     NOT) in C1 and negatively (as is) in C2 if id = true (id = false).
    //   C is a clause resulting from collecting all the literals in C1, minus
    //   the first occurrence of the pivot or its negation, and C2, minus the
    //   first occurrence of the pivot or its negation, according to the policy
    //   above. If the resulting clause has a single literal, that literal
    //   itself is the result; if it has no literals, then the result is false;
    //   otherwise it's an OR node of the resulting literals.
    //
    //
    // In the case that C = (or G1 ... Gn) the result is ambigous. E.g.,
    //
    // (cl F1 (or F2 F3))    (cl (not F1))
    // -------------------------------------- RESOLUTION
    // (cl (or F2 F3))
    //
    // (cl F1 F2 F3)        (cl (not F1))
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
    //  proof rule: or
    //  proof node: (VP1:(cl F1 ... Fn))
    //  proof term: (cl F1 ... Fn)
    //  premises: P1
    //  args: ()
    //
    //  Otherwise VP1 = P1
    //
    // If rule(C2) = ASSUME or rule(C2) = EQ_RESOLVE:
    //
    //  If C2 = (or F1 ... Fn) and C1 != (not (or F1 ... Fn)):
    //
    //  proof rule: or
    //  proof node: (VP2:(cl F1 ... Fn))
    //  proof term: (cl F1 ... Fn)
    //  premises: P2
    //  args: ()
    //
    //  Otherwise VP2 = P2
    //
    // If C = (or G1 ... Gn) and C is not a singleton:
    //
    //  proof rule: resolution
    //  proof node: (or G1 ... Gn)
    //  proof term: (cl G1 ... Gn)
    //  premises: VP1 VP2
    //  args: ()
    //
    // Otherwise if C = false
    //
    //  proof rule: resolution
    //  proof node: C
    //  proof term: (cl)
    //  premises: VP1 VP2
    //  args: ()
    //
    // Otherwise,
    //
    //  proof rule: resolution
    //  proof node: C
    //  proof term: (cl C)
    //  premises: VP1 VP2
    //  args: ()
    case PfRule::RESOLUTION:
    {  // This can be simplified
      // The only way that or steps can be added is if one child is the negation
      // of the other, i.e. they resolve to (cl)
      bool success = true;
      std::vector<Node> vps = children;

      // Needed to determine if (cl C) or (cl G1 ... Gn) should be added in the
      // end.
      std::vector<Node> current_resolvent;

      // If the rule of the child is ASSUME or EQ_RESOLUTION and additional or
      // step might be needed.
      for (unsigned long int i = 0; i < 2; i++)
      {
        if (cdp->getProofFor(children[i])->getRule() == PfRule::ASSUME
            || cdp->getProofFor(children[i])->getRule() == PfRule::EQ_RESOLVE)
        {
          // The child is not a singleton but an or-node if the other child is
          // its negation
          Node child2;
          if (i == 0)
          {
            child2 = children[1];
          }
          else
          {
            child2 = children[0];
          }
          if (children[i].getKind() == kind::OR
              && children[i] != child2.notNode())
          {
            std::vector<Node> clauses;
            clauses.push_back(d_cl);
            clauses.insert(
                clauses.end(), children[i].begin(), children[i].end());
            vps[i] = d_nm->mkNode(kind::SEXPR, clauses);
            success &=
                addVeritStep(vps[i], VeritRule::OR, {children[i]}, {}, *cdp);
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
        return success &= addVeritStepFromOr(res,
                                             VeritRule::RESOLUTION,
                                             vps,
                                             {},
                                             *cdp);  //(cl G1 ... Gn)
      }
      else if (res == d_nm->mkConst(false))
      {
        return success &= addVeritStep(res,
                                       VeritRule::RESOLUTION,
                                       d_nm->mkNode(kind::SEXPR, d_cl),
                                       vps,
                                       {},
                                       *cdp);  //(cl)
      }
      return success &= addVeritStep(res,
                                     VeritRule::RESOLUTION,
                                     d_nm->mkNode(kind::SEXPR, d_cl, res),
                                     vps,
                                     {},
                                     *cdp);  //(cl C)
    }
    // ======== N-ary Resolution
    // Children: (P1:C_1, ..., Pm:C_n)
    // Arguments: (id_1, L_1, ..., id_{n-1}, L_{n-1})
    // ---------------------
    // Conclusion: C
    // where
    //   - let C_1 ... C_n be nodes viewed as clauses, as defined above
    //   - let "C_1 <>_{L,id} C_2" represent the resolution of C_1 with C_2 with
    //     pivot L and policy id, as defined above
    //   - let C_1' = C_1 (from P1),
    //   - for each i > 1, let C_i' = C_{i-1}' <>_{L_{i-1}, id_{i-1}} C_i
    //   The result of the chain resolution is C = C_n'
    //
    // If for any Ci, rule(Ci) = ASSUME or rule(Ci) = EQ_RESOLVE and Ci = (or F1
    // ... Fn) and Ci != L_{i-1} (for C1, C1 != L_1) then:
    //
    //  proof rule: or
    //  proof node: (VPi:(cl F1 ... Fn))
    //  proof term: (cl F1 ... Fn)
    //  premises: Pi
    //  args: ()
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
    // (cl (not (or a b)))
    // (cl (or a b) (or a b))
    // ----------------------
    // (cl (or a b))
    //
    // are not possible by design of the proof generation.
    //
    //
    // If C = (or F1 ... Fn) is a non-singleton clause then:
    //
    //  proof rule: resolution
    //  proof node: C
    //  proof term: (cl F1 ... Fn)
    //  premises: VP1 ... VPn
    //  args: ()
    //
    // Else if C = false:
    //
    //  proof rule: resolution
    //  proof node: C
    //  proof term: (cl)
    //  premises: VP1 ... VPn
    //  args: ()
    //
    // Otherwise:
    //
    //  proof rule: resolution
    //  proof node: C
    //  proof term: (cl C)
    //  premises: VP1 ... VPn
    //  args: ()
    case PfRule::CHAIN_RESOLUTION:
    {
      Node trueNode = d_nm->mkConst(true);
      Node falseNode = d_nm->mkConst(false);
      std::vector<Node> new_children = children;

      // If a child F = (or F1 ... Fn) is the result of a ASSUME or
      // EQ_RESOLUTION it might be necessary to add an additional step with the
      // veriT or rule since otherwise it will be used as (cl (or F1 ... Fn)).

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
          Node conclusion = d_nm->mkNode(kind::SEXPR, subterms);
          addVeritStep(conclusion, VeritRule::OR, {children[0]}, {}, *cdp);
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
            Node conclusion = d_nm->mkNode(kind::SEXPR, lits);
            addVeritStep(conclusion, VeritRule::OR, {children[i]}, {}, *cdp);
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
        return addVeritStepFromOr(
            res, VeritRule::RESOLUTION, new_children, {}, *cdp);
      }
      if (res == falseNode)
      {
        return addVeritStep(res,
                            VeritRule::RESOLUTION,
                            d_nm->mkNode(kind::SEXPR, d_cl),
                            new_children,
                            {},
                            *cdp);
      }
      return addVeritStep(res,
                          VeritRule::RESOLUTION,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          new_children,
                          {},
                          *cdp);
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
    //
    // If C2 = (or F1 ... Fn) but not C1 = (or C2 ... C2) then VC2 = (cl F1 ...
    // Fn) Otherwise VC2 = (cl C2)
    //
    // proof rule: duplicated_literals
    // proof node: C2
    // proof term: VC2
    // premises: P
    // args: ()
    case PfRule::FACTORING:
    {
      if (res.getKind() == kind::OR)
      {
        bool singleton = true;
        for (auto child : children[0])
        {
          if (child != res)
          {
            singleton = false;
            break;
          }
        }
        if (!singleton)
        {
          return addVeritStepFromOr(
              res, VeritRule::DUPLICATED_LITERALS, children, {}, *cdp);
        }
      }
      return addVeritStep(res,
                          VeritRule::DUPLICATED_LITERALS,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Split
    // Children: none
    // Arguments: (F)
    // ---------------------
    // Conclusion: (or F (not F))
    //
    // proof rule: not_not
    // proof node: (VP1:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: not_not
    // proof node: (VP2:(cl (not (not (not (not F)))) (not F))
    // proof term: (cl (not (not (not (not F)))) (not F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (or F (not F))
    // proof term: (cl F (not F))
    // premises: VP1 VP2
    // args: ()
    case PfRule::SPLIT:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, args[0].notNode().notNode().notNode(), args[0]);
      Node vp2 = d_nm->mkNode(kind::SEXPR,
                              d_cl,
                              args[0].notNode().notNode().notNode().notNode(),
                              args[0].notNode());

      return addVeritStep(vp2, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStepFromOr(
                    res, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp);
    }
    // ======== Equality resolution
    // Children: (P1:F1, P2:(= F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    // proof rule: equiv_pos2
    // proof node: (VP1:(cl (not (= F1 F2)) (not F1) (F2)))
    // proof term: (cl (not (= F1 F2)) (not F1) (F2))
    // premises: ()
    // args: ()
    //
    // There is a special case occurring here, if F1 = (or G1 ... Gn) because
    // then P1 will be printed as (cl G1 ... Gn) but needs to be printed as (cl
    // (or G1 ... Gn)). The only exception to this are ASSUME steps that are
    // always printed as (cl (or G1 ... Gn)) and EQ_RESOLVE steps itself.
    //
    // Repeat the following two step for i=1 to n:
    //
    // for i=1 to n:
    //
    // proof rule: or_neg
    // proof node: (VP2i:(cl (or G1 ... Gn) (not Gi)))
    // proof term: (cl (or G1 ... Gn) (not Gi))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (or G1 ... Gn)^n))
    // proof term: (cl (or G1 ... Gn)^n)
    // premises: P1 VP21 ... VPn
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (VP4:(cl (or (G1 ... Gn)))
    // proof term: (cl (or G1 ... Gn))
    // premises: VP3
    // args: ()
    //
    // Set child1 = VP3
    //
    // Otherwise child1 = VP1
    //
    // Then,
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: VP1 P2 P1
    // args: ()
    //
    // Or if F2 = false:
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl)
    // premises: VP1 P2 P1
    // args: ()
    case PfRule::EQ_RESOLVE:
    {
      bool success = true;
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, children[1].notNode(), children[0].notNode(), res);
      Node child1 = children[0];
      Node child2 = children[1];

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
            Node vp2i = d_nm->mkNode(
                kind::SEXPR,
                d_cl,
                children[0],
                children[0][i].notNode());  //(cl (or G1 ... Gn) (not Gi))
            success &= addVeritStep(vp2i, VeritRule::OR_NEG, {}, {}, *cdp);
            vp2Nodes.push_back(vp2i);
            resNodes.push_back(children[0]);
          }
          Node vp3 = d_nm->mkNode(kind::SEXPR, resNodes);
          success &=
              addVeritStep(vp3, VeritRule::RESOLUTION, vp2Nodes, {}, *cdp);

          Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, children[0]);
          success &= addVeritStep(
              vp4, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, *cdp);
          child1 = vp4;
        }
      }

      success &= addVeritStep(vp1, VeritRule::EQUIV_POS2, {}, {}, *cdp);

      if (res.toString() == "false")
      {
        return success &= addVeritStep(res,
                                       VeritRule::RESOLUTION,
                                       d_nm->mkNode(kind::SEXPR, d_cl),
                                       {vp1, child2, child1},
                                       {},
                                       *cdp);
      }

      return success &= addVeritStep(res,
                                     VeritRule::RESOLUTION,
                                     d_nm->mkNode(kind::SEXPR, d_cl, res),
                                     {vp1, child2, child1},
                                     {},
                                     *cdp);
    }
    // ======== Modus ponens
    // Children: (P1:F1, P2:(=> F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    //
    // proof rule: implies
    // proof term: (VP1:(cl (not F1) F2))
    // proof term: (cl (not F1) F2)
    // premises: P2
    // args: ()
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: VP1 P1
    // args: ()
    case PfRule::MODUS_PONENS:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::IMPLIES, {children[1]}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp1, children[0]},
                             {},
                             *cdp);
    }
    // ======== Double negation elimination
    // Children: (P:(not (not F)))
    // Arguments: none
    // ---------------------
    // Conclusion: (F)
    //
    // proof rule: not_not
    // proof node: (VP1:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: F
    // proof term: (cl F)
    // premises: VP1 P
    // args: ()
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp1, children[0]},
                             {},
                             *cdp);
    }
    // ======== Contradiction
    // Children: (P1:F P2:(not F))
    // Arguments: ()
    // ---------------------
    // Conclusion: false
    //
    // proof rule: resolution
    // proof node: false
    // proof term: (cl)
    // premises: P1 P2
    // args: ()
    case PfRule::CONTRA:
    {
      return addVeritStep(res,
                          VeritRule::RESOLUTION,
                          d_nm->mkNode(kind::SEXPR, d_cl),
                          children,
                          {},
                          *cdp);
    }
    // ======== And elimination
    // Children: (P:(and F1 ... Fn))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (Fi)
    //
    // proof rule: and
    // proof node: (VP:Fi)
    // proof term: (cl Fi)
    // premises: P
    // args: ()
    case PfRule::AND_ELIM:
    {
      return addVeritStep(res,
                          VeritRule::AND,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== And introduction
    // Children: (P1:F1 ... Pn:Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (and F1 ... Fn)
    //
    // proof rule: and_neg
    // proof node: (VP1:(cl (and F1 ... Fn) (not F1) ... (not Fn)))
    // proof term: (cl (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (and F1 ... Fn)
    // proof term: (cl (and F1 ... Fn))
    // premises: VP1 P1 ... Pn
    // args: ()
    case PfRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes;
      neg_Nodes.push_back(d_cl);
      neg_Nodes.push_back(res);
      for (size_t i = 0; i < children.size(); i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = d_nm->mkNode(kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children;
      new_children.push_back(vp1);
      new_children.insert(new_children.end(), children.begin(), children.end());

      return addVeritStep(vp1, VeritRule::AND_NEG, {}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             new_children,
                             {},
                             *cdp);
    }
    // ======== Not Or elimination
    // Children: (P:(not (or F1 ... Fn)))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (not Fi)
    //
    // proof rule: not_or
    // proof node: (not Fi)
    // proof term: (cl (not Fi))
    // premises: P
    // args: ()
    case PfRule::NOT_OR_ELIM:
    {
      return addVeritStep(res,
                          VeritRule::NOT_OR,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Implication elimination
    // Children: (P:(=> F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: implies
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::IMPLIES_ELIM:
    {
      return addVeritStepFromOr(res, VeritRule::IMPLIES, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 1
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (F1)
    //
    // proof rule: not_implies1
    // proof node: (VP:F1)
    // proof term: (cl F1)
    // premises: P
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM1:
    {
      return addVeritStep(res,
                          VeritRule::NOT_IMPLIES1,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Not Implication elimination version 2
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (not F2)
    //
    // proof rule: not_implies2
    // proof node: (not F2)
    // proof term: (cl (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM2:
    {
      return addVeritStep(res,
                          VeritRule::NOT_IMPLIES2,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Equivalence elimination version 1
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: equiv1
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::EQUIV_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV1, children, {}, *cdp);
    }
    // ======== Equivalence elimination version 2
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: equiv2
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::EQUIV_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV2, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 1
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: not_equiv1
    // proof node: (or F1 F2)
    // proof term: (cl F1 F2)
    // premises: P
    // args: ()
    case PfRule::NOT_EQUIV_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_EQUIV1, children, {}, *cdp);
    }
    // ======== Not Equivalence elimination version 2
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) (not F2))
    //
    // proof rule: not_equiv2
    // proof node: (or (not F1) (not F2))
    // proof term: (cl (not F1) (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_EQUIV_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_EQUIV2, children, {}, *cdp);
    }
    // ======== XOR elimination version 1
    // Children: (P:(xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // proof rule: XOR1
    // proof node: (or F1 F2)
    // proof term: (cl F1 F2)
    // premises: P
    // args: ()
    case PfRule::XOR_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR1, children, {}, *cdp);
    }
    // ======== XOR elimination version 2
    // Children: (P:(not (xor F1 F2))))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: XOR2
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::XOR_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR2, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 1
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // proof rule: NOT_XOR1
    // proof node: (or F1 (not F2))
    // proof term: (cl F1 (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_XOR_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_XOR1, children, {}, *cdp);
    }
    // ======== Not XOR elimination version 2
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // proof rule: NOT_XOR1
    // proof node: (or (not F1) F2)
    // proof term: (cl (not F1) F2)
    // premises: P
    // args: ()
    case PfRule::NOT_XOR_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_XOR2, children, {}, *cdp);
    }
    // ======== ITE elimination version 1
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) F1)
    //
    // proof rule: ite2
    // proof node: (or (not C) F1)
    // proof term: (cl (not C) F1)
    // premises: P
    // args: ()
    case PfRule::ITE_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE2, children, {}, *cdp);
    }
    // ======== ITE elimination version 2
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C F2)
    //
    // proof rule: ite1
    // proof node: (or C F2)
    // proof term: (cl C F2)
    // premises: P
    // args: ()
    case PfRule::ITE_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE1, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) (not F1))
    //
    // proof rule: not_ite2
    // proof node: (or (not C) (not F1))
    // proof term: (cl (not C) (not F1))
    // premises: P
    // args: ()
    case PfRule::NOT_ITE_ELIM1:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_ITE2, children, {}, *cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C (not F2))
    //
    // proof rule: not_ite1
    // proof node: (or C (not F2))
    // proof term: (cl C (not F2))
    // premises: P
    // args: ()
    case PfRule::NOT_ITE_ELIM2:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_ITE1, children, {}, *cdp);
    }

    //================================================= De Morgan rules
    // ======== Not And
    // Children: (P:(not (and F1 ... Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) ... (not Fn))
    //
    // proof rule: not_and
    // proof node: (or (not F1) ... (not Fn))
    // proof term: (cl (not F1) ... (not Fn))
    // premises: P
    // args: ()
    case PfRule::NOT_AND:
    {
      return addVeritStepFromOr(res, VeritRule::NOT_AND, children, {}, *cdp);
    }

    //================================================= CNF rules
    // ======== CNF And Pos
    // Children: ()
    // Arguments: ((and F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (not (and F1 ... Fn)) Fi)
    //
    // proof rule: and_pos
    // proof node: (or (not (and F1 ... Fn)) Fi)
    // proof term: (cl (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_POS:
    {
      return addVeritStepFromOr(res, VeritRule::AND_POS, children, {}, *cdp);
    }
    // ======== CNF And Neg
    // Children: ()
    // Arguments: ((and F1 ... Fn))
    // ---------------------
    // Conclusion: (or (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // proof rule: and_neg
    // proof node: (or (and F1 ... Fn) (not F1) ... (not Fn))
    // proof term: (cl (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    case PfRule::CNF_AND_NEG:
    {
      return addVeritStepFromOr(res, VeritRule::AND_NEG, children, {}, *cdp);
    }
    // ======== CNF Or Pos
    // Children: ()
    // Arguments: ((or F1 ... Fn))
    // ---------------------
    // Conclusion: (or (not (or F1 ... Fn)) F1 ... Fn)
    //
    // proof rule: or_pos
    // proof node: (or (not (or F1 ... Fn)) F1 ... Fn)
    // proof term: (cl (not (or F1 ... Fn)) F1 ... Fn)
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_POS:
    {
      return addVeritStepFromOr(res, VeritRule::OR_POS, children, {}, *cdp);
    }
    // ======== CNF Or Neg
    // Children: ()
    // Arguments: ((or F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (or F1 ... Fn) (not Fi))
    //
    // proof rule: or_neg
    // proof node: (or (or F1 ... Fn) (not Fi))
    // proof term: (cl (or F1 ... Fn) (not Fi))
    // premises: ()
    // args: ()
    case PfRule::CNF_OR_NEG:
    {
      return addVeritStepFromOr(res, VeritRule::OR_NEG, children, {}, *cdp);
    }
    // ======== CNF Implies Pos
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (not (implies F1 F2)) (not F1) F2)
    //
    // proof rule: implies_pos
    // proof node: (or (not (implies F1 F2)) (not F1) F2)
    // proof term: (cl (not (implies F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_POS:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_POS, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 1
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) F1)
    //
    // proof rule: implies_neg1
    // proof node: (or (implies F1 F2) F1)
    // proof term: (cl (implies F1 F2) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG1:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_NEG1, children, {}, *cdp);
    }
    // ======== CNF Implies Neg version 2
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) (not F2))
    //
    // proof rule: implies_neg2
    // proof node: (or (implies F1 F2) (not F2))
    // proof term: (cl (implies F1 F2) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_IMPLIES_NEG2:
    {
      return addVeritStepFromOr(
          res, VeritRule::IMPLIES_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) (not F1) F2)
    //
    // proof rule: equiv_pos2
    // proof node: (or (not (= F1 F2)) (not F1) F2)
    // proof term: (cl (not (= F1 F2)) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_POS2, children, {}, *cdp);
    }
    // ======== CNF Equiv Pos version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) F1 (not F2))
    //
    // proof rule: equiv_pos1
    // proof node: (or (not (= F1 F2)) F1 (not F2))
    // proof term: (cl (not (= F1 F2)) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_POS1, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) F1 F2)
    //
    // proof rule: equiv_neg2
    // proof node: (or (= F1 F2) F1 F2)
    // proof term: (cl (= F1 F2) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_NEG2, children, {}, *cdp);
    }
    // ======== CNF Equiv Neg version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) (not F1) (not F2))
    //
    // proof rule: equiv_neg1
    // proof node: (or (= F1 F2) (not F1) (not F2))
    // proof term: (cl (= F1 F2) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_EQUIV_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::EQUIV_NEG1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) F1 F2)
    //
    // proof rule: xor_pos1
    // proof node: (or (not (xor F1 F2)) F1 F2)
    // proof term: (cl (not (xor F1 F2)) F1 F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_POS1, children, {}, *cdp);
    }
    // ======== CNF Xor Pos version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) (not F1) (not F2))
    //
    // proof rule: xor_pos2
    // proof node: (or (not (xor F1 F2)) (not F1) (not F2))
    // proof term: (cl (not (xor F1 F2)) (not F1) (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_POS2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) (not F1) F2)
    //
    // proof rule: xor_neg2
    // proof node: (or (xor F1 F2) (not F1) F2)
    // proof term: (cl (xor F1 F2) (not F1) F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_NEG2, children, {}, *cdp);
    }
    // ======== CNF Xor Neg version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) F1 (not F2))
    //
    // proof rule: xor_neg1
    // proof node: (or (xor F1 F2) F1 (not F2))
    // proof term: (cl (xor F1 F2) F1 (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_XOR_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::XOR_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) (not C) F1)
    //
    // proof rule: ite_pos2
    // proof node: (or (not (ite C F1 F2)) (not C) F1)
    // proof term: (cl (not (ite C F1 F2)) (not C) F1)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_POS2, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) C F2)
    //
    // proof rule: ite_pos1
    // proof node: (or (not (ite C F1 F2)) C F2)
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_POS2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_POS1, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) F1 F2)
    //
    // proof rule: ite_pos1
    // proof node: (VP1:(cl (not (ite C F1 F2)) C F2))
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    //
    // proof rule: ite_pos2
    // proof node: (VP2:(cl (not (ite C F1 F2)) (not C) F1))
    // proof term: (cl (not (ite C F1 F2)) (not C) F2)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (not (ite C F1 F2)) F2 (not (ite C F1 F2)) F1))
    // proof term: (cl (not (ite C F1 F2)) F2 (not (ite C F1 F2)) F1)
    // premises: VP1 VP2
    // args: ()
    //
    // proof rule: reorder
    // proof node: (VP4:(cl (not (ite C F1 F2)) (not (ite C F1 F2)) F1 F2))
    // proof term: (cl (not (ite C F1 F2)) (not (ite C F1 F2)) F1 F2)
    // premises: VP3
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (or (not (ite C F1 F2)) F1 F2)
    // proof term: (cl (not (ite C F1 F2)) F1 F2)
    // premises: VP4
    // args: ()
    case PfRule::CNF_ITE_POS3:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].notNode(), res[1]);
      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[2], res[0], res[1]);
      Node vp4 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[0], res[1], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_POS1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_POS2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStep(vp4, VeritRule::REORDER, {vp3}, {}, *cdp)
             && addVeritStepFromOr(
                    res, VeritRule::DUPLICATED_LITERALS, {vp4}, {}, *cdp);
    }
    // ======== CNF ITE Neg version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not C) (not F1))
    //
    // proof rule: ite_neg2
    // proof node: (or (ite C F1 F2) (not C) (not F1))
    // proof term: (cl (ite C F1 F2) (not C) (not F1))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG1:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_NEG2, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) C (not F2))
    //
    // proof rule: ite_neg1
    // proof node: (or (ite C F1 F2) C (not F2))
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: ()
    // args: ()
    case PfRule::CNF_ITE_NEG2:
    {
      return addVeritStepFromOr(res, VeritRule::ITE_NEG1, children, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not F1) (not F2))
    //
    // proof rule: ite_neg1
    // proof node: (VP1:(or (ite C F1 F2) C (not F2)))
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: ()
    // args: ()
    //
    // proof rule: ite_neg2
    // proof node: (VP2:(or (ite C F1 F2) (not C) (not F1)))
    // proof term: (cl (ite C F1 F2) (not C) (not F1))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(or (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
    // proof term: (cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1))
    // premises: VP1 VP2
    // args: ()
    //
    // proof rule: reorder
    // proof node: (VP4:(or (ite C F1 F2) (ite C F1 F2) (not F1) (not F2)))
    // proof term: (cl (ite C F1 F2) (ite C F1 F2) (not F1) (not F2))
    // premises: VP3
    // args:()
    //
    // proof rule: duplicated_literals
    // proof node: (or (ite C F1 F2) C (not F2))
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: VP3
    // args: ()
    case PfRule::CNF_ITE_NEG3:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].notNode(), res[1]);
      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[2], res[0], res[1]);
      Node vp4 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[0], res[1], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_NEG1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_NEG2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addVeritStep(vp4, VeritRule::REORDER, {vp3}, {}, *cdp)
             && addVeritStepFromOr(
                    res, VeritRule::DUPLICATED_LITERALS, {vp4}, {}, *cdp);
    }

    //================================================= Equality rules
    // ======== Reflexive
    // Children: none
    // Arguments: (t)
    // ---------------------
    // Conclusion: (= t t)
    //
    // proof rule: refl
    // proof term: (cl (= t t))
    // premises: ()
    // args: ()
    case PfRule::REFL:
    {
      return addVeritStep(res,
                          VeritRule::REFL,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== Transitivity
    // Children: (P1:(= t1 t2), ..., Pn:(= t{n-1} tn))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t1 tn)
    //
    // proof rule: trans
    // proof node: (= t1 tn)
    // proof term: (cl (= t1 tn))
    // premises: P1, ..., Pn
    // args: ()
    case PfRule::TRANS:
    {
      return addVeritStep(res,
                          VeritRule::TRANS,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
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
    // In the case that <kind> is forall the cong rule needs to be translated
    // into a bind rule. The first child will be a refl rule that can be
    // omitted.
    //
    //  let t1 = (BOUND_VARIABLE LIST (v1 A1) ... (vn An)) and s1 =
    //  (BOUND_VARIABLE LIST (w1 B1) ... (wn Bn))
    //
    //  proof rule: bind
    //  proof node: (= (forall ((v1 A1)...(vn An)) t2) (forall ((w1 B1)...(wn
    //  Bn)) s2)) proof term: (cl (= (forall ((v1 A1)...(vn An)) t2) (forall
    //  ((w1 B1)...(wn Bn)) s2))) premises: P2 args: ((:= v1 w1) ... (:= vn wn))
    //
    // Otherwise
    //
    //  proof rule: cong
    //  proof node: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    //  proof term: (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))
    //  premises: P1, ..., Pn
    //  args: ()
    case PfRule::CONG:
    {
      if (args[0] == ProofRuleChecker::mkKindNode(kind::FORALL))
      {
        std::vector<Node> new_children;
        std::vector<Node> vars;
        for (long int i = 0;
             i < (children[0][0].end() - children[0][0].begin());
             i++)
        {
          vars.push_back(
              d_nm->mkNode(kind::EQUAL, children[0][0][i], children[0][1][i]));
          // Node vpi = d_nm->mkNode(kind::SEXPR, d_cl, vars.back());
          // addVeritStep(vpi,VeritRule::REFL,{},{},*cdp);
          // new_children.push_back(vpi);
        }
        new_children.insert(
            new_children.end(), children.begin() + 1, children.end());
        return addVeritStep(res,
                            VeritRule::ANCHOR_BIND,
                            d_nm->mkNode(kind::SEXPR, d_cl, res),
                            new_children,
                            vars,
                            *cdp);
      }
      return addVeritStep(res,
                          VeritRule::CONG,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }
    // ======== True intro
    // Children: (P:F)
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F true)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F true) F)))
    // proof term: (cl (= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof node: (VP2:(cl (= F true) (not F)))
    // proof term: (cl (= F true) (not F))
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (= F true)
    // proof term: (cl (= F true))
    // premises: VP2 P
    // args: ()
    case PfRule::TRUE_INTRO:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    // ======== True elim
    // Children: (P:(= F true))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: F
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F true) F)))
    // proof term: (cl (= (= F true) F))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node: (VP2:(cl (not (= F true)) F))
    // proof term: (cl (not (= F true)) F)
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (F)
    // proof term: (cl F)
    // premises: VP2
    // args: ()
    //
    case PfRule::TRUE_ELIM:
    {
      bool success = true;
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      success &= addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
                 && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp);
      return success
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    // ======== False intro
    // Children: (P:(not F))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= F false)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F false) (not F))))
    // proof term: (cl (= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv2
    // proof node: (VP2:(cl (= F false) (not (not F))))
    // proof term: (cl (= F false) (not (not F)))
    // premises: VP1
    // args: ()
    //
    // proof rule: not_not
    // proof node: (VP3:(cl (not (not (not F))) F))
    // proof term: (cl (not (not (not F))) F)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP4:(cl (= F false) F))
    // proof term: (cl (= F false) F)
    // premises: VP2 VP3
    // args: ()
    //
    // proof rule: resolution
    // proof node: (= F false)
    // proof term: (cl (= F false))
    // premises: VP4 P
    // args: ()
    case PfRule::FALSE_INTRO:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      Node vp3 = d_nm->mkNode(
          kind::SEXPR, d_cl, children[0].notNode().notNode(), children[0][0]);
      Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0][0]);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp4, VeritRule::RESOLUTION, {vp2, vp3}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp4, children[0]},
                             {},
                             *cdp);
    }
    // ======== False elim
    // Children: (P:(= F false))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (not F)
    //
    // proof rule: equiv_simplify
    // proof node: (VP1:(cl (= (= F false) (not F))))
    // proof term: (cl (= (= F false) (not F)))
    // premises: ()
    // args: ()
    //
    // proof rule: equiv1
    // proof node: (VP2:(cl (not (= F false)) (not F)))
    // proof term: (cl (not (= F false)) (not F))
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: (not F)
    // proof term: (cl (not F))
    // premises: VP2 P
    // args: ()
    case PfRule::FALSE_ELIM:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }

    //================================================= Quantifiers rules
    // ======== Witness intro
    // Children: (P:(exists ((x T)) F[x]))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: (= k (witness ((x T)) F[x]))
    // where k is the Skolem form of (witness ((x T)) F[x]).
    /*case PfRule::WITNESS_INTRO:
    {
            return false;
    }*/
    // ======== Exists intro
    // Children: (P:F[t])
    // Arguments: ((exists ((x T)) F[x]))
    // ----------------------------------------
    // Conclusion: (exists ((x T)) F[x])
    // This rule verifies that F[x] indeed matches F[t] with a substitution
    // over x.
    /*case PfRule::EXISTS_INTRO:
    {
            return false;
    }*/
    // ======== Skolemize
    // Children: (P:(exists ((x1 T1) ... (xn Tn)) F))
    // Arguments: none
    // ----------------------------------------
    // Conclusion: F*sigma
    // sigma maps x1 ... xn to their representative skolems obtained by
    // SkolemManager::mkSkolemize, returned in the skolems argument of that
    // method. Alternatively, can use negated forall as a premise.
    /*case PfRule::SKOLEMIZE:
    {
    }*/
    // ======== Instantiate
    // Children: (P:(forall ((x1 T1) ... (xn Tn)) F))
    // Arguments: (t1 ... tn)
    // ----------------------------------------
    // Conclusion: F*sigma
    // sigma maps x1 ... xn to t1 ... tn.
    //
    // proof rule: forall_inst
    // proof node: (VP1:(cl (or (not (forall ((x1 T1) ... (xn Tn)) F))
    // F*sigma)))
    // proof term: (cl (or (not (forall ((x1 T1) ... (xn Tn)) F))
    // F*sigma))
    // premises: ()
    // args: (= x1 t1) ... (= xn tn)
    //
    // proof rule: or
    // proof node: (VP2:(cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma))
    // proof term: (cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma)
    // premises: VP1
    // args: ()
    //
    // proof rule: resolution
    // proof node: F*sigma
    // proof term: (cl F*sigma)
    // premises: VP2 P
    // args: ()
    case PfRule::INSTANTIATE:
    {
      for (unsigned long int i = 0; i < args.size(); i++)
      {
        new_args.push_back(
            d_nm->mkNode(kind::EQUAL, args[i], children[0][0][i]));
      }
      Node vp1 =
          d_nm->mkNode(kind::SEXPR,
                       d_cl,
                       d_nm->mkNode(kind::OR, children[0].notNode(), res));
      bool success =
          addVeritStep(vp1, VeritRule::FORALL_INST, {}, new_args, *cdp);
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      success &= addVeritStep(vp2, VeritRule::OR, {vp1}, {}, *cdp);
      return success
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }

    //================================================= Arithmetic rules
    // ======== Adding Inequalities
    // Note: an ArithLiteral is a term of the form (>< poly const)
    // where
    //   >< is >=, >, ==, <, <=, or not(== ...).
    //   poly is a polynomial
    //   const is a rational constant
    //
    // Children: (P1:l1, ..., Pn:ln)
    //           where each li is an ArithLiteral
    //           not(= ...) is dis-allowed!
    //
    // Arguments: (k1, ..., kn), non-zero reals
    // ---------------------
    // Conclusion: (>< (* k t1) (* k t2))
    //    where >< is the fusion of the combination of the ><i, (flipping each
    //    it its ki is negative). >< is always one of <, <= NB: this implies
    //    that lower bounds must have negative ki,
    //                      and upper bounds must have positive ki.
    //    t1 is the sum of the polynomials.
    //    t2 is the sum of the constants.
    // case PfRule::ARITH_SCALE_SUM_UPPER_BOUNDS:{
    //
    //}
    // ======== Tightening Strict Integer Upper Bounds
    // Children: (P:(< i c))
    //         where i has integer type.
    // Arguments: none
    // ---------------------
    // Conclusion: (<= i greatestIntLessThan(c)})
    // INT_TIGHT_UB,
    // ======== Tightening Strict Integer Lower Bounds
    // Children: (P:(> i c))
    //         where i has integer type.
    // Arguments: none
    // ---------------------
    // Conclusion: (>= i leastIntGreaterThan(c)})
    // INT_TIGHT_LB,
    // ======== Trichotomy of the reals
    // Children: (A B)
    // Arguments: (C)
    // ---------------------
    // Conclusion: (C),
    //                 where (not A) (not B) and C
    //                   are (> x c) (< x c) and (= x c)
    //                   in some order
    //                 note that "not" here denotes arithmetic negation,
    //                 flipping
    //                 >= to <, etc.
    //
    // If C = (= x c) or C = (> x c) pre-processing has to transform (>= x c)
    // into (<= c x)
    //
    // proof rule: la_disequality
    // proof node: (VP1: (or (= x c) (not (<= x c)) (not (<= c x))))
    // proof term: (cl (or (= x c) (not (<= x c)) (not (<= c x))))
    // premises: ()
    // args: ()
    //
    // proof rule: or
    // proof node: (VP2: (cl (= x c) (not (<= x c)) (not (<= c x))))
    // proof term: (cl (= x c) (not (<= x c)) (not (<= c x)))
    // premises: ()
    // args: ()
    //
    // If C = (> x c) or C = (< x c) post-processing has to be added. In these
    // cases resolution on VP2 A B yields (not (<=x c)) or (not (<= c x)) and
    // comp_simplify is used to transform it into C. Otherwise,
    //
    // proof rule: resolution
    // proof node: C
    // proof term: (cl C)
    // premises: VP2 A B
    // args: ()
    //
    // TODO(lachnitt@stanford.edu):
    // isabelle-mirabelle/Green_cvc42/x2020_07_31_11_27_36_291_7704406.smt_in
    case PfRule::ARITH_TRICHOTOMY:
    {
      bool success = true;
      Node equal;
      Node lesser;
      Node greater;

      if (res.getKind() == kind::EQUAL)
      {
        equal = res;
      }
      else if (children[0].getKind() == kind::NOT)
      {
        equal = children[0];
      }
      else if (children[1].getKind() == kind::NOT)
      {
        equal = children[1];
      }

      if (res.getKind() == kind::GT)
      {
        greater = res;
      }
      else if (children[0].getKind() == kind::LEQ)
      {
        greater = children[0];
      }
      else if (children[1].getKind() == kind::LEQ)
      {
        greater = children[1];
      }

      if (res.getKind() == kind::LT)
      {
        lesser = res;
      }
      else if (children[0].getKind() == kind::GEQ)
      {
        lesser = children[0];
      }
      else if (children[1].getKind() == kind::GEQ)
      {
        lesser = children[1];
      }

      Node x = equal[0][0];
      Node c = equal[0][1];
      Node vp_child1 = children[0];
      Node vp_child2 = children[1];

      // Preprocessing
      if (res == equal || res == greater)
      {  // C = (= x c) or C = (> x c)
        // lesser = (>= x c)
        Node vpc2 = d_nm->mkNode(kind::SEXPR,
                                 d_cl,
                                 d_nm->mkNode(kind::EQUAL,
                                              d_nm->mkNode(kind::GEQ, x, c),
                                              d_nm->mkNode(kind::LEQ, c, x)));
        // (cl (= (>= x c) (<= c x)))
        Node vpc1 = d_nm->mkNode(kind::SEXPR,
                                 d_cl,
                                 vpc2[1].notNode(),
                                 d_nm->mkNode(kind::GEQ, x, c).notNode(),
                                 d_nm->mkNode(kind::LEQ, c, x));
        // (cl (not(= (>= x c) (<= c x))) (not (>= x c)) (<= c x))
        vp_child1 = d_nm->mkNode(
            kind::SEXPR, d_cl, d_nm->mkNode(kind::LEQ, c, x));  // (cl (<= c x))

        success &= addVeritStep(vpc1, VeritRule::EQUIV_POS2, {}, {}, *cdp)
                   && addVeritStep(vpc2, VeritRule::COMP_SIMPLIFY, {}, {}, *cdp)
                   && addVeritStep(vp_child1,
                                   VeritRule::RESOLUTION,
                                   {vpc1, vpc2, lesser},
                                   {},
                                   *cdp);
        // greater = (<= x c) or greater = (not (= x c)) -> no preprocessing
        // necessary
        if (res == equal)
        {
          vp_child2 = greater;
        }
        else
        {
          vp_child2 = equal;
        }
      }

      // Process
      Node vp1 =
          d_nm->mkNode(kind::SEXPR,
                       d_cl,
                       d_nm->mkNode(kind::OR,
                                    d_nm->mkNode(kind::EQUAL, x, c),
                                    d_nm->mkNode(kind::LEQ, x, c).notNode(),
                                    d_nm->mkNode(kind::LEQ, c, x).notNode()));
      // (cl (or (= x c) (not (<= x c)) (not (<= c x))))
      Node vp2 = d_nm->mkNode(kind::SEXPR,
                              d_cl,
                              d_nm->mkNode(kind::EQUAL, x, c),
                              d_nm->mkNode(kind::LEQ, x, c).notNode(),
                              d_nm->mkNode(kind::LEQ, c, x).notNode());
      // (cl (= x c) (not (<= x c)) (not (<= c x)))
      success &= addVeritStep(vp1, VeritRule::LA_DISEQUALITY, {}, {}, *cdp)
                 && addVeritStep(vp2, VeritRule::OR, {vp1}, {}, *cdp);

      // Postprocessing
      if (res == equal)
      {  // no postprocessing necessary
        return success
               && addVeritStep(res,
                               VeritRule::RESOLUTION,
                               d_nm->mkNode(kind::SEXPR, d_cl, res),
                               {vp2, vp_child1, vp_child2},
                               {},
                               *cdp);
      }
      else if (res == greater)
      {  // have (not (<= x c)) but result should be (> x c)
        Node vp3 = d_nm->mkNode(
            kind::SEXPR,
            d_cl,
            d_nm->mkNode(kind::LEQ, x, c).notNode());  // (cl (not (<= x c)))
        Node vp4 = d_nm->mkNode(
            kind::SEXPR,
            d_cl,
            d_nm->mkNode(kind::EQUAL,
                         d_nm->mkNode(kind::GT, x, c),
                         d_nm->mkNode(kind::LEQ, x, c).notNode())
                .notNode(),
            d_nm->mkNode(kind::GT, x, c),
            d_nm->mkNode(kind::LEQ, x, c)
                .notNode()
                .notNode());  // (cl (not(= (> x c) (not (<= x c)))) (> x c)
                              // (not (not (<= x c))))
        Node vp5 =
            d_nm->mkNode(kind::SEXPR,
                         d_cl,
                         d_nm->mkNode(kind::EQUAL,
                                      d_nm->mkNode(kind::GT, x, c),
                                      d_nm->mkNode(kind::LEQ, x, c).notNode()));
        // (cl (= (> x c) (not (<= x c))))

        return success
               && addVeritStep(vp3,
                               VeritRule::RESOLUTION,
                               {vp2, vp_child1, vp_child2},
                               {},
                               *cdp)
               && addVeritStep(vp4, VeritRule::EQUIV_POS1, {}, {}, *cdp)
               && addVeritStep(vp5, VeritRule::COMP_SIMPLIFY, {}, {}, *cdp)
               && addVeritStep(res,
                               VeritRule::RESOLUTION,
                               d_nm->mkNode(kind::SEXPR, d_cl, res),
                               {vp3, vp4, vp5},
                               {},
                               *cdp);
      }
      else
      {  // have (not (<= c x)) but result should be (< x c)
        Node vp3 = d_nm->mkNode(
            kind::SEXPR,
            d_cl,
            d_nm->mkNode(kind::LEQ, c, x).notNode());  // (cl (not (<= c x)))
        Node vp4 = d_nm->mkNode(
            kind::SEXPR,
            d_cl,
            d_nm->mkNode(kind::EQUAL,
                         d_nm->mkNode(kind::LT, x, c),
                         d_nm->mkNode(kind::LEQ, c, x).notNode())
                .notNode(),
            d_nm->mkNode(kind::LT, x, c),
            d_nm->mkNode(kind::LEQ, c, x)
                .notNode()
                .notNode());  // (cl (not(= (< x c) (not (<= c x)))) (< x c)
                              // (not (not (<= c x))))
        Node vp5 = d_nm->mkNode(
            kind::SEXPR,
            d_cl,
            d_nm->mkNode(kind::EQUAL,
                         d_nm->mkNode(kind::LT, x, c),
                         d_nm->mkNode(kind::LEQ, c, x)
                             .notNode()));  // (cl (= (< x c) (not (<= c x))))

        return success
               && addVeritStep(vp3,
                               VeritRule::RESOLUTION,
                               {vp2, vp_child1, vp_child2},
                               {},
                               *cdp)
               && addVeritStep(vp4, VeritRule::EQUIV_POS1, {}, {}, *cdp)
               && addVeritStep(vp5, VeritRule::COMP_SIMPLIFY, {}, {}, *cdp)
               && addVeritStep(res,
                               VeritRule::RESOLUTION,
                               d_nm->mkNode(kind::SEXPR, d_cl, res),
                               {vp3, vp4, vp5},
                               {},
                               *cdp);
      }
    }
    // ======== Arithmetic operator elimination
    // Children: none
    // Arguments: (t)
    // ---------------------
    // Conclusion: arith::OperatorElim::getAxiomFor(t)
    // ARITH_OP_ELIM_AXIOM,
    // ======== Int Trust
    // Children: (P1 ... Pn)
    // Arguments: (Q)
    // ---------------------
    // Conclusion: (Q)
    // INT_TRUST,
    //======== Multiplication sign inference
    // Children: none
    // Arguments: (f1, ..., fk, m)
    // ---------------------
    // Conclusion: (=> (and f1 ... fk) (~ m 0))
    // Where f1, ..., fk are variables compared to zero (less, greater or not
    // equal), m is a monomial from these variables, and ~ is the comparison
    // (less or greater) that results from the signs of the variables. All
    // variables with even exponent in m should be given as not equal to zero
    // while all variables with odd exponent in m should be given as less or
    // greater than zero.
    // ARITH_MULT_SIGN,
    //======== Multiplication with positive factor
    // Children: none
    // Arguments: (m, orig, lhs, rel, rhs)
    // ---------------------
    // Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
    // Where orig is the origin that implies (rel lhs rhs) and rel is a relation
    // symbol.
    // ARITH_MULT_POS,
    //======== Multiplication with negative factor
    // Children: none
    // Arguments: (m, orig, (rel lhs rhs))
    // ---------------------
    // Conclusion: (=> (and (< m 0) (rel lhs rhs)) (rel_inv (* m lhs) (* m
    // rhs))) Where orig is the origin that implies (rel lhs rhs) and rel is a
    // relation symbol and rel_inv the inverted relation symbol.
    // ARITH_MULT_NEG,
    //======== Multiplication tangent plane
    // Children: none
    // Arguments: (t, x, y, a, b, sgn)
    // ---------------------
    // Conclusion:
    //   sgn=-1: (= (<= t tplane) (or (and (<= x a) (>= y b)) (and (>= x a) (<=
    //   y b))) sgn= 1: (= (>= t tplane) (or (and (<= x a) (<= y b)) (and (>= x
    //   a)
    //   (>= y b)))
    // Where x,y are real terms (variables or extended terms), t = (* x y)
    // (possibly under rewriting), a,b are real constants, and sgn is either -1
    // or 1. tplane is the tangent plane of x*y at (a,b): b*x + a*y - a*b
    // ARITH_MULT_TANGENT,
    //

    //================================================= Extended rules
    // ======== Symmetric
    // Children: (P:(= t1 t2)) or (P:(not (= t1 t2)))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t2 t1) or (not (= t2 t1))
    //
    // proof rule: symm
    // proof node: (= t2 t1)
    // proof term: (cl (= t2 t1))
    // premises: ((P:(= t1 t2))
    // args: ()
    //
    // proof rule: not_symm
    // proof node: (not (= t2 t1))
    // proof term: (cl (not (= t2 t1)))
    // premises: (P:(not (= t1 t2))
    // args: ()
    case PfRule::SYMM:
    {
      if (res.getKind() == kind::NOT)
      {
        return addVeritStep(res,
                            VeritRule::NOT_SYMM,
                            d_nm->mkNode(kind::SEXPR, d_cl, res),
                            children,
                            {},
                            *cdp);
      }
      return addVeritStep(res,
                          VeritRule::SYMM,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
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
    //
    // Let C2 = (or F1 ... Fn)
    //
    // proof rule: reordering
    // proof node: C2
    // proof term: (cl F1 ... Fn)
    // premises: P
    // args: ()
    case PfRule::REORDERING:
    {
      return addVeritStepFromOr(res, VeritRule::REORDER, children, {}, *cdp);
    }

    default:  // TBD
    {
      std::cout << "Not implemented yet " << id << std::endl;
      return addVeritStep(res,
                          VeritRule::UNDEFINED,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          args,
                          *cdp);
    }
  }

  Trace("verit-proof") << "... error translating rule " << id << " / " << res
                       << " " << children << " " << args << std::endl;
  return false;
}

bool VeritProofPostprocessCallback::addVeritStep(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  return addVeritStep(res, rule, res, children, args, cdp);
}

bool VeritProofPostprocessCallback::addVeritStep(
    Node res,
    VeritRule rule,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(rule)));
  new_args.push_back(res);
  new_args.push_back(conclusion);
  new_args.insert(new_args.end(), args.begin(), args.end());
  Trace("verit-proof") << "... add veriT step " << res << " / " << conclusion
                       << " " << rule << " " << children << " / " << new_args
                       << std::endl;
  return cdp.addStep(res, PfRule::VERIT_RULE, children, new_args);
}

// Replace a node (or F1 ... Fn) by (cl F1 ... Fn)
bool VeritProofPostprocessCallback::addVeritStepFromOr(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> subterms = {d_cl};
  subterms.insert(subterms.end(), res.begin(), res.end());
  Node conclusion = d_nm->mkNode(kind::SEXPR, subterms);
  return addVeritStep(res, rule, conclusion, children, args, cdp);
}

VeritProofPostprocessFinalCallback::VeritProofPostprocessFinalCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_nm(NodeManager::currentNM())
{
  d_cl = d_nm->mkBoundVar("cl", d_nm->stringType());
}

bool VeritProofPostprocessFinalCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn,
    const std::vector<Node>& fa,
    bool& continueUpdate)
{
  // The proof node should not be traversed further
  continueUpdate = false;
  if (pn->getArguments()[2].toString() == "(cl)")
  {
    return false;
  }
  // This case can only occur if the last step is an assumption
  if ((pn->getArguments()[2].end() - pn->getArguments()[2].begin()) <= 1)
  {
    return true;
  }
  // If the proof node has result (false) additional steps have to be added.
  else if (pn->getArguments()[2][1].toString()
           == d_nm->mkConst(false).toString())
  {
    return true;
  }
  return false;
}

// Children:  (P1:C1) ... (Pn:Cn)
// Arguments: (VeritRule::vrule,false,(cl false))
// ---------------------
// Conclusion: (false)
//
// proof rule: vrule
// proof node: (VP1:((false)))
// proof term: (cl false)
// premises: P
// args: ()
//
// proof rule: false
// proof node: (VP2:(not true))
// proof term: (cl (not true))
// premises: ()
// args: ()
//
// proof rule: resolution
// proof node: (false)
// proof term: (cl)
// premises: VP1 VP2
bool VeritProofPostprocessFinalCallback::update(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp,
    bool& continueUpdate)
{
  bool success = true;
  d_nm = NodeManager::currentNM();
  std::vector<Node> new_args = std::vector<Node>();

  Node vp1 = d_nm->mkNode(kind::SEXPR, res);    // ((false))
  Node vp2 = d_nm->mkConst(false).notNode();    // (not true)
  Node res2 = d_nm->mkNode(kind::SEXPR, d_cl);  // (cl)

  VeritRule vrule = static_cast<VeritRule>(std::stoul(args[0].toString()));
  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(vrule)));
  new_args.push_back(vp1);
  // In the special case that false is an assumption, we print false instead of
  // (cl false)
  if (vrule == VeritRule::ASSUME)
  {
    new_args.push_back(res);  // (false)
  }
  else
  {
    new_args.push_back(d_nm->mkNode(kind::SEXPR, d_cl, res));  // (cl false)
  }
  Trace("verit-proof") << "... add veriT step " << vp1 << " / "
                       << d_nm->mkNode(kind::SEXPR, d_cl, res) << " " << vrule
                       << " " << children << " / {}" << std::endl;
  success &= cdp->addStep(
      vp1, PfRule::VERIT_RULE, children, new_args, true, CDPOverwrite::ALWAYS);

  new_args.clear();
  new_args.push_back(
      d_nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::FALSE)));
  new_args.push_back(vp2);
  new_args.push_back(d_nm->mkNode(kind::SEXPR, d_cl, vp2));  // (cl (not false))
  Trace("verit-proof") << "... add veriT step " << vp2 << " / "
                       << d_nm->mkNode(kind::SEXPR, d_cl, vp2) << " "
                       << VeritRule::FALSE << " {} / {}" << std::endl;
  success &= cdp->addStep(
      vp2, PfRule::VERIT_RULE, {}, new_args, true, CDPOverwrite::ALWAYS);

  new_args.clear();
  new_args.push_back(
      d_nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::RESOLUTION)));
  new_args.push_back(res);
  new_args.push_back(res2);
  Trace("verit-proof") << "... add veriT step " << res << " / " << res2 << " "
                       << VeritRule::RESOLUTION << " {" << vp2 << ", " << vp1
                       << " / {}" << std::endl;
  success &= cdp->addStep(res,
                          PfRule::VERIT_RULE,
                          {vp2, vp1},
                          new_args,
                          true,
                          CDPOverwrite::ALWAYS);
  return success;
}

VeritProofPostprocess::VeritProofPostprocess(ProofNodeManager* pnm)
    : d_pnm(pnm),
      d_cb(d_pnm),
      d_updater(d_pnm, d_cb, false, false, false),
      d_fcb(d_pnm),
      d_finalize(d_pnm, d_fcb, false, false, false)
{
}

VeritProofPostprocess::~VeritProofPostprocess() {}

void VeritProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  // Translate proof node
  d_updater.process(pf->getChildren()[0]);

  // In the veriT proof format the final step has to be (cl). However, after the
  // translation it might be (cl false). In that case additional steps are
  // required.
  d_finalize.process(pf->getChildren()[0]);
}

}  // namespace proof

}  // namespace cvc5
