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

#include "expr/proof_ensure_closed.h"
#include "expr/proof_node_algorithm.h"

namespace CVC4 {

namespace proof {

VeritProofPostprocessCallback::VeritProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  d_nm = NodeManager::currentNM();
  d_cl = d_nm->mkBoundVar("cl",d_nm->stringType());
}

void VeritProofPostprocessCallback::initializeUpdate(bool extended)
{
  d_extended = extended;
}

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
  new_args.push_back(res);
  new_args.insert(new_args.end(), args.begin(), args.end());
  Trace("verit-proof") << "... add veriT step " << res << " " << children
                       << " / " << new_args << std::endl;
  return cdp.addStep(res, PfRule::VERIT_RULE, children, new_args);
}

bool VeritProofPostprocessCallback::addVeritStep(Node res,
	       				         VeritRule rule,
						 Node conclusion,
						 const std::vector<Node>& children,
						 const std::vector<Node>& args,
					 	 CDProof& cdp){
  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(d_nm->mkConst<Rational>(static_cast<unsigned>(rule)));
  new_args.push_back(res);
  new_args.push_back(conclusion);
  new_args.insert(new_args.end(),args.begin(),args.end());
  Trace("verit-proof") << "... add veriT step " << res << " " << children
                       << " / " << new_args << std::endl;
  return cdp.addStep(res,PfRule::VERIT_RULE,children,new_args);
}

//Replace a or node (or F1 ... Fn) by (cl F1 ... Fn)
bool VeritProofPostprocessCallback::addVeritStepFromOr(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> clauses;
  clauses.push_back(d_cl);
  clauses.insert(clauses.end(),res.begin(),res.end());
  Node conclusion = d_nm->mkNode(kind::SEXPR,clauses);
  return addVeritStep(res,rule,conclusion,children,args,cdp);
}

// Get a node (cl F)
Node VeritProofPostprocessCallback::mkClNode(std::vector<Node> clauses)
{
  clauses.insert(clauses.begin(), d_cl);
  return d_nm->mkNode(kind::SEXPR, clauses);
}

// Input:
// Proof rule RULE that asserts (cl F1 ... Fn)
// Gives out proof for: (cl (or F1 ... Fn))
// and adds or rule: (cl F1 ... Fn)
//
// proof rule: RULE
// proof node: (VP1:(cl F1 ... Fn))
// proof term: (cl F1 ... Fn)
// premises: children
// args: ()
//
// for i=1 to n:
//
// proof rule: or_neg
// proof node: (VP2i:(cl (or F1 ... Fn) (not Fi)))
// proof term: (cl (or F1 ... Fn) (not Fi))
// premises: ()
// args: ()
//
// proof rule: resolution
// proof node: (VP3:(cl (or F1 ... Fn)^n))
// proof term: (cl (or F1 ... Fn)^n)
// premises: VP1 VP21 ... VPn
// args: ()
//
// proof rule: duplicated_literals
// proof node: (VP4:(cl (or (F1 ... Fn)))
// proof term: (cl (or F1 ... Fn))
// premises: VP3
// args: ()
//
// proof rule: or
// proof node: (or F1 ... Fn)
// proof term: (cl F1 ... Fn)
// premises: VP4
// args: ()
bool VeritProofPostprocessCallback::addClProof(
    Node res,
    VeritRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp)
{
  std::vector<Node> clauses;
  clauses.push_back(d_cl);
  clauses.insert(clauses.end(),res.begin(),res.end());
  Node vp1 = d_nm->mkNode(kind::SEXPR,clauses);
  bool success = addVeritStep(vp1,rule,children,args,*cdp);

  std::vector<Node> vp2Nodes = {vp1};
  std::vector<Node> resNodes;
  for(int i = 0; i < res.end()-res.begin(); i++){
    Node vp2i = d_nm->mkNode(kind::SEXPR,d_cl,res,res[i].notNode());
    success &= addVeritStep(vp2i,VeritRule::OR_NEG,{},{},*cdp);
    vp2Nodes.push_back(vp2i);
    resNodes.push_back(res);
  }
  Node vp3 = mkClNode(resNodes);
  success &= addVeritStep(vp3,VeritRule::RESOLUTION,vp2Nodes,{},*cdp);

  Node vp4 = d_nm->mkNode(kind::SEXPR,d_cl,res);
  return success
      && addVeritStep(vp4,VeritRule::DUPLICATED_LITERALS,{vp3},{},*cdp)
      && addVeritStepFromOr(res,VeritRule::OR,{vp4},{},*cdp);
}

bool VeritProofPostprocessCallback::update(Node res,
                                           PfRule id,
				           const std::vector<std::shared_ptr<ProofNode>>& pf_children,
                                           const std::vector<Node>& args,
                                           CDProof* cdp,
                                           bool& continueUpdate)
{
  std::vector<Node> children;
  for(std::shared_ptr<ProofNode> child:pf_children){
    children.push_back(child->getResult());
  }

  std::vector<Node> new_args = std::vector<Node>();
  // Test print
  //std::cout << id << std::endl;

  Trace("verit-proof") << "- veriT post process callback " << res << " " << id
                       << " " << children << " / " << args << std::endl;

  // If the proof node is the same as the proof term it is left out in the
  // comments.
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
    // In case that F = (or G1 ... Gn):
    //
    // proof rule: assume
    // proof node: (VP:(F'))
    // proof term: F
    // premises: ()
    // args: ()
    //
    // proof rule: or
    // proof node: F
    // proof term: (cl G1 ... Gn)
    // premises: (VP:(F'))
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: assume
    // proof node: (VP:F)
    // proof term: F
    case PfRule::ASSUME:
    {
      if(res.getKind() == kind::OR){
        Node vp = d_nm->mkNode(kind::SEXPR, res);
        return addVeritStep(vp, VeritRule::ASSUME, res, {}, {}, *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp}, {}, *cdp);
      }
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
    // premises: (P:F)
    // args: (F1, ..., Fn)
    //
    // Repeat the following two step for i=1 to n:
    //
    // proof rule: and_neg
    // proof node: (VP2_i:(cl (not (and F1 ... Fn)) Fi))
    // proof term: (cl (not (and F1 ... Fn)) Fi)
    // premises: ()
    // args: ()
    //
    // Let (not (and F1 ... Fn))^i denote the repetition of (not (and F1 ...
    // Fn)) for i times
    //
    // proof rule: resolution
    // proof node: (VP2:(cl (not (and F1 ... Fn))^i F))
    // proof term: (cl (not (and F1 ... Fn))^i F)
    // premises: (VP2_i:(cl (not (and F1 ... Fn)) Fi)) for all i in {1..n},
    //           (VP1:(or (not F1) ... (not Fn) F))
    // args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (VP3:(cl (not (and F1 ... Fn)) F))
    // proof term: (cl (not (and F1 ... Fn)) F)
    // premises: (VP2:(cl (not (and F1 ... Fn))^n F))
    // args: ()
    //
    // proof rule: implies_neg1
    // proof node: (VP4:(cl (=> (and F1 ... Fn) F) (and F1 ... Fn)))
    // proof term: (VP4:(cl (=> (and F1 ... Fn) F) (and F1 ... Fn)))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP5:(cl (=> (and F1 ... Fn) F) F))
    // proof term: (cl (=> (and F1 ... Fn) F) F)
    // premises: (VP3:(cl (not (and F1 ... Fn)) F)) (VP4:(cl (=> (and F1 ... Fn)
    // F) (and F1 ... Fn))) args: ()
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
    // premises: (VP5:(cl (=> (and F1 ... Fn) F) F)) (VP6:(cl (=> (and F1 ...
    // Fn) F) (not F))) args: ()
    //
    // If F = false:
    //
    // proof rule: duplicated_literals
    // proof node: (VP8:(cl (=> (and F1 ... Fn) F)))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: (VP7:(cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F)))
    // args: ()
    //
    // proof rule: implies_simplify
    // proof node: (VP9:(cl (= (=> (and F1 ... Fn) false) (not (and F1 ...
    // Fn))))) proof term: (cl (= (=> (and F1 ... Fn) false) (not (and F1 ...
    // Fn)))) premises: () args: ()
    //
    // proof rule: equiv1
    // proof node: (VP10:(cl (not (=> (and F1 ... Fn) false)) (not (and F1 ...
    // Fn)))) proof term: (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ...
    // Fn))) premises: (VP9:(cl (= (=> (and F1 ... Fn) false) (not (and F1 ...
    // Fn))))) args: ()
    //
    // proof rule: resolution
    // proof node: (or (not (and F1 ... Fn)))
    // proof term: (cl (not (and F1 ... Fn)))
    // premises: (VP8:(cl (=> (and F1 ... Fn) F))) (VP10:(cl (not (=> (and F1
    // ... Fn) false)) (not (and F1 ... Fn)))) args: ()
    //
    // Otherwise:
    //
    // proof rule: duplicated_literals
    // proof node: (or (=> (and F1 ... Fn) F))
    // proof term: (cl (=> (and F1 ... Fn) F))
    // premises: (VP7:(cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F)))
    // args: ()
    case PfRule::SCOPE:
    {
      bool success = true;

      std::vector<Node> negNode;
      for(Node arg:args){
        negNode.push_back(arg.notNode());
      }
      negNode.push_back(children[0]);
      Node andNode;
      if (args.size() != 1)
      {
        andNode = d_nm->mkNode(kind::AND, args);
      }
      else
      {
        andNode = args[0];
      }

      Node vp1 = mkClNode(negNode);
      success &=
          addVeritStep(vp1, VeritRule::ANCHOR_SUBPROOF, children, args, *cdp);

      std::vector<Node> andNegs;
      andNegs.push_back(vp1);
      std::vector<Node> notAnd;
      Node vp2_i;
      for (int i = 0; i < args.size(); i++)
      {
        vp2_i = d_nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), args[i]);
        success &= addVeritStep(vp2_i, VeritRule::AND_NEG, {}, {}, *cdp);
        andNegs.push_back(vp2_i);
        notAnd.push_back(andNode.notNode());
      }
      notAnd.push_back(children[0]);
      Node vp2 = mkClNode(notAnd);
      success &= addVeritStep(vp2, VeritRule::RESOLUTION, andNegs, {}, *cdp);

      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
      success &=
          addVeritStep(vp3, VeritRule::DUPLICATED_LITERALS, {vp2}, {}, *cdp);

      Node vp8 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::IMPLIES, andNode, children[0]));

      Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], andNode);
      success &= addVeritStep(vp4, VeritRule::IMPLIES_NEG1, {}, {}, *cdp);

      Node vp5 = d_nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0]);
      success &= addVeritStep(vp5, VeritRule::RESOLUTION, {vp3, vp4}, {}, *cdp);

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
                         d_nm->mkNode(kind::EQUAL, vp8[1], andNode.negate()));
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
    // Notice that the checker for this rule does not replay the rewrite to ensure
    // correctness, since theory rewriter methods are not static. For example,
    // the quantifiers rewriter involves constructing new bound variables that are
    // not guaranteed to be consistent on each call.
    /*case PfRule::THEORY_REWRITE:{
      return addVeritStep(res,
                          VeritRule::EQ_SIMPLIFY, //TODO
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);
    }*/
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
    // P1 and P2 were printed as (cl F_1 ... F_n) and (cl G_1 ... G_m)
    // respectively. There are however cases were this is wrong.
    //
    // E.g. (P1:(cl F1 ... Fn)) and (P2:(cl(not (or F1 ... Fn)))) cannot be resolved. But P1
    // will have a child (cl (or F1 ... Fn)) in this case and was generated by an
    // application of the or rule. Therefore, this needs to be the child
    //
    //  (cl (or a a b))
    //  --------------- OR
    //  (cl a a b)
    //  ---------- DUPLICATE_LITERALS
    //  (cl a b)                                (cl (not (or a b)))
    //  -----------------------------------------------------------
    //
    //
    //
    // This can only be the case if one of the children is a unit clause (cl F1)
    // and the other is of the form (cl (not (or F1)) ...)
    //
    //
    // If C1 = (cl F1) and C2 = (cl (not(or F1)):
    // P = {child(P1:C1),(P2:C2)}
    //
    // If C1 = (cl (not(or F1))):
    // P = {(P1:C1),child(P2:C2)}
    //
    // Otherwise:
    // P = {(P1:C2),(P2:C2)}
    //
    //
    // If C = false:
    //
    // If C1 = (cl (not(or F1))):
    // P = {(P1:C1),child(P2:C2)}
    //
    // Otherwise:
    // P = {(P1:C2),(P2:C2)}
    //
    //
    // If C = false:
    // PT = {(cl)}
    //
    // Otherwise:
    // PT = {(cl C')}
    //
    // Thus,
    //
    // proof rule: resolution
    // proof term: PT
    // premises: P
    // args: ()
    //
    // In case that C' = (or G1 ... Gn), i.e.  additionally
    //
    // proof rule: or
    // proof term: (cl G1 ... Gn)
    // premises: (VP:F)
    // args: ()
    case PfRule::RESOLUTION:{
      bool success = true;
      // This case can only occur when both of the children are unit clauses.
      if (res == d_nm->mkConst(false))
      {
        if (std::stoi(args[0].toString()) == 1
            && children[0].getKind() == kind::OR
	    && pf_children[0]->getChildren().end()-pf_children[0]->getChildren().begin() > 0)//TODO: Find out if get is necessary
        {
          Node child = pf_children[0].get()->getChildren()[0]->getResult();
          return addVeritStep(res,
                              VeritRule::RESOLUTION,
                              d_nm->mkNode(kind::SEXPR, d_cl),
                              {child, children[1]},
                              {},
                              *cdp);
        }
        if (std::stoi(args[0].toString()) == 0
            && children[1].getKind() == kind::OR
	    && pf_children[1]->getChildren().end()-pf_children[1]->getChildren().begin() > 0)
        {
          Node child = pf_children[1].get()->getChildren()[0]->getResult();
          return addVeritStep(res,
                              VeritRule::RESOLUTION,
                              d_nm->mkNode(kind::SEXPR, d_cl),
                              {children[0], child},
                              {},
                              *cdp);
        }
        return addVeritStep(res,
                            VeritRule::RESOLUTION,
                            d_nm->mkNode(kind::SEXPR, d_cl),
                            children,
                            {},
                            *cdp);
      }

      // Get number of children
      int num_children1 = children[0].end()-children[0].begin();
      int num_pf_children = children[1].end()-children[1].begin();
      if(children[0].isVar()){num_children1 = 1;}
      if(children[1].isVar()){num_pf_children = 1;}

      // The case that C' = (or G1 ... Gn) can only occur if the result if C is
      // a unit clause and has kind OR
      if (res.getKind() == kind::OR
          && ((num_children1 == 1 && num_pf_children == 2)
              || (num_children1 == 2 && num_pf_children == 1)))
      {
        Node vp = d_nm->mkNode(kind::SEXPR, d_cl, res);
        // In some cases the child of the child has to be taken
        if (children[0] == args[1] && children[0].getKind() == kind::OR && pf_children[0]->getChildren().end()-pf_children[0]->getChildren().begin() > 0)
        {
	  Node child = pf_children[0].get()->getChildren()[0]->getResult();
          success &= addVeritStep(vp,
                                  VeritRule::RESOLUTION,
                                  d_nm->mkNode(kind::SEXPR, d_cl, res),
                                  {child, children[1]},
                                  {},
                                  *cdp);
        }
        else if (children[1] == args[1] && children[1].getKind() == kind::OR && pf_children[1]->getChildren().end()-pf_children[1]->getChildren().begin() > 0)
        {
	  Node child = pf_children[1].get()->getChildren()[0]->getResult();
          success &= addVeritStep(vp,
                                  VeritRule::RESOLUTION,
                                  d_nm->mkNode(kind::SEXPR, d_cl, res),
                                  {children[0], child},
                                  {},
                                  *cdp);
        }
        else
        {
          success &= addVeritStep(vp,
                                  VeritRule::RESOLUTION,
                                  d_nm->mkNode(kind::SEXPR, d_cl, res),
                                  children,
                                  {},
                                  *cdp);
        }
        success &= addVeritStepFromOr(res, VeritRule::OR, {vp}, {}, *cdp);
        return success;
      }

      // In some cases the child of the child has to be taken
      if (children[0] == args[1])
      {
	Node child = pf_children[0].get()->getChildren()[0]->getResult();
        success &= addVeritStep(res,
                                VeritRule::RESOLUTION,
                                d_nm->mkNode(kind::SEXPR, d_cl, res),
                                {child, children[1]},
                                {},
                                *cdp);
      }
      if (children[1] == args[1])
      {
	Node child = pf_children[1].get()->getChildren()[0]->getResult();
        success &= addVeritStep(res,
                                VeritRule::RESOLUTION,
                                d_nm->mkNode(kind::SEXPR, d_cl, res),
                                {children[0], child},
                                {},
                                *cdp);
      }
      return success
             & addVeritStepFromOr(
                 res, VeritRule::RESOLUTION, children, {}, *cdp);
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
    //   - for each i > 1, let C_i' = C_{i-1} <>_{L_{i-1}, id_{i-1}} C_i'
    //   The result of the chain resolution is C = C_n'
    //
    // proof rule: resolution
    // proof term: (C_m')
    // premises: (P1:(or F_{1,1} ... F_{1,n1}), ..., Pm:(or F_{m,1} ...
    // F_{m,nm})) args: ()
    //
    //
    // If the result is only one clause, i.e. (and F1 F2) it should be
    // translated to (cl (and F1 F2)) and in case that its kind is OR and
    // additonal or step should be added, i.e. (or F1) is translated to (cl (or
    // F1)) this is translated to (cl F1). If the result consists of more then
    // one clause i.e. (or (and F1 F2) F3) it should be (cl (and F1 F2) F3)
    //
    // If a unit clause is resolved against another clause a problem might
    // occur, consider e.g. t1: (cl (or a (not a))) t2: (cl a (not a)) :rule or
    // :premises t1 t3: (cl (not (or a (not a)))) t4: (cl) :rule resolution
    // :premises t2 t3
    //
    // In this case the t4 needs to get the right premises
    case PfRule::CHAIN_RESOLUTION: //TODO: This rule changed, also consider order, special case
    {
      std::vector<Node> new_children;
      for (int i = 0; i < children.size(); i++)
      {
        if (args[2 * i + 1] == children[i])
        {
          new_children.push_back(pf_children[i].get()->getChildren()[0]->getResult());
        }
        else
        {
          new_children.push_back(children[i]);
        }
      }
      if (res == d_nm->mkConst(false))
      {
         return addVeritStep(res, VeritRule::RESOLUTION, d_nm->mkNode(kind::SEXPR,d_cl), new_children, {}, *cdp);
      }
      else{
         return addVeritStep(res, VeritRule::RESOLUTION, d_nm->mkNode(kind::SEXPR,d_cl,res), new_children, {}, *cdp);
      }
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
    //  If C1 = (or (or F1 ... Fn) ... (or F1 ... Fn)) and C2 = (or F1 ... Fn)
    //  then:
    //
    //  proof rule: duplicated_literals
    //  proof node: (VP:(cl C2))
    //  proof term: (cl (or F1 ... Fn))
    //  premises: (P:C1)
    //  args: ()
    //
    //  proof rule: or
    //  proof node: C2
    //  proof term: (cl F1 ... Fn)
    //  premises: (VP:(cl C2))
    //  args: ()
    //
    //  Otherwise, let C2 = (or F1 ... Fn)
    //
    //  proof rule: duplicated_literals
    //  proof node: C2
    //  proof term: (cl F1 ... Fn)
    //  premises: (P:C1)
    //  args: ()
    //
    //  TODO: addClProof
    case PfRule::FACTORING:
    {
      bool special_case = true;
      for (auto i = children[0].begin(); i != children[0].end(); i++)
      {
        if (*i != res)
        {
          special_case = false;
        }
      }
      if (special_case)
      {
        Node vp = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return addVeritStepFromOr(
                   vp, VeritRule::DUPLICATED_LITERALS, children, {}, *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp}, {}, *cdp);
      }
      return addVeritStepFromOr(
          res, VeritRule::DUPLICATED_LITERALS, children, {}, *cdp);
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
    // TODO: ASK HANIEL IF THIS SHOULD BE DONE, MIGHT NOT MAKE SENSE TO STORE
    // THIS INFORMATION Also should this be tautolgy + resolution style?
    //
    // This rule is skipped in VeritProofPostprocess::processInternal when in
    // verit proof-format-mode. In verit-extended mode:
    //
    // Let C2 = (or F1 ... Fn)
    //
    // proof rule: reordering
    // proof node: C2
    // proof term: (cl F1 ... Fn)
    // premises: ()
    // args: ()
    case PfRule::REORDERING:
    {
      if (d_extended)//TODO: not necessary
      {
        return addVeritStepFromOr(res, VeritRule::REORDER, children, {}, *cdp);
      }
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
    // proof node: (cl F (not F))
    // proof term: (cl F (not F))
    // premises: (VP1:(cl (not (not (not F))) F)) (VP2:(cl (not (not (not (not
    // F)))) (not F)) args: ()
    //
    // Use addClProof to first prove (cl (or (not F1) F2)) followed by (cl (not F1) F2)
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
             && addClProof(res, VeritRule::RESOLUTION, {vp1, vp2}, {}, cdp);
    }
    // ======== Equality resolution
    // Children: (P1:F1, P2:(= F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    // If P1 is of the form (or G1 ... Gn) then the set of premises P =
    // {(VP1:(cl (not (= F1 F2)) (not F1) (F2))) (Child(P1:F1)) (P2:(= F1 F2))}
    // otherwise P = {(VP1:(cl (not (= F1 F2)) (not F1) (F2))) (P1:F1) (P2:(= F1
    // F2))}
    //
    // proof rule: equiv_pos2
    // proof node: (VP1:(cl (not (= F1 F2)) (not F1) (F2)))
    // proof term: (cl (not (= F1 F2)) (not F1) (F2))
    // premises: ()
    // args: ()
    //
    // In case that F2 = (or G1 ... Gn)
    //
    // proof rule: resolution
    // proof node: (VP2:(cl F2))
    // proof term: (cl F2)
    // premises: P
    // args: ()
    //
    // proof rule: or
    // proof node: F2
    // proof term: (cl G1 ... Gn)
    // premises: (VP2:(cl F2))
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: P
    // args: ()
    case PfRule::EQ_RESOLVE:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[1].notNode(), children[0].notNode(), res);
      bool success = addVeritStep(vp1, VeritRule::EQUIV_POS2, {}, {}, *cdp);

      std::vector<Node> new_children;

      if (children[0].getKind() == kind::OR && children[0] == children[1][0] && pf_children[0]->getChildren().end()-pf_children[0]->getChildren().begin() > 0)
      {//TODO: Add last bit to all?
	Node child = pf_children[0].get()->getChildren()[0]->getResult();
	new_children = {vp1, child, children[1]};
      }
      else
      {
        new_children = {vp1, children[0], children[1]};
      }

      if(res.getKind() == kind::OR){
        Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return success
               && addVeritStep(vp2,
                               VeritRule::RESOLUTION,
                               new_children,
                               {},
                               *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp2}, {}, *cdp);
      }
      else{
        return success
               && addVeritStep(res,
                               VeritRule::RESOLUTION,
                               d_nm->mkNode(kind::SEXPR, d_cl, res),
                               new_children,
                               {},
                               *cdp);
      }
    }
    // ======== Modus ponens
    // Children: (P1:F1, P2:(=> F1 F2))
    // Arguments: none
    // ---------------------
    // Conclusion: (F2)
    //
    // proof rule: implies
    // proof term: (VP1:(cl (not F1) F2))
    // proof term: (cl (not F1) F2)
    // premises: (P2:(=> F1 F2))
    // args: ()
    //
    // If P1 is of the form (or G1 ... Gn) then the set of premises P =
    // {(Child(P1:F1)) (VP1:(cl (not F1) F2))} otherwise P = {(VP1:(cl (not (=
    // F1 F2)) (not F1) (F2))) (Child(P1:F1)) (P2:(= F1 F2))}
    //
    // In case that F2 = (or G1 ... Gn)
    //
    // proof rule: resolution
    // proof node: (VP2:(cl F2))
    // proof term: (cl F2)
    // premises: (P1:F1) (VP1:(cl (not F1) F2))
    // args: ()
    //
    // proof rule: or
    // proof node: F2
    // proof term: (cl G1 ... Gn)
    // premises: (VP2:(cl F))
    // args: ()
    //
    // Otherwise
    //
    // proof rule: resolution
    // proof node: F2
    // proof term: (cl F2)
    // premises: (P1:F1) (VP1:(cl (not F1) F2))
    // args: ()
    case PfRule::MODUS_PONENS:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].negate(), res);
      std::vector<Node> new_children;

      if (children[0].getKind() == kind::OR && children[0] == children[1][0])
      {
	Node child = pf_children[0].get()->getChildren()[0]->getResult(); //TODO
        new_children = {vp1, child};
      }
      else
      {
        new_children = {vp1, children[0]};
      }

      bool success =
          addVeritStep(vp1, VeritRule::IMPLIES, {children[1]}, {}, *cdp);

      if(res.getKind() == kind::OR){
        Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return success
               && addVeritStep(vp2,
                               VeritRule::RESOLUTION,
                               new_children,
                               {},
                               *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp2}, {}, *cdp);
      }
      else{
        return success
               && addVeritStep(res,
                               VeritRule::RESOLUTION,
                               d_nm->mkNode(kind::SEXPR, d_cl, res),
                               new_children,
                               {},
                               *cdp);
      }
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
    // premises:
    // args: ()
    //
    // In case that F = (or G1 ... Gn)
    //
    // proof rule: resolution
    // proof node: (VP2:(cl F))
    // proof term: (cl F)
    // premises: (VP1:(cl (not (not (not F))) F)) (P:(not (not F)))
    // args: ()
    //
    // proof rule: or
    // proof node: F
    // proof term: (cl G1 ... Gn)
    // premises: (VP2:(cl F))
    // args: ()
    //
    // Otherwise
    //
    // proof rule: resolution
    // proof node: F
    // proof term: (cl F)
    // premises: (VP1:(cl (not (not (not F))) F)) (P:(not (not F)))
    // args: ()
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].negate(), res);

      bool success = addVeritStep(vp1, VeritRule::NOT_NOT, {}, {}, *cdp);

      if(res.getKind() == kind::OR){
        Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return success
               && addVeritStep(
                   vp2, VeritRule::RESOLUTION, {vp1, children[0]}, {}, *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp2}, {}, *cdp);
      }
      else{
        return success
               && addVeritStep(res,
                               VeritRule::RESOLUTION,
                               d_nm->mkNode(kind::SEXPR, d_cl, res),
                               {vp1, children[0]},
                               {},
                               *cdp);
      }
    }
    // ======== Contradiction
    // Children: (P1:F P2:(not F))
    // Arguments: ()
    // ---------------------
    // Conclusion: false
    //
    // If F = (or G1 ... Gn) then:
    //
    // proof rule: resolution
    // proof node: false
    // proof term: (cl)
    // premises: (Child(P1:F)) (P2:(not F))
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: resolution
    // proof node: false
    // proof term: (cl)
    // premises: (P1:F) (P2:(not F))
    // args: ()
    case PfRule::CONTRA:
    {
      if (children[0].getKind() == kind::OR)
      {
	Node child = pf_children[0].get()->getChildren()[0]->getResult();
        return addVeritStep(res,
                            VeritRule::RESOLUTION,
                            d_nm->mkNode(kind::SEXPR, d_cl),
                            {child, children[1]},
                            {},
                            *cdp);
      }
      return addVeritStep(res, VeritRule::RESOLUTION, d_nm->mkNode(kind::SEXPR,d_cl), children, {}, *cdp);
    }
    // ======== And elimination
    // Children: (P:(and F1 ... Fn))
    // Arguments: (i)
    // ---------------------
    // Conclusion: (Fi)
    //
    // In case that Fi = (or G1 ... Gn)
    //
    // proof rule: and
    // proof node: (VP:(cl Fi))
    // proof term: (cl Fi)
    // premises: (P:(and F1 ... Fn))
    // args: ()
    //
    // proof rule: or
    // proof node: Fi
    // proof term: (cl G1 ... Gn)
    // premises: (VP:(cl Fi))
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: and
    // proof node: (VP:(cl Fi))
    // proof term: Fi
    // premises: (P:(and F1 ... Fn))
    // args: ()
    case PfRule::AND_ELIM:
    {
      if(res.getKind() == kind::OR){
        Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return addVeritStep(vp1, VeritRule::AND, children, {}, *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp1}, {}, *cdp);
      }
      else{
        return addVeritStep(res,
                            VeritRule::AND,
                            d_nm->mkNode(kind::SEXPR, d_cl, res),
                            children,
                            {},
                            *cdp);
      }
    }
    // ======== And introduction
    // Children: (P1:F1 ... Pn:Fn))
    // Arguments: ()
    // ---------------------
    // Conclusion: (and P1 ... Pn)
    //
    // proof rule: and_neg
    // proof node: (VP1:(cl (and F1 ... Fn) (not F1) ... (not Fn)))
    // proof term: (cl (and F1 ... Fn) (not F1) ... (not Fn))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (and P1 ... Pn)
    // proof term: (cl (and P1 ... Pn))
    // premises: (P1:F1 ... Pn:Fn) (VP1:(cl (and F1 ... Fn) (not F1) ... (not
    // Fn))) args: ()
    case PfRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes;
      neg_Nodes.push_back(d_cl);
      neg_Nodes.push_back(d_nm->mkNode(kind::AND, children));
      for (int i = 0; i < children.size(); i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = d_nm->mkNode(kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children;
      new_children.insert(new_children.end(),children.begin(),children.end());
      new_children.push_back(vp1);

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
    // premises: (P:(not (or F1 ... Fn)))
    // args: ()
    case PfRule::NOT_OR_ELIM:
    {
      return addVeritStep(res, VeritRule::NOT_OR, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== Implication elimination
    // Children: (P:(=> F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // Use addClProof to first prove (cl (or (not F1) F2)) followed by (cl (not F1) F2)
    case PfRule::IMPLIES_ELIM:
    {
      return addClProof(res, VeritRule::IMPLIES, children, {}, cdp);
    }
    // ======== Not Implication elimination version 1
    // Children: (P:(not (=> F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (F1)
    //
    // In case that Fi = (or G1 ... Gn)
    //
    // proof rule: not_implies1
    // proof node: (VP:(cl F1))
    // proof term: (cl F1)
    // premises: (P:(not (=> F1 F2)))
    // args: ()
    //
    // proof rule: or
    // proof node: (F1)
    // proof term: (cl G1 ... Gn)
    // premises: (VP:(cl F))
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: not_implies1
    // proof node: (VP:F1)
    // proof term: (cl F1)
    // premises: (P:(not (=> F1 F2)))
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM1:
    {
      if(res.getKind() == kind::OR){
        Node vp = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return addVeritStep(vp,
                            VeritRule::NOT_IMPLIES1,
                            d_nm->mkNode(kind::SEXPR, d_cl, res),
                            children,
                            {},
                            *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp}, {}, *cdp);
      }
      else{
        return addVeritStep(res,
                            VeritRule::NOT_IMPLIES1,
                            d_nm->mkNode(kind::SEXPR, d_cl, res),
                            children,
                            {},
                            *cdp);
      }
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
    // premises: (P:(not (=> F1 F2)))
    // args: ()
    case PfRule::NOT_IMPLIES_ELIM2:
    {
      return addVeritStep(res, VeritRule::NOT_IMPLIES2, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== Equivalence elimination version 1
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // Use addClProof to first prove (cl (or (not F1) F2)) followed by (cl (not F1) F2)
    case PfRule::EQUIV_ELIM1:
    {
      return addClProof(res, VeritRule::EQUIV1, children, {}, cdp);
    }
    // ======== Equivalence elimination version 2
    // Children: (P:(= F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // Use addClProof to first prove (cl (or F1 (not F2))) followed by (cl F1 (not F2))
    case PfRule::EQUIV_ELIM2:
    {
      return addClProof(res, VeritRule::EQUIV2, children, {}, cdp);
    }
    // ======== Not Equivalence elimination version 1
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // Use addClProof to first prove (cl (or F1 F2)) followed by (cl F1 F2)
    case PfRule::NOT_EQUIV_ELIM1:
    {
      return addClProof(res, VeritRule::NOT_EQUIV1, children, {}, cdp);
    }
    // ======== Not Equivalence elimination version 2
    // Children: (P:(not (= F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) (not F2))
    //
    // Use addClProof to first prove (cl (or (not F1) (not F2))) followed by (cl (not F1) (not F2))
    case PfRule::NOT_EQUIV_ELIM2:
    {
      return addClProof(res, VeritRule::NOT_EQUIV2, children, {}, cdp);
    }
    // ======== XOR elimination version 1
    // Children: (P:(xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 F2)
    //
    // Use addClProof to first prove (cl (or F1 F2)) followed by (cl F1 F2)
    case PfRule::XOR_ELIM1:
    {
      return addClProof(res, VeritRule::XOR1, children, {}, cdp);
    }
    // ======== XOR elimination version 2
    // Children: (P:(not (xor F1 F2))))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // Use addClProof to first prove (cl (or F1 (not F2))) followed by (cl F1 (not F2))
    case PfRule::XOR_ELIM2:
    {
      return addClProof(res, VeritRule::XOR2, children, {}, cdp);
    }
    // ======== Not XOR elimination version 1
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or F1 (not F2))
    //
    // Use addClProof to first prove (cl (or F1 (not F2))) followed by (cl F1 (not F2))
    case PfRule::NOT_XOR_ELIM1:
    {
      return addClProof(res, VeritRule::NOT_XOR1, children, {}, cdp);
    }
    // ======== Not XOR elimination version 2
    // Children: (P:(not (xor F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not F1) F2)
    //
    // Use addClProof to first prove (cl (or (not F1) F2)) followed by (cl (not F1) F2)
    case PfRule::NOT_XOR_ELIM2:
    {
      return addClProof(res, VeritRule::NOT_XOR2, children, {}, cdp);
    }
    // ======== ITE elimination version 1
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) F1)
    //
    // Use addClProof to first prove (cl (or (not C) F1)) followed by (cl (not C) F1)
    case PfRule::ITE_ELIM1:
    {
      return addClProof(res, VeritRule::ITE2, children, {}, cdp);
    }
    // ======== ITE elimination version 2
    // Children: (P:(ite C F1 F2))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C F2)
    //
    // Use addClProof to first prove (cl (or C F2)) followed by (cl C F2)
    case PfRule::ITE_ELIM2:
    {
      return addClProof(res, VeritRule::ITE1, children, {}, cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or (not C) (not F1))
    //
    // Use addClProof to first prove (cl (or (not C) (not F1))) followed by (cl (not C) (not F1))
    case PfRule::NOT_ITE_ELIM1:
    {
      return addClProof(res, VeritRule::NOT_ITE2, children, {}, cdp);
    }
    // ======== Not ITE elimination version 1
    // Children: (P:(not (ite C F1 F2)))
    // Arguments: ()
    // ---------------------
    // Conclusion: (or C (not F2))
    //
    // Use addClProof to first prove (cl (or C (not F2))) followed by (cl C (not F2))
    case PfRule::NOT_ITE_ELIM2:
    {
      return addClProof(res, VeritRule::NOT_ITE1, children, {}, cdp);
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
    // premises: (P:(not (and F1 ... Fn))
    // args: ()
    case PfRule::NOT_AND:
    {
      return addClProof(res,VeritRule::NOT_AND,children,args,cdp);
    }

    //================================================= CNF rules
    // ======== CNF And Pos
    // Children: ()
    // Arguments: ((and F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (not (and F1 ... Fn)) Fi)
    //
    // Use addClProof to first prove (cl (or (not (and F1 ... Fn)) Fi)) followed by (cl (not (and F1 ... Fn)) Fi)
    case PfRule::CNF_AND_POS:
    {
      return addClProof(res,VeritRule::AND_POS, {}, {},cdp);
    }
    // ======== CNF And Neg
    // Children: ()
    // Arguments: ((and F1 ... Fn))
    // ---------------------
    // Conclusion: (or (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // Use addClProof to first prove (cl (or (and F1 ... Fn) (not F1) ... (not Fn))) followed by (cl (and F1 ... Fn) (not F1) ... (not Fn))
    case PfRule::CNF_AND_NEG:
    {
      return addClProof(res,VeritRule::AND_NEG,{},{},cdp);
    }
    // ======== CNF Or Pos
    // Children: ()
    // Arguments: ((or F1 ... Fn))
    // ---------------------
    // Conclusion: (or (not (or F1 ... Fn)) F1 ... Fn)
    //
    // Use addClProof to first prove (cl (or (and F1 ... Fn) (not F1) ... (not Fn))) followed by (cl (and F1 ... Fn) (not F1) ... (not Fn))
    case PfRule::CNF_OR_POS:
    {
      addClProof(res,VeritRule::OR_POS,{},{},cdp);
    }
    // ======== CNF Or Neg
    // Children: ()
    // Arguments: ((or F1 ... Fn), i)
    // ---------------------
    // Conclusion: (or (or F1 ... Fn) (not Fi))
    //
    // Use addClProof to first prove (cl (or (or F1 ... Fn) (not Fi))) followed by (cl (or F1 ... Fn) (not Fi))
    case PfRule::CNF_OR_NEG:
    {
      return addClProof(res, VeritRule::OR_NEG, {}, {}, cdp);
    }
    // ======== CNF Implies Pos
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (not (implies F1 F2)) (not F1) F2)
    //
    // Use addClProof to first prove (cl (or (not (implies F1 F2)) (not F1) F2)) followed by (cl (or F1 ... Fn) (not Fi))
    case PfRule::CNF_IMPLIES_POS:
    {
      return addClProof(res,VeritRule::IMPLIES_POS,{},{},cdp);
    }
    // ======== CNF Implies Neg version 1
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) F1)
    //
    // Use addClProof to first prove (cl (or (implies F1 F2) F1)) followed by (cl (implies F1 F2) F1)
    case PfRule::CNF_IMPLIES_NEG1:
    {
      return addClProof(res,VeritRule::IMPLIES_NEG1,{},{},cdp);
    }
    // ======== CNF Implies Neg version 2
    // Children: ()
    // Arguments: ((implies F1 F2))
    // ---------------------
    // Conclusion: (or (implies F1 F2) (not F2))
    //
    // Use addClProof to first prove (cl (or (implies F1 F2) (not F2))) followed by (cl (implies F1 F2) (not F2))
    case PfRule::CNF_IMPLIES_NEG2:
    {
      return addClProof(res,VeritRule::IMPLIES_NEG2,{},{},cdp);
    }
    // ======== CNF Equiv Pos version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) (not F1) F2)
    //
    // Use addClProof to first prove (cl (or (not (= F1 F2)) (not F1) F2)) followed by (cl (not (= F1 F2)) (not F1) F2)
    case PfRule::CNF_EQUIV_POS1:
    {
      return addClProof(res,VeritRule::EQUIV_POS2,{},{},cdp);
    }
    // ======== CNF Equiv Pos version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (not (= F1 F2)) F1 (not F2))
    //
    // Use addClProof to first prove (cl (or (not (= F1 F2)) F1 (not F2))) followed by (cl (not (= F1 F2)) F1 (not F2))
    case PfRule::CNF_EQUIV_POS2:
    {
      return addClProof(res,VeritRule::EQUIV_POS1,{},{},cdp);
    }
    // ======== CNF Equiv Neg version 1
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) F1 F2)
    //
    // Use addClProof to first prove (cl (or (= F1 F2) F1 F2)) followed by (cl (= F1 F2) F1 F2)
    case PfRule::CNF_EQUIV_NEG1:
    {
      return addClProof(res,VeritRule::EQUIV_NEG2,{},{},cdp);
    }
    // ======== CNF Equiv Neg version 2
    // Children: ()
    // Arguments: ((= F1 F2))
    // ---------------------
    // Conclusion: (or (= F1 F2) (not F1) (not F2))
    //
    // Use addClProof to first prove (cl (or (= F1 F2) (not F1) (not F2))) followed by (cl (= F1 F2) (not F1) (not F2))
    case PfRule::CNF_EQUIV_NEG2:
    {
      return addClProof(res,VeritRule::EQUIV_NEG1,{},{},cdp);
    }
    // ======== CNF Xor Pos version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) F1 F2)
    //
    // Use addClProof to first prove (cl (or (not (xor F1 F2)) F1 F2)) followed by (cl (not (xor F1 F2)) F1 F2)
    case PfRule::CNF_XOR_POS1:
    {
      return addClProof(res,VeritRule::XOR_POS1,{},{},cdp);
    }
    // ======== CNF Xor Pos version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (not (xor F1 F2)) (not F1) (not F2))
    //
    // Use addClProof to first prove (cl (or (not (xor F1 F2)) (not F1) (not F2))) followed by (cl (not (xor F1 F2)) (not F1) (not F2))
    case PfRule::CNF_XOR_POS2:
    {
      return addClProof(res,VeritRule::XOR_POS2,{},{},cdp);
    }
    // ======== CNF Xor Neg version 1
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) (not F1) F2)
    //
    // Use addClProof to first prove (cl (or (xor F1 F2) (not F1) F2)) followed by (cl (xor F1 F2) (not F1) F2)
    case PfRule::CNF_XOR_NEG1:
    {
      return addClProof(res,VeritRule::XOR_NEG2,{},{},cdp);
    }
    // ======== CNF Xor Neg version 2
    // Children: ()
    // Arguments: ((xor F1 F2))
    // ---------------------
    // Conclusion: (or (xor F1 F2) F1 (not F2))
    //
    // Use addClProof to first prove (cl (or (xor F1 F2) F1 (not F2))) followed by (cl (xor F1 F2) F1 (not F2))
    case PfRule::CNF_XOR_NEG2:
    {
      return addClProof(res,VeritRule::XOR_NEG1,{},{},cdp);
    }
    // ======== CNF ITE Pos version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) (not C) F1)
    //
    // Use addClProof to first prove (cl (or (not (ite C F1 F2)) (not C) F1)) followed by (cl (not (ite C F1 F2)) (not C) F1)
    case PfRule::CNF_ITE_POS1:
    {
      return addClProof(res,VeritRule::ITE_POS2,{},{},cdp);
    }
    // ======== CNF ITE Pos version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (not (ite C F1 F2)) C F2)
    //
    // Use addClProof to first prove (cl (or (not (ite C F1 F2)) C F2)) followed by (cl (not (ite C F1 F2)) C F2)
    case PfRule::CNF_ITE_POS2:
    {
      return addClProof(res,VeritRule::ITE_POS1,{},{},cdp);
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
    // proof term: (cl (not (ite C F1 F2)) C F2)
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
    // proof term: (cl (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2)
    // premises: (VP1:(not (ite C F1 F2)) C F2) (VP2:(not (ite C F1 F2)) (not C)
    // F1) args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (cl (not (ite C F1 F2)) F1 F2)
    // proof term: (cl (not (ite C F1 F2)) F1 F2)
    // premises: (VP3:(or (not (ite C F1 F2)) F1 (not (ite C F1 F2)) F2))
    // args: ()
    //
    // Then use addClProof to first prove (cl (or (not (ite C F1 F2)) F1 F2)) and then  (cl (not (ite C F1 F2)) F1 F2)
    case PfRule::CNF_ITE_POS3:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].negate(), res[1]);
      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_POS1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_POS2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
	     && addClProof(res, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, cdp);
    }
    // ======== CNF ITE Neg version 1
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not C) (not F1))
    //
    // Use addClProof to first prove (cl (or (ite C F1 F2) (not C) (not F1))) followed by (cl (ite C F1 F2) (not C) (not F1))
    case PfRule::CNF_ITE_NEG1:
    {
      return addClProof(res, VeritRule::ITE_NEG2, children, {}, cdp);
    }
    // ======== CNF ITE Neg version 2
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) C (not F2))
    //
    // Use addClProof to first prove (cl (or (ite C F1 F2) C (not F2))) followed by (cl (ite C F1 F2) C (not F2))
    case PfRule::CNF_ITE_NEG2:
    {
      return addClProof(res, VeritRule::ITE_NEG1, children, {}, cdp);
    }
    // ======== CNF ITE Neg version 3
    // Children: ()
    // Arguments: ((ite C F1 F2))
    // ---------------------
    // Conclusion: (or (ite C F1 F2) (not F1) (not F2))
    //
    // proof rule: ite_neg1
    // proof node: (VP1:(cl (ite C F1 F2) C (not F2)))
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: ()
    // args: ()
    //
    // proof rule: ite_neg2
    // proof node: (VP2:(cl (ite C F1 F2) (not C) (not F1)))
    // proof term: (cl (ite C F1 F2) (not C) (not F1))
    // premises: ()
    // args: ()
    //
    // proof rule: resolution
    // proof node: (VP3:(cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
    // proof term: (cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1))
    // premises: ((VP1:(cl (ite C F1 F2) C (not F2))) (VP2:(cl (ite C F1 F2)
    // (not C) (not F1)))) args: ()
    //
    // proof rule: duplicated_literals
    // proof node: (cl (ite C F1 F2) C (not F2))
    // proof term: (cl (ite C F1 F2) C (not F2))
    // premises: (VP3:(or (ite C F1 F2) (not F2) (ite C F1 F2) (not F1)))
    // args: ()
    //
    // Then use addClProof to first prove (cl (or (ite C F1 F2) C (not F2))) and then (cl (ite C F1 F2) C (not F2))
    case PfRule::CNF_ITE_NEG3:
    {
      Node vp1 = d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0], res[2]);
      Node vp2 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], args[0][0].negate(), res[1]);
      Node vp3 =
          d_nm->mkNode(kind::SEXPR, d_cl, res[0], res[1], res[0], res[2]);

      return addVeritStep(vp1, VeritRule::ITE_NEG1, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::ITE_NEG2, {}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::RESOLUTION, {vp1, vp2}, {}, *cdp)
             && addClProof(res, VeritRule::DUPLICATED_LITERALS, {vp3}, {}, cdp);
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
      return addVeritStep(res, VeritRule::REFL, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
    }
    // ======== Symmetric
    // Children: (P:(= t1 t2)) or (P:(not (= t1 t2)))
    // Arguments: none
    // -----------------------
    // Conclusion: (= t2 t1) or (not (= t2 t1))
    //
    // This rule is skipped in VeritProofPostprocess::processInternal when in
    // verit proof-format-mode. In verit-extended mode:
    //
    // proof rule: symm
    // proof node: (= t2 t1) or (not (= t2 t1))
    // proof term: (cl (= t2 t1)) or (cl (not (= t2 t1)))
    // premises: ((P:(= t1 t2)) or (P:(not (= t1 t2))
    // args: ()
    case PfRule::SYMM:  // TODO:TEST
    {
      // if (d_extended)
      //{
      return addVeritStep(res,
                          VeritRule::REFL,
                          d_nm->mkNode(kind::SEXPR, d_cl, res),
                          children,
                          {},
                          *cdp);

      //}
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
    // premises: (P1:(= t1 t2), ..., Pn:(= t{n-1} tn))
    // args: ()
    case PfRule::TRANS:
    {
      return addVeritStep(res, VeritRule::TRANS, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
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
    // proof node: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
    // proof term: (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))
    // premises: (P1:(= t1 s1), ..., Pn:(= tn sn))
    // args: ()
    case PfRule::CONG:
    {
      return addVeritStep(res, VeritRule::CONG, d_nm->mkNode(kind::SEXPR,d_cl,res), children, {}, *cdp);
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
    // premises: (VP1:(cl (= (= F true) F)))
    // args: ()
    //
    // proof rule: resolution
    // proof node: (= F true)
    // proof term: (cl (= F true))
    // premises: (P:F) (VP2:(cl (= F true) (not F)))
    // args: ()
    case PfRule::TRUE_INTRO:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0].negate());
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
    // proof rule: equiv2
    // proof node: (VP2:(cl (not (= F true)) F))
    // proof term: (cl (not (= F true)) F)
    // premises: (VP1:(cl (= (= F true) F)))
    // args: ()
    //
    // If F = (or G1 ... Gn) then:
    //
    // proof rule: resolution
    // proof node: (VP3:(cl F))
    // proof term: (cl F)
    // premises: (VP2:(or (not (= F true)) F)) (P:(= F true))
    // args: ()
    //
    // proof rule: or
    // proof node: F
    // proof term: (cl G1 ... Gn)
    // premises:
    // args: ()
    //
    // Otherwise:
    //
    // proof rule: resolution
    // proof node: (cl F)
    // proof term: (F)
    // premises: (VP2:(or (not (= F true)) F)) (P:(= F true))
    // args: ()
    //
    case PfRule::TRUE_ELIM:
    {
      bool success = true;
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].negate(), res);
      success &= addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
                 && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp);
      if (res.getKind() == kind::OR)
      {
        Node vp3 = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return success
               && addVeritStep(
                   vp3, VeritRule::RESOLUTION, {vp2, children[0]}, {}, *cdp)
               && addVeritStepFromOr(res, VeritRule::OR, {vp3}, {}, *cdp);
      }
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
    // premises: (VP1:(cl (= (= F false) (not F))))
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
    // premises: (VP2:(cl (= F false) (not (not F)))) (VP3:(cl (not (not (not
    // F))) F)) args: ()
    //
    // proof rule: resolution
    // proof node: (= F false)
    // proof term: (cl (= F false))
    // premises: (VP4:(cl (= F false) F)) (P:(not F))
    // args: ()
    case PfRule::FALSE_INTRO:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, res, children[0]));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0].negate());
      Node vp3 = d_nm->mkNode(
          kind::SEXPR, d_cl, children[0].negate().negate(), children[0][0]);
      Node vp4 = d_nm->mkNode(kind::SEXPR, d_cl, res, children[0][0]);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV2, {vp1}, {}, *cdp)
             && addVeritStep(vp3, VeritRule::NOT_NOT, {}, {}, *cdp)
             && addVeritStep(vp4, VeritRule::RESOLUTION, {vp2, vp3}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp4},
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
    // premises: (VP1:(cl (= (= F false) (not F))))
    // args: ()
    //
    // proof rule: resolution
    // proof node: (not F)
    // proof term: (cl (not F))
    // premises: (VP1:(cl (= (= F false) (not F)))) (P:(= F false))
    // args: ()
    case PfRule::FALSE_ELIM:
    {
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::EQUAL, children[0], res));
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].negate(), res);

      return addVeritStep(vp1, VeritRule::EQUIV_SIMPLIFY, {}, {}, *cdp)
             && addVeritStep(vp2, VeritRule::EQUIV1, {vp1}, {}, *cdp)
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp1, children[0]},
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
    // premises: (VP1:(cl (or (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma)))
    // args: ()
    //
    // If F*sigma = (or G1 ... Gn)
    //
    // proof rule: resolution
    // proof node: (VP3:(cl F*sigma))
    // proof term: (cl F*sigma)
    // premises: (VP2:(cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma))
    // (P:(forall ((x1 T1) ... (xn Tn)) F)) args: ()
    //
    // proof rule: or
    // proof node: F*sigma
    // proof term: (cl G1 ... Gn)
    // premises: (VP3:(cl F*sigma))
    // args: ()
    //
    // Otherwise
    //
    // proof rule: resolution
    // proof node: F*sigma
    // proof term: (cl F*sigma)
    // premises: (VP2:(cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma))
    // (P:(forall ((x1 T1) ... (xn Tn)) F)) args: ()
    case PfRule::INSTANTIATE:
    {
      std::vector<Node> new_args;
      for (int i = 0; i < args.size(); i++)
      {
        new_args.push_back(
            d_nm->mkNode(kind::EQUAL, children[0][0][i], args[i]));
      }
      Node vp1 = d_nm->mkNode(
          kind::SEXPR, d_cl, d_nm->mkNode(kind::OR, children[0].negate(), res));
      bool success =
          addVeritStep(vp1, VeritRule::FORALL_INST, {}, new_args, *cdp);
      Node vp2 = d_nm->mkNode(kind::SEXPR, d_cl, children[0].negate(), res);
      success &= addVeritStep(vp2, VeritRule::OR, {vp1}, {}, *cdp);
      if (res.getKind() == kind::OR)
      {
        Node vp3 = d_nm->mkNode(kind::SEXPR, d_cl, res);
        return success
               && addVeritStep(
                   vp3, VeritRule::RESOLUTION, {vp2, children[0]}, {}, *cdp)
               && addVeritStep(res, VeritRule::OR, {vp3}, {}, *cdp);
      }
      return success
             && addVeritStep(res,
                             VeritRule::RESOLUTION,
                             d_nm->mkNode(kind::SEXPR, d_cl, res),
                             {vp2, children[0]},
                             {},
                             *cdp);
    }
    default:
    {
      std::cout << id << std::endl;
      return addVeritStep(res, VeritRule::UNDEFINED, d_nm->mkNode(kind::SEXPR,d_cl,res),children, args, *cdp);
    }
  }
  return true;
}

VeritProofPostprocess::VeritProofPostprocess(ProofNodeManager* pnm,
                                             bool extended)
    : d_pnm(pnm),
      d_cb(new VeritProofPostprocessCallback(d_pnm)),
      d_extended(extended)
{
  d_cb->initializeUpdate(extended);
}

VeritProofPostprocess::~VeritProofPostprocess() {}

void VeritProofPostprocess::processFirstScope(std::shared_ptr<ProofNode> pf,
                                              CDProof* cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  Node cl = nm->mkBoundVar("cl", nm->stringType());
  std::vector<Node> children;
  for (const std::shared_ptr<ProofNode>& child : pf->getChildren())
  {
    children.push_back(child->getResult());
  }
  std::vector<Node> args = pf->getArguments();
  Node res = pf->getResult();

  bool success = true;

  std::vector<Node> negNode;
  for (Node arg : args)
  {
    negNode.push_back(arg.notNode());
  }
  negNode.push_back(children[0]);

  negNode.insert(negNode.begin(), cl);
  Node vp1 = nm->mkNode(kind::SEXPR, negNode);

  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(
      nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::ANCHOR_SUBPROOF)));
  new_args.push_back(vp1);
  new_args.push_back(vp1);
  new_args.insert(new_args.end(), args.begin(), args.end());
  success &= cdp->addStep(vp1, PfRule::VERIT_RULE, children, new_args);

  std::vector<Node> andNegs;
  andNegs.push_back(vp1);
  for (Node arg : args)
  {
    new_args.clear();
    new_args.push_back(
        nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::ASSUME)));
    new_args.push_back(arg);
    new_args.push_back(arg);
    success &= cdp->addStep(arg, PfRule::VERIT_RULE, {}, new_args);
  }
  args.push_back(vp1);
  new_args.clear();
  new_args.push_back(
      nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::RESOLUTION)));
  new_args.push_back(res);
  new_args.push_back(nm->mkNode(kind::SEXPR, cl));
  success &= cdp->addStep(res, PfRule::VERIT_RULE, args, new_args);

  d_pnm->updateNode(pf.get(), cdp->getProofFor(pf->getResult()).get());
}

void VeritProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  CDProof* cdp = new CDProof(d_pnm);

  Trace("verit-proof") << "-  veriT proof postprocess " << pf->getResult()
                       << " " << pf->getRule() << " / " << pf->getArguments()
                       << std::endl;
  processInternal(pf->getChildren()[0], cdp);
  processFirstScope(pf, cdp);
  //processSYMM(pf,cdp);
}

void VeritProofPostprocess::processSYMM(std::shared_ptr<ProofNode> pf, CDProof *cdp){
	NodeManager* nm = NodeManager::currentNM();
  for (const std::shared_ptr<ProofNode>& child :pf->getChildren()){
    if(child->getRule() == PfRule::SYMM){
      std::vector<Node> new_args = std::vector<Node>();
      new_args.push_back(nm->mkConst<Rational>(static_cast<unsigned>(VeritRule::SYMM)));
      new_args.push_back(child->getResult());
      new_args.push_back(child->getResult());
      std::vector<Node> new_children;
      for(auto cchild : child->getChildren()){
        new_children.push_back(cchild->getResult());
      }
      std::cout << child->getResult() << " " << child->getRule() << " " << new_children <<std::endl;
      cdp->addStep(child->getResult(), PfRule::VERIT_RULE, new_children, new_args);
      d_pnm->updateNode(child.get(), cdp->getProofFor(child->getResult()).get());
    }
    processSYMM(child,cdp);
  }

};


void VeritProofPostprocess::processInternal(std::shared_ptr<ProofNode> pf,
                                            CDProof* cdp)//TODO: Change this to &?
{
  std::vector<std::shared_ptr<ProofNode>> new_children;

  //First, update children
  for (const std::shared_ptr<ProofNode>& child :pf->getChildren()){
    std::shared_ptr<ProofNode> next_child = child;
    //In non-extended mode symm and reordering should be skipped.
    if(!d_extended && (next_child->getRule() == PfRule::REORDERING || next_child->getRule() == PfRule::SYMM)){
      while (next_child->getRule() == PfRule::SYMM || next_child->getRule() == PfRule::REORDERING){
        if(next_child->getChildren().end()-next_child->getChildren().begin() > 0){
          next_child = next_child->getChildren()[0];
         }
  	else{
	  break;
	}
      }
    }
    processInternal(next_child, cdp);
    new_children.push_back(next_child);
    cdp->addProof(next_child);
  }

  bool continueUpdate = true;
  if (d_cb->shouldUpdate(pf, continueUpdate))
  {
    //update node
    if (d_cb->update(pf->getResult(),
                     pf->getRule(),
		     new_children,
                     pf->getArguments(),
                     cdp,
                     continueUpdate))
    {
      d_pnm->updateNode(pf.get(), cdp->getProofFor(pf->getResult()).get());
      Trace("verit-proof") << "... updated proof for " << pf->getResult()
                           << std::endl;
    }
    else
    {
      // Add Trace
    }
  }
}

}  // namespace proof

}  // namespace CVC4
