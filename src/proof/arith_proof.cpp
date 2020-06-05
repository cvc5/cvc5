/*********************                                                        */
/*! \file arith_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Guy Katz, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/
#include "proof/arith_proof.h"

#include <memory>
#include <stack>

#include "base/check.h"
#include "expr/node.h"
#include "expr/type_checker_util.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/theory_arith.h"

#define CVC4_ARITH_VAR_TERM_PREFIX "term."

namespace CVC4 {

inline static Node eqNode(TNode n1, TNode n2) {
  return NodeManager::currentNM()->mkNode(kind::EQUAL, n1, n2);
}

// congrence matching term helper
inline static bool match(TNode n1, TNode n2) {
  Debug("pf::arith") << "match " << n1 << " " << n2 << std::endl;
  if(ProofManager::currentPM()->hasOp(n1)) {
    n1 = ProofManager::currentPM()->lookupOp(n1);
  }
  if(ProofManager::currentPM()->hasOp(n2)) {
    n2 = ProofManager::currentPM()->lookupOp(n2);
  }
  Debug("pf::arith") << "+ match " << n1 << " " << n2 << std::endl;
  if(n1 == n2) {
    return true;
  }
  if(n1.getType().isFunction() && n2.hasOperator()) {
    if(ProofManager::currentPM()->hasOp(n2.getOperator())) {
      return n1 == ProofManager::currentPM()->lookupOp(n2.getOperator());
    } else {
      return n1 == n2.getOperator();
    }
  }
  if(n2.getType().isFunction() && n1.hasOperator()) {
    if(ProofManager::currentPM()->hasOp(n1.getOperator())) {
      return n2 == ProofManager::currentPM()->lookupOp(n1.getOperator());
    } else {
      return n2 == n1.getOperator();
    }
  }
  if(n1.hasOperator() && n2.hasOperator() && n1.getOperator() != n2.getOperator()) {
    return false;
  }
  for(size_t i = 0; i < n1.getNumChildren() && i < n2.getNumChildren(); ++i) {
    if(n1[i] != n2[i]) {
      return false;
    }
  }
  return true;
}

void ProofArith::toStream(std::ostream& out) const
{
  Trace("theory-proof-debug") << "; Print Arith proof..." << std::endl;
  //AJR : carry this further?
  ProofLetMap map;
  toStreamLFSC(out, ProofManager::getArithProof(), *d_proof, map);
}

void ProofArith::toStreamLFSC(std::ostream& out,
                              TheoryProof* tp,
                              const theory::eq::EqProof& pf,
                              const ProofLetMap& map)
{
  Debug("lfsc-arith") << "Printing arith proof in LFSC : " << std::endl;
  pf.debug_print("lfsc-arith");
  Debug("lfsc-arith") << std::endl;
  toStreamRecLFSC(out, tp, pf, 0, map);
}

Node ProofArith::toStreamRecLFSC(std::ostream& out,
                                 TheoryProof* tp,
                                 const theory::eq::EqProof& pf,
                                 unsigned tb,
                                 const ProofLetMap& map)
{
  Debug("pf::arith") << std::endl
                     << std::endl
                     << "toStreamRecLFSC called. tb = " << tb
                     << " . proof:" << std::endl;
  pf.debug_print("pf::arith");
  Debug("pf::arith") << std::endl;

  if(tb == 0) {
    Assert(pf.d_id == theory::eq::MERGED_THROUGH_TRANS);
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.size() >= 2);

    int neg = -1;
    std::shared_ptr<theory::eq::EqProof> subTrans =
        std::make_shared<theory::eq::EqProof>();
    subTrans->d_id = theory::eq::MERGED_THROUGH_TRANS;
    subTrans->d_node = pf.d_node;

    size_t i = 0;
    while (i < pf.d_children.size()) {
      // Look for the negative clause, with which we will form a contradiction.
      if(!pf.d_children[i]->d_node.isNull() && pf.d_children[i]->d_node.getKind() == kind::NOT) {
        Assert(neg < 0);
        neg = i;
        ++i;
      }

      // Handle congruence closures over equalities.
      else if (pf.d_children[i]->d_id==theory::eq::MERGED_THROUGH_CONGRUENCE && pf.d_children[i]->d_node.isNull()) {
        Debug("pf::arith") << "Handling congruence over equalities" << std::endl;

        // Gather the sequence of consecutive congruence closures.
        std::vector<std::shared_ptr<const theory::eq::EqProof>> congruenceClosures;
        unsigned count;
        Debug("pf::arith") << "Collecting congruence sequence" << std::endl;
        for (count = 0;
             i + count < pf.d_children.size() &&
             pf.d_children[i + count]->d_id==theory::eq::MERGED_THROUGH_CONGRUENCE &&
             pf.d_children[i + count]->d_node.isNull();
             ++count) {
          Debug("pf::arith") << "Found a congruence: " << std::endl;
          pf.d_children[i+count]->debug_print("pf::arith");
          congruenceClosures.push_back(pf.d_children[i+count]);
        }

        Debug("pf::arith") << "Total number of congruences found: " << congruenceClosures.size() << std::endl;

        // Determine if the "target" of the congruence sequence appears right before or right after the sequence.
        bool targetAppearsBefore = true;
        bool targetAppearsAfter = true;

        if ((i == 0) || (i == 1 && neg == 0)) {
          Debug("pf::arith") << "Target does not appear before" << std::endl;
          targetAppearsBefore = false;
        }

        if ((i + count >= pf.d_children.size()) ||
            (!pf.d_children[i + count]->d_node.isNull() &&
             pf.d_children[i + count]->d_node.getKind() == kind::NOT)) {
          Debug("pf::arith") << "Target does not appear after" << std::endl;
          targetAppearsAfter = false;
        }

        // Assert that we have precisely one target clause.
        Assert(targetAppearsBefore != targetAppearsAfter);

        // Begin breaking up the congruences and ordering the equalities correctly.
        std::vector<std::shared_ptr<theory::eq::EqProof>> orderedEqualities;


        // Insert target clause first.
        if (targetAppearsBefore) {
          orderedEqualities.push_back(pf.d_children[i - 1]);
          // The target has already been added to subTrans; remove it.
          subTrans->d_children.pop_back();
        } else {
          orderedEqualities.push_back(pf.d_children[i + count]);
        }

        // Start with the congruence closure closest to the target clause, and work our way back/forward.
        if (targetAppearsBefore) {
          for (unsigned j = 0; j < count; ++j) {
            if (pf.d_children[i + j]->d_children[0]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
              orderedEqualities.insert(orderedEqualities.begin(), pf.d_children[i + j]->d_children[0]);
            if (pf.d_children[i + j]->d_children[1]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(orderedEqualities.end(), pf.d_children[i + j]->d_children[1]);
          }
        } else {
          for (unsigned j = 0; j < count; ++j) {
            if (pf.d_children[i + count - 1 - j]->d_children[0]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
              orderedEqualities.insert(orderedEqualities.begin(), pf.d_children[i + count - 1 - j]->d_children[0]);
            if (pf.d_children[i + count - 1 - j]->d_children[1]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
              orderedEqualities.insert(orderedEqualities.end(), pf.d_children[i + count - 1 - j]->d_children[1]);
          }
        }

        // Copy the result into the main transitivity proof.
        subTrans->d_children.insert(subTrans->d_children.end(), orderedEqualities.begin(), orderedEqualities.end());

        // Increase i to skip over the children that have been processed.
        i += count;
        if (targetAppearsAfter) {
          ++i;
        }
      }

      // Else, just copy the child proof as is
      else {
        subTrans->d_children.push_back(pf.d_children[i]);
        ++i;
      }
    }
    Assert(neg >= 0);

    Node n1;
    std::stringstream ss;
    //Assert(subTrans->d_children.size() == pf.d_children.size() - 1);
    Debug("pf::arith") << "\nsubtrans has " << subTrans->d_children.size() << " children\n";
    if(pf.d_children.size() > 2) {
      n1 = toStreamRecLFSC(ss, tp, *subTrans, 1, map);
    } else {
      n1 = toStreamRecLFSC(ss, tp, *(subTrans->d_children[0]), 1, map);
      Debug("pf::arith") << "\nsubTrans unique child " << subTrans->d_children[0]->d_id << " was proven\ngot: " << n1 << std::endl;
    }

    Node n2 = pf.d_children[neg]->d_node;
    Assert(n2.getKind() == kind::NOT);
    out << "(clausify_false (contra _ ";
    Debug("pf::arith") << "\nhave proven: " << n1 << std::endl;
    Debug("pf::arith") << "n2 is " << n2[0] << std::endl;

    if (n2[0].getNumChildren() > 0) { Debug("pf::arith") << "\nn2[0]: " << n2[0][0] << std::endl; }
    if (n1.getNumChildren() > 1) { Debug("pf::arith") << "n1[1]: " << n1[1] << std::endl; }

    if(n2[0].getKind() == kind::APPLY_UF) {
      out << "(trans _ _ _ _ ";
      out << "(symm _ _ _ ";
      out << ss.str();
      out << ") (pred_eq_f _ " << ProofManager::getLitName(n2[0]) << ")) t_t_neq_f))" << std::endl;
    } else {
      Assert((n1[0] == n2[0][0] && n1[1] == n2[0][1])
             || (n1[1] == n2[0][0] && n1[0] == n2[0][1]));
      if(n1[1] == n2[0][0]) {
        out << "(symm _ _ _ " << ss.str() << ")";
      } else {
        out << ss.str();
      }
      out << " " << ProofManager::getLitName(n2[0]) << "))" << std::endl;
    }
    return Node();
  }

  switch(pf.d_id) {
  case theory::eq::MERGED_THROUGH_CONGRUENCE: {
    Debug("pf::arith") << "\nok, looking at congruence:\n";
    pf.debug_print("pf::arith");
    std::stack<const theory::eq::EqProof*> stk;
    for (const theory::eq::EqProof* pf2 = &pf;
         pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE;
         pf2 = pf2->d_children[0].get()) {
      Assert(!pf2->d_node.isNull());
      Assert(pf2->d_node.getKind() == kind::PARTIAL_APPLY_UF
             || pf2->d_node.getKind() == kind::BUILTIN
             || pf2->d_node.getKind() == kind::APPLY_UF
             || pf2->d_node.getKind() == kind::SELECT
             || pf2->d_node.getKind() == kind::STORE);
      Assert(pf2->d_children.size() == 2);
      out << "(cong _ _ _ _ _ _ ";
      stk.push(pf2);
    }
    Assert(stk.top()->d_children[0]->d_id
           != theory::eq::MERGED_THROUGH_CONGRUENCE);
    NodeBuilder<> b1(kind::PARTIAL_APPLY_UF), b2(kind::PARTIAL_APPLY_UF);
    const theory::eq::EqProof* pf2 = stk.top();
    stk.pop();
    Assert(pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE);
    Node n1 = toStreamRecLFSC(out, tp, *(pf2->d_children[0]), tb + 1, map);
    out << " ";
    std::stringstream ss;
    Node n2 = toStreamRecLFSC(ss, tp, *(pf2->d_children[1]), tb + 1, map);
    Debug("pf::arith") << "\nok, in FIRST cong[" << stk.size() << "]" << "\n";
    pf2->debug_print("pf::arith");
    Debug("pf::arith") << "looking at " << pf2->d_node << "\n";
    Debug("pf::arith") << "           " << n1 << "\n";
    Debug("pf::arith") << "           " << n2 << "\n";
    int side = 0;
    if(match(pf2->d_node, n1[0])) {
      //if(tb == 1) {
      Debug("pf::arith") << "SIDE IS 0\n";
      //}
      side = 0;
    } else {
      //if(tb == 1) {
      Debug("pf::arith") << "SIDE IS 1\n";
      //}
      if(!match(pf2->d_node, n1[1])) {
      Debug("pf::arith") << "IN BAD CASE, our first subproof is\n";
      pf2->d_children[0]->debug_print("pf::arith");
      }
      Assert(match(pf2->d_node, n1[1]));
      side = 1;
    }
    if(n1[side].getKind() == kind::APPLY_UF || n1[side].getKind() == kind::PARTIAL_APPLY_UF || n1[side].getKind() == kind::SELECT || n1[side].getKind() == kind::STORE) {
      if(n1[side].getKind() == kind::APPLY_UF || n1[side].getKind() == kind::PARTIAL_APPLY_UF) {
        b1 << n1[side].getOperator();
      } else {
        b1 << ProofManager::currentPM()->mkOp(n1[side].getOperator());
      }
      b1.append(n1[side].begin(), n1[side].end());
    } else {
      b1 << n1[side];
    }
    if(n1[1-side].getKind() == kind::PARTIAL_APPLY_UF || n1[1-side].getKind() == kind::APPLY_UF || n1[side].getKind() == kind::SELECT || n1[side].getKind() == kind::STORE) {
      if(n1[1-side].getKind() == kind::PARTIAL_APPLY_UF || n1[1-side].getKind() == kind::APPLY_UF) {
        b2 << n1[1-side].getOperator();
      } else {
        b2 << ProofManager::currentPM()->mkOp(n1[1-side].getOperator());
      }
      b2.append(n1[1-side].begin(), n1[1-side].end());
    } else {
      b2 << n1[1-side];
    }
    Debug("pf::arith") << "pf2->d_node " << pf2->d_node << std::endl;
    Debug("pf::arith") << "b1.getNumChildren() " << b1.getNumChildren() << std::endl;
    Debug("pf::arith") << "n1 " << n1 << std::endl;
    Debug("pf::arith") << "n2 " << n2 << std::endl;
    Debug("pf::arith") << "side " << side << std::endl;
    if(pf2->d_node[b1.getNumChildren() - (pf2->d_node.getMetaKind() == kind::metakind::PARAMETERIZED ? 0 : 1)] == n2[side]) {
      b1 << n2[side];
      b2 << n2[1-side];
      out << ss.str();
    } else {
      Assert(pf2->d_node[b1.getNumChildren()
                         - (pf2->d_node.getMetaKind()
                                    == kind::metakind::PARAMETERIZED
                                ? 0
                                : 1)]
             == n2[1 - side]);
      b1 << n2[1-side];
      b2 << n2[side];
      out << "(symm _ _ _ " << ss.str() << ")";
    }
    out << ")";
    while(!stk.empty()) {
      if(tb == 1) {
      Debug("pf::arith") << "\nMORE TO DO\n";
      }
      pf2 = stk.top();
      stk.pop();
      Assert(pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE);
      out << " ";
      ss.str("");
      n2 = toStreamRecLFSC(ss, tp, *(pf2->d_children[1]), tb + 1, map);
      Debug("pf::arith") << "\nok, in cong[" << stk.size() << "]" << "\n";
      Debug("pf::arith") << "looking at " << pf2->d_node << "\n";
      Debug("pf::arith") << "           " << n1 << "\n";
      Debug("pf::arith") << "           " << n2 << "\n";
      Debug("pf::arith") << "           " << b1 << "\n";
      Debug("pf::arith") << "           " << b2 << "\n";
      if(pf2->d_node[b1.getNumChildren()] == n2[side]) {
        b1 << n2[side];
        b2 << n2[1-side];
        out << ss.str();
      } else {
        Assert(pf2->d_node[b1.getNumChildren()] == n2[1 - side]);
        b1 << n2[1-side];
        b2 << n2[side];
        out << "(symm _ _ _ " << ss.str() << ")";
      }
      out << ")";
    }
    n1 = b1;
    n2 = b2;
    Debug("pf::arith") << "at end assert, got " << pf2->d_node << "  and  " << n1 << std::endl;
    if(pf2->d_node.getKind() == kind::PARTIAL_APPLY_UF) {
      Assert(n1 == pf2->d_node);
    }
    if(n1.getOperator().getType().getNumChildren() == n1.getNumChildren() + 1) {
      if(ProofManager::currentPM()->hasOp(n1.getOperator())) {
        b1.clear(ProofManager::currentPM()->lookupOp(n2.getOperator()).getConst<Kind>());
      } else {
        b1.clear(kind::APPLY_UF);
        b1 << n1.getOperator();
      }
      b1.append(n1.begin(), n1.end());
      n1 = b1;
      Debug("pf::arith") << "at[2] end assert, got " << pf2->d_node << "  and  " << n1 << std::endl;
      if(pf2->d_node.getKind() == kind::APPLY_UF) {
        Assert(n1 == pf2->d_node);
      }
    }
    if(n2.getOperator().getType().getNumChildren() == n2.getNumChildren() + 1) {
      if(ProofManager::currentPM()->hasOp(n2.getOperator())) {
        b2.clear(ProofManager::currentPM()->lookupOp(n2.getOperator()).getConst<Kind>());
      } else {
        b2.clear(kind::APPLY_UF);
        b2 << n2.getOperator();
      }
      b2.append(n2.begin(), n2.end());
      n2 = b2;
    }
    Node n = (side == 0 ? eqNode(n1, n2) : eqNode(n2, n1));
    if(tb == 1) {
    Debug("pf::arith") << "\ncong proved: " << n << "\n";
    }
    return n;
  }

  case theory::eq::MERGED_THROUGH_REFLEXIVITY:
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.empty());
    out << "(refl _ ";
    tp->printTerm(NodeManager::currentNM()->toExpr(pf.d_node), out, map);
    out << ")";
    return eqNode(pf.d_node, pf.d_node);

  case theory::eq::MERGED_THROUGH_EQUALITY:
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.empty());
    out << ProofManager::getLitName(pf.d_node.negate());
    return pf.d_node;

  case theory::eq::MERGED_THROUGH_TRANS: {
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.size() >= 2);
    std::stringstream ss;
    Debug("pf::arith") << "\ndoing trans proof[[\n";
    pf.debug_print("pf::arith");
    Debug("pf::arith") << "\n";
    Node n1 = toStreamRecLFSC(ss, tp, *(pf.d_children[0]), tb + 1, map);
    Debug("pf::arith") << "\ndoing trans proof, got n1 " << n1 << "\n";
    if(tb == 1) {
      Debug("pf::arith") << "\ntrans proof[0], got n1 " << n1 << "\n";
    }

    bool identicalEqualities = false;
    bool evenLengthSequence;
    Node nodeAfterEqualitySequence;

    std::map<size_t, Node> childToStream;

    for(size_t i = 1; i < pf.d_children.size(); ++i) {
      std::stringstream ss1(ss.str()), ss2;
      ss.str("");

      // It is possible that we've already converted the i'th child to stream. If so,
      // use previously stored result. Otherwise, convert and store.
      Node n2;
      if (childToStream.find(i) != childToStream.end())
        n2 = childToStream[i];
      else {
        n2 = toStreamRecLFSC(ss2, tp, *(pf.d_children[i]), tb + 1, map);
        childToStream[i] = n2;
      }

      // The following branch is dedicated to handling sequences of identical equalities,
      // i.e. trans[ a=b, a=b, a=b ].
      //
      // There are two cases:
      //    1. The number of equalities is odd. Then, the sequence can be collapsed to just one equality,
      //       i.e. a=b.
      //    2. The number of equalities is even. Now, we have two options: a=a or b=b. To determine this,
      //       we look at the node after the equality sequence. If it needs a, we go for a=a; and if it needs
      //       b, we go for b=b. If there is no following node, we look at the goal of the transitivity proof,
      //       and use it to determine which option we need.
      if(n2.getKind() == kind::EQUAL) {
        if (((n1[0] == n2[0]) && (n1[1] == n2[1])) || ((n1[0] == n2[1]) && (n1[1] == n2[0]))) {
          // We are in a sequence of identical equalities

          Debug("pf::arith") << "Detected identical equalities: " << std::endl << "\t" << n1 << std::endl;

          if (!identicalEqualities) {
            // The sequence of identical equalities has started just now
            identicalEqualities = true;

            Debug("pf::arith") << "The sequence is just beginning. Determining length..." << std::endl;

            // Determine whether the length of this sequence is odd or even.
            evenLengthSequence = true;
            bool sequenceOver = false;
            size_t j = i + 1;

            while (j < pf.d_children.size() && !sequenceOver) {
              std::stringstream dontCare;
              nodeAfterEqualitySequence = toStreamRecLFSC(
                  dontCare, tp, *(pf.d_children[j]), tb + 1, map);

              if (((nodeAfterEqualitySequence[0] == n1[0]) && (nodeAfterEqualitySequence[1] == n1[1])) ||
                  ((nodeAfterEqualitySequence[0] == n1[1]) && (nodeAfterEqualitySequence[1] == n1[0]))) {
                evenLengthSequence = !evenLengthSequence;
              } else {
                sequenceOver = true;
              }

              ++j;
            }

            if (evenLengthSequence) {
              // If the length is even, we need to apply transitivity for the "correct" hand of the equality.

              Debug("pf::arith") << "Equality sequence of even length" << std::endl;
              Debug("pf::arith") << "n1 is: " << n1 << std::endl;
              Debug("pf::arith") << "n2 is: " << n2 << std::endl;
              Debug("pf::arith") << "pf-d_node is: " << pf.d_node << std::endl;
              Debug("pf::arith") << "Next node is: " << nodeAfterEqualitySequence << std::endl;

              ss << "(trans _ _ _ _ ";

              // If the sequence is at the very end of the transitivity proof, use pf.d_node to guide us.
              if (!sequenceOver) {
                if (match(n1[0], pf.d_node[0])) {
                  n1 = eqNode(n1[0], n1[0]);
                  ss << ss1.str() << " (symm _ _ _ " << ss1.str() << ")";
                } else if (match(n1[1], pf.d_node[1])) {
                  n1 = eqNode(n1[1], n1[1]);
                  ss << " (symm _ _ _ " << ss1.str() << ")" << ss1.str();
                } else {
                  Debug("pf::arith") << "Error: identical equalities over, but hands don't match what we're proving."
                                     << std::endl;
                  Assert(false);
                }
              } else {
                // We have a "next node". Use it to guide us.

                Assert(nodeAfterEqualitySequence.getKind() == kind::EQUAL);

                if ((n1[0] == nodeAfterEqualitySequence[0]) || (n1[0] == nodeAfterEqualitySequence[1])) {

                  // Eliminate n1[1]
                  ss << ss1.str() << " (symm _ _ _ " << ss1.str() << ")";
                  n1 = eqNode(n1[0], n1[0]);

                } else if ((n1[1] == nodeAfterEqualitySequence[0]) || (n1[1] == nodeAfterEqualitySequence[1])) {

                  // Eliminate n1[0]
                  ss << " (symm _ _ _ " << ss1.str() << ")" << ss1.str();
                  n1 = eqNode(n1[1], n1[1]);

                } else {
                  Debug("pf::arith") << "Error: even length sequence, but I don't know which hand to keep!" << std::endl;
                  Assert(false);
                }
              }

              ss << ")";

            } else {
              Debug("pf::arith") << "Equality sequence length is odd!" << std::endl;
              ss.str(ss1.str());
            }

            Debug("pf::arith") << "Have proven: " << n1 << std::endl;
          } else {
            ss.str(ss1.str());
          }

          // Ignore the redundancy.
          continue;
        }
      }

      if (identicalEqualities) {
        // We were in a sequence of identical equalities, but it has now ended. Resume normal operation.
        identicalEqualities = false;
      }

      Debug("pf::arith") << "\ndoing trans proof, got n2 " << n2 << "\n";
      if(tb == 1) {
        Debug("pf::arith") << "\ntrans proof[" << i << "], got n2 " << n2 << "\n";
        Debug("pf::arith") << (n2.getKind() == kind::EQUAL) << "\n";

        if ((n1.getNumChildren() >= 2) && (n2.getNumChildren() >= 2)) {
          Debug("pf::arith") << n1[0].getId() << " " << n1[1].getId() << " / " << n2[0].getId() << " " << n2[1].getId() << "\n";
          Debug("pf::arith") << n1[0].getId() << " " << n1[0] << "\n";
          Debug("pf::arith") << n1[1].getId() << " " << n1[1] << "\n";
          Debug("pf::arith") << n2[0].getId() << " " << n2[0] << "\n";
          Debug("pf::arith") << n2[1].getId() << " " << n2[1] << "\n";
          Debug("pf::arith") << (n1[0] == n2[0]) << "\n";
          Debug("pf::arith") << (n1[1] == n2[1]) << "\n";
          Debug("pf::arith") << (n1[0] == n2[1]) << "\n";
          Debug("pf::arith") << (n1[1] == n2[0]) << "\n";
        }
      }
      ss << "(trans _ _ _ _ ";

      if((n2.getKind() == kind::EQUAL) && (n1.getKind() == kind::EQUAL))
        // Both elements of the transitivity rule are equalities/iffs
      {
        if(n1[0] == n2[0]) {
            if(tb == 1) { Debug("pf::arith") << "case 1\n"; }
            n1 = eqNode(n1[1], n2[1]);
            ss << "(symm _ _ _ " << ss1.str() << ") " << ss2.str();
        } else if(n1[1] == n2[1]) {
          if(tb == 1) { Debug("pf::arith") << "case 2\n"; }
          n1 = eqNode(n1[0], n2[0]);
          ss << ss1.str() << " (symm _ _ _ " << ss2.str() << ")";
        } else if(n1[0] == n2[1]) {
            if(tb == 1) { Debug("pf::arith") << "case 3\n"; }
            n1 = eqNode(n2[0], n1[1]);
            ss << ss2.str() << " " << ss1.str();
            if(tb == 1) { Debug("pf::arith") << "++ proved " << n1 << "\n"; }
        } else if(n1[1] == n2[0]) {
          if(tb == 1) { Debug("pf::arith") << "case 4\n"; }
          n1 = eqNode(n1[0], n2[1]);
          ss << ss1.str() << " " << ss2.str();
        } else {
          Warning() << "\n\ntrans proof failure at step " << i << "\n\n";
          Warning() << "0 proves " << n1 << "\n";
          Warning() << "1 proves " << n2 << "\n\n";
          pf.debug_print("pf::arith",0);
          //toStreamRec(Warning.getStream(), pf, 0);
          Warning() << "\n\n";
          Unreachable();
        }
        Debug("pf::arith") << "++ trans proof[" << i << "], now have " << n1 << std::endl;
      } else if(n1.getKind() == kind::EQUAL) {
        // n1 is an equality/iff, but n2 is a predicate
        if(n1[0] == n2) {
          n1 = n1[1];
          ss << "(symm _ _ _ " << ss1.str() << ") (pred_eq_t _ " << ss2.str() << ")";
        } else if(n1[1] == n2) {
          n1 = n1[0];
          ss << ss1.str() << " (pred_eq_t _ " << ss2.str() << ")";
        } else {
          Unreachable();
        }
      } else if(n2.getKind() == kind::EQUAL) {
        // n2 is an equality/iff, but n1 is a predicate
        if(n2[0] == n1) {
          n1 = n2[1];
          ss << "(symm _ _ _ " << ss2.str() << ") (pred_eq_t _ " << ss1.str() << ")";
        } else if(n2[1] == n1) {
          n1 = n2[0];
          ss << ss2.str() << " (pred_eq_t _ " << ss1.str() << ")";
        } else {
          Unreachable();
        }
      } else {
        // Both n1 and n2 are prediacates. Don't know what to do...
        Unreachable();
      }

      ss << ")";
    }
    out << ss.str();
    Debug("pf::arith") << "\n++ trans proof done, have proven " << n1 << std::endl;
    return n1;
  }

  default:
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.empty());
    Debug("pf::arith") << "theory proof: " << pf.d_node << " by rule " << int(pf.d_id) << std::endl;
    AlwaysAssert(false);
    return pf.d_node;
  }
}

ArithProof::ArithProof(theory::arith::TheoryArith* arith, TheoryProofEngine* pe)
  : TheoryProof(arith, pe), d_recorder()
{
  arith->setProofRecorder(&d_recorder);
}

theory::TheoryId ArithProof::getTheoryId() { return theory::THEORY_ARITH; }
void ArithProof::registerTerm(Expr term) {
  Debug("pf::arith") << "Arith register term: " << term << ". Kind: " << term.getKind()
                            << ". Type: " << term.getType() << std::endl;

  if (term.getType().isReal() && !term.getType().isInteger()) {
    Debug("pf::arith") << "Entering real mode" << std::endl;
  }

  if (term.isVariable() && !ProofManager::getSkolemizationManager()->isSkolem(term)) {
    d_declarations.insert(term);
  }

  // recursively declare all other terms
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    // could belong to other theories
    d_proofEngine->registerTerm(term[i]);
  }
}

void LFSCArithProof::printOwnedTermAsType(Expr term,
                                          std::ostream& os,
                                          const ProofLetMap& map,
                                          TypeNode expectedType)
{
  Debug("pf::arith") << "Arith print term: " << term << ". Kind: " << term.getKind()
                     << ". Type: " << term.getType()
                     << ". Number of children: " << term.getNumChildren() << std::endl;

  // !d_realMode <--> term.getType().isInteger()

  Assert (theory::Theory::theoryOf(term) == theory::THEORY_ARITH);
  std::ostringstream closing;
  if (!expectedType.isNull() && !expectedType.isInteger() && term.getType().isInteger()) {
    os << "(term_int_to_real ";
    closing << ")";
  }
  switch (term.getKind())
  {
    case kind::CONST_RATIONAL:
    {
      Assert(term.getNumChildren() == 0);
      Assert(term.getType().isInteger() || term.getType().isReal());

      const Rational& r = term.getConst<Rational>();
      bool neg = (r < 0);

      os << (term.getType().isInteger() ? "(a_int " : "(a_real ");
      closing << ") ";

      if (neg)
      {
        os << "(~ ";
        closing << ")";
      }

      if (term.getType().isInteger())
      {
        os << r.abs();
      }
      else
      {
        printRational(os, r.abs());
      }

      break;
    }

    case kind::PLUS:
    case kind::MINUS:
    case kind::MULT:
    case kind::DIVISION:
    case kind::DIVISION_TOTAL:
    {
      Assert(term.getNumChildren() >= 1);
      TypeNode ty = Node::fromExpr(term).getType();

      std::string lfscFunction = getLfscFunction(term);
      for (unsigned i = 0; i < term.getNumChildren() - 1; ++i)
      {
        os << "(" << lfscFunction << " ";
        closing << ")";
        d_proofEngine->printBoundTerm(term[i], os, map, ty);
        os << " ";
      }

      d_proofEngine->printBoundTerm(term[term.getNumChildren() - 1], os, map, ty);
      break;
    }

    case kind::UMINUS:
    {
      Assert(term.getNumChildren() == 1);
      os << "(" << getLfscFunction(term) << " ";
      closing << ")";
      d_proofEngine->printBoundTerm(term[0], os, map, Node::fromExpr(term).getType());
      break;
    }

    case kind::GT:
    case kind::GEQ:
    case kind::LT:
    case kind::LEQ:
    {
      Assert(term.getNumChildren() == 2);
      Assert(term.getType().isBoolean());

      std::string lfscFunction = getLfscFunction(term);
      TypeNode realType = NodeManager::currentNM()->realType();

      os << "(" << lfscFunction << " ";
      closing << ")";

      d_proofEngine->printBoundTerm(term[0], os, map);
      os << " ";
      d_proofEngine->printBoundTerm(term[1], os, map, realType);
      break;
    }
    case kind::EQUAL:
    {
      Assert(term.getType().isBoolean());
      Assert(term.getNumChildren() == 2);

      TypeNode eqType = equalityType(term[0], term[1]);

      os << "(= " << eqType << " ";
      closing << ")";

      d_proofEngine->printBoundTerm(term[0], os, map, eqType);
      d_proofEngine->printBoundTerm(term[1], os, map, eqType);
      break;
    }

    case kind::VARIABLE:
    case kind::SKOLEM:
      os << CVC4_ARITH_VAR_TERM_PREFIX << ProofManager::sanitize(term);
      break;

    default:
      Debug("pf::arith") << "Default printing of term: " << term << std::endl;
      os << term;
      break;
  }
  os << closing.str();
}

void LFSCArithProof::printOwnedSort(Type type, std::ostream& os) {
  Debug("pf::arith") << "Arith print sort: " << type << std::endl;
  os << type;
}

std::string LFSCArithProof::getLfscFunction(const Node & n) {
  Assert(n.getType().isInteger() || n.getType().isReal() || n.getType().isBoolean());
  std::string opString;
  switch (n.getKind()) {
    case kind::UMINUS:
      opString = "u-_";
      break;
    case kind::PLUS:
      opString = "+_";
      break;
    case kind::MINUS:
      opString = "-_";
      break;
    case kind::MULT:
      opString = "*_";
      break;
    case kind::DIVISION:
    case kind::DIVISION_TOTAL:
      opString = "/_";
      break;
    case kind::GT:
      opString = ">_";
      break;
    case kind::GEQ:
      opString = ">=_";
      break;
    case kind::LT:
      opString = "<_";
      break;
    case kind::LEQ:
      opString = "<=_";
      break;
    default:
      Unreachable() << "Tried to get the operator for a non-operator kind: " << n.getKind();
  }
  std::string typeString;
  if (n.getType().isInteger()) {
    typeString = "Int";
  } else if (n.getType().isReal()) {
    typeString = "Real";
  } else { // Boolean
    if (n[0].getType().isInteger()) {
      typeString = "IntReal";
    } else {
      typeString = "Real";
    }
  }
  return opString + typeString;
}

void LFSCArithProof::printRational(std::ostream& o, const Rational& r)
{
  if (r.sgn() < 0)
  {
    o << "(~ " << r.getNumerator().abs() << "/" << r.getDenominator().abs()
      << ")";
  }
  else
  {
    o << r.getNumerator() << "/" << r.getDenominator();
  }
}

void LFSCArithProof::printInteger(std::ostream& o, const Integer& i)
{
  if (i.sgn() < 0)
  {
    o << "(~ " << i.abs() << ")";
  }
  else
  {
    o << i;
  }
}

void LFSCArithProof::printLinearPolynomialNormalizer(std::ostream& o,
                                                     const Node& n)
{
  switch (n.getKind())
  {
    case kind::PLUS:
    {
      // Since our axioms are binary, but n may be n-ary, we rig up
      // a right-associative tree.
      size_t nchildren = n.getNumChildren();
      for (size_t i = 0; i < nchildren; ++i)
      {
        if (i < nchildren - 1)
        {
          o << "\n      (is_aff_+ _ _ _ _ _ ";
        }
        printLinearMonomialNormalizer(o, n[i]);
      }
      std::fill_n(std::ostream_iterator<char>(o), nchildren - 1, ')');
      break;
    }
    case kind::MULT:
    case kind::VARIABLE:
    case kind::CONST_RATIONAL:
    case kind::SKOLEM:
    {
      printLinearMonomialNormalizer(o, n);
      break;
    }
    default:
      Unreachable() << "Invalid operation " << n.getKind()
                    << " in linear polynomial";
      break;
  }
}

void LFSCArithProof::printLinearMonomialNormalizer(std::ostream& o,
                                                   const Node& n)
{
  switch (n.getKind())
  {
    case kind::MULT: {
      Assert((n[0].getKind() == kind::CONST_RATIONAL
              && (n[1].getKind() == kind::VARIABLE
                  || n[1].getKind() == kind::SKOLEM)))
          << "node " << n << " is not a linear monomial"
          << " " << n[0].getKind() << " " << n[1].getKind();

      o << "\n        (is_aff_mul_c_L _ _ _ ";
      printConstRational(o, n[0]);
      o << " ";
      printVariableNormalizer(o, n[1]);
      o << ")";
      break;
    }
    case kind::CONST_RATIONAL:
    {
      o << "\n        (is_aff_const ";
      printConstRational(o, n);
      o << ")";
      break;
    }
    case kind::VARIABLE:
    case kind::SKOLEM:
    {
      o << "\n        ";
      printVariableNormalizer(o, n);
      break;
    }
    default:
      Unreachable() << "Invalid operation " << n.getKind()
                    << " in linear monomial";
      break;
  }
}

void LFSCArithProof::printConstRational(std::ostream& o, const Node& n)
{
  Assert(n.getKind() == kind::CONST_RATIONAL);
  const Rational value = n.getConst<Rational>();
  printRational(o, value);
}

void LFSCArithProof::printVariableNormalizer(std::ostream& o, const Node& n)
{
  std::ostringstream msg;
  Assert(n.getKind() == kind::VARIABLE || n.getKind() == kind::SKOLEM)
      << "Invalid variable kind " << n.getKind() << " in linear monomial";
  if (n.getType().isInteger()) {
    o << "(is_aff_var_int ";
  } else if (n.getType().isReal()) {
    o << "(is_aff_var_real ";
  } else {
    Unreachable();
  }
  o << n << ")";
}

void LFSCArithProof::printLinearPolynomialPredicateNormalizer(std::ostream& o,
                                                              const Node& n)
{
  Assert(n.getKind() == kind::GEQ)
      << "can only print normalization witnesses for (>=) nodes";
  Assert(n[1].getKind() == kind::CONST_RATIONAL);
  o << "\n    (is_aff_- _ _ _ _ _ ";
  printLinearPolynomialNormalizer(o, n[0]);
  o << "\n      (is_aff_const ";
  printConstRational(o, n[1]);
  o << "))";
}

std::pair<Node, std::string> LFSCArithProof::printProofAndMaybeTighten(
    const Node& bound)
{
  const Node & nonNegBound = bound.getKind() == kind::NOT ? bound[0] : bound;
  std::ostringstream pfOfPossiblyTightenedPredicate;
  if (nonNegBound[0].getType().isInteger()) {
    switch(bound.getKind())
    {
      case kind::NOT:
      {
        // Tighten ~[i >= r] to [i < r] to [i <= {r}] to [-i >= -{r}]
        // where
        //    * i is an integer
        //    * r is a real
        //    * {r} denotes the greatest int less than r
        //      it is equivalent to (ceil(r) - 1)
        Assert(nonNegBound[1].getKind() == kind::CONST_RATIONAL);
        Rational oldBound = nonNegBound[1].getConst<Rational>();
        Integer newBound = -(oldBound.ceiling() - 1);
        // Since the arith theory rewrites bounds to be purely integral or
        // purely real, mixed bounds should not appear in proofs
        AlwaysAssert(oldBound.isIntegral()) << "Mixed int/real bound in arith proof";
        pfOfPossiblyTightenedPredicate
            << "(tighten_not_>=_IntInt"
            << " _ _ _ _ ("
            << "check_neg_of_greatest_integer_below_int ";
        printInteger(pfOfPossiblyTightenedPredicate, newBound);
        pfOfPossiblyTightenedPredicate << " ";
        printInteger(pfOfPossiblyTightenedPredicate, oldBound.ceiling());
        pfOfPossiblyTightenedPredicate << ") " << ProofManager::getLitName(bound.negate(), "") << ")";
        Node newLeft = (theory::arith::Polynomial::parsePolynomial(nonNegBound[0]) * -1).getNode();
        Node newRight = NodeManager::currentNM()->mkConst(Rational(newBound));
        Node newTerm = NodeManager::currentNM()->mkNode(kind::GEQ, newLeft, newRight);
        return std::make_pair(newTerm, pfOfPossiblyTightenedPredicate.str());
      }
      case kind::GEQ:
      {
        // Tighten [i >= r] to [i >= ceil(r)]
        // where
        //    * i is an integer
        //    * r is a real
        Assert(nonNegBound[1].getKind() == kind::CONST_RATIONAL);

        Rational oldBound = nonNegBound[1].getConst<Rational>();
        // Since the arith theory rewrites bounds to be purely integral or
        // purely real, mixed bounds should not appear in proofs
        AlwaysAssert(oldBound.isIntegral()) << "Mixed int/real bound in arith proof";
        pfOfPossiblyTightenedPredicate << ProofManager::getLitName(bound.negate(), "");
        return std::make_pair(bound, pfOfPossiblyTightenedPredicate.str());
      }
      default: Unreachable();
    }
  } else {
    return std::make_pair(bound, ProofManager::getLitName(bound.negate(), ""));
  }
  // Silence compiler warnings about missing a return.
  Unreachable();
}

void LFSCArithProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                           std::ostream& os,
                                           std::ostream& paren,
                                           const ProofLetMap& map)
{
  Debug("pf::arith") << "Printing proof for lemma " << lemma << std::endl;
  if (Debug.isOn("pf::arith::printTheoryLemmaProof")) {
    Debug("pf::arith::printTheoryLemmaProof") << "Printing proof for lemma:" << std::endl;
    for (const auto & conjunct : lemma) {
      Debug("pf::arith::printTheoryLemmaProof") << "  " << conjunct << std::endl;
    }
  }
  // Prefixes for the names of linearity witnesses
  const char* linearizedProofPrefix = "pf_aff";
  std::ostringstream lemmaParen;

  // Construct the set of conflicting literals
  std::set<Node> conflictSet;
  std::transform(lemma.begin(),
                 lemma.end(),
                 std::inserter(conflictSet, conflictSet.begin()),
                 [](const Expr& e) {
                   return NodeManager::currentNM()->fromExpr(e).negate();
                 });

  // If we have Farkas coefficients stored for this lemma, use them to write a
  // proof. Otherwise, just `trust` the lemma.
  if (d_recorder.hasFarkasCoefficients(conflictSet))
  {
    // Get farkas coefficients & literal order
    const auto& farkasInfo = d_recorder.getFarkasCoefficients(conflictSet);
    const Node& conflict = farkasInfo.first;
    theory::arith::RationalVectorCP farkasCoefficients = farkasInfo.second;
    Assert(farkasCoefficients != theory::arith::RationalVectorCPSentinel);
    Assert(conflict.getNumChildren() == farkasCoefficients->size());
    const size_t nAntecedents = conflict.getNumChildren();

    // Print proof
    if (Debug.isOn("pf::arith::printTheoryLemmaProof")) {
      os << "Farkas:" << std::endl;
      for (const auto & n : *farkasCoefficients) {
        os << "  " << n << std::endl;
      }
    }

    // Prove affine function bounds from term bounds
    os << "\n;; Farkas Proof ;;" << std::endl;
    os << "\n;  Linear Polynomial Proof Conversions";
    for (size_t i = 0; i != nAntecedents; ++i)
    {
      const Node& antecedent = conflict[i];
      os << "\n  (@ "
         << ProofManager::getLitName(antecedent.negate(), linearizedProofPrefix)
         << " ";
      lemmaParen << ")";
      const std::pair<Node, std::string> tightened = printProofAndMaybeTighten(antecedent);
      switch (tightened.first.getKind())
      {
        case kind::NOT:
        {
          Assert(conflict[i][0].getKind() == kind::GEQ);
          os << "(aff_>_from_term _ _ _ _ ";
          break;
        }
        case kind::GEQ:
        {
          os << "(aff_>=_from_term _ _ _ ";
          break;
        }
        default: Unreachable();
      }
      const Node& nonNegTightened = tightened.first.getKind() == kind::NOT ? tightened.first[0] : tightened.first;
      printLinearPolynomialPredicateNormalizer(os, nonNegTightened);
      os << " (pf_reified_arith_pred _ _ " << tightened.second << "))";
    }

    // Now, print the proof of bottom, from affine function bounds
    os << "\n;  Farkas Combination";
    os << "\n  (clausify_false (bounded_aff_contra _ _";
    lemmaParen << "))";
    for (size_t i = 0; i != nAntecedents; ++i)
    {
      const Node& lit = conflict[i];
      os << "\n    (bounded_aff_add _ _ _ _ _";
      os << "\n       (bounded_aff_mul_c _ _ _ ";
      printRational(os, (*farkasCoefficients)[i].abs());
      os << " " << ProofManager::getLitName(lit.negate(), linearizedProofPrefix)
         << ")"
         << " ; " << lit;
      lemmaParen << ")";
    }

    os << "\n    bounded_aff_ax_0_>=_0";
    os << lemmaParen.str();  // Close lemma proof
  }
  else
  {
    os << "\n; Arithmetic proofs which use reasoning more complex than Farkas "
          "proofs and bound tightening are currently unsupported\n"
          "(clausify_false trust)\n";
  }
}

void LFSCArithProof::printSortDeclarations(std::ostream& os, std::ostream& paren) {
  // Nothing to do here at this point.
}

void LFSCArithProof::printTermDeclarations(std::ostream& os, std::ostream& paren) {
  for (ExprSet::const_iterator it = d_declarations.begin();
       it != d_declarations.end();
       ++it)
  {
    Expr term = *it;
    Assert(term.isVariable());
    bool isInt = term.getType().isInteger();
    const char * var_type = isInt ? "int_var" : "real_var";
    os << "(% " << ProofManager::sanitize(term) << " " << var_type << "\n";
    os << "(@ " << CVC4_ARITH_VAR_TERM_PREFIX << ProofManager::sanitize(term)
       << " ";
    os << "(term_" << var_type << " " << ProofManager::sanitize(term) << ")\n";
    paren << ")";
    paren << ")";
  }
}

void LFSCArithProof::printDeferredDeclarations(std::ostream& os, std::ostream& paren) {
  // Nothing to do here at this point.
}

void LFSCArithProof::printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) {
  // Nothing to do here at this point.
}

bool LFSCArithProof::printsAsBool(const Node& n)
{
  // Our boolean variables and constants print as sort Bool.
  // All complex booleans print as formulas.
  return n.getType().isBoolean() and (n.isVar() or n.isConst());
}

TypeNode LFSCArithProof::equalityType(const Expr& left, const Expr& right)
{
  return TypeNode::fromType(!left.getType().isInteger() ? left.getType() : right.getType());
}

} /* CVC4  namespace */
