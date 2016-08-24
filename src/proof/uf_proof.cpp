/*********************                                                        */
/*! \file uf_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "proof/uf_proof.h"
#include "theory/uf/theory_uf.h"
#include <stack>

namespace CVC4 {

inline static Node eqNode(TNode n1, TNode n2) {
  return NodeManager::currentNM()->mkNode(n1.getType().isBoolean() ? kind::IFF : kind::EQUAL, n1, n2);
}

// congrence matching term helper
inline static bool match(TNode n1, TNode n2) {
  Debug("pf::uf") << "match " << n1 << " " << n2 << std::endl;
  if(ProofManager::currentPM()->hasOp(n1)) {
    n1 = ProofManager::currentPM()->lookupOp(n1);
  }
  if(ProofManager::currentPM()->hasOp(n2)) {
    n2 = ProofManager::currentPM()->lookupOp(n2);
  }
  Debug("pf::uf") << "+ match " << n1 << " " << n2 << std::endl;
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


void ProofUF::toStream(std::ostream& out) {
  ProofLetMap map;
  toStream(out, map);
}

void ProofUF::toStream(std::ostream& out, const ProofLetMap& map) {
  Trace("theory-proof-debug") << "; Print UF proof..." << std::endl;
  //AJR : carry this further?
  toStreamLFSC(out, ProofManager::getUfProof(), d_proof, map);
}

void ProofUF::toStreamLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, const ProofLetMap& map) {
  Debug("pf::uf") << "ProofUF::toStreamLFSC starting" << std::endl;
  Debug("lfsc-uf") << "Printing uf proof in LFSC : " << std::endl;
  pf->debug_print("lfsc-uf");
  Debug("lfsc-uf") << std::endl;
  toStreamRecLFSC( out, tp, pf, 0, map );
}

Node ProofUF::toStreamRecLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, unsigned tb, const ProofLetMap& map) {
  Debug("pf::uf") << std::endl << std::endl << "toStreamRecLFSC called. tb = " << tb << " . proof:" << std::endl;
  pf->debug_print("pf::uf");
  Debug("pf::uf") << std::endl;

  if (tb == 0) {
    // Special case: false was an input, so the proof is just "false".
    if (pf->d_id == theory::eq::MERGED_THROUGH_EQUALITY &&
        pf->d_node == NodeManager::currentNM()->mkConst(false)) {
      out << "(clausify_false ";
      out << ProofManager::getLitName(NodeManager::currentNM()->mkConst(false).notNode());
      out << ")" << std::endl;
      return Node();
    }

    Assert(pf->d_id == theory::eq::MERGED_THROUGH_TRANS);
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.size() >= 2);

    int neg = -1;
    theory::eq::EqProof subTrans;
    subTrans.d_id = theory::eq::MERGED_THROUGH_TRANS;
    subTrans.d_node = pf->d_node;

    size_t i = 0;
    while (i < pf->d_children.size()) {
      // Look for the negative clause, with which we will form a contradiction.
      if(!pf->d_children[i]->d_node.isNull() && pf->d_children[i]->d_node.getKind() == kind::NOT) {
        Assert(neg < 0);
        neg = i;
        ++i;
      }

      // Handle congruence closures over equalities.
      else if (pf->d_children[i]->d_id==theory::eq::MERGED_THROUGH_CONGRUENCE && pf->d_children[i]->d_node.isNull()) {
        Debug("pf::uf") << "Handling congruence over equalities" << std::endl;

        // Gather the sequence of consecutive congruence closures.
        std::vector<const theory::eq::EqProof *> congruenceClosures;
        unsigned count;
        Debug("pf::uf") << "Collecting congruence sequence" << std::endl;
        for (count = 0;
             i + count < pf->d_children.size() &&
             pf->d_children[i + count]->d_id==theory::eq::MERGED_THROUGH_CONGRUENCE &&
             pf->d_children[i + count]->d_node.isNull();
             ++count) {
          Debug("pf::uf") << "Found a congruence: " << std::endl;
          pf->d_children[i+count]->debug_print("pf::uf");
          congruenceClosures.push_back(pf->d_children[i+count]);
        }

        Debug("pf::uf") << "Total number of congruences found: " << congruenceClosures.size() << std::endl;

        // Determine if the "target" of the congruence sequence appears right before or right after the sequence.
        bool targetAppearsBefore = true;
        bool targetAppearsAfter = true;

        if ((i == 0) || (i == 1 && neg == 0)) {
          Debug("pf::uf") << "Target does not appear before" << std::endl;
          targetAppearsBefore = false;
        }

        if ((i + count >= pf->d_children.size()) ||
            (!pf->d_children[i + count]->d_node.isNull() &&
             pf->d_children[i + count]->d_node.getKind() == kind::NOT)) {
          Debug("pf::uf") << "Target does not appear after" << std::endl;
          targetAppearsAfter = false;
        }

        // Assert that we have precisely one target clause.
        Assert(targetAppearsBefore != targetAppearsAfter);

        // Begin breaking up the congruences and ordering the equalities correctly.
        std::vector<theory::eq::EqProof *> orderedEqualities;


        // Insert target clause first.
        if (targetAppearsBefore) {
          orderedEqualities.push_back(pf->d_children[i - 1]);
          // The target has already been added to subTrans; remove it.
          subTrans.d_children.pop_back();
        } else {
          orderedEqualities.push_back(pf->d_children[i + count]);
        }

        // Start with the congruence closure closest to the target clause, and work our way back/forward.
        if (targetAppearsBefore) {
          for (unsigned j = 0; j < count; ++j) {
            if (pf->d_children[i + j]->d_children[0]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
              orderedEqualities.insert(orderedEqualities.begin(), pf->d_children[i + j]->d_children[0]);
            if (pf->d_children[i + j]->d_children[1]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(orderedEqualities.end(), pf->d_children[i + j]->d_children[1]);
          }
        } else {
          for (unsigned j = 0; j < count; ++j) {
            if (pf->d_children[i + count - 1 - j]->d_children[0]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
              orderedEqualities.insert(orderedEqualities.begin(), pf->d_children[i + count - 1 - j]->d_children[0]);
            if (pf->d_children[i + count - 1 - j]->d_children[1]->d_id != theory::eq::MERGED_THROUGH_REFLEXIVITY)
              orderedEqualities.insert(orderedEqualities.end(), pf->d_children[i + count - 1 - j]->d_children[1]);
          }
        }

        // Copy the result into the main transitivity proof.
        subTrans.d_children.insert(subTrans.d_children.end(), orderedEqualities.begin(), orderedEqualities.end());

        // Increase i to skip over the children that have been processed.
        i += count;
        if (targetAppearsAfter) {
          ++i;
        }
      }

      // Else, just copy the child proof as is
      else {
        subTrans.d_children.push_back(pf->d_children[i]);
        ++i;
      }
    }

    bool disequalityFound = (neg >= 0);
    if (!disequalityFound) {
      Debug("pf::uf") << "A disequality was NOT found. UNSAT due to merged constants" << std::endl;
      Debug("pf::uf") << "Proof for: " << pf->d_node << std::endl;
      Assert(pf->d_node.getKind() == kind::EQUAL);
      Assert(pf->d_node.getNumChildren() == 2);
      Assert (pf->d_node[0].isConst() && pf->d_node[1].isConst());
    }

    Node n1;
    std::stringstream ss;
    Debug("pf::uf") << "\nsubtrans has " << subTrans.d_children.size() << " children\n";

    if(!disequalityFound || subTrans.d_children.size() >= 2) {
      n1 = toStreamRecLFSC(ss, tp, &subTrans, 1, map);
    } else {
      n1 = toStreamRecLFSC(ss, tp, subTrans.d_children[0], 1, map);
      Debug("pf::uf") << "\nsubTrans unique child " << subTrans.d_children[0]->d_id << " was proven\ngot: " << n1 << std::endl;
    }

    Debug("pf::uf") << "\nhave proven: " << n1 << std::endl;

    out << "(clausify_false (contra _ ";

    if (disequalityFound) {
      Node n2 = pf->d_children[neg]->d_node;
      Assert(n2.getKind() == kind::NOT);
      Debug("pf::uf") << "n2 is " << n2[0] << std::endl;

      if (n2[0].getNumChildren() > 0) { Debug("pf::uf") << "\nn2[0]: " << n2[0][0] << std::endl; }
      if (n1.getNumChildren() > 1) { Debug("pf::uf") << "n1[1]: " << n1[1] << std::endl; }

      if(n2[0].getKind() == kind::APPLY_UF) {
        out << "(trans _ _ _ _ ";

        if (n1[0] == n2[0]) {
          out << "(symm _ _ _ ";
          out << ss.str();
          out << ") ";
        } else {
          Assert(n1[1] == n2[0]);
          out << ss.str();
        }
        out << "(pred_eq_f _ " << ProofManager::getLitName(n2[0]) << ")) t_t_neq_f))" << std::endl;
      } else {
        Assert((n1[0] == n2[0][0] && n1[1] == n2[0][1]) || (n1[1] == n2[0][0] && n1[0] == n2[0][1]));
        if(n1[1] == n2[0][0]) {
          out << "(symm _ _ _ " << ss.str() << ")";
        } else {
          out << ss.str();
        }
        out << " " << ProofManager::getLitName(n2[0]) << "))" << std::endl;
      }
    } else {
      Node n2 = pf->d_node;
      Assert(n2.getKind() == kind::EQUAL);
      Assert((n1[0] == n2[0] && n1[1] == n2[1]) || (n1[1] == n2[0] && n1[0] == n2[1]));

      out << ss.str();
      out << " ";
      ProofManager::getTheoryProofEngine()->printConstantDisequalityProof(out, n1[0].toExpr(), n1[1].toExpr(), map);
      out << "))" << std::endl;
    }

    return Node();
  }

  switch(pf->d_id) {
  case theory::eq::MERGED_THROUGH_CONGRUENCE: {
    Debug("pf::uf") << "\nok, looking at congruence:\n";
    pf->debug_print("pf::uf");
    std::stack<const theory::eq::EqProof*> stk;
    for(const theory::eq::EqProof* pf2 = pf; pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE; pf2 = pf2->d_children[0]) {
      Assert(!pf2->d_node.isNull());
      Assert(pf2->d_node.getKind() == kind::PARTIAL_APPLY_UF || pf2->d_node.getKind() == kind::BUILTIN || pf2->d_node.getKind() == kind::APPLY_UF || pf2->d_node.getKind() == kind::SELECT || pf2->d_node.getKind() == kind::STORE);
      Assert(pf2->d_children.size() == 2);
      out << "(cong _ _ _ _ _ _ ";
      stk.push(pf2);
    }
    Assert(stk.top()->d_children[0]->d_id != theory::eq::MERGED_THROUGH_CONGRUENCE);
    NodeBuilder<> b1(kind::PARTIAL_APPLY_UF), b2(kind::PARTIAL_APPLY_UF);
    const theory::eq::EqProof* pf2 = stk.top();
    stk.pop();
    Assert(pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE);
    Node n1 = toStreamRecLFSC(out, tp, pf2->d_children[0], tb + 1, map);
    out << " ";
    std::stringstream ss;
    Node n2 = toStreamRecLFSC(ss, tp, pf2->d_children[1], tb + 1, map);
    Debug("pf::uf") << "\nok, in FIRST cong[" << stk.size() << "]" << "\n";
    pf2->debug_print("pf::uf");
    Debug("pf::uf") << "looking at " << pf2->d_node << "\n";
    Debug("pf::uf") << "           " << n1 << "\n";
    Debug("pf::uf") << "           " << n2 << "\n";
    int side = 0;
    if(match(pf2->d_node, n1[0])) {
      //if(tb == 1) {
      Debug("pf::uf") << "SIDE IS 0\n";
      //}
      side = 0;
    } else {
      //if(tb == 1) {
      Debug("pf::uf") << "SIDE IS 1\n";
      //}
      if(!match(pf2->d_node, n1[1])) {
      Debug("pf::uf") << "IN BAD CASE, our first subproof is\n";
      pf2->d_children[0]->debug_print("pf::uf");
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
    Debug("pf::uf") << "pf2->d_node " << pf2->d_node << std::endl;
    Debug("pf::uf") << "b1.getNumChildren() " << b1.getNumChildren() << std::endl;
    Debug("pf::uf") << "n1 " << n1 << std::endl;
    Debug("pf::uf") << "n2 " << n2 << std::endl;
    Debug("pf::uf") << "side " << side << std::endl;
    if(pf2->d_node[b1.getNumChildren() - (pf2->d_node.getMetaKind() == kind::metakind::PARAMETERIZED ? 0 : 1)] == n2[side]) {
      b1 << n2[side];
      b2 << n2[1-side];
      out << ss.str();
    } else {
      Assert(pf2->d_node[b1.getNumChildren() - (pf2->d_node.getMetaKind() == kind::metakind::PARAMETERIZED ? 0 : 1)] == n2[1-side]);
      b1 << n2[1-side];
      b2 << n2[side];
      out << "(symm _ _ _ " << ss.str() << ")";
    }
    out << ")";
    while(!stk.empty()) {
      if(tb == 1) {
      Debug("pf::uf") << "\nMORE TO DO\n";
      }
      pf2 = stk.top();
      stk.pop();
      Assert(pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE);
      out << " ";
      ss.str("");
      n2 = toStreamRecLFSC(ss, tp, pf2->d_children[1], tb + 1, map);
      Debug("pf::uf") << "\nok, in cong[" << stk.size() << "]" << "\n";
      Debug("pf::uf") << "looking at " << pf2->d_node << "\n";
      Debug("pf::uf") << "           " << n1 << "\n";
      Debug("pf::uf") << "           " << n2 << "\n";
      Debug("pf::uf") << "           " << b1 << "\n";
      Debug("pf::uf") << "           " << b2 << "\n";
      if(pf2->d_node[b1.getNumChildren()] == n2[side]) {
        b1 << n2[side];
        b2 << n2[1-side];
        out << ss.str();
      } else {
        Assert(pf2->d_node[b1.getNumChildren()] == n2[1-side]);
        b1 << n2[1-side];
        b2 << n2[side];
        out << "(symm _ _ _ " << ss.str() << ")";
      }
      out << ")";
    }
    n1 = b1;
    n2 = b2;
    Debug("pf::uf") << "at end assert, got " << pf2->d_node << "  and  " << n1 << std::endl;
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
      Debug("pf::uf") << "at[2] end assert, got " << pf2->d_node << "  and  " << n1 << std::endl;
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
    Debug("pf::uf") << "\ncong proved: " << n << "\n";
    }
    return n;
  }

  case theory::eq::MERGED_THROUGH_REFLEXIVITY:
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    out << "(refl _ ";
    tp->printTerm(NodeManager::currentNM()->toExpr(pf->d_node), out, map);
    out << ")";
    return eqNode(pf->d_node, pf->d_node);

  case theory::eq::MERGED_THROUGH_EQUALITY:
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    out << ProofManager::getLitName(pf->d_node.negate());
    return pf->d_node;

  case theory::eq::MERGED_THROUGH_TRANS: {
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.size() >= 2);
    std::stringstream ss;
    Debug("pf::uf") << "\ndoing trans proof[[\n";
    pf->debug_print("pf::uf");
    Debug("pf::uf") << "\n";
    Node n1 = toStreamRecLFSC(ss, tp, pf->d_children[0], tb + 1, map);
    Debug("pf::uf") << "\ndoing trans proof, got n1 " << n1 << "\n";
    if(tb == 1) {
      Debug("pf::uf") << "\ntrans proof[0], got n1 " << n1 << "\n";
    }

    bool identicalEqualities = false;
    bool evenLengthSequence;
    Node nodeAfterEqualitySequence;

    std::map<size_t, Node> childToStream;

    for(size_t i = 1; i < pf->d_children.size(); ++i) {
      std::stringstream ss1(ss.str()), ss2;
      ss.str("");

      // It is possible that we've already converted the i'th child to stream. If so,
      // use previously stored result. Otherwise, convert and store.
      Node n2;
      if (childToStream.find(i) != childToStream.end())
        n2 = childToStream[i];
      else {
        n2 = toStreamRecLFSC(ss2, tp, pf->d_children[i], tb + 1, map);
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
      if(n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) {
        if (((n1[0] == n2[0]) && (n1[1] == n2[1])) || ((n1[0] == n2[1]) && (n1[1] == n2[0]))) {
          // We are in a sequence of identical equalities

          Debug("pf::uf") << "Detected identical equalities: " << std::endl << "\t" << n1 << std::endl;

          if (!identicalEqualities) {
            // The sequence of identical equalities has started just now
            identicalEqualities = true;

            Debug("pf::uf") << "The sequence is just beginning. Determining length..." << std::endl;

            // Determine whether the length of this sequence is odd or even.
            evenLengthSequence = true;
            bool sequenceOver = false;
            size_t j = i + 1;

            while (j < pf->d_children.size() && !sequenceOver) {
              std::stringstream dontCare;
              nodeAfterEqualitySequence = toStreamRecLFSC(dontCare, tp, pf->d_children[j], tb + 1, map );

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

              Debug("pf::uf") << "Equality sequence of even length" << std::endl;
              Debug("pf::uf") << "n1 is: " << n1 << std::endl;
              Debug("pf::uf") << "n2 is: " << n2 << std::endl;
              Debug("pf::uf") << "pf-d_node is: " << pf->d_node << std::endl;
              Debug("pf::uf") << "Next node is: " << nodeAfterEqualitySequence << std::endl;

              ss << "(trans _ _ _ _ ";

              // If the sequence is at the very end of the transitivity proof, use pf->d_node to guide us.
              if (!sequenceOver) {
                if (match(n1[0], pf->d_node[0])) {
                  n1 = eqNode(n1[0], n1[0]);
                  ss << ss1.str() << " (symm _ _ _ " << ss1.str() << ")";
                } else if (match(n1[1], pf->d_node[1])) {
                  n1 = eqNode(n1[1], n1[1]);
                  ss << " (symm _ _ _ " << ss1.str() << ")" << ss1.str();
                } else {
                  Debug("pf::uf") << "Error: identical equalities over, but hands don't match what we're proving."
                                     << std::endl;
                  Assert(false);
                }
              } else {
                // We have a "next node". Use it to guide us.

                Assert(nodeAfterEqualitySequence.getKind() == kind::EQUAL ||
                       nodeAfterEqualitySequence.getKind() == kind::IFF);

                if ((n1[0] == nodeAfterEqualitySequence[0]) || (n1[0] == nodeAfterEqualitySequence[1])) {

                  // Eliminate n1[1]
                  ss << ss1.str() << " (symm _ _ _ " << ss1.str() << ")";
                  n1 = eqNode(n1[0], n1[0]);

                } else if ((n1[1] == nodeAfterEqualitySequence[0]) || (n1[1] == nodeAfterEqualitySequence[1])) {

                  // Eliminate n1[0]
                  ss << " (symm _ _ _ " << ss1.str() << ")" << ss1.str();
                  n1 = eqNode(n1[1], n1[1]);

                } else {
                  Debug("pf::uf") << "Error: even length sequence, but I don't know which hand to keep!" << std::endl;
                  Assert(false);
                }
              }

              ss << ")";

            } else {
              Debug("pf::uf") << "Equality sequence length is odd!" << std::endl;
              ss.str(ss1.str());
            }

            Debug("pf::uf") << "Have proven: " << n1 << std::endl;
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

      Debug("pf::uf") << "\ndoing trans proof, got n2 " << n2 << "\n";
      if(tb == 1) {
        Debug("pf::uf") << "\ntrans proof[" << i << "], got n2 " << n2 << "\n";
        Debug("pf::uf") << (n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) << "\n";

        if ((n1.getNumChildren() >= 2) && (n2.getNumChildren() >= 2)) {
          Debug("pf::uf") << n1[0].getId() << " " << n1[1].getId() << " / " << n2[0].getId() << " " << n2[1].getId() << "\n";
          Debug("pf::uf") << n1[0].getId() << " " << n1[0] << "\n";
          Debug("pf::uf") << n1[1].getId() << " " << n1[1] << "\n";
          Debug("pf::uf") << n2[0].getId() << " " << n2[0] << "\n";
          Debug("pf::uf") << n2[1].getId() << " " << n2[1] << "\n";
          Debug("pf::uf") << (n1[0] == n2[0]) << "\n";
          Debug("pf::uf") << (n1[1] == n2[1]) << "\n";
          Debug("pf::uf") << (n1[0] == n2[1]) << "\n";
          Debug("pf::uf") << (n1[1] == n2[0]) << "\n";
        }
      }
      ss << "(trans _ _ _ _ ";

      if((n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) &&
         (n1.getKind() == kind::EQUAL || n1.getKind() == kind::IFF))
        // Both elements of the transitivity rule are equalities/iffs
      {
        if(n1[0] == n2[0]) {
            if(tb == 1) { Debug("pf::uf") << "case 1\n"; }
            n1 = eqNode(n1[1], n2[1]);
            ss << "(symm _ _ _ " << ss1.str() << ") " << ss2.str();
        } else if(n1[1] == n2[1]) {
          if(tb == 1) { Debug("pf::uf") << "case 2\n"; }
          n1 = eqNode(n1[0], n2[0]);
          ss << ss1.str() << " (symm _ _ _ " << ss2.str() << ")";
        } else if(n1[0] == n2[1]) {
            if(tb == 1) { Debug("pf::uf") << "case 3\n"; }
            n1 = eqNode(n2[0], n1[1]);
            ss << ss2.str() << " " << ss1.str();
            if(tb == 1) { Debug("pf::uf") << "++ proved " << n1 << "\n"; }
        } else if(n1[1] == n2[0]) {
          if(tb == 1) { Debug("pf::uf") << "case 4\n"; }
          n1 = eqNode(n1[0], n2[1]);
          ss << ss1.str() << " " << ss2.str();
        } else {
          Warning() << "\n\ntrans proof failure at step " << i << "\n\n";
          Warning() << "0 proves " << n1 << "\n";
          Warning() << "1 proves " << n2 << "\n\n";
          pf->debug_print("pf::uf",0);
          //toStreamRec(Warning.getStream(), pf, 0);
          Warning() << "\n\n";
          Unreachable();
        }
        Debug("pf::uf") << "++ trans proof[" << i << "], now have " << n1 << std::endl;
      } else if(n1.getKind() == kind::EQUAL || n1.getKind() == kind::IFF) {
        // n1 is an equality/iff, but n2 is a predicate
        if(n1[0] == n2) {
          n1 = n1[1].iffNode(NodeManager::currentNM()->mkConst(true));
          ss << "(symm _ _ _ " << ss1.str() << ") (pred_eq_t _ " << ss2.str() << ")";
        } else if(n1[1] == n2) {
          n1 = n1[0].iffNode(NodeManager::currentNM()->mkConst(true));
          ss << ss1.str() << " (pred_eq_t _ " << ss2.str() << ")";
        } else {
          Unreachable();
        }
      } else if(n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) {
        // n2 is an equality/iff, but n1 is a predicate
        if(n2[0] == n1) {
          n1 = n2[1].iffNode(NodeManager::currentNM()->mkConst(true));
          ss << "(symm _ _ _ " << ss2.str() << ") (pred_eq_t _ " << ss1.str() << ")";
        } else if(n2[1] == n1) {
          n1 = n2[0].iffNode(NodeManager::currentNM()->mkConst(true));
          ss << ss2.str() << " (pred_eq_t _ " << ss1.str() << ")";
        } else {
          Unreachable();
        }
      } else {
        // Both n1 and n2 are predicates. Don't know what to do...
        Unreachable();
      }

      ss << ")";
    }
    out << ss.str();
    Debug("pf::uf") << "\n++ trans proof done, have proven " << n1 << std::endl;
    return n1;
  }

  default:
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    Debug("pf::uf") << "theory proof: " << pf->d_node << " by rule " << int(pf->d_id) << std::endl;
    AlwaysAssert(false);
    return pf->d_node;
  }
}

UFProof::UFProof(theory::uf::TheoryUF* uf, TheoryProofEngine* pe)
  : TheoryProof(uf, pe)
{}

void UFProof::registerTerm(Expr term) {
  // already registered
  if (d_declarations.find(term) != d_declarations.end())
    return;

  Type type = term.getType();
  if (type.isSort()) {
    // declare uninterpreted sorts
    d_sorts.insert(type);
  }

  if (term.getKind() == kind::APPLY_UF) {
    Expr function = term.getOperator();
    d_declarations.insert(function);
  }

  if (term.isVariable()) {
    d_declarations.insert(term);
  }

  // recursively declare all other terms
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    // could belong to other theories
    d_proofEngine->registerTerm(term[i]);
  }
}

void LFSCUFProof::printOwnedTerm(Expr term, std::ostream& os, const ProofLetMap& map) {
  Debug("pf::uf") << std::endl << "(pf::uf) LFSCUfProof::printOwnedTerm: term = " << term << std::endl;

  Assert (theory::Theory::theoryOf(term) == theory::THEORY_UF);

  if (term.getKind() == kind::VARIABLE ||
      term.getKind() == kind::SKOLEM) {
    os << term;
    return;
  }

  Assert (term.getKind() == kind::APPLY_UF);
  d_proofEngine->treatBoolsAsFormulas(false);

  if(term.getType().isBoolean()) {
    os << "(p_app ";
  }
  Expr func = term.getOperator();
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    os << "(apply _ _ ";
  }
  os << func << " ";
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    d_proofEngine->printBoundTerm(term[i], os, map);
    os << ")";
  }
  if(term.getType().isBoolean()) {
    os << ")";
  }
  d_proofEngine->treatBoolsAsFormulas(true);
}

void LFSCUFProof::printOwnedSort(Type type, std::ostream& os) {
  Debug("pf::uf") << std::endl << "(pf::uf) LFSCArrayProof::printOwnedSort: type is: " << type << std::endl;

  Assert (type.isSort());
  os << type;
}

void LFSCUFProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren, const ProofLetMap& map) {
  os << " ;; UF Theory Lemma \n;;";
  for (unsigned i = 0; i < lemma.size(); ++i) {
    os << lemma[i] <<" ";
  }
  os <<"\n";
  //os << " (clausify_false trust)";
  UFProof::printTheoryLemmaProof(lemma, os, paren, map);
}

void LFSCUFProof::printSortDeclarations(std::ostream& os, std::ostream& paren) {
  for (TypeSet::const_iterator it = d_sorts.begin(); it != d_sorts.end(); ++it) {
    if (!ProofManager::currentPM()->wasPrinted(*it)) {
      os << "(% " << *it << " sort\n";
      paren << ")";
      ProofManager::currentPM()->markPrinted(*it);
    }
  }
}

void LFSCUFProof::printTermDeclarations(std::ostream& os, std::ostream& paren) {
  // declaring the terms
  Debug("pf::uf") << "LFSCUFProof::printTermDeclarations called" << std::endl;

  for (ExprSet::const_iterator it = d_declarations.begin(); it != d_declarations.end(); ++it) {
    Expr term = *it;

    os << "(% " << ProofManager::sanitize(term) << " ";
    os << "(term ";

    Type type = term.getType();
    if (type.isFunction()) {
      std::ostringstream fparen;
      FunctionType ftype = (FunctionType)type;
      std::vector<Type> args = ftype.getArgTypes();
      args.push_back(ftype.getRangeType());
      os << "(arrow";
      for (unsigned i = 0; i < args.size(); i++) {
        Type arg_type = args[i];
        os << " ";
        d_proofEngine->printSort(arg_type, os);
        if (i < args.size() - 2) {
          os << " (arrow";
          fparen << ")";
        }
      }
      os << fparen.str() << "))\n";
    } else {
      Assert (term.isVariable());
      os << type << ")\n";
    }
    paren << ")";
  }

  Debug("pf::uf") << "LFSCUFProof::printTermDeclarations done" << std::endl;
}

void LFSCUFProof::printDeferredDeclarations(std::ostream& os, std::ostream& paren) {
  // Nothing to do here at this point.
}

void LFSCUFProof::printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) {
  // Nothing to do here at this point.
}

} /* namespace CVC4 */
