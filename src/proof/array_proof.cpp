/*********************                                                        */
/*! \file array_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz
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
#include "proof/array_proof.h"
#include "theory/arrays/theory_arrays.h"
#include <stack>

namespace CVC4 {

inline static Node eqNode(TNode n1, TNode n2) {
  return NodeManager::currentNM()->mkNode(n1.getType().isBoolean() ? kind::IFF : kind::EQUAL, n1, n2);
}

// congrence matching term helper
inline static bool match(TNode n1, TNode n2) {
  Debug("mgd") << "match " << n1 << " " << n2 << std::endl;
  if(ProofManager::currentPM()->hasOp(n1)) {
    n1 = ProofManager::currentPM()->lookupOp(n1);
  }
  if(ProofManager::currentPM()->hasOp(n2)) {
    n2 = ProofManager::currentPM()->lookupOp(n2);
  }
  Debug("mgd") << "+ match " << n1 << " " << n2 << std::endl;
  Debug("pf::array") << "+ match: step 1" << std::endl;
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
    if (!((n1.getKind() == kind::SELECT && n2.getKind() == kind::PARTIAL_SELECT_0) ||
          (n1.getKind() == kind::SELECT && n2.getKind() == kind::PARTIAL_SELECT_1) ||
          (n1.getKind() == kind::PARTIAL_SELECT_1 && n2.getKind() == kind::SELECT) ||
          (n1.getKind() == kind::PARTIAL_SELECT_1 && n2.getKind() == kind::PARTIAL_SELECT_0) ||
          (n1.getKind() == kind::PARTIAL_SELECT_0 && n2.getKind() == kind::SELECT) ||
          (n1.getKind() == kind::PARTIAL_SELECT_0 && n2.getKind() == kind::PARTIAL_SELECT_1)
          )) {
      return false;
    }
  }

  for(size_t i = 0; i < n1.getNumChildren() && i < n2.getNumChildren(); ++i) {
    if(n1[i] != n2[i]) {
      return false;
    }
  }

  return true;
}

void ProofArray::setRowMergeTag(unsigned tag) {
  d_reasonRow = tag;
  d_proofPrinter.d_row = tag;
}

void ProofArray::setRow1MergeTag(unsigned tag) {
  d_reasonRow1 = tag;
  d_proofPrinter.d_row1 = tag;
}

void ProofArray::setExtMergeTag(unsigned tag) {
  d_reasonExt = tag;
  d_proofPrinter.d_ext = tag;
}

unsigned ProofArray::getRowMergeTag() const {
  return d_reasonRow;
}

unsigned ProofArray::getRow1MergeTag() const {
  return d_reasonRow1;
}

unsigned ProofArray::getExtMergeTag() const {
  return d_reasonExt;
}

void ProofArray::toStream(std::ostream& out) {
  ProofLetMap map;
  toStream(out, map);
}

void ProofArray::toStream(std::ostream& out, const ProofLetMap& map) {
  Trace("pf::array") << "; Print Array proof..." << std::endl;
  toStreamLFSC(out, ProofManager::getArrayProof(), d_proof, map);
  Debug("pf::array") << "; Print Array proof done!" << std::endl;
}

void ProofArray::toStreamLFSC(std::ostream& out, TheoryProof* tp, theory::eq::EqProof* pf, const ProofLetMap& map) {
  Debug("pf::array") << "Printing array proof in LFSC : " << std::endl;
  pf->debug_print("pf::array", 0, &d_proofPrinter);
  Debug("pf::array") << std::endl;
  toStreamRecLFSC( out, tp, pf, 0, map );
  Debug("pf::array") << "Printing array proof in LFSC DONE" << std::endl;
}

Node ProofArray::toStreamRecLFSC(std::ostream& out,
                                 TheoryProof* tp,
                                 theory::eq::EqProof* pf,
                                 unsigned tb,
                                 const ProofLetMap& map) {

  Debug("pf::array") << std::endl << std::endl << "toStreamRecLFSC called. tb = " << tb << " . proof:" << std::endl;
  pf->debug_print("pf::array", 0, &d_proofPrinter);
  Debug("pf::array") << std::endl;

  if(tb == 0) {
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
        Debug("pf::array") << "Handling congruence over equalities" << std::endl;

        // Gather the sequence of consecutive congruence closures.
        std::vector<const theory::eq::EqProof *> congruenceClosures;
        unsigned count;
        Debug("pf::array") << "Collecting congruence sequence" << std::endl;
        for (count = 0;
             i + count < pf->d_children.size() &&
               pf->d_children[i + count]->d_id==theory::eq::MERGED_THROUGH_CONGRUENCE &&
               pf->d_children[i + count]->d_node.isNull();
             ++count) {
          Debug("pf::array") << "Found a congruence: " << std::endl;
          pf->d_children[i+count]->debug_print("pf::array", 0, &d_proofPrinter);
          congruenceClosures.push_back(pf->d_children[i+count]);
        }

        Debug("pf::array") << "Total number of congruences found: " << congruenceClosures.size() << std::endl;

        // Determine if the "target" of the congruence sequence appears right before or right after the sequence.
        bool targetAppearsBefore = true;
        bool targetAppearsAfter = true;

        if ((i == 0) || (i == 1 && neg == 0)) {
          Debug("pf::array") << "Target does not appear before" << std::endl;
          targetAppearsBefore = false;
        }

        if ((i + count >= pf->d_children.size()) ||
            (!pf->d_children[i + count]->d_node.isNull() &&
             pf->d_children[i + count]->d_node.getKind() == kind::NOT)) {
          Debug("pf::array") << "Target does not appear after" << std::endl;
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
      Debug("pf::array") << "A disequality was NOT found. UNSAT due to merged constants" << std::endl;
      Debug("pf::array") << "Proof for: " << pf->d_node << std::endl;
      Assert(pf->d_node.getKind() == kind::EQUAL);
      Assert(pf->d_node.getNumChildren() == 2);
      Assert (pf->d_node[0].isConst() && pf->d_node[1].isConst());
    }

    Node n1;
    std::stringstream ss, ss2;
    //Assert(subTrans.d_children.size() == pf->d_children.size() - 1);
    Debug("mgdx") << "\nsubtrans has " << subTrans.d_children.size() << " children\n";
    if(!disequalityFound || pf->d_children.size() > 2) {
      n1 = toStreamRecLFSC(ss, tp, &subTrans, 1, map);
    } else {
      n1 = toStreamRecLFSC(ss, tp, subTrans.d_children[0], 1, map);
      Debug("mgdx") << "\nsubTrans unique child " << subTrans.d_children[0]->d_id << " was proven\ngot: " << n1 << std::endl;
    }

    out << "(clausify_false (contra _ ";

    if (disequalityFound) {
      Node n2 = pf->d_children[neg]->d_node;
      Assert(n2.getKind() == kind::NOT);
      Debug("mgdx") << "\nhave proven: " << n1 << std::endl;
      Debug("mgdx") << "n2 is " << n2 << std::endl;
      Debug("mgdx") << "n2->d_id is " << pf->d_children[neg]->d_id << std::endl;
      Debug("mgdx") << "n2[0] is " << n2[0] << std::endl;

      if (n2[0].getNumChildren() > 0) { Debug("mgdx") << "\nn2[0]: " << n2[0][0] << std::endl; }
      if (n1.getNumChildren() > 1) { Debug("mgdx") << "n1[1]: " << n1[1] << std::endl; }

      if ((pf->d_children[neg]->d_id == d_reasonExt) ||
          (pf->d_children[neg]->d_id == theory::eq::MERGED_THROUGH_TRANS)) {
        // Ext case: The negative node was created by an EXT rule; e.g. it is a[k]!=b[k], due to a!=b.
        out << ss.str();
        out << " ";
        toStreamRecLFSC(ss2, tp, pf->d_children[neg], 1, map);
        out << ss2.str();
      } else if (n2[0].getKind() == kind::APPLY_UF) {
        out << "(trans _ _ _ _ ";
        out << "(symm _ _ _ ";
        out << ss.str();
        out << ") (pred_eq_f _ " << ProofManager::getLitName(n2[0]) << ")) t_t_neq_f))" << std::endl;
      } else {
        Assert((n1[0] == n2[0][0] && n1[1] == n2[0][1]) || (n1[1] == n2[0][0] && n1[0] == n2[0][1]));
        if(n1[1] == n2[0][0]) {
          out << "(symm _ _ _ " << ss.str() << ")";
        } else {
          out << ss.str();
        }
        Debug("pf::array") << "ArrayProof::toStream: getLitName( " << n2[0] << " ) = " <<
          ProofManager::getLitName(n2[0]) << std::endl;

        out << " " << ProofManager::getLitName(n2[0]);
      }
    } else {
      Node n2 = pf->d_node;
      Assert(n2.getKind() == kind::EQUAL);
      Assert((n1[0] == n2[0] && n1[1] == n2[1]) || (n1[1] == n2[0] && n1[0] == n2[1]));

      out << ss.str();
      out << " ";
      ProofManager::getTheoryProofEngine()->printConstantDisequalityProof(out,
                                                                          n1[0].toExpr(),
                                                                          n1[1].toExpr(),
                                                                          map);
    }

    out << "))" << std::endl;
    return Node();
  }

  if (pf->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE) {
    Debug("mgd") << "\nok, looking at congruence:\n";
    pf->debug_print("mgd", 0, &d_proofPrinter);
    std::stack<const theory::eq::EqProof*> stk;
    for(const theory::eq::EqProof* pf2 = pf; pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE; pf2 = pf2->d_children[0]) {
      Assert(!pf2->d_node.isNull());
      Assert(pf2->d_node.getKind() == kind::PARTIAL_APPLY_UF ||
             pf2->d_node.getKind() == kind::BUILTIN ||
             pf2->d_node.getKind() == kind::APPLY_UF ||
             pf2->d_node.getKind() == kind::SELECT ||
             pf2->d_node.getKind() == kind::PARTIAL_SELECT_0 ||
             pf2->d_node.getKind() == kind::PARTIAL_SELECT_1 ||
             pf2->d_node.getKind() == kind::STORE);

      Assert(pf2->d_children.size() == 2);
      out << "(cong _ _ _ _ _ _ ";
      stk.push(pf2);
    }
    Assert(stk.top()->d_children[0]->d_id != theory::eq::MERGED_THROUGH_CONGRUENCE);
    //    NodeBuilder<> b1(kind::PARTIAL_APPLY_UF), b2(kind::PARTIAL_APPLY_UF);
    NodeBuilder<> b1, b2;

    const theory::eq::EqProof* pf2 = stk.top();
    stk.pop();
    Assert(pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE);
    Node n1 = toStreamRecLFSC(out, tp, pf2->d_children[0], tb + 1, map);
    out << " ";
    std::stringstream ss;
    Node n2 = toStreamRecLFSC(ss, tp, pf2->d_children[1], tb + 1, map);


    Debug("mgd") << "\nok, in FIRST cong[" << stk.size() << "]" << "\n";
    pf2->debug_print("mgd", 0, &d_proofPrinter);
    // Temp
    Debug("mgd") << "n1 is a proof for: " << pf2->d_children[0]->d_node << ". It is: " << n1 << std::endl;
    Debug("mgd") << "n2 is a proof for: " << pf2->d_children[1]->d_node << ". It is: " << n2 << std::endl;
    //
    Debug("mgd") << "looking at " << pf2->d_node << "\n";
    Debug("mgd") << "           " << n1 << "\n";
    Debug("mgd") << "           " << n2 << "\n";

    int side = 0;
    if(match(pf2->d_node, n1[0])) {
      Debug("mgd") << "SIDE IS 0\n";
      side = 0;
    } else {
      Debug("mgd") << "SIDE IS 1\n";
      if(!match(pf2->d_node, n1[1])) {
        Debug("mgd") << "IN BAD CASE, our first subproof is\n";
        pf2->d_children[0]->debug_print("mgd", 0, &d_proofPrinter);
      }
      Assert(match(pf2->d_node, n1[1]));
      side = 1;
    }

    if(n1[side].getKind() == kind::APPLY_UF ||
       n1[side].getKind() == kind::PARTIAL_APPLY_UF ||
       n1[side].getKind() == kind::SELECT ||
       n1[side].getKind() == kind::PARTIAL_SELECT_1 ||
       n1[side].getKind() == kind::STORE) {
      if(n1[side].getKind() == kind::APPLY_UF || n1[side].getKind() == kind::PARTIAL_APPLY_UF) {
        b1 << kind::PARTIAL_APPLY_UF;
        b1 << n1[side].getOperator();
      } else if (n1[side].getKind() == kind::SELECT || n1[side].getKind() == kind::PARTIAL_SELECT_1) {
        // b1 << n1[side].getKind();
        b1 << kind::SELECT;
      } else {
        b1 << kind::PARTIAL_APPLY_UF;
        b1 << ProofManager::currentPM()->mkOp(n1[side].getOperator());
      }
      b1.append(n1[side].begin(), n1[side].end());
    }
    else if (n1[side].getKind() == kind::PARTIAL_SELECT_0) {
      b1 << kind::PARTIAL_SELECT_1;
    } else {
      b1 << n1[side];
    }

    if(n1[1-side].getKind() == kind::PARTIAL_APPLY_UF ||
       n1[1-side].getKind() == kind::APPLY_UF ||
       n1[1-side].getKind() == kind::SELECT ||
       n1[1-side].getKind() == kind::PARTIAL_SELECT_1 ||
       n1[1-side].getKind() == kind::STORE) {
      if(n1[1-side].getKind() == kind::APPLY_UF ||
         n1[1-side].getKind() == kind::PARTIAL_APPLY_UF) {
        b2 << kind::PARTIAL_APPLY_UF;
        b2 << n1[1-side].getOperator();
      } else if (n1[1-side].getKind() == kind::SELECT || n1[1-side].getKind() == kind::PARTIAL_SELECT_1) {
        // b2 << n1[1-side].getKind();
        b2 << kind::SELECT;
      } else {
        b2 << kind::PARTIAL_APPLY_UF;
        b2 << ProofManager::currentPM()->mkOp(n1[1-side].getOperator());
      }
      b2.append(n1[1-side].begin(), n1[1-side].end());
    } else if (n1[1-side].getKind() == kind::PARTIAL_SELECT_0) {
      b2 << kind::PARTIAL_SELECT_1;
    } else {
      b2 << n1[1-side];
    }
    Debug("mgd") << "pf2->d_node " << pf2->d_node << std::endl;
    Debug("mgd") << "b1.getNumChildren() " << b1.getNumChildren() << std::endl;
    Debug("mgd") << "n1 " << n1 << std::endl;
    Debug("mgd") << "n2 " << n2 << std::endl;
    // These debug prints can cause a problem if we're constructing a SELECT node and it doesn't have enough
    // children yet.
    // Debug("mgd") << "b1 " << b1 << std::endl;
    // Debug("mgd") << "b2 " << b2 << std::endl;
    Debug("mgd") << "side " << side << std::endl;
    Debug("mgd") << "pf2->d_node's number of children: " << pf2->d_node.getNumChildren() << std::endl;
    Debug("mgd") << "pf2->d_node's meta kind: " << pf2->d_node.getMetaKind() << std::endl;
    Debug("mgd") << "Is this meta kind considered parameterized? " << (pf2->d_node.getMetaKind() == kind::metakind::PARAMETERIZED) << std::endl;

    if(pf2->d_node[b1.getNumChildren() +
                   (n1[side].getKind() == kind::PARTIAL_SELECT_0 ? 1 : 0) +
                   (n1[side].getKind() == kind::PARTIAL_SELECT_1 ? 1 : 0) -
                   (pf2->d_node.getMetaKind() == kind::metakind::PARAMETERIZED ? 0 : 1)] == n2[side]) {
      b1 << n2[side];
      b2 << n2[1-side];
      out << ss.str();
    } else {
      Assert(pf2->d_node[b1.getNumChildren() +
                         (n1[side].getKind() == kind::PARTIAL_SELECT_0 ? 1 : 0) +
                         (n1[side].getKind() == kind::PARTIAL_SELECT_1 ? 1 : 0) -
                         (pf2->d_node.getMetaKind() == kind::metakind::PARAMETERIZED ? 0 : 1)] == n2[1-side]);
      b1 << n2[1-side];
      b2 << n2[side];
      out << "(symm _ _ _ " << ss.str() << ")";
    }

    Debug("mgd") << "After first insertion:" << std::endl;
    Debug("mgd") << "b1 " << b1 << std::endl;
    Debug("mgd") << "b2 " << b2 << std::endl;

    out << ")";
    while(!stk.empty()) {

      Debug("mgd") << "\nMORE TO DO\n";

      pf2 = stk.top();
      stk.pop();
      Assert(pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE);
      out << " ";
      ss.str("");
      n2 = toStreamRecLFSC(ss, tp, pf2->d_children[1], tb + 1, map);

      Debug("mgd") << "\nok, in cong[" << stk.size() << "]" << "\n";
      Debug("mgd") << "looking at " << pf2->d_node << "\n";
      Debug("mgd") << "           " << n1 << "\n";
      Debug("mgd") << "           " << n2 << "\n";
      Debug("mgd") << "           " << b1 << "\n";
      Debug("mgd") << "           " << b2 << "\n";
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

    Debug("mgd") << "at end assert!" << std::endl
                 << "pf2->d_node = " << pf2->d_node << std::endl
                 << "n1 (assigned from b1) = " << n1 << std::endl
                 << "n2 (assigned from b2) = " << n2 << std::endl;

    if(pf2->d_node.getKind() == kind::PARTIAL_APPLY_UF) {
      Assert(n1 == pf2->d_node);
    }

    Debug("mgd") << "n1.getOperator().getType().getNumChildren() = "
                 << n1.getOperator().getType().getNumChildren() << std::endl;
    Debug("mgd") << "n1.getNumChildren() + 1 = "
                 << n1.getNumChildren() + 1 << std::endl;

    Assert(!((n1.getKind() == kind::PARTIAL_SELECT_0 && n1.getNumChildren() == 2)));
    if (n1.getKind() == kind::PARTIAL_SELECT_1 && n1.getNumChildren() == 2) {
      Debug("mgd") << "Finished a SELECT. Updating.." << std::endl;
      b1.clear(kind::SELECT);
      b1.append(n1.begin(), n1.end());
      n1 = b1;
      Debug("mgd") << "New n1: " << n1 << std::endl;
      // } else if (n1.getKind() == kind::PARTIAL_SELECT_0 && n1.getNumChildren() == 1) {
      //   Debug("mgd") << "Finished a PARTIAL_SELECT_1. Updating.." << std::endl;
      //   b1.clear(kind::PARTIAL_SELECT_1);
      //   b1.append(n1.begin(), n1.end());
      //   n1 = b1;
      //   Debug("mgd") << "New n1: " << n1 << std::endl;
      // } else
    } else if(n1.getOperator().getType().getNumChildren() == n1.getNumChildren() + 1) {
      if(ProofManager::currentPM()->hasOp(n1.getOperator())) {
        b1.clear(ProofManager::currentPM()->lookupOp(n2.getOperator()).getConst<Kind>());
      } else {
        b1.clear(kind::APPLY_UF);
        b1 << n1.getOperator();
      }
      b1.append(n1.begin(), n1.end());
      n1 = b1;
      Debug("mgd") << "at[2] end assert, got " << pf2->d_node << "  and  " << n1 << std::endl;
      if(pf2->d_node.getKind() == kind::APPLY_UF) {
        Assert(n1 == pf2->d_node);
      }
    }

    Debug("mgd") << "n2.getOperator().getType().getNumChildren() = "
                 << n2.getOperator().getType().getNumChildren() << std::endl;
    Debug("mgd") << "n2.getNumChildren() + 1 = "
                 << n2.getNumChildren() + 1 << std::endl;

    Assert(!((n2.getKind() == kind::PARTIAL_SELECT_0 && n2.getNumChildren() == 2)));
    if (n2.getKind() == kind::PARTIAL_SELECT_1 && n2.getNumChildren() == 2) {
      Debug("mgd") << "Finished a SELECT. Updating.." << std::endl;
      b2.clear(kind::SELECT);
      b2.append(n2.begin(), n2.end());
      n2 = b2;
      Debug("mgd") << "New n2: " << n2 << std::endl;
      // } else if (n2.getKind() == kind::PARTIAL_SELECT_0 && n2.getNumChildren() == 1) {
      //   Debug("mgd") << "Finished a PARTIAL_SELECT_1. Updating.." << std::endl;
      //   b2.clear(kind::PARTIAL_SELECT_1);
      //   b2.append(n2.begin(), n2.end());
      //   n2 = b2;
      //   Debug("mgd") << "New n2: " << n2 << std::endl;
      // } else
    } else if(n2.getOperator().getType().getNumChildren() == n2.getNumChildren() + 1) {
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

    Debug("mgdx") << "\ncong proved: " << n << "\n";
    return n;
  }

  else if (pf->d_id == theory::eq::MERGED_THROUGH_REFLEXIVITY) {
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    out << "(refl _ ";
    tp->printTerm(NodeManager::currentNM()->toExpr(pf->d_node), out, map);
    out << ")";
    return eqNode(pf->d_node, pf->d_node);
  }

  else if (pf->d_id == theory::eq::MERGED_THROUGH_EQUALITY) {
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    Debug("pf::array") << "ArrayProof::toStream: getLitName( " << pf->d_node.negate() << " ) = " <<
      ProofManager::getLitName(pf->d_node.negate()) << std::endl;
    out << ProofManager::getLitName(pf->d_node.negate());
    return pf->d_node;
  }

  else if (pf->d_id == theory::eq::MERGED_THROUGH_CONSTANTS) {
    Debug("pf::array") << "Proof for: " << pf->d_node << std::endl;
    Assert(pf->d_node.getKind() == kind::NOT);
    Node n = pf->d_node[0];
    Assert(n.getKind() == kind::EQUAL);
    Assert(n.getNumChildren() == 2);
    Assert(n[0].isConst() && n[1].isConst());

    ProofManager::getTheoryProofEngine()->printConstantDisequalityProof(out,
                                                                        n[0].toExpr(),
                                                                        n[1].toExpr(),
                                                                        map);
    return pf->d_node;
  }

  else if (pf->d_id == theory::eq::MERGED_THROUGH_TRANS) {
    bool firstNeg = false;
    bool secondNeg = false;

    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.size() >= 2);
    std::stringstream ss;
    Debug("mgd") << "\ndoing trans proof[[\n";
    pf->debug_print("mgd", 0, &d_proofPrinter);
    Debug("mgd") << "\n";
    Node n1 = toStreamRecLFSC(ss, tp, pf->d_children[0], tb + 1, map);
    Debug("mgd") << "\ndoing trans proof, got n1 " << n1 << "\n";
    if(tb == 1) {
      Debug("mgdx") << "\ntrans proof[0], got n1 " << n1 << "\n";
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

      Debug("mgd") << "\ndoing trans proof, got (first) n2 " << n2 << "\n";

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

          Debug("pf::array") << "Detected identical equalities: " << std::endl << "\t" << n1 << std::endl;

          if (!identicalEqualities) {
            // The sequence of identical equalities has started just now
            identicalEqualities = true;

            Debug("pf::array") << "The sequence is just beginning. Determining length..." << std::endl;

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

              Debug("pf::array") << "Equality sequence of even length" << std::endl;
              Debug("pf::array") << "n1 is: " << n1 << std::endl;
              Debug("pf::array") << "n2 is: " << n2 << std::endl;
              Debug("pf::array") << "pf-d_node is: " << pf->d_node << std::endl;
              Debug("pf::array") << "Next node is: " << nodeAfterEqualitySequence << std::endl;

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
                  Debug("pf::array") << "Error: identical equalities over, but hands don't match what we're proving."
                                     << std::endl;
                  Assert(false);
                }
              } else {
                // We have a "next node". Use it to guide us.
                if (nodeAfterEqualitySequence.getKind() == kind::NOT) {
                  nodeAfterEqualitySequence = nodeAfterEqualitySequence[0];
                }

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
                  Debug("pf::array") << "Error: even length sequence, but I don't know which hand to keep!" << std::endl;
                  Assert(false);
                }
              }

              ss << ")";

            } else {
              Debug("pf::array") << "Equality sequence length is odd!" << std::endl;
              ss.str(ss1.str());
            }

            Debug("pf::array") << "Have proven: " << n1 << std::endl;
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

      Debug("mgd") << "\ndoing trans proof, got n2 " << n2 << "\n";
      if(tb == 1) {
        Debug("mgdx") << "\ntrans proof[" << i << "], got n2 " << n2 << "\n";
        Debug("mgdx") << (n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) << "\n";

        if ((n1.getNumChildren() >= 2) && (n2.getNumChildren() >= 2)) {
          Debug("mgdx") << n1[0].getId() << " " << n1[1].getId() << " / " << n2[0].getId() << " " << n2[1].getId() << "\n";
          Debug("mgdx") << n1[0].getId() << " " << n1[0] << "\n";
          Debug("mgdx") << n1[1].getId() << " " << n1[1] << "\n";
          Debug("mgdx") << n2[0].getId() << " " << n2[0] << "\n";
          Debug("mgdx") << n2[1].getId() << " " << n2[1] << "\n";
          Debug("mgdx") << (n1[0] == n2[0]) << "\n";
          Debug("mgdx") << (n1[1] == n2[1]) << "\n";
          Debug("mgdx") << (n1[0] == n2[1]) << "\n";
          Debug("mgdx") << (n1[1] == n2[0]) << "\n";
        }
      }

      // We can hadnle one of the equalities being negative, but not both
      Assert((n1.getKind() != kind::NOT) || (n2.getKind() != kind::NOT));

      firstNeg = false;
      secondNeg = false;

      if (n1.getKind() == kind::NOT) {
        Debug("mgdx") << "n1 is negative" << std::endl;
        Debug("pf::array") << "n1 = " << n1 << ", n2 = " << n2 << std::endl;
        firstNeg = true;
        ss << "(negtrans1 _ _ _ _ ";
        n1 = n1[0];
      } else if (n2.getKind() == kind::NOT) {
        Debug("mgdx") << "n2 is negative" << std::endl;
        Debug("pf::array") << "n1 = " << n1 << ", n2 = " << n2 << std::endl;
        secondNeg = true;
        ss << "(negtrans2 _ _ _ _ ";
        n2 = n2[0];
      } else {
        ss << "(trans _ _ _ _ ";
      }

      if((n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) &&
         (n1.getKind() == kind::EQUAL || n1.getKind() == kind::IFF))
        // Both elements of the transitivity rule are equalities/iffs
      {
        if(n1[0] == n2[0]) {
          if(tb == 1) { Debug("mgdx") << "case 1\n"; }
          n1 = eqNode(n1[1], n2[1]);
          ss << (firstNeg ? "(negsymm _ _ _ " : "(symm _ _ _ ") << ss1.str() << ") " << ss2.str();
        } else if(n1[1] == n2[1]) {
          if(tb == 1) { Debug("mgdx") << "case 2\n"; }
          n1 = eqNode(n1[0], n2[0]);
          ss << ss1.str() << (secondNeg ? " (negsymm _ _ _ " : " (symm _ _ _ " ) << ss2.str() << ")";
        } else if(n1[0] == n2[1]) {
          if(tb == 1) { Debug("mgdx") << "case 3\n"; }
          if(!firstNeg && !secondNeg) {
            n1 = eqNode(n2[0], n1[1]);
            ss << ss2.str() << " " << ss1.str();
          } else if (firstNeg) {
            n1 = eqNode(n1[1], n2[0]);
            ss << " (negsymm _ _ _ " << ss1.str() << ") (symm _ _ _ " << ss2.str() << ")";
          } else {
            Assert(secondNeg);
            n1 = eqNode(n1[1], n2[0]);
            ss << " (symm _ _ _ " << ss1.str() << ") (negsymm _ _ _ " << ss2.str() << ")";
          }
          if(tb == 1) { Debug("mgdx") << "++ proved " << n1 << "\n"; }
        } else if(n1[1] == n2[0]) {
          if(tb == 1) { Debug("mgdx") << "case 4\n"; }
          n1 = eqNode(n1[0], n2[1]);
          ss << ss1.str() << " " << ss2.str();
        } else {
          Warning() << "\n\ntrans proof failure at step " << i << "\n\n";
          Warning() << "0 proves " << n1 << "\n";
          Warning() << "1 proves " << n2 << "\n\n";
          pf->debug_print("mgdx", 0, &d_proofPrinter);
          //toStreamRec(Warning.getStream(), pf, 0);
          Warning() << "\n\n";
          Unreachable();
        }
        Debug("mgd") << "++ trans proof[" << i << "], now have " << n1 << std::endl;
      } else if(n1.getKind() == kind::EQUAL || n1.getKind() == kind::IFF) {
        // n1 is an equality/iff, but n2 is a predicate
        if(n1[0] == n2) {
          n1 = n1[1];
          ss << (firstNeg ? "(negsymm _ _ _ " : "(symm _ _ _ ")
             << ss1.str() << ") (pred_eq_t _ " << ss2.str() << ")";
        } else if(n1[1] == n2) {
          n1 = n1[0];
          ss << ss1.str() << " (pred_eq_t _ " << ss2.str() << ")";
        } else {
          Unreachable();
        }
      } else if(n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) {
        // n2 is an equality/iff, but n1 is a predicate
        if(n2[0] == n1) {
          n1 = n2[1];
          ss << (secondNeg ? "(negsymm _ _ _ " : "(symm _ _ _ ")
             << ss2.str() << ") (pred_eq_t _ " << ss1.str() << ")";
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

      if (firstNeg || secondNeg) {
        n1 = (n1.getKind() == kind::NOT) ? n1[0] : n1.notNode();
      }
    }

    out << ss.str();
    Debug("mgd") << "\n++ trans proof done, have proven " << n1 << std::endl;
    //return (firstNeg || secondNeg) ? n1.notNode() : n1;
    return n1;
  }

  else if (pf->d_id == d_reasonRow) {
    Debug("mgd") << "row lemma: " << pf->d_node << std::endl;
    Assert(pf->d_node.getKind() == kind::EQUAL);


    if (pf->d_node[1].getKind() == kind::SELECT) {
      // This is the case where ((a[i]:=t)[k] == a[k]), and the sub-proof explains why (i != k).
      TNode t1, t2, t3, t4;
      Node ret;
      if(pf->d_node[1].getKind() == kind::SELECT &&
         pf->d_node[1][0].getKind() == kind::STORE &&
         pf->d_node[0].getKind() == kind::SELECT &&
         pf->d_node[0][0] == pf->d_node[1][0][0] &&
         pf->d_node[0][1] == pf->d_node[1][1]) {
        t2 = pf->d_node[1][0][1];
        t3 = pf->d_node[1][1];
        t1 = pf->d_node[0][0];
        t4 = pf->d_node[1][0][2];
        ret = pf->d_node[1].eqNode(pf->d_node[0]);
        Debug("mgd") << "t1 " << t1 << "\nt2 " << t2 << "\nt3 " << t3 << "\nt4 " << t4 << "\n";
      } else {
        Assert(pf->d_node[0].getKind() == kind::SELECT &&
               pf->d_node[0][0].getKind() == kind::STORE &&
               pf->d_node[1].getKind() == kind::SELECT &&
               pf->d_node[1][0] == pf->d_node[0][0][0] &&
               pf->d_node[1][1] == pf->d_node[0][1]);
        t2 = pf->d_node[0][0][1];
        t3 = pf->d_node[0][1];
        t1 = pf->d_node[1][0];
        t4 = pf->d_node[0][0][2];
        ret = pf->d_node;
        Debug("mgd") << "t1 " << t1 << "\nt2 " << t2 << "\nt3 " << t3 << "\nt4 " << t4 << "\n";
      }

      // inner index != outer index
      // t3 is the outer index

      Assert(pf->d_children.size() == 1);
      std::stringstream ss;
      Node subproof = toStreamRecLFSC(ss, tp, pf->d_children[0], tb + 1, map);

      out << "(row _ _ ";
      tp->printTerm(t2.toExpr(), out, map);
      out << " ";
      tp->printTerm(t3.toExpr(), out, map);
      out << " ";
      tp->printTerm(t1.toExpr(), out, map);
      out << " ";
      tp->printTerm(t4.toExpr(), out, map);
      out << " ";


      Debug("pf::array") << "pf->d_children[0]->d_node is: " << pf->d_children[0]->d_node
                         << ". t3 is: " << t3 << std::endl
                         << "subproof is: " << subproof << std::endl;

      Debug("pf::array") << "Subproof is: " << ss.str() << std::endl;

      // The subproof needs to show that t2 != t3. This can either be a direct disequality,
      // or, if (wlog) t2 is constant, it can show that t3 is equal to another constant.
      if (subproof.getKind() == kind::NOT) {
        // The subproof is for t2 != t3 (or t3 != t2)
        if (subproof[0][1] == t3) {
          Debug("pf::array") << "Dont need symmetry!" << std::endl;
          out << ss.str();
        } else {
          Debug("pf::array") << "Need symmetry!" << std::endl;
          out << "(negsymm _ _ _ " << ss.str() << ")";
        }
      } else {
        // Either t2 or t3 is a constant.
        Assert(subproof.getKind() == kind::EQUAL);
        Assert(subproof[0].isConst() || subproof[1].isConst());
        Assert(t2.isConst() || t3.isConst());
        Assert(!(t2.isConst() && t3.isConst()));

        bool t2IsConst = t2.isConst();
        if (subproof[0].isConst()) {
          if (t2IsConst) {
            // (t3 == subproof[1]) == subproof[0] != t2
            // goal is t2 != t3
            // subproof already shows constant = t3
            Assert(t3 == subproof[1]);
            out << "(negtrans _ _ _ _ ";
            tp->printConstantDisequalityProof(out, t2.toExpr(), subproof[0].toExpr(), map);
            out << " ";
            out << ss.str();
            out << ")";
          } else {
            Assert(t2 == subproof[1]);
            out << "(negsymm _ _ _ ";
            out << "(negtrans _ _ _ _ ";
            tp->printConstantDisequalityProof(out, t3.toExpr(), subproof[0].toExpr(), map);
            out << " ";
            out << ss.str();
            out << "))";
          }
        } else {
          if (t2IsConst) {
            // (t3 == subproof[0]) == subproof[1] != t2
            // goal is t2 != t3
            // subproof already shows constant = t3
            Assert(t3 == subproof[0]);
            out << "(negtrans _ _ _ _ ";
            tp->printConstantDisequalityProof(out, t2.toExpr(), subproof[1].toExpr(), map);
            out << " ";
            out << "(symm _ _ _ " << ss.str() << ")";
            out << ")";
          } else {
            Assert(t2 == subproof[0]);
            out << "(negsymm _ _ _ ";
            out << "(negtrans _ _ _ _ ";
            tp->printConstantDisequalityProof(out, t3.toExpr(), subproof[1].toExpr(), map);
            out << " ";
            out << "(symm _ _ _ " << ss.str() << ")";
            out << "))";
          }
        }
      }

      out << ")";
      return ret;
    } else {
      Debug("pf::array") << "In the case of NEGATIVE ROW" << std::endl;

      Debug("pf::array") << "pf->d_children[0]->d_node is: " << pf->d_children[0]->d_node << std::endl;

      // This is the case where (i == k), and the sub-proof explains why ((a[i]:=t)[k] != a[k])

      // If we wanted to remove the need for "negativerow", we would need to prove i==k using a new satlem. We would:
      // 1. Create a new satlem.
      // 2. Assume that i != k
      // 3. Apply ROW to show that ((a[i]:=t)[k] == a[k])
      // 4. Contradict this with the fact that ((a[i]:=t)[k] != a[k]), obtaining our contradiction

      TNode t1, t2, t3, t4;
      Node ret;

      // pf->d_node is an equality, i==k.
      t1 = pf->d_node[0];
      t2 = pf->d_node[1];

      // pf->d_children[0]->d_node will have the form: (not (= (select (store a_565 i7 e_566) i1) (select a_565 i1))),
      // or its symmetrical version.

      unsigned side;
      if (pf->d_children[0]->d_node[0][0].getKind() == kind::SELECT &&
          pf->d_children[0]->d_node[0][0][0].getKind() == kind::STORE) {
        side = 0;
      } else if (pf->d_children[0]->d_node[0][1].getKind() == kind::SELECT &&
                 pf->d_children[0]->d_node[0][1][0].getKind() == kind::STORE) {
        side = 1;
      }
      else {
        Unreachable();
      }

      Debug("pf::array") << "Side is: " << side << std::endl;

      // The array's index and element types will come from the subproof...
      t3 = pf->d_children[0]->d_node[0][side][0][0];
      t4 = pf->d_children[0]->d_node[0][side][0][2];
      ret = pf->d_node;

      // The order of indices needs to match; we might have to swap t1 and t2 and then apply symmetry.
      bool swap = (t2 == pf->d_children[0]->d_node[0][side][0][1]);

      Debug("mgd") << "t1 " << t1 << "\nt2 " << t2 << "\nt3 " << t3 << "\nt4 " << t4 << "\n";

      Assert(pf->d_children.size() == 1);
      std::stringstream ss;
      Node subproof = toStreamRecLFSC(ss, tp, pf->d_children[0], tb + 1, map);

      Debug("pf::array") << "Subproof is: " << ss.str() << std::endl;

      if (swap) {
        out << "(symm _ _ _ ";
      }

      out << "(negativerow _ _ ";
      tp->printTerm(swap ? t2.toExpr() : t1.toExpr(), out, map);
      out << " ";
      tp->printTerm(swap ? t1.toExpr() : t2.toExpr(), out, map);
      out << " ";
      tp->printTerm(t3.toExpr(), out, map);
      out << " ";
      tp->printTerm(t4.toExpr(), out, map);
      out << " ";

      if (side != 0) {
        out << "(negsymm _ _ _ " << ss.str() << ")";
      } else {
        out << ss.str();
      }

      out << ")";

      if (swap) {
        out << ") ";
      }

      return ret;
    }
  }

  else if (pf->d_id == d_reasonRow1) {
    Debug("mgd") << "row1 lemma: " << pf->d_node << std::endl;
    Assert(pf->d_node.getKind() == kind::EQUAL);
    TNode t1, t2, t3;
    Node ret;
    if(pf->d_node[1].getKind() == kind::SELECT &&
       pf->d_node[1][0].getKind() == kind::STORE &&
       pf->d_node[1][0][1] == pf->d_node[1][1] &&
       pf->d_node[1][0][2] == pf->d_node[0]) {
      t1 = pf->d_node[1][0][0];
      t2 = pf->d_node[1][0][1];
      t3 = pf->d_node[0];
      ret = pf->d_node[1].eqNode(pf->d_node[0]);
      Debug("mgd") << "t1 " << t1 << "\nt2 " << t2 << "\nt3 " << t3 << "\n";
    } else {
      Assert(pf->d_node[0].getKind() == kind::SELECT &&
             pf->d_node[0][0].getKind() == kind::STORE &&
             pf->d_node[0][0][1] == pf->d_node[0][1] &&
             pf->d_node[0][0][2] == pf->d_node[1]);
      t1 = pf->d_node[0][0][0];
      t2 = pf->d_node[0][0][1];
      t3 = pf->d_node[1];
      ret = pf->d_node;
      Debug("mgd") << "t1 " << t1 << "\nt2 " << t2 << "\nt3 " << t3 << "\n";
    }
    out << "(row1 _ _ ";
    tp->printTerm(t1.toExpr(), out, map);
    out << " ";
    tp->printTerm(t2.toExpr(), out, map);
    out << " ";
    tp->printTerm(t3.toExpr(), out, map);
    out << ")";
    return ret;
  }

  else if (pf->d_id == d_reasonExt) {
    theory::eq::EqProof *child_proof;

    Assert(pf->d_node.getKind() == kind::NOT);
    Assert(pf->d_node[0].getKind() == kind::EQUAL);
    Assert(pf->d_children.size() == 1);

    child_proof = pf->d_children[0];
    Assert(child_proof->d_node.getKind() == kind::NOT);
    Assert(child_proof->d_node[0].getKind() == kind::EQUAL);

    Debug("mgd") << "EXT lemma: " << pf->d_node << std::endl;

    TNode t1, t2, t3;
    t1 = child_proof->d_node[0][0];
    t2 = child_proof->d_node[0][1];
    t3 = pf->d_node[0][0][1];

    Debug("mgd") << "t1 " << t1 << "\nt2 " << t2 << "\nt3 " << t3 << "\n";

    out << "(or_elim_1 _ _ ";
    out << ProofManager::getLitName(child_proof->d_node[0]);
    out << " ";
    out << ProofManager::getArrayProof()->skolemToLiteral(t3.toExpr());
    out << ")";

    return pf->d_node;
  }

  else {
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    Debug("mgd") << "theory proof: " << pf->d_node << " by rule " << int(pf->d_id) << std::endl;
    AlwaysAssert(false);
    return pf->d_node;
  }
}

ArrayProof::ArrayProof(theory::arrays::TheoryArrays* arrays, TheoryProofEngine* pe)
  : TheoryProof(arrays, pe)
{}

void ArrayProof::registerTerm(Expr term) {
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

std::string ArrayProof::skolemToLiteral(Expr skolem) {
  Debug("pf::array") << "ArrayProof::skolemToLiteral( " << skolem << ")" << std::endl;
  Assert(d_skolemToLiteral.find(skolem) != d_skolemToLiteral.end());
  return d_skolemToLiteral[skolem];
}

void LFSCArrayProof::printOwnedTerm(Expr term, std::ostream& os, const ProofLetMap& map) {
  Assert (theory::Theory::theoryOf(term) == theory::THEORY_ARRAY);

  if (theory::Theory::theoryOf(term) != theory::THEORY_ARRAY) {
    // We can get here, for instance, if there's a (select ite ...), e.g. a non-array term
    // hiding as a subterm of an array term. In that case, send it back to the dispatcher.
    d_proofEngine->printBoundTerm(term, os, map);
    return;
  }

  if (term.getKind() == kind::VARIABLE || term.getKind() == kind::SKOLEM) {
    os << term;
    return;
  }

  Assert ((term.getKind() == kind::SELECT) || (term.getKind() == kind::PARTIAL_SELECT_0) || (term.getKind() == kind::PARTIAL_SELECT_1) || (term.getKind() == kind::STORE));

  switch (term.getKind()) {
  case kind::SELECT:
    Assert(term.getNumChildren() == 2);
    os << "(apply _ _ (apply _ _ (read ";
    printSort(ArrayType(term[0].getType()).getIndexType(), os);
    os << " ";
    printSort(ArrayType(term[0].getType()).getConstituentType(), os);
    os << ") ";
    printTerm(term[0], os, map);
    os << ") ";
    printTerm(term[1], os, map);
    os << ") ";
    return;

  case kind::PARTIAL_SELECT_0:
    Assert(term.getNumChildren() == 1);
    os << "(read ";
    printSort(ArrayType(term[0].getType()).getIndexType(), os);
    os << " ";
    printSort(ArrayType(term[0].getType()).getConstituentType(), os);
    os << ") ";
    return;

  case kind::PARTIAL_SELECT_1:
    Debug("pf::array") << "This branch has not beed tested yet." << std::endl;
    Unreachable();

    Assert(term.getNumChildren() == 1);
    os << "(apply _ _ (read ";
    printSort(ArrayType(term[0].getType()).getIndexType(), os);
    os << " ";
    printSort(ArrayType(term[0].getType()).getConstituentType(), os);
    os << ") ";
    printTerm(term[0], os, map);
    os << ") ";
    return;

  case kind::STORE:
    os << "(apply _ _ (apply _ _ (apply _ _ (write ";
    printSort(ArrayType(term[0].getType()).getIndexType(), os);
    os << " ";
    printSort(ArrayType(term[0].getType()).getConstituentType(), os);
    os << ") ";
    printTerm(term[0], os, map);
    os << ") ";
    printTerm(term[1], os, map);
    os << ") ";
    printTerm(term[2], os, map);
    os << ") ";
    return;

  default:
    Unreachable();
    return;
  }
}

void LFSCArrayProof::printOwnedSort(Type type, std::ostream& os) {
  Debug("pf::array") << std::endl << "(pf::array) LFSCArrayProof::printOwnedSort: type is: " << type << std::endl;
  Assert (type.isArray() || type.isSort());
  if (type.isArray()){
    ArrayType array_type(type);

    Debug("pf::array") << "LFSCArrayProof::printOwnedSort: type is an array. Index type: "
                       << array_type.getIndexType()
                       << ", element type: " << array_type.getConstituentType() << std::endl;

    os << "(Array ";
    printSort(array_type.getIndexType(), os);
    os << " ";
    printSort(array_type.getConstituentType(), os);
    os << ")";
  } else {
    os << type;
  }
}

void LFSCArrayProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren, const ProofLetMap& map) {
  os << " ;; Array Theory Lemma \n;;";
  for (unsigned i = 0; i < lemma.size(); ++i) {
    os << lemma[i] <<" ";
  }
  os <<"\n";
  //os << " (clausify_false trust)";
  ArrayProof::printTheoryLemmaProof(lemma, os, paren, map);
}

void LFSCArrayProof::printSortDeclarations(std::ostream& os, std::ostream& paren) {
  // declaring the sorts
  for (TypeSet::const_iterator it = d_sorts.begin(); it != d_sorts.end(); ++it) {
    if (!ProofManager::currentPM()->wasPrinted(*it)) {
      os << "(% " << *it << " sort\n";
      paren << ")";
      ProofManager::currentPM()->markPrinted(*it);
    }
  }
}

void LFSCArrayProof::printTermDeclarations(std::ostream& os, std::ostream& paren) {
  Debug("pf::array") << "Arrays declaring terms..." << std::endl;

  for (ExprSet::const_iterator it = d_declarations.begin(); it != d_declarations.end(); ++it) {
    Expr term = *it;

    Assert(term.getType().isArray() || term.isVariable());

    Debug("pf::array") << "LFSCArrayProof::printDeclarations: term is: " << term
                       << ". It's type is: " << term.getType()
                       << std::endl;

    if (term.getType().isArray()){
      ArrayType array_type(term.getType());

      Debug("pf::array") << "LFSCArrayProof::printDeclarations: term is an array. Index type: "
                         << array_type.getIndexType()
                         << ", element type: " << array_type.getConstituentType() << std::endl;

      os << "(% " << ProofManager::sanitize(term) << " ";
      os << "(term ";
      os << "(Array ";

      printSort(array_type.getIndexType(), os);
      os << " ";
      printSort(array_type.getConstituentType(), os);

      os << "))\n";
      paren << ")";
    } else {
      Assert(term.isVariable());
      if (ProofManager::getSkolemizationManager()->isSkolem(*it)) {
        Debug("pf::array") << "This term is a skoelm!" << std::endl;
        d_skolemDeclarations.insert(*it);
      } else {
        os << "(% " << ProofManager::sanitize(term) << " ";
        os << "(term ";
        os << term.getType() << ")\n";
        paren << ")";
      }
    }
  }

  Debug("pf::array") << "Declaring terms done!" << std::endl;
}

void LFSCArrayProof::printDeferredDeclarations(std::ostream& os, std::ostream& paren) {
  Debug("pf::array") << "Array: print deferred declarations called" << std::endl;

  unsigned count = 1;
  for (ExprSet::const_iterator it = d_skolemDeclarations.begin(); it != d_skolemDeclarations.end(); ++it) {
    Expr term = *it;
    Node equality = ProofManager::getSkolemizationManager()->getDisequality(*it);

    Debug("pf::array") << "LFSCArrayProof::printDeferredDeclarations: term is: " << *it << std::endl
                       << "It is a witness for: " << equality << std::endl;

    std::ostringstream newSkolemLiteral;
    newSkolemLiteral << ".sl" << count++;
    std::string skolemLiteral = newSkolemLiteral.str();

    d_skolemToLiteral[*it] = skolemLiteral;

    Debug("pf::array") << "LFSCArrayProof::printDeferredDeclarations: new skolem literal is: " << skolemLiteral << std::endl;

    Assert(equality.getKind() == kind::NOT);
    Assert(equality[0].getKind() == kind::EQUAL);

    Node array_one = equality[0][0];
    Node array_two = equality[0][1];

    ProofLetMap map;
    os << "(ext _ _ ";
    printTerm(array_one.toExpr(), os, map);
    os << " ";
    printTerm(array_two.toExpr(), os, map);
    os << " (\\ ";
    os << ProofManager::sanitize(*it);
    os << " (\\ ";
    os << skolemLiteral.c_str();
    os << "\n";

    paren << ")))";
  }
}

void LFSCArrayProof::printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) {
    // Nothing to do here at this point.
}

} /* CVC4  namespace */
