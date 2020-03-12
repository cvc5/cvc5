/*********************                                                        */
/*! \file uf_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/
#include "proof/uf_proof.h"

#include <stack>

#include "proof/proof_manager.h"
#include "proof/simplify_boolean_node.h"
#include "theory/uf/theory_uf.h"

namespace CVC4 {

void ProofUF::toStream(std::ostream& out) const
{
  ProofLetMap map;
  toStream(out, map);
}

void ProofUF::toStream(std::ostream& out, const ProofLetMap& map) const
{
  Trace("theory-proof-debug") << "; Print UF proof..." << std::endl;
  //AJR : carry this further?
  toStreamLFSC(out, ProofManager::getUfProof(), *d_proof, map);
}

void ProofUF::toStreamLFSC(std::ostream& out,
                           TheoryProof* tp,
                           const theory::eq::EqProof& pf,
                           const ProofLetMap& map)
{
  Debug("pf::uf") << "ProofUF::toStreamLFSC starting" << std::endl;
  Debug("lfsc-uf") << "Printing uf proof in LFSC : " << std::endl;
  pf.debug_print("lfsc-uf");
  Debug("lfsc-uf") << std::endl;
  toStreamRecLFSC( out, tp, pf, 0, map );
}

Node ProofUF::toStreamRecLFSC(std::ostream& out,
                              TheoryProof* tp,
                              const theory::eq::EqProof& pf,
                              unsigned tb,
                              const ProofLetMap& map)
{
  Debug("pf::uf") << std::endl
                  << std::endl
                  << "toStreamRecLFSC called. tb = " << tb
                  << " . proof:" << std::endl;
  if (tb == 0)
  {
    // Special case: false was an input, so the proof is just "false".
    if (pf.d_id == theory::eq::MERGED_THROUGH_EQUALITY &&
        pf.d_node == NodeManager::currentNM()->mkConst(false)) {
      out << "(clausify_false ";
      out << ProofManager::getLitName(NodeManager::currentNM()->mkConst(false).notNode());
      out << ")" << std::endl;
      return Node();
    }

    std::shared_ptr<theory::eq::EqProof> subTrans =
        std::make_shared<theory::eq::EqProof>();

    int neg = tp->assertAndPrint(pf, map, subTrans);

    Node n1;
    std::stringstream ss, ss2;
    Debug("pf::uf") << "\nsubtrans has " << subTrans->d_children.size() << " children\n";
    bool disequalityFound = (neg >= 0);

    if(!disequalityFound || subTrans->d_children.size() >= 2) {
      n1 = toStreamRecLFSC(ss, tp, *subTrans, 1, map);
    } else {
      n1 = toStreamRecLFSC(ss, tp, *(subTrans->d_children[0]), 1, map);
      Debug("pf::uf") << "\nsubTrans unique child "
                      << subTrans->d_children[0]->d_id
                      << " was proven\ngot: " << n1 << std::endl;
    }

    Debug("pf::uf") << "\nhave proven: " << n1 << std::endl;

    out << "(clausify_false (contra _ ";
    if (disequalityFound) {
      Node n2 = pf.d_children[neg]->d_node;
      Assert(n2.getKind() == kind::NOT);

      Debug("pf::uf") << "n2 is " << n2[0] << std::endl;

      if (n2[0].getNumChildren() > 0)
      {
        Debug("pf::uf") << "\nn2[0]: " << n2[0][0] << std::endl;
      }
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
      } else if (n2[0].getKind() == kind::BOOLEAN_TERM_VARIABLE) {
        out << ss.str() << " " << ProofManager::getLitName(n2[0]) << "))";
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
    } else {
      Node n2 = pf.d_node;
      Assert(n2.getKind() == kind::EQUAL);
      Assert((n1[0] == n2[0] && n1[1] == n2[1])
             || (n1[1] == n2[0] && n1[0] == n2[1]));

      out << ss.str();
      out << " ";
      ProofManager::getTheoryProofEngine()->printConstantDisequalityProof(
          out, n1[0].toExpr(), n1[1].toExpr(), map);
      out << "))" << std::endl;
    }

    return Node();
  }
  // TODO (#2965): improve this code, which is highly complicated.
  switch(pf.d_id) {
  case theory::eq::MERGED_THROUGH_CONGRUENCE: {
    Debug("pf::uf") << "\nok, looking at congruence:\n";
    pf.debug_print("pf::uf");
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
    Debug("pf::uf") << "\nok, in FIRST cong[" << stk.size() << "]" << "\n";
    pf2->debug_print("pf::uf");
    Debug("pf::uf") << "looking at " << pf2->d_node << "\n";
    Debug("pf::uf") << "           " << n1 << "\n";
    Debug("pf::uf") << "           " << n2 << "\n";
    int side = 0;
    if (tp->match(pf2->d_node, n1[0]))
    {
      //if(tb == 1) {
      Debug("pf::uf") << "SIDE IS 0\n";
      //}
      side = 0;
    } else {
      //if(tb == 1) {
      Debug("pf::uf") << "SIDE IS 1\n";
      //}
      if (!tp->match(pf2->d_node, n1[1]))
      {
        Debug("pf::uf") << "IN BAD CASE, our first subproof is\n";
        pf2->d_children[0]->debug_print("pf::uf");
      }
      Assert(tp->match(pf2->d_node, n1[1]));
      side = 1;
    }
    if (n1[side].getKind() == kind::APPLY_UF
        || n1[side].getKind() == kind::PARTIAL_APPLY_UF
        || n1[side].getKind() == kind::SELECT
        || n1[side].getKind() == kind::STORE)
    {
      if (n1[side].getKind() == kind::APPLY_UF
          || n1[side].getKind() == kind::PARTIAL_APPLY_UF)
      {
        b1 << n1[side].getOperator();
      } else {
        b1 << ProofManager::currentPM()->mkOp(n1[side].getOperator());
      }
      b1.append(n1[side].begin(), n1[side].end());
    } else {
      b1 << n1[side];
    }
    if(n1[1-side].getKind() == kind::PARTIAL_APPLY_UF || n1[1-side].getKind() == kind::APPLY_UF || n1[side].getKind() == kind::SELECT || n1[side].getKind() == kind::STORE) {
      if (n1[1 - side].getKind() == kind::PARTIAL_APPLY_UF
          || n1[1 - side].getKind() == kind::APPLY_UF)
      {
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
        Debug("pf::uf") << "\nMORE TO DO\n";
      }
      pf2 = stk.top();
      stk.pop();
      Assert(pf2->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE);
      out << " ";
      ss.str("");
      n2 = toStreamRecLFSC(ss, tp, *(pf2->d_children[1]), tb + 1, map);
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
        Assert(pf2->d_node[b1.getNumChildren()] == n2[1 - side]);
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
    Node n = (side == 0 ? n1.eqNode(n2) : n2.eqNode(n1));
    if(tb == 1) {
      Debug("pf::uf") << "\ncong proved: " << n << "\n";
    }
    return n;
  }

  case theory::eq::MERGED_THROUGH_REFLEXIVITY:
  {
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.empty());
    out << "(refl _ ";
    tp->printTerm(NodeManager::currentNM()->toExpr(pf.d_node), out, map);
    out << ")";
    return pf.d_node.eqNode(pf.d_node);
  }
  case theory::eq::MERGED_THROUGH_EQUALITY:
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.empty());
    out << ProofManager::getLitName(pf.d_node.negate());
    return pf.d_node;

  case theory::eq::MERGED_THROUGH_TRANS: {
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.size() >= 2);
    std::stringstream ss;
    Debug("pf::uf") << "\ndoing trans proof[[\n";
    pf.debug_print("pf::uf");
    Debug("pf::uf") << "\n";

    pf.d_children[0]->d_node = simplifyBooleanNode(pf.d_children[0]->d_node);

    Node n1 = toStreamRecLFSC(ss, tp, *(pf.d_children[0]), tb + 1, map);
    Debug("pf::uf") << "\ndoing trans proof, got n1 " << n1 << "\n";
    if(tb == 1) {
      Debug("pf::uf") << "\ntrans proof[0], got n1 " << n1 << "\n";
    }

    bool identicalEqualities = false;
    bool evenLengthSequence;
    std::stringstream dontCare;
    Node nodeAfterEqualitySequence =
        toStreamRecLFSC(dontCare, tp, *(pf.d_children[0]), tb + 1, map);

    std::map<size_t, Node> childToStream;
    std::pair<Node, Node> nodePair;
    for(size_t i = 1; i < pf.d_children.size(); ++i) {
      std::stringstream ss1(ss.str()), ss2;
      ss.str("");

      pf.d_children[i]->d_node = simplifyBooleanNode(pf.d_children[i]->d_node);

      // It is possible that we've already converted the i'th child to stream.
      // If so,
      // use previously stored result. Otherwise, convert and store.
      Node n2;
      if (childToStream.find(i) != childToStream.end())
        n2 = childToStream[i];
      else
      {
        n2 = toStreamRecLFSC(ss2, tp, *(pf.d_children[i]), tb + 1, map);
        childToStream[i] = n2;
      }

      // The following branch is dedicated to handling sequences of identical
      // equalities,
      // i.e. trans[ a=b, a=b, a=b ].
      //
      // There are two cases:
      //    1. The number of equalities is odd. Then, the sequence can be
      //    collapsed to just one equality,
      //       i.e. a=b.
      //    2. The number of equalities is even. Now, we have two options: a=a
      //    or b=b. To determine this,
      //       we look at the node after the equality sequence. If it needs a,
      //       we go for a=a; and if it needs
      //       b, we go for b=b. If there is no following node, we look at the
      //       goal of the transitivity proof,
      //       and use it to determine which option we need.
      if (n2.getKind() == kind::EQUAL)
      {
        if (((n1[0] == n2[0]) && (n1[1] == n2[1]))
            || ((n1[0] == n2[1]) && (n1[1] == n2[0])))
        {
          // We are in a sequence of identical equalities

          Debug("pf::uf") << "Detected identical equalities: " << std::endl
                          << "\t" << n1 << std::endl;

          if (!identicalEqualities)
          {
            // The sequence of identical equalities has started just now
            identicalEqualities = true;

            Debug("pf::uf")
                << "The sequence is just beginning. Determining length..."
                << std::endl;

            // Determine whether the length of this sequence is odd or even.
            evenLengthSequence = true;
            bool sequenceOver = false;
            size_t j = i + 1;

            while (j < pf.d_children.size() && !sequenceOver)
            {
              std::stringstream ignore;
              nodeAfterEqualitySequence =
                  toStreamRecLFSC(ignore, tp, *(pf.d_children[j]), tb + 1, map);

              if (((nodeAfterEqualitySequence[0] == n1[0])
                   && (nodeAfterEqualitySequence[1] == n1[1]))
                  || ((nodeAfterEqualitySequence[0] == n1[1])
                      && (nodeAfterEqualitySequence[1] == n1[0])))
              {
                evenLengthSequence = !evenLengthSequence;
              }
              else
              {
                sequenceOver = true;
              }

              ++j;
            }

            nodePair =
                tp->identicalEqualitiesPrinterHelper(evenLengthSequence,
                                                     sequenceOver,
                                                     pf,
                                                     map,
                                                     ss1.str(),
                                                     &ss,
                                                     n1,
                                                     nodeAfterEqualitySequence);
            n1 = nodePair.first;
            nodeAfterEqualitySequence = nodePair.second;
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
        Debug("pf::uf") << (n2.getKind() == kind::EQUAL) << "\n";

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

      if(n2.getKind() == kind::EQUAL && n1.getKind() == kind::EQUAL)
        // Both elements of the transitivity rule are equalities/iffs
      {
        if(n1[0] == n2[0]) {
          if(tb == 1) { Debug("pf::uf") << "case 1\n"; }
          n1 = n1[1].eqNode(n2[1]);
          ss << "(symm _ _ _ " << ss1.str() << ") " << ss2.str();
        } else if(n1[1] == n2[1]) {
          if(tb == 1) { Debug("pf::uf") << "case 2\n"; }
          n1 = n1[0].eqNode(n2[0]);
          ss << ss1.str() << " (symm _ _ _ " << ss2.str() << ")";
        } else if(n1[0] == n2[1]) {
          if(tb == 1) { Debug("pf::uf") << "case 3\n"; }
          n1 = n2[0].eqNode(n1[1]);
          ss << ss2.str() << " " << ss1.str();
          if(tb == 1) { Debug("pf::uf") << "++ proved " << n1 << "\n"; }
        } else if(n1[1] == n2[0]) {
          if(tb == 1) { Debug("pf::uf") << "case 4\n"; }
          n1 = n1[0].eqNode(n2[1]);
          ss << ss1.str() << " " << ss2.str();
        } else {
          Warning() << "\n\ntrans proof failure at step " << i << "\n\n";
          Warning() << "0 proves " << n1 << "\n";
          Warning() << "1 proves " << n2 << "\n\n";
          pf.debug_print("pf::uf",0);
          //toStreamRec(Warning.getStream(), pf, 0);
          Warning() << "\n\n";
          Unreachable();
        }
        Debug("pf::uf") << "++ trans proof[" << i << "], now have " << n1 << std::endl;
      } else if(n1.getKind() == kind::EQUAL) {
        // n1 is an equality/iff, but n2 is a predicate
        if(n1[0] == n2) {
          n1 = n1[1].eqNode(NodeManager::currentNM()->mkConst(true));
          ss << "(symm _ _ _ " << ss1.str() << ") (pred_eq_t _ " << ss2.str() << ")";
        } else if(n1[1] == n2) {
          n1 = n1[0].eqNode(NodeManager::currentNM()->mkConst(true));
          ss << ss1.str() << " (pred_eq_t _ " << ss2.str() << ")";
        } else {
          Unreachable();
        }
      } else if(n2.getKind() == kind::EQUAL) {
        // n2 is an equality/iff, but n1 is a predicate
        if(n2[0] == n1) {
          n1 = n2[1].eqNode(NodeManager::currentNM()->mkConst(true));
          ss << "(symm _ _ _ " << ss2.str() << ") (pred_eq_t _ " << ss1.str() << ")";
        } else if(n2[1] == n1) {
          n1 = n2[0].eqNode(NodeManager::currentNM()->mkConst(true));
          ss << ss2.str() << " (pred_eq_t _ " << ss1.str() << ")";
        } else {
          Unreachable();
        }
      } else {
        // Both n1 and n2 are predicates.
        // We want to prove b1 = b2, and we know that ((b1), (b2)) or ((not b1), (not b2))
        if (n1.getKind() == kind::NOT) {
          Assert(n2.getKind() == kind::NOT);
          Assert(pf.d_node[0] == n1[0] || pf.d_node[0] == n2[0]);
          Assert(pf.d_node[1] == n1[0] || pf.d_node[1] == n2[0]);
          Assert(n1[0].getKind() == kind::BOOLEAN_TERM_VARIABLE);
          Assert(n2[0].getKind() == kind::BOOLEAN_TERM_VARIABLE);

          if (pf.d_node[0] == n1[0]) {
            ss << "(false_preds_equal _ _ " << ss1.str() << " " << ss2.str() << ") ";
            ss << "(pred_refl_neg _ " << ss2.str() << ")";
          } else {
            ss << "(false_preds_equal _ _ " << ss2.str() << " " << ss1.str() << ") ";
            ss << "(pred_refl_neg _ " << ss1.str() << ")";
          }
          n1 = pf.d_node;

        } else if (n1.getKind() == kind::BOOLEAN_TERM_VARIABLE) {
          Assert(n2.getKind() == kind::BOOLEAN_TERM_VARIABLE);
          Assert(pf.d_node[0] == n1 || pf.d_node[0] == n2);
          Assert(pf.d_node[1] == n1 || pf.d_node[2] == n2);

          if (pf.d_node[0] == n1) {
            ss << "(true_preds_equal _ _ " << ss1.str() << " " << ss2.str() << ") ";
            ss << "(pred_refl_pos _ " << ss2.str() << ")";
          } else {
            ss << "(true_preds_equal _ _ " << ss2.str() << " " << ss1.str() << ") ";
            ss << "(pred_refl_pos _ " << ss1.str() << ")";
          }
          n1 = pf.d_node;

        } else {

          Unreachable();
        }
      }

      ss << ")";
    }
    out << ss.str();
    Debug("pf::uf") << "\n++ trans proof done, have proven " << n1 << std::endl;
    return n1;
  }

  default:
    Assert(!pf.d_node.isNull());
    Assert(pf.d_children.empty());
    Debug("pf::uf") << "theory proof: " << pf.d_node << " by rule " << int(pf.d_id) << std::endl;
    AlwaysAssert(false);
    return pf.d_node;
  }
}

UFProof::UFProof(theory::uf::TheoryUF* uf, TheoryProofEngine* pe)
  : TheoryProof(uf, pe)
{}

theory::TheoryId UFProof::getTheoryId() { return theory::THEORY_UF; }
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


    if (term.getKind() == kind::BOOLEAN_TERM_VARIABLE) {
      // Ensure cnf literals
      Node asNode(term);
      ProofManager::currentPM()->ensureLiteral(
          asNode.eqNode(NodeManager::currentNM()->mkConst(true)));
      ProofManager::currentPM()->ensureLiteral(
          asNode.eqNode(NodeManager::currentNM()->mkConst(false)));
    }
  }

  // recursively declare all other terms
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    // could belong to other theories
    d_proofEngine->registerTerm(term[i]);
  }
}

void LFSCUFProof::printOwnedTermAsType(Expr term,
                                       std::ostream& os,
                                       const ProofLetMap& map,
                                       TypeNode expectedType)
{
  Node node = Node::fromExpr(term);
  Debug("pf::uf") << std::endl << "(pf::uf) LFSCUfProof::printOwnedTerm: term = " << node << std::endl;

  Assert(theory::Theory::theoryOf(node) == theory::THEORY_UF);

  if (node.getKind() == kind::VARIABLE ||
      node.getKind() == kind::SKOLEM ||
      node.getKind() == kind::BOOLEAN_TERM_VARIABLE) {
    os << node;
    return;
  }

  Assert(node.getKind() == kind::APPLY_UF);

  if(node.getType().isBoolean()) {
    os << "(p_app ";
  }
  Node func = node.getOperator();
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    os << "(apply _ _ ";
  }
  os << func << " ";
  Assert(func.getType().isFunction());
  std::vector<TypeNode> argsTypes = node.getOperator().getType().getArgTypes();
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {

    bool convertToBool = (node[i].getType().isBoolean() && !d_proofEngine->printsAsBool(node[i]));
    if (convertToBool) os << "(f_to_b ";
    d_proofEngine->printBoundTerm(term[i], os, map, argsTypes[i]);
    if (convertToBool) os << ")";
    os << ")";
  }
  if(term.getType().isBoolean()) {
    os << ")";
  }
}

void LFSCUFProof::printOwnedSort(Type type, std::ostream& os) {
  Debug("pf::uf") << std::endl << "(pf::uf) LFSCArrayProof::printOwnedSort: type is: " << type << std::endl;

  Assert(type.isSort());
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
      Assert(term.isVariable());
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

bool LFSCUFProof::printsAsBool(const Node &n) {
  if (n.getKind() == kind::BOOLEAN_TERM_VARIABLE)
    return true;

  return false;
}

void LFSCUFProof::printConstantDisequalityProof(std::ostream& os, Expr c1, Expr c2, const ProofLetMap &globalLetMap) {
  Node falseNode = NodeManager::currentNM()->mkConst(false);
  Node trueNode = NodeManager::currentNM()->mkConst(true);

  Assert(c1 == falseNode.toExpr() || c1 == trueNode.toExpr());
  Assert(c2 == falseNode.toExpr() || c2 == trueNode.toExpr());
  Assert(c1 != c2);

  if (c1 == trueNode.toExpr())
    os << "t_t_neq_f";
  else
    os << "(symm _ _ _ t_t_neq_f)";
}

} /* namespace CVC4 */
