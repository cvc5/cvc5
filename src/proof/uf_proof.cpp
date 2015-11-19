/*********************                                                        */
/*! \file uf_proof.cpp
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "proof/uf_proof.h"
#include "theory/uf/theory_uf.h"
#include <stack>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;


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
  Trace("theory-proof-debug") << "; Print UF proof..." << std::endl;
  //AJR : carry this further?
  LetMap map;
  toStreamLFSC(out, ProofManager::getUfProof(), d_proof, map);
}

void ProofUF::toStreamLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, const LetMap& map) {
  Debug("lfsc-uf") << "Printing uf proof in LFSC : " << std::endl;
  pf->debug_print("lfsc-uf");
  Debug("lfsc-uf") << std::endl;
  toStreamRecLFSC( out, tp, pf, 0, map );
}

Node ProofUF::toStreamRecLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, unsigned tb, const LetMap& map) {
  if(tb == 0) {
    Assert(pf->d_id == eq::MERGED_THROUGH_TRANS);
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.size() >= 2);

    int neg = -1;
    theory::eq::EqProof subTrans;
    subTrans.d_id = eq::MERGED_THROUGH_TRANS;
    subTrans.d_node = pf->d_node;
    std::vector<theory::eq::EqProof *> childrenTail;
    for(size_t i = 0; i < pf->d_children.size(); ++i) {
      if(!pf->d_children[i]->d_node.isNull() && pf->d_children[i]->d_node.getKind() == kind::NOT) {
        Assert(neg < 0);
        neg = i;
      //equality congruences
      } else if( pf->d_children[i]->d_id==eq::MERGED_THROUGH_CONGRUENCE && pf->d_children[i]->d_node.isNull() ){
        // When encountering equality congruences, the 2nd child needs to be concatenated to the
        // end of the transitivity proof
        Assert( pf->d_children[i]->d_children.size()==2 );

        // If the first child is a reflexitivity child, we can omit it; this will be sorted out
        // by transitivity
        if ( pf->d_children[i]->d_children[0]->d_id != eq::MERGED_THROUGH_REFLEXIVITY) {
          subTrans.d_children.insert( subTrans.d_children.begin(), pf->d_children[i]->d_children[0] );
        }

        // If the second child is a reflexitivity child, we can omit it; this will be sorted out
        // by transitivity
        if ( pf->d_children[i]->d_children[1]->d_id != eq::MERGED_THROUGH_REFLEXIVITY) {
          childrenTail.insert( childrenTail.end(), pf->d_children[i]->d_children[1] );
        }
      } else {
        subTrans.d_children.push_back(pf->d_children[i]);
      }
    }
    Assert(neg >= 0);
    // When done, add the tail of children to the transitivity proof
    subTrans.d_children.insert( subTrans.d_children.end(), childrenTail.begin(), childrenTail.end() );

    Node n1;
    std::stringstream ss;
    //Assert(subTrans.d_children.size() == pf->d_children.size() - 1);
    Debug("mgdx") << "\nsubtrans has " << subTrans.d_children.size() << " children\n";
    if(pf->d_children.size() > 2) {
      n1 = toStreamRecLFSC(ss, tp, &subTrans, 1, map);
    } else {
      n1 = toStreamRecLFSC(ss, tp, subTrans.d_children[0], 1, map);
      Debug("mgdx") << "\nsubTrans unique child " << subTrans.d_children[0]->d_id << " was proven\ngot: " << n1 << std::endl;
    }

    Node n2 = pf->d_children[neg]->d_node;
    Assert(n2.getKind() == kind::NOT);
    out << "(clausify_false (contra _ ";
    Debug("mgdx") << "\nhave proven: " << n1 << std::endl;
    Debug("mgdx") << "n2 is " << n2[0] << std::endl;

    if (n2[0].getNumChildren() > 0) { Debug("mgdx") << "\nn2[0]: " << n2[0][0] << std::endl; }
    if (n1.getNumChildren() > 1) { Debug("mgdx") << "n1[1]: " << n1[1] << std::endl; }

    if(n2[0].getKind() == kind::APPLY_UF) {
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
      out << " " << ProofManager::getLitName(n2[0]) << "))" << std::endl;
    }
    return Node();
  }

  switch(pf->d_id) {
  case eq::MERGED_THROUGH_CONGRUENCE: {
    Debug("mgd") << "\nok, looking at congruence:\n";
    pf->debug_print("mgd");
    std::stack<const theory::eq::EqProof*> stk;
    for(const theory::eq::EqProof* pf2 = pf; pf2->d_id == eq::MERGED_THROUGH_CONGRUENCE; pf2 = pf2->d_children[0]) {
      Assert(!pf2->d_node.isNull());
      Assert(pf2->d_node.getKind() == kind::PARTIAL_APPLY_UF || pf2->d_node.getKind() == kind::BUILTIN || pf2->d_node.getKind() == kind::APPLY_UF || pf2->d_node.getKind() == kind::SELECT || pf2->d_node.getKind() == kind::STORE);
      Assert(pf2->d_children.size() == 2);
      out << "(cong _ _ _ _ _ _ ";
      stk.push(pf2);
    }
    Assert(stk.top()->d_children[0]->d_id != eq::MERGED_THROUGH_CONGRUENCE);
    NodeBuilder<> b1(kind::PARTIAL_APPLY_UF), b2(kind::PARTIAL_APPLY_UF);
    const theory::eq::EqProof* pf2 = stk.top();
    stk.pop();
    Assert(pf2->d_id == eq::MERGED_THROUGH_CONGRUENCE);
    Node n1 = toStreamRecLFSC(out, tp, pf2->d_children[0], tb + 1, map);
    out << " ";
    std::stringstream ss;
    Node n2 = toStreamRecLFSC(ss, tp, pf2->d_children[1], tb + 1, map);
    Debug("mgd") << "\nok, in FIRST cong[" << stk.size() << "]" << "\n";
    pf2->debug_print("mgd");
    Debug("mgd") << "looking at " << pf2->d_node << "\n";
    Debug("mgd") << "           " << n1 << "\n";
    Debug("mgd") << "           " << n2 << "\n";
    int side = 0;
    if(match(pf2->d_node, n1[0])) {
      //if(tb == 1) {
      Debug("mgd") << "SIDE IS 0\n";
      //}
      side = 0;
    } else {
      //if(tb == 1) {
      Debug("mgd") << "SIDE IS 1\n";
      //}
      if(!match(pf2->d_node, n1[1])) {
      Debug("mgd") << "IN BAD CASE, our first subproof is\n";
      pf2->d_children[0]->debug_print("mgd");
      }
      Assert(match(pf2->d_node, n1[1]));
      side = 1;
    }
    if(n1[side].getKind() == kind::APPLY_UF || n1[side].getKind() == kind::SELECT || n1[side].getKind() == kind::STORE) {
      if(n1[side].getKind() == kind::APPLY_UF) {
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
    Debug("mgd") << "pf2->d_node " << pf2->d_node << std::endl;
    Debug("mgd") << "b1.getNumChildren() " << b1.getNumChildren() << std::endl;
    Debug("mgd") << "n1 " << n1 << std::endl;
    Debug("mgd") << "n2 " << n2 << std::endl;
    Debug("mgd") << "side " << side << std::endl;
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
      Debug("mgd") << "\nMORE TO DO\n";
      }
      pf2 = stk.top();
      stk.pop();
      Assert(pf2->d_id == eq::MERGED_THROUGH_CONGRUENCE);
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
    Debug("mgd") << "at end assert, got " << pf2->d_node << "  and  " << n1 << std::endl;
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
      Debug("mgd") << "at[2] end assert, got " << pf2->d_node << "  and  " << n1 << std::endl;
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
    Debug("mgdx") << "\ncong proved: " << n << "\n";
    }
    return n;
  }

  case eq::MERGED_THROUGH_REFLEXIVITY:
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    out << "(refl _ ";
    tp->printTerm(NodeManager::currentNM()->toExpr(pf->d_node), out, map);
    out << ")";
    return eqNode(pf->d_node, pf->d_node);

  case eq::MERGED_THROUGH_EQUALITY:
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    out << ProofManager::getLitName(pf->d_node.negate());
    return pf->d_node;

  case eq::MERGED_THROUGH_TRANS: {
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.size() >= 2);
    std::stringstream ss;
    Debug("mgd") << "\ndoing trans proof[[\n";
    pf->debug_print("mgd");
    Debug("mgd") << "\n";
    Node n1 = toStreamRecLFSC(ss, tp, pf->d_children[0], tb + 1, map);
    Debug("mgd") << "\ndoing trans proof, got n1 " << n1 << "\n";
    if(tb == 1) {
      Debug("mgdx") << "\ntrans proof[0], got n1 " << n1 << "\n";
    }
    for(size_t i = 1; i < pf->d_children.size(); ++i) {
      std::stringstream ss1(ss.str()), ss2;
      ss.str("");
      Node n2 = toStreamRecLFSC(ss2, tp, pf->d_children[i], tb + 1, map);
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
      ss << "(trans _ _ _ _ ";
      if(n2.getKind() == kind::EQUAL || n2.getKind() == kind::IFF) {
        if(n1[0] == n2[0]) {
          if(n1[1] == n2[1] && match(n1[0], pf->d_node[0])) {
            if(match(n1[1], pf->d_node[1])) {
              // We have multiple identical nodes in the transitivity proof.
              // Simply ignore the redundancy, until we reach a different node.

              //Warning() << "TRICKY CASE 1!\n";
              ss.str(ss1.str());
              continue;
            }
            //ambiguity -- could replace with refl
            n1 = eqNode(n1[0], n2[0]);
            ss << ss1.str() << " (symm _ _ _ " << ss2.str() << ")";
          } else {
            if(tb == 1) { Debug("mgdx") << "case 1\n"; }
            n1 = eqNode(n1[1], n2[1]);
            ss << "(symm _ _ _ " << ss1.str() << ") " << ss2.str();
          }
        } else if(n1[1] == n2[1]) {
          if(tb == 1) { Debug("mgdx") << "case 2\n"; }
          n1 = eqNode(n1[0], n2[0]);
          ss << ss1.str() << " (symm _ _ _ " << ss2.str() << ")";
        } else if(n1[0] == n2[1]) {
          if(n1[1] == n2[0] && match(n1[0], pf->d_node[0])) {
            if(match(n1[1], pf->d_node[1])) {
              // We have multiple identical nodes in the transitivity proof.
              // Simply ignore the redundancy, until we reach a different node.

              //Warning() << "TRICKY CASE 2!\n";
              ss.str(ss1.str());
              continue;
            }
            //ambiguity -- could replace with refl
            n1 = eqNode(n1[0], n2[1]);
            Debug("mgdx") << "ambiguity resolved in favor of " << n1 << "\n";
            ss << ss1.str() << " " << ss2.str();
          } else {
            if(tb == 1) { Debug("mgdx") << "case 3\n"; }
            n1 = eqNode(n2[0], n1[1]);
            ss << ss2.str() << " " << ss1.str();
            if(tb == 1) { Debug("mgdx") << "++ proved " << n1 << "\n"; }
          }
        } else if(n1[1] == n2[0]) {
          if(tb == 1) { Debug("mgdx") << "case 4\n"; }
          n1 = eqNode(n1[0], n2[1]);
          ss << ss1.str() << " " << ss2.str();
        } else {
          Warning() << "\n\ntrans proof failure at step " << i << "\n\n";
          Warning() << "0 proves " << n1 << "\n";
          Warning() << "1 proves " << n2 << "\n\n";
          pf->debug_print("mgdx",0);
          //toStreamRec(Warning.getStream(), pf, 0);
          Warning() << "\n\n";
          Unreachable();
        }
        Debug("mgd") << "++ trans proof[" << i << "], now have " << n1 << std::endl;
      } else {
        if(n1[0] == n2) {
          n1 = n1[1];
          ss << "(symm _ _ _ " << ss1.str() << ") (pred_eq_t _ " << ss2.str() << ")";
        } else if(n1[1] == n2) {
          n1 = n1[0];
          ss << ss1.str() << " (pred_eq_t _ " << ss2.str() << ")";
        } else {
          Unreachable();
        }
      }
      ss << ")";
    }
    out << ss.str();
    Debug("mgd") << "\n++ trans proof done, have proven " << n1 << std::endl;
    return n1;
  }

  case eq::MERGED_ARRAYS_ROW: {
    Debug("mgd") << "row lemma: " << pf->d_node << std::endl;
    Assert(pf->d_node.getKind() == kind::EQUAL);
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
    out << "(row _ _ ";
    tp->printTerm(t2.toExpr(), out, map);
    out << " ";
    tp->printTerm(t3.toExpr(), out, map);
    out << " ";
    tp->printTerm(t1.toExpr(), out, map);
    out << " ";
    tp->printTerm(t4.toExpr(), out, map);
    out << " " << ProofManager::getLitName(t2.eqNode(t3)) << ")";
    return ret;
  }

  case eq::MERGED_ARRAYS_ROW1: {
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

  default:
    Assert(!pf->d_node.isNull());
    Assert(pf->d_children.empty());
    Debug("mgd") << "theory proof: " << pf->d_node << " by rule " << int(pf->d_id) << std::endl;
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

void LFSCUFProof::printTerm(Expr term, std::ostream& os, const LetMap& map) {
  Assert (Theory::theoryOf(term) == THEORY_UF);

  if (term.getKind() == kind::VARIABLE ||
      term.getKind() == kind::SKOLEM) {
    os << term;
    return;
  }

  Assert (term.getKind() == kind::APPLY_UF);

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
}

void LFSCUFProof::printSort(Type type, std::ostream& os) {
  Assert (type.isSort());
  os << type <<" ";
}

void LFSCUFProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren) {
  os << " ;; UF Theory Lemma \n;;";
  for (unsigned i = 0; i < lemma.size(); ++i) {
    os << lemma[i] <<" ";
  }
  os <<"\n";
  //os << " (clausify_false trust)";
  UFProof::printTheoryLemmaProof( lemma, os, paren );
}

void LFSCUFProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  // declaring the sorts
  for (TypeSet::const_iterator it = d_sorts.begin(); it != d_sorts.end(); ++it) {
    os << "(% " << *it << " sort\n";
    paren << ")";
  }

  // declaring the terms
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
        os << " " << arg_type;
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
}
