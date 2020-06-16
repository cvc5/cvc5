/*********************                                                        */
/*! \file simplify_boolean_node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Liana Hadarean, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simplifying a boolean node, needed for constructing LFSC proofs.
 **
 **/

#include "cvc4_private.h"

#include "proof_manager.h"

namespace CVC4 {

inline static Node eqNode(TNode n1, TNode n2) {
  return NodeManager::currentNM()->mkNode(kind::EQUAL, n1, n2);
}

Node simplifyBooleanNode(const Node &n) {
  if (n.isNull())
    return n;

  // Only simplify boolean nodes
  if (!n.getType().isBoolean())
    return n;

  // Sometimes we get sent intermediate nodes that we shouldn't simplify.
  // If a node doesn't have a literal, it's clearly intermediate - ignore.
  if (!ProofManager::hasLitName(n))
    return n;

  // If we already simplified the node, ignore.
  if (ProofManager::currentPM()->haveRewriteFilter(n.negate()))
    return n;


  std::string litName = ProofManager::getLitName(n.negate());
  Node falseNode = NodeManager::currentNM()->mkConst(false);
  Node trueNode = NodeManager::currentNM()->mkConst(true);
  Node simplified = n;

  // (not (= false b)), (not (= true b)))
  if ((n.getKind() == kind::NOT) && (n[0].getKind() == kind::EQUAL) &&
      (n[0][0].getKind() == kind::BOOLEAN_TERM_VARIABLE || n[0][1].getKind() == kind::BOOLEAN_TERM_VARIABLE)) {
    Node lhs = n[0][0];
    Node rhs = n[0][1];

    if (lhs == falseNode) {
      Assert(rhs != falseNode);
      Assert(rhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (not (= false b)) --> true = b

      simplified = eqNode(trueNode, rhs);

      std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
      std::stringstream newLitName;
      newLitName << "(pred_not_iff_f _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());

    } else if (rhs == falseNode) {
      Assert(lhs != falseNode);
      Assert(lhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (not (= b false)) --> b = true

      simplified = eqNode(lhs, trueNode);
      std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
      std::stringstream newLitName;
      newLitName << "(pred_not_iff_f_2 _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());

    } else if (lhs == trueNode) {
      Assert(rhs != trueNode);
      Assert(rhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (not (= true b)) --> b = false

      simplified = eqNode(falseNode, rhs);
      std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
      std::stringstream newLitName;
      newLitName << "(pred_not_iff_t _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());

    } else if (rhs == trueNode) {
      Assert(lhs != trueNode);
      Assert(lhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (not (= b true)) --> b = false

      simplified = eqNode(lhs, falseNode);
      std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
      std::stringstream newLitName;
      newLitName << "(pred_not_iff_t_2 _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());
    }

  } else if ((n.getKind() == kind::EQUAL) &&
             (n[0].getKind() == kind::BOOLEAN_TERM_VARIABLE || n[1].getKind() == kind::BOOLEAN_TERM_VARIABLE)) {
    Node lhs = n[0];
    Node rhs = n[1];

    if (lhs == falseNode) {
      Assert(rhs != falseNode);
      Assert(rhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (= false b)

      std::stringstream newLitName;
      newLitName << "(pred_iff_f _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(litName, newLitName.str());

    } else if (rhs == falseNode) {
      Assert(lhs != falseNode);
      Assert(lhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (= b false))

      std::stringstream newLitName;
      newLitName << "(pred_iff_f_2 _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(litName, newLitName.str());

    } else if (lhs == trueNode) {
      Assert(rhs != trueNode);
      Assert(rhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (= true b)

      std::stringstream newLitName;
      newLitName << "(pred_iff_t _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(litName, newLitName.str());

    } else if (rhs == trueNode) {
      Assert(lhs != trueNode);
      Assert(lhs.getKind() == kind::BOOLEAN_TERM_VARIABLE);
      // (= b true)


      std::stringstream newLitName;
      newLitName << "(pred_iff_t_2 _ " << litName << ")";
      ProofManager::currentPM()->addRewriteFilter(litName, newLitName.str());
    }

  } else if ((n.getKind() == kind::NOT) && (n[0].getKind() == kind::BOOLEAN_TERM_VARIABLE)) {
    // (not b) --> b = false
    simplified = eqNode(n[0], falseNode);
    std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
    std::stringstream newLitName;
    newLitName << "(pred_eq_f _ " << litName << ")";
    ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());

  } else if (n.getKind() == kind::BOOLEAN_TERM_VARIABLE) {
    // (b) --> b = true
    simplified = eqNode(n, trueNode);
    std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
    std::stringstream newLitName;
    newLitName << "(pred_eq_t _ " << litName << ")";
    ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());

  } else if ((n.getKind() == kind::NOT) && (n[0].getKind() == kind::SELECT)) {
    // not(a[x]) --> a[x] = false
    simplified = eqNode(n[0], falseNode);
    std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
    std::stringstream newLitName;
    newLitName << "(pred_eq_f _ " << litName << ")";
    ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());

  } else if (n.getKind() == kind::SELECT) {
    // a[x] --> a[x] = true
    simplified = eqNode(n, trueNode);
    std::string simplifiedLitName = ProofManager::getLitName(simplified.negate());
    std::stringstream newLitName;
    newLitName << "(pred_eq_t _ " << litName << ")";
    ProofManager::currentPM()->addRewriteFilter(simplifiedLitName, newLitName.str());
  }

  if (simplified != n)
    Debug("pf::simplify") << "simplifyBooleanNode: " << n << " --> " << simplified << std::endl;

  return simplified;
}

}/* CVC4 namespace */
