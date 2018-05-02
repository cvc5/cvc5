/*********************                                                        */
/*! \file symmetry_breaker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry breaker module
 **/

#include "preprocessing/passes/symmetry_breaker.h"

using namespace std;

namespace CVC4 {
namespace preprocessing {
namespace passes {

Node SymmetryBreaker::generateSymBkConstraints(vector<vector<Node>>& parts)
{
  Node sbConstraint = d_trueNode;

  for (vector<Node>& part : parts)
  {
    if (part.size() >= 2)
    {
      Kind kd = getOrderKind(part[0]);

      if (kd != kind::EQUAL)
      {
        for (unsigned int i = 0; i < part.size() - 1; ++i)
        {
          // Generate less than or equal to constraints: part[i] <= part[i+1]
          Node constraint =
              NodeManager::currentNM()->mkNode(kd, part[i], part[i + 1]);
          sbConstraint = NodeManager::currentNM()->mkNode(
              kind::AND, sbConstraint, constraint);
          Trace("sym-bk")
              << "[sym-bk] Generate a symmetry breaking constraint: "
              << constraint << endl;
        }
      }
      else if (part.size() >= 3)
      {
        for (unsigned int i = 0; i < part.size(); ++i)
        {
          for (unsigned int j = i + 2; j < part.size(); ++i)
          {
            // Generate triplet constraints v_i = v_j => v_i = v_{j-1} for all 0
            // <= i < j-1 < j < part.size()
            Node constraint = NodeManager::currentNM()->mkNode(
                kind::IMPLIES,
                NodeManager::currentNM()->mkNode(kd, part[i], part[j]),
                NodeManager::currentNM()->mkNode(kd, part[i], part[j - 1]));
            sbConstraint = NodeManager::currentNM()->mkNode(
                kind::AND, sbConstraint, constraint);
            Trace("sym-bk")
                << "[sym-bk] Generate a symmetry breaking constraint: "
                << constraint << endl;
          }
          if (i >= 1)
          {
            for (unsigned int j = i + 1; j < part.size(); ++j)
            {
              Node rhs = d_falseNode;
              Node lhs = NodeManager::currentNM()->mkNode(kd, part[i], part[j]);

              for (unsigned int k = 0; k < i; ++k)
              {
                rhs = NodeManager::currentNM()->mkNode(
                    kind::OR,
                    rhs,
                    NodeManager::currentNM()->mkNode(kd, part[k], part[k + 1]));
              }
              // Generate segment constraints
              // v_i = v_j => (v_0 = v_1 OR \ldots OR v_{i-1} = v_{i}) for all 1
              // <= i < j < part.size()
              Node constraint =
                  NodeManager::currentNM()->mkNode(kind::IMPLIES, lhs, rhs);
              sbConstraint = NodeManager::currentNM()->mkNode(
                  kind::AND, sbConstraint, constraint);
              Trace("sym-bk")
                  << "[sym-bk] Generate a symmetry breaking constraint: "
                  << constraint << endl;
            }
          }
        }
      }
    }
  }
  return sbConstraint;
}

Kind SymmetryBreaker::getOrderKind(Node node)
{
  if (node.getType().isInteger() || node.getType().isReal())
  {
    return kind::LEQ;
  }
  else if (node.getType().isBitVector())
  {
    return kind::BITVECTOR_ULE;
  }
  else
  {
    return kind::EQUAL;
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
