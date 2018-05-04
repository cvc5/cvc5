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

Node SymmetryBreaker::generateSymBkConstraints(const vector<vector<Node>>& parts)
{
  vector<Node> constraints;

  for (const vector<Node>& part : parts)
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
          constraints.push_back(constraint);
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
            // Generate consecutive constraints v_i = v_j => v_i = v_{j-1} for all 0
            // <= i < j-1 < j < part.size()
            Node constraint = NodeManager::currentNM()->mkNode(
                kind::IMPLIES,
                NodeManager::currentNM()->mkNode(kd, part[i], part[j]),
                NodeManager::currentNM()->mkNode(kd, part[i], part[j - 1]));
            constraints.push_back(constraint);
            Trace("sym-bk")
                << "[sym-bk] Generate a symmetry breaking constraint: "
                << constraint << endl;
          }
          if (i >= 1)
          {
            for (unsigned int j = i + 1; j < part.size(); ++j)
            {
              Node lhs = NodeManager::currentNM()->mkNode(kd, part[i], part[j]);
              Node rhs = NodeManager::currentNM()->mkNode(kd, part[i], part[i - 1]);
              int prev_seg_start_index = 2*i - j - 1;

              // Since prev_seg_len is always less than i - 1, we just need to make
              // sure prev_seg_len is greater than or equal to 0
              if(prev_seg_start_index >= 0)
              {
                rhs = NodeManager::currentNM()->mkNode(
                    kind::OR,
                    rhs,
                    NodeManager::currentNM()->mkNode(kd, part[i-1], part[prev_seg_start_index]));
              }
              // Generate length order constraints
              // v_i = v_j => (v_{i} = v_{i-1} OR v_{i-1} = x_{(i-1)-(j-i)})
              // for all 1 <= i < j < part.size() and (i-1)-(j-i) >= 0
              Node constraint =
                  NodeManager::currentNM()->mkNode(kind::IMPLIES, lhs, rhs);
              constraints.push_back(constraint);
              Trace("sym-bk")
                  << "[sym-bk] Generate a symmetry breaking constraint: "
                  << constraint << endl;
            }
          }
        }
      }
    }
  }
  if(constraints.empty())
  {
    return d_trueNode;
  }
  else if(constraints.size() == 1)
  {
    return constraints[0];
  }
  return NodeManager::currentNM()->mkNode(kind::AND, constraints);;
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
