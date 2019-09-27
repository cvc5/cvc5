/*********************                                                        */
/*! \file symmetry_breaker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry breaker module
 **/

#include "preprocessing/passes/symmetry_breaker.h"

#include "preprocessing/passes/symmetry_detect.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

Node SymmetryBreaker::generateSymBkConstraints(const vector<vector<Node>>& parts)
{
  vector<Node> constraints;
  NodeManager* nm = NodeManager::currentNM();

  for (const vector<Node>& part : parts)
  {
    if (part.size() >= 2)
    {
      Kind kd = getOrderKind(part[0]);
      if (kd == UNDEFINED_KIND)
      {
        // no symmetry breaking possible
        continue;
      }
      if (kd != EQUAL)
      {
        for (unsigned int i = 0; i < part.size() - 1; ++i)
        {
          // Generate less than or equal to constraints: part[i] <= part[i+1]
          Node constraint = nm->mkNode(kd, part[i], part[i + 1]);
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
          for (unsigned int j = i + 2; j < part.size(); ++j)
          {
            // Generate consecutive constraints v_i = v_j => v_i = v_{j-1},
            // for all 0 <= i < j-1 < j < part.size()
            Node constraint = nm->mkNode(IMPLIES,
                                         nm->mkNode(kd, part[i], part[j]),
                                         nm->mkNode(kd, part[i], part[j - 1]));
            constraints.push_back(constraint);
            Trace("sym-bk")
                << "[sym-bk] Generate a symmetry breaking constraint: "
                << constraint << endl;
          }
          if (i >= 1)
          {
            for (unsigned int j = i + 1; j < part.size(); ++j)
            {
              Node lhs = nm->mkNode(kd, part[i], part[j]);
              Node rhs = nm->mkNode(kd, part[i], part[i - 1]);
              int prev_seg_start_index = 2*i - j - 1;

              // Since prev_seg_len is always less than i - 1, we just need to make
              // sure prev_seg_len is greater than or equal to 0
              if(prev_seg_start_index >= 0)
              {
                rhs = nm->mkNode(
                    OR,
                    rhs,
                    nm->mkNode(kd, part[i - 1], part[prev_seg_start_index]));
              }
              // Generate length order constraints
              // v_i = v_j => (v_{i} = v_{i-1} OR v_{i-1} = x_{(i-1)-(j-i)})
              // for all 1 <= i < j < part.size() and (i-1)-(j-i) >= 0
              Node constraint = nm->mkNode(IMPLIES, lhs, rhs);
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
  return nm->mkNode(AND, constraints);
}

Kind SymmetryBreaker::getOrderKind(Node node)
{
  TypeNode tn = node.getType();
  if (tn.isBoolean())
  {
    return IMPLIES;
  }
  else if (tn.isReal())
  {
    return LEQ;
  }
  else if (tn.isBitVector())
  {
    return BITVECTOR_ULE;
  }
  if (tn.isFirstClass())
  {
    return EQUAL;
  }
  return UNDEFINED_KIND;
}

SymBreakerPass::SymBreakerPass(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sym-break"){};

PreprocessingPassResult SymBreakerPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Trace("sym-break-pass") << "Apply symmetry breaker pass..." << std::endl;
  // detect symmetries
  std::vector<std::vector<Node>> sterms;
  symbreak::SymmetryDetect symd;
  symd.computeTerms(sterms, assertionsToPreprocess->ref());
  if (Trace.isOn("sym-break-pass") || Trace.isOn("sb-constraint"))
  {
    if (sterms.empty())
    {
      Trace("sym-break-pass") << "Detected no symmetric terms." << std::endl;
    }
    else
    {
      Trace("sb-constraint") << "; found symmetry" << std::endl;
      Trace("sym-break-pass") << "Detected symmetric terms:" << std::endl;
      for (const std::vector<Node>& p : sterms)
      {
        Trace("sym-break-pass") << "  " << p << std::endl;
      }
    }
  }
  // construct the symmetry breaking constraint
  Trace("sym-break-pass") << "Construct symmetry breaking constraint..."
                          << std::endl;
  SymmetryBreaker symb;
  Node sbConstraint = symb.generateSymBkConstraints(sterms);
  // add symmetry breaking constraint to the set of assertions
  Trace("sym-break-pass") << "...got: " << sbConstraint << std::endl;
  // if not true
  if (!sbConstraint.isConst())
  {
    Trace("sb-constraint") << "(symmetry-break " << sbConstraint << ")"
                           << std::endl;
    // add to assertions
    assertionsToPreprocess->push_back(sbConstraint);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
