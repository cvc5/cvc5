/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of arithmetic proof checker
 **/

#include "theory/arith/proof_checker.h"

#include <iostream>

#include "theory/arith/arith_utilities.h"
#include "theory/arith/constraint.h"
#include "theory/arith/normal_form.h"

namespace CVC4 {
namespace theory {
namespace arith {

void ArithProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::SCALE_SUM_UPPER_BOUNDS, this);
  pc->registerChecker(PfRule::TRICHOTOMY, this);
  pc->registerChecker(PfRule::INT_TIGHT_UB, this);
  pc->registerChecker(PfRule::INT_TIGHT_LB, this);
  pc->registerChecker(PfRule::INT_TRUST, this);
}

Node ArithProofRuleChecker::checkInternal(PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args)
{
  if (Debug.isOn("arith::pf::check"))
  {
    Debug("arith::pf::check") << "Arith PfRule:" << id << std::endl;
    Debug("arith::pf::check") << "  children: " << std::endl;
    for (const auto& c : children)
    {
      Debug("arith::pf::check") << "  * " << c << std::endl;
    }
    Debug("arith::pf::check") << "  args:" << std::endl;
    for (const auto& c : args)
    {
      Debug("arith::pf::check") << "  * " << c << std::endl;
    }
  }
  switch (id)
  {
    case PfRule::SCALE_SUM_UPPER_BOUNDS:
    {
      // Children: (P1:(><1 l1 r1), ... , Pn(><n ln rn))
      //           where each ><i is a (possibly negated) >, >=, =
      //           not(= ...) is dis-allowed!
      //
      // Arguments: (k1, ..., kn), non-zero reals
      // ---------------------
      // Conclusion: (>< (* k t1) (* k t2))
      //    where >< is the fusion of the combination of the ><i, (flipping each
      //    it its ki is negative). >< is always one of <, <= NB: this implies
      //    that lower bounds must have negative ki,
      //                      and upper bounds must have positive ki.
      Assert(children.size() == args.size());

      // Whether a strict inequality is in the sum.
      auto nm = NodeManager::currentNM();
      bool strict = false;
      NodeBuilder<> leftSum(Kind::PLUS);
      NodeBuilder<> rightSum(Kind::PLUS);
      for (size_t i = 0; i < children.size(); ++i)
      {
        Rational scalar = args[i].getConst<Rational>();
        if (scalar == 0)
        {
          Debug("arith::pf::check") << "Error: zeor scalar" << std::endl;
          return Node::null();
        }
        if (children[i].getKind() == Kind::NOT)
        {
          if (scalar < 0)
          {
            Debug("arith::pf::check") << "Warning: upper bound with negative "
                                         "scalar. Fixing scalar sign."
                                      << std::endl;
            scalar = -scalar;
          }
          leftSum << nm->mkNode(
              Kind::MULT, children[i][0][0], nm->mkConst<Rational>(scalar));
          rightSum << nm->mkNode(
              Kind::MULT, children[i][0][1], nm->mkConst<Rational>(scalar));
          switch (children[i][0].getKind())
          {
            case Kind::GT:
            {
              break;
            }
            case Kind::GEQ:
            {
              strict = true;
              break;
            }
            default:
            {
              Debug("arith::pf::check")
                  << "Error: not without >/>= in it" << std::endl;
              return Node::null();
            }
          }
        }
        else
        {
          if (scalar >= 0 && Kind::EQUAL != children[i].getKind())
          {
            Debug("arith::pf::check") << "Warning: lower bound with postive "
                                         "scalar. Fixing scalar sign."
                                      << std::endl;
            scalar = -scalar;
          }
          leftSum << nm->mkNode(
              Kind::MULT, children[i][0], nm->mkConst<Rational>(scalar));
          rightSum << nm->mkNode(
              Kind::MULT, children[i][1], nm->mkConst<Rational>(scalar));
          switch (children[i].getKind())
          {
            case Kind::GT:
            {
              strict = true;
              break;
            }
            case Kind::GEQ:
            {
              break;
            }
            case Kind::EQUAL:
            {
              break;
            }
            default:
            {
              Debug("arith::pf::check")
                  << "Arith lit without >/>=/=/not at the top" << std::endl;
              return Node::null();
            }
          }
        }
      }
      if (strict)
      {
        return nm->mkNode(
            Kind::LT, leftSum.constructNode(), rightSum.constructNode());
      }
      else
      {
        return nm->mkNode(
            Kind::LEQ, leftSum.constructNode(), rightSum.constructNode());
      }
    }
    case PfRule::INT_TIGHT_LB:
    {
      // ======== Tightening Strict Integer Lower Bounds
      // Children: (P:(> i c))
      // Arguments: none
      // ---------------------
      // Conclusion: (>= i leastIntGreaterThan(c)})
      Assert(children.size() == 1);
      Assert(children[0].getKind() == Kind::GT) << children[0];
      Assert(children[0].getNumChildren() == 2) << children[0];
      Assert(children[0][0].getType().isInteger()) << children[0];
      Assert(children[0][1].getKind() == kind::CONST_RATIONAL) << children[0];
      Rational originalBound = children[0][1].getConst<Rational>();
      Rational newBound = leastIntGreaterThan(originalBound);
      auto nm = NodeManager::currentNM();
      Node rational = nm->mkConst<Rational>(newBound);
      Node n = nm->mkNode(kind::GEQ, children[0][0], rational);
      return n;
    }
    case PfRule::INT_TIGHT_UB:
    {
      // Children: (P:(not (>= i c)))
      // Arguments: none
      // ---------------------
      // Conclusion: (not (> i greatestIntLessThan(c)}))
      Assert(children.size() == 1);
      Assert(children[0].getKind() == kind::NOT) << children[0];
      Assert(children[0].getNumChildren() == 1) << children[0];
      Assert(children[0][0].getKind() == kind::GEQ) << children[0];
      Assert(children[0][0].getNumChildren() == 2) << children[0];
      Assert(children[0][0][0].getType().isInteger()) << children[0];
      Assert(children[0][0][1].getKind() == kind::CONST_RATIONAL)
          << children[0];
      Rational originalBound = children[0][0][1].getConst<Rational>();
      Rational newBound = greatestIntLessThan(originalBound);
      auto nm = NodeManager::currentNM();
      return nm
          ->mkNode(kind::GT, children[0][0][0], nm->mkConst<Rational>(newBound))
          .negate();
    }
    case PfRule::TRICHOTOMY:
    {
      Node a = children[0].negate();
      Node b = children[1].negate();
      Node c = args[0];
      Comparison aCmp = Comparison::parseNormalForm(a);
      Comparison bCmp = Comparison::parseNormalForm(b);
      Comparison cCmp = Comparison::parseNormalForm(c);
      DeltaRational aBound = aCmp.normalizedDeltaRational();
      DeltaRational bBound = bCmp.normalizedDeltaRational();
      DeltaRational cBound = cCmp.normalizedDeltaRational();
      Polynomial aPoly = aCmp.normalizedVariablePart();
      Polynomial bPoly = bCmp.normalizedVariablePart();
      Polynomial cPoly = cCmp.normalizedVariablePart();
      Rational constA = aBound.getNoninfinitesimalPart();
      Rational constB = bBound.getNoninfinitesimalPart();
      Rational constC = cBound.getNoninfinitesimalPart();
      if (constA == constB && constB == constC)
      {
        if (aPoly.getNode() == bPoly.getNode()
            && bPoly.getNode() == cPoly.getNode())
        {
          std::unordered_set<int> infinitesimalSgns;
          infinitesimalSgns.insert(aBound.infinitesimalSgn());
          infinitesimalSgns.insert(bBound.infinitesimalSgn());
          infinitesimalSgns.insert(cBound.infinitesimalSgn());
          if (infinitesimalSgns.count(0) == 0)
          {
            Debug("arith::pf::check") << "Error: No = " << std::endl;
            return Node::null();
          }
          if (infinitesimalSgns.count(-1) == 0)
          {
            Debug("arith::pf::check") << "Error: No -1 " << std::endl;
            return Node::null();
          }
          if (infinitesimalSgns.count(1) == 0)
          {
            Debug("arith::pf::check") << "Error: No 1 " << std::endl;
            return Node::null();
          }
          return args[0];
        }
        else
        {
          Debug("arith::pf::check")
              << "Error: Different polynomial parts " << aPoly.getNode() << " "
              << bPoly.getNode() << " " << cPoly.getNode() << std::endl;
          return Node::null();
        }
      }
      else
      {
        Debug("arith::pf::check")
            << "Error: Different constants " << constA << " " << constB << " "
            << constC << std::endl;
        return Node::null();
      }
      // Check that all have the same constant:
    }
    case PfRule::INT_TRUST:
    {
      Assert(args.size() == 1);
      return args[0];
    }
    default: return Node::null();
  }
}
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
