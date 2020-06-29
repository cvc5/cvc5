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
#include <set>

#include "expr/skolem_manager.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/constraint.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/operator_elim.h"

namespace CVC4 {
namespace theory {
namespace arith {

void ArithProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ARITH_SCALE_SUM_UPPER_BOUNDS, this);
  pc->registerChecker(PfRule::ARITH_TRICHOTOMY, this);
  pc->registerChecker(PfRule::INT_TIGHT_UB, this);
  pc->registerChecker(PfRule::INT_TIGHT_LB, this);
  pc->registerChecker(PfRule::INT_TRUST, this);
  pc->registerChecker(PfRule::ARITH_OP_ELIM_AXIOM, this);
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
    case PfRule::ARITH_SCALE_SUM_UPPER_BOUNDS:
    {
      // Children: (P1:l1, ..., Pn:ln)
      //           where each li is an ArithLiteral
      //           not(= ...) is dis-allowed!
      //
      // Arguments: (k1, ..., kn), non-zero reals
      // ---------------------
      // Conclusion: (>< (* k t1) (* k t2))
      //    where >< is the fusion of the combination of the ><i, (flipping each
      //    it its ki is negative). >< is always one of <, <= NB: this implies
      //    that lower bounds must have negative ki,
      //                      and upper bounds must have positive ki.
      //    t1 is the sum of the polynomials.
      //    t2 is the sum of the constants.
      Assert(children.size() == args.size());
      if (children.size() < 2)
      {
        return Node::null();
      }

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
          Debug("arith::pf::check") << "Error: zero scalar" << std::endl;
          return Node::null();
        }

        // Adjust strictness
        switch (children[i].getKind())
        {
          case Kind::GT:
          case Kind::LT:
          {
            strict = true;
            break;
          }
          case Kind::GEQ:
          case Kind::LEQ:
          case Kind::EQUAL:
          {
            break;
          }
          default:
          {
            Debug("arith::pf::check")
                << "Bad kind: " << children[i].getKind() << std::endl;
          }
        }
        // Check sign
        switch (children[i].getKind())
        {
          case Kind::GT:
          case Kind::GEQ:
          {
            if (scalar > 0)
            {
              Debug("arith::pf::check")
                  << "Positive scalar for lower bound: " << scalar << " for "
                  << children[i] << std::endl;
              return Node::null();
            }
            break;
          }
          case Kind::LEQ:
          case Kind::LT:
          {
            if (scalar < 0)
            {
              Debug("arith::pf::check")
                  << "Negative scalar for upper bound: " << scalar << " for "
                  << children[i] << std::endl;
              return Node::null();
            }
            break;
          }
          case Kind::EQUAL:
          {
            break;
          }
          default:
          {
            Debug("arith::pf::check")
                << "Bad kind: " << children[i].getKind() << std::endl;
          }
        }
        leftSum << nm->mkNode(
            Kind::MULT, children[i][0], nm->mkConst<Rational>(scalar));
        rightSum << nm->mkNode(
            Kind::MULT, children[i][1], nm->mkConst<Rational>(scalar));
      }
      Node r = nm->mkNode(strict ? Kind::LT : Kind::LEQ,
                          leftSum.constructNode(),
                          rightSum.constructNode());
      return r;
    }
    case PfRule::INT_TIGHT_LB:
    {
      // Children: (P:(> i c))
      //         where i has integer type.
      // Arguments: none
      // ---------------------
      // Conclusion: (>= i leastIntGreaterThan(c)})
      if (children.size() != 1
          || (children[0].getKind() != Kind::GT
              && children[0].getKind() != Kind::GEQ)
          || !children[0][0].getType().isInteger()
          || children[0][1].getKind() != Kind::CONST_RATIONAL)
      {
        Debug("arith::pf::check") << "Illformed input: " << children;
        return Node::null();
      }
      else
      {
        Rational originalBound = children[0][1].getConst<Rational>();
        Rational newBound = leastIntGreaterThan(originalBound);
        auto nm = NodeManager::currentNM();
        Node rational = nm->mkConst<Rational>(newBound);
        return nm->mkNode(kind::GEQ, children[0][0], rational);
      }
    }
    case PfRule::INT_TIGHT_UB:
    {
      // ======== Tightening Strict Integer Upper Bounds
      // Children: (P:(< i c))
      //         where i has integer type.
      // Arguments: none
      // ---------------------
      // Conclusion: (<= i greatestIntLessThan(c)})
      if (children.size() != 1
          || (children[0].getKind() != Kind::LT
              && children[0].getKind() != Kind::LEQ)
          || !children[0][0].getType().isInteger()
          || children[0][1].getKind() != Kind::CONST_RATIONAL)
      {
        Debug("arith::pf::check") << "Illformed input: " << children;
        return Node::null();
      }
      else
      {
        Rational originalBound = children[0][1].getConst<Rational>();
        Rational newBound = greatestIntLessThan(originalBound);
        auto nm = NodeManager::currentNM();
        Node rational = nm->mkConst<Rational>(newBound);
        return nm->mkNode(kind::LEQ, children[0][0], rational);
      }
    }
    case PfRule::ARITH_TRICHOTOMY:
    {
      Node a = negateProofLiteral(children[0]);
      Node b = negateProofLiteral(children[1]);
      Node c = args[0];
      if (a[0] == b[0] && b[0] == c[0] && a[1] == b[1] && b[1] == c[1])
      {
        std::set<Kind> cmps;
        cmps.insert(a.getKind());
        cmps.insert(b.getKind());
        cmps.insert(c.getKind());
        if (cmps.count(Kind::EQUAL) == 0)
        {
          Debug("arith::pf::check") << "Error: No = " << std::endl;
          return Node::null();
        }
        if (cmps.count(Kind::GT) == 0)
        {
          Debug("arith::pf::check") << "Error: No > " << std::endl;
          return Node::null();
        }
        if (cmps.count(Kind::LT) == 0)
        {
          Debug("arith::pf::check") << "Error: No < " << std::endl;
          return Node::null();
        }
        return args[0];
      }
      else
      {
        Debug("arith::pf::check")
            << "Error: Different polynomials / values" << std::endl;
        Debug("arith::pf::check") << "  a: " << a << std::endl;
        Debug("arith::pf::check") << "  b: " << b << std::endl;
        Debug("arith::pf::check") << "  c: " << c << std::endl;
        return Node::null();
      }
      // Check that all have the same constant:
    }
    case PfRule::INT_TRUST:
    {
      Assert(args.size() == 1);
      return args[0];
    }
    case PfRule::ARITH_OP_ELIM_AXIOM:
    {
      Assert(children.empty());
      Assert(args.size() == 1);
      return OperatorElim::getAxiomFor(args[0]);
    }
    default: return Node::null();
  }
}
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
