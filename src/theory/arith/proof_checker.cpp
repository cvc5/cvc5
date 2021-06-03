/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of arithmetic proof checker.
 */

#include "theory/arith/proof_checker.h"

#include <iostream>
#include <set>

#include "expr/skolem_manager.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/constraint.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/operator_elim.h"

namespace cvc5 {
namespace theory {
namespace arith {

void ArithProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::MACRO_ARITH_SCALE_SUM_UB, this);
  pc->registerChecker(PfRule::ARITH_SUM_UB, this);
  pc->registerChecker(PfRule::ARITH_TRICHOTOMY, this);
  pc->registerChecker(PfRule::INT_TIGHT_UB, this);
  pc->registerChecker(PfRule::INT_TIGHT_LB, this);
  pc->registerChecker(PfRule::ARITH_OP_ELIM_AXIOM, this);

  pc->registerChecker(PfRule::ARITH_MULT_POS, this);
  pc->registerChecker(PfRule::ARITH_MULT_NEG, this);
  // trusted rules
  pc->registerTrustedChecker(PfRule::INT_TRUST, this, 2);
}

Node ArithProofRuleChecker::checkInternal(PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  auto zero = nm->mkConst<Rational>(0);
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
    case PfRule::ARITH_MULT_POS:
    {
      Assert(children.empty());
      Assert(args.size() == 2);
      Node mult = args[0];
      Kind rel = args[1].getKind();
      Assert(rel == Kind::EQUAL || rel == Kind::DISTINCT || rel == Kind::LT
             || rel == Kind::LEQ || rel == Kind::GT || rel == Kind::GEQ);
      Node lhs = args[1][0];
      Node rhs = args[1][1];
      return nm->mkNode(Kind::IMPLIES,
                        nm->mkAnd(std::vector<Node>{
                            nm->mkNode(Kind::GT, mult, zero), args[1]}),
                        nm->mkNode(rel,
                                   nm->mkNode(Kind::MULT, mult, lhs),
                                   nm->mkNode(Kind::MULT, mult, rhs)));
    }
    case PfRule::ARITH_MULT_NEG:
    {
      Assert(children.empty());
      Assert(args.size() == 2);
      Node mult = args[0];
      Kind rel = args[1].getKind();
      Assert(rel == Kind::EQUAL || rel == Kind::DISTINCT || rel == Kind::LT
             || rel == Kind::LEQ || rel == Kind::GT || rel == Kind::GEQ);
      Kind rel_inv = (rel == Kind::DISTINCT ? rel : reverseRelationKind(rel));
      Node lhs = args[1][0];
      Node rhs = args[1][1];
      return nm->mkNode(Kind::IMPLIES,
                        nm->mkAnd(std::vector<Node>{
                            nm->mkNode(Kind::LT, mult, zero), args[1]}),
                        nm->mkNode(rel_inv,
                                   nm->mkNode(Kind::MULT, mult, lhs),
                                   nm->mkNode(Kind::MULT, mult, rhs)));
    }
    case PfRule::ARITH_SUM_UB:
    {
      if (children.size() < 2)
      {
        return Node::null();
      }

      // Whether a strict inequality is in the sum.
      bool strict = false;
      NodeBuilder leftSum(Kind::PLUS);
      NodeBuilder rightSum(Kind::PLUS);
      for (size_t i = 0; i < children.size(); ++i)
      {
        // Adjust strictness
        switch (children[i].getKind())
        {
          case Kind::LT:
          {
            strict = true;
            break;
          }
          case Kind::LEQ:
          case Kind::EQUAL:
          {
            break;
          }
          default:
          {
            Debug("arith::pf::check")
                << "Bad kind: " << children[i].getKind() << std::endl;
            return Node::null();
          }
        }
        leftSum << children[i][0];
        rightSum << children[i][1];
      }
      Node r = nm->mkNode(strict ? Kind::LT : Kind::LEQ,
                          leftSum.constructNode(),
                          rightSum.constructNode());
      return r;
    }
    case PfRule::MACRO_ARITH_SCALE_SUM_UB:
    {
      //================================================= Arithmetic rules
      // ======== Adding Inequalities
      // Note: an ArithLiteral is a term of the form (>< poly const)
      // where
      //   >< is >=, >, ==, <, <=, or not(== ...).
      //   poly is a polynomial
      //   const is a rational constant

      // Children: (P1:l1, ..., Pn:ln)
      //           where each li is an ArithLiteral
      //           not(= ...) is dis-allowed!
      //
      // Arguments: (k1, ..., kn), non-zero reals
      // ---------------------
      // Conclusion: (>< t1 t2)
      //    where >< is the fusion of the combination of the ><i, (flipping each
      //    it its ki is negative). >< is always one of <, <= NB: this implies
      //    that lower bounds must have negative ki,
      //                      and upper bounds must have positive ki.
      //    t1 is the sum of the scaled polynomials (k_1 * poly_1 + ... + k_n *
      //    poly_n) t2 is the sum of the scaled constants (k_1 * const_1 + ... +
      //    k_n * const_n)
      Assert(children.size() == args.size());
      if (children.size() < 2)
      {
        return Node::null();
      }

      // Whether a strict inequality is in the sum.
      bool strict = false;
      NodeBuilder leftSum(Kind::PLUS);
      NodeBuilder rightSum(Kind::PLUS);
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
            Kind::MULT, nm->mkConst<Rational>(scalar), children[i][0]);
        rightSum << nm->mkNode(
            Kind::MULT, nm->mkConst<Rational>(scalar), children[i][1]);
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
      if (Debug.isOn("arith::pf::check::trust"))
      {
        Debug("arith::pf::check::trust") << "Arith PfRule:" << id << std::endl;
        Debug("arith::pf::check::trust") << "  children: " << std::endl;
        for (const auto& c : children)
        {
          Debug("arith::pf::check::trust") << "  * " << c << std::endl;
        }
        Debug("arith::pf::check::trust") << "  args:" << std::endl;
        for (const auto& c : args)
        {
          Debug("arith::pf::check::trust") << "  * " << c << std::endl;
        }
      }
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
}  // namespace cvc5
