/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/operator_elim.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

ArithProofRuleChecker::ArithProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm),
      d_extChecker(nm),
      d_trChecker(nm)
#ifdef CVC5_POLY_IMP
      ,
      d_covChecker(nm)
#endif
{
}

void ArithProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::MACRO_ARITH_SCALE_SUM_UB, this);
  pc->registerChecker(ProofRule::ARITH_SUM_UB, this);
  pc->registerChecker(ProofRule::ARITH_TRICHOTOMY, this);
  pc->registerChecker(ProofRule::INT_TIGHT_UB, this);
  pc->registerChecker(ProofRule::INT_TIGHT_LB, this);
  pc->registerChecker(ProofRule::ARITH_REDUCTION, this);
  pc->registerChecker(ProofRule::ARITH_MULT_POS, this);
  pc->registerChecker(ProofRule::ARITH_MULT_NEG, this);
  pc->registerChecker(ProofRule::ARITH_POLY_NORM, this);
  pc->registerChecker(ProofRule::ARITH_POLY_NORM_REL, this);
  // register the extended proof checkers
  d_extChecker.registerTo(pc);
  d_trChecker.registerTo(pc);
#ifdef CVC5_POLY_IMP
  d_covChecker.registerTo(pc);
#endif
}

Node ArithProofRuleChecker::checkInternal(ProofRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (TraceIsOn("arith::pf::check"))
  {
    Trace("arith::pf::check") << "Arith ProofRule:" << id << std::endl;
    Trace("arith::pf::check") << "  children: " << std::endl;
    for (const auto& c : children)
    {
      Trace("arith::pf::check") << "  * " << c << std::endl;
    }
    Trace("arith::pf::check") << "  args:" << std::endl;
    for (const auto& c : args)
    {
      Trace("arith::pf::check") << "  * " << c << std::endl;
    }
  }
  switch (id)
  {
    case ProofRule::ARITH_MULT_POS:
    {
      Assert(children.empty());
      Assert(args.size() == 2);
      Node mult = args[0];
      Kind rel = args[1].getKind();
      Assert(rel == Kind::EQUAL || rel == Kind::DISTINCT || rel == Kind::LT
             || rel == Kind::LEQ || rel == Kind::GT || rel == Kind::GEQ);
      Node lhs = args[1][0];
      Node rhs = args[1][1];
      Node zero = nm->mkConstRealOrInt(mult.getType(), Rational(0));
      return nm->mkNode(Kind::IMPLIES,
                        nm->mkAnd(std::vector<Node>{
                            nm->mkNode(Kind::GT, mult, zero), args[1]}),
                        nm->mkNode(rel,
                                   nm->mkNode(Kind::MULT, mult, lhs),
                                   nm->mkNode(Kind::MULT, mult, rhs)));
    }
    case ProofRule::ARITH_MULT_NEG:
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
      Node zero = nm->mkConstRealOrInt(mult.getType(), Rational(0));
      return nm->mkNode(Kind::IMPLIES,
                        nm->mkAnd(std::vector<Node>{
                            nm->mkNode(Kind::LT, mult, zero), args[1]}),
                        nm->mkNode(rel_inv,
                                   nm->mkNode(Kind::MULT, mult, lhs),
                                   nm->mkNode(Kind::MULT, mult, rhs)));
    }
    case ProofRule::ARITH_SUM_UB:
    {
      if (children.size() < 2)
      {
        return Node::null();
      }

      // Whether a strict inequality is in the sum.
      bool strict = false;
      NodeBuilder leftSum(nm, Kind::ADD);
      NodeBuilder rightSum(nm, Kind::ADD);
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
            Trace("arith::pf::check")
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
    case ProofRule::MACRO_ARITH_SCALE_SUM_UB:
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
      NodeBuilder leftSum(nm, Kind::ADD);
      NodeBuilder rightSum(nm, Kind::ADD);
      for (size_t i = 0; i < children.size(); ++i)
      {
        Rational scalar = args[i].getConst<Rational>();
        if (scalar == 0)
        {
          Trace("arith::pf::check") << "Error: zero scalar" << std::endl;
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
            Trace("arith::pf::check")
                << "Bad kind: " << children[i].getKind() << std::endl;
          }
        }
        // check for spurious mixed arithmetic
        if (children[i][0].getType().isReal()
            || children[i][1].getType().isReal())
        {
          if (args[i].getType().isInteger())
          {
            // Should use real for predicates over reals. This is only
            // necessary for avoiding spurious usage of mixed arithmetic, but we
            // check here to be pedantic.
            return Node::null();
          }
        }
        else if (args[i].getType().isReal() && scalar.isIntegral())
        {
          // conversely, don't use (integral) real for integer relation.
          return Node::null();
        }
        // Check sign
        switch (children[i].getKind())
        {
          case Kind::GT:
          case Kind::GEQ:
          {
            if (scalar > 0)
            {
              Trace("arith::pf::check")
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
              Trace("arith::pf::check")
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
            Trace("arith::pf::check")
                << "Bad kind: " << children[i].getKind() << std::endl;
          }
        }
        // if multiplying by one, don't introduce MULT
        if (scalar == 1)
        {
          leftSum << children[i][0];
          rightSum << children[i][1];
        }
        else
        {
          leftSum << nm->mkNode(Kind::MULT, args[i], children[i][0]);
          rightSum << nm->mkNode(Kind::MULT, args[i], children[i][1]);
        }
      }
      Node r = nm->mkNode(strict ? Kind::LT : Kind::LEQ,
                          leftSum.constructNode(),
                          rightSum.constructNode());
      return r;
    }
    case ProofRule::INT_TIGHT_LB:
    {
      // Children: (P:(> i c))
      //         where i has integer type.
      // Arguments: none
      // ---------------------
      // Conclusion: (>= i leastIntGreaterThan(c)})
      if (children.size() != 1
          || (children[0].getKind() != Kind::GT
              && children[0].getKind() != Kind::GEQ)
          || !children[0][0].getType().isInteger() || !children[0][1].isConst())
      {
        Trace("arith::pf::check") << "Illformed input: " << children;
        return Node::null();
      }
      else
      {
        Rational originalBound = children[0][1].getConst<Rational>();
        Rational newBound = leastIntGreaterThan(originalBound);
        Node rational = nm->mkConstInt(newBound);
        return nm->mkNode(Kind::GEQ, children[0][0], rational);
      }
    }
    case ProofRule::INT_TIGHT_UB:
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
          || !children[0][0].getType().isInteger() || !children[0][1].isConst())
      {
        Trace("arith::pf::check") << "Illformed input: " << children;
        return Node::null();
      }
      else
      {
        Rational originalBound = children[0][1].getConst<Rational>();
        Rational newBound = greatestIntLessThan(originalBound);
        Node rational = nm->mkConstInt(newBound);
        return nm->mkNode(Kind::LEQ, children[0][0], rational);
      }
    }
    case ProofRule::ARITH_TRICHOTOMY:
    {
      Node a = negateProofLiteral(children[0]);
      Node b = negateProofLiteral(children[1]);
      if (a[0] == b[0] && a[1] == b[1])
      {
        std::set<Kind> cmps;
        cmps.insert(a.getKind());
        cmps.insert(b.getKind());
        Kind retk = Kind::UNDEFINED_KIND;
        if (cmps.count(Kind::EQUAL) == 0)
        {
          retk = Kind::EQUAL;
        }
        if (cmps.count(Kind::GT) == 0)
        {
          if (retk != Kind::UNDEFINED_KIND)
          {
            Trace("arith::pf::check")
                << "Error: No GT and " << retk << std::endl;
            return Node::null();
          }
          retk = Kind::GT;
        }
        if (cmps.count(Kind::LT) == 0)
        {
          if (retk != Kind::UNDEFINED_KIND)
          {
            Trace("arith::pf::check")
                << "Error: No LT and " << retk << std::endl;
            return Node::null();
          }
          retk = Kind::LT;
        }
        return nm->mkNode(retk, a[0], a[1]);
      }
      else
      {
        Trace("arith::pf::check")
            << "Error: Different polynomials / values" << std::endl;
        Trace("arith::pf::check") << "  a: " << a << std::endl;
        Trace("arith::pf::check") << "  b: " << b << std::endl;
        return Node::null();
      }
      // Check that all have the same constant:
    }
    case ProofRule::ARITH_REDUCTION:
    {
      Assert(children.empty());
      Assert(args.size() == 1);
      return OperatorElim::getAxiomFor(nm, args[0]);
    }
    case ProofRule::ARITH_POLY_NORM:
    {
      Assert(children.empty());
      Assert(args.size() == 1);
      if (args[0].getKind() != Kind::EQUAL
          || !args[0][0].getType().isRealOrInt())
      {
        return Node::null();
      }
      if (!PolyNorm::isArithPolyNorm(args[0][0], args[0][1]))
      {
        return Node::null();
      }
      return args[0];
    }
    case ProofRule::ARITH_POLY_NORM_REL:
    {
      Assert(children.size() == 1);
      Assert(args.size() == 1);
      if (args[0].getKind() != Kind::EQUAL)
      {
        return Node::null();
      }
      Kind k = args[0][0].getKind();
      if (k != Kind::LT && k != Kind::LEQ && k != Kind::EQUAL && k != Kind::GT
          && k != Kind::GEQ)
      {
        return Node::null();
      }
      if (children[0].getKind() != Kind::EQUAL)
      {
        return Node::null();
      }
      Node l = children[0][0];
      Node r = children[0][1];
      if (l.getKind() != Kind::MULT || r.getKind() != Kind::MULT)
      {
        return Node::null();
      }
      Node lr = l[1];
      lr = lr.getKind() == Kind::TO_REAL ? lr[0] : lr;
      Node rr = r[1];
      rr = rr.getKind() == Kind::TO_REAL ? rr[0] : rr;
      if (lr.getKind() != Kind::SUB || rr.getKind() != Kind::SUB)
      {
        return Node::null();
      }
      Node cx = l[0];
      Node x1 = lr[0];
      Node x2 = lr[1];
      Node cy = r[0];
      Node y1 = rr[0];
      Node y2 = rr[1];
      if ((cx.getKind() == Kind::CONST_INTEGER
           || cx.getKind() == Kind::CONST_RATIONAL)
          && (cy.getKind() == Kind::CONST_INTEGER
              || cy.getKind() == Kind::CONST_RATIONAL))
      {
        Rational c1 = cx.getConst<Rational>();
        Rational c2 = cy.getConst<Rational>();
        if (k != Kind::EQUAL && c1.sgn() != c2.sgn())
        {
          return Node::null();
        }
      }
      Node ret = nm->mkNode(k, x1, x2).eqNode(nm->mkNode(k, y1, y2));
      if (ret != args[0])
      {
        return Node::null();
      }
      return ret;
    }
    default: return Node::null();
  }
}
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
