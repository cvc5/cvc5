/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of NlExt proof checker.
 */

#include "theory/arith/nl/ext/proof_checker.h"

#include "expr/sequence.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/ext/arith_nl_compare_proof_gen.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ExtProofRuleChecker::ExtProofRuleChecker(NodeManager* nm) : ProofRuleChecker(nm)
{
}

void ExtProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::ARITH_MULT_SIGN, this);
  pc->registerChecker(ProofRule::ARITH_MULT_TANGENT, this);
  pc->registerChecker(ProofRule::MACRO_ARITH_NL_COMPARISON, this);
  pc->registerChecker(ProofRule::MACRO_ARITH_NL_ABS_COMPARISON, this);
}

Node ExtProofRuleChecker::checkInternal(ProofRule id,
                                        const std::vector<Node>& children,
                                        const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  Trace("nl-ext-checker") << "Checking " << id << std::endl;
  for (const auto& c : children)
  {
    Trace("nl-ext-checker") << "\t" << c << std::endl;
  }
  if (id == ProofRule::ARITH_MULT_SIGN)
  {
    Assert(children.empty());
    Assert(args.size() > 1);
    Node mon = args.back();
    std::map<Node, int> exps;
    std::vector<Node> premise = args;
    premise.pop_back();
    Assert(mon.getKind() == Kind::MULT
           || mon.getKind() == Kind::NONLINEAR_MULT);
    for (const auto& v : mon)
    {
      exps[v]++;
    }
    std::map<Node, int> signs;
    for (const auto& f : premise)
    {
      if (f.getKind() == Kind::NOT)
      {
        Assert(f[0].getKind() == Kind::EQUAL);
        Assert(f[0][1].isConst() && f[0][1].getConst<Rational>().isZero());
        Assert(signs.find(f[0][0]) == signs.end());
        signs.emplace(f[0][0], 0);
        continue;
      }
      Assert(f.getKind() == Kind::LT || f.getKind() == Kind::GT);
      Assert(f[1].isConst() && f[1].getConst<Rational>().isZero());
      Assert(signs.find(f[0]) == signs.end());
      signs.emplace(f[0], f.getKind() == Kind::LT ? -1 : 1);
    }
    int sign = 0;
    for (const auto& ve : exps)
    {
      auto sit = signs.find(ve.first);
      Assert(sit != signs.end());
      if (ve.second % 2 == 0)
      {
        Assert(sit->second == 0);
        if (sign == 0)
        {
          sign = 1;
        }
      }
      else
      {
        Assert(sit->second != 0);
        if (sign == 0)
        {
          sign = sit->second;
        }
        else
        {
          sign *= sit->second;
        }
      }
    }
    Node zero = nm->mkConstRealOrInt(mon.getType(), Rational(0));
    switch (sign)
    {
      case -1:
        return nm->mkNode(
            Kind::IMPLIES, nm->mkAnd(premise), nm->mkNode(Kind::GT, zero, mon));
      case 0:
        return nm->mkNode(Kind::IMPLIES,
                          nm->mkAnd(premise),
                          nm->mkNode(Kind::DISTINCT, mon, zero));
      case 1:
        return nm->mkNode(
            Kind::IMPLIES, nm->mkAnd(premise), nm->mkNode(Kind::GT, mon, zero));
      default: Assert(false); return Node();
    }
  }
  else if (id == ProofRule::ARITH_MULT_TANGENT)
  {
    Assert(children.empty());
    Assert(args.size() == 5);
    Assert(args[0].getType().isRealOrInt());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].getType().isRealOrInt());
    Assert(args[3].getType().isRealOrInt());
    Assert(args[4].isConst() && args[4].getConst<Rational>().isIntegral());
    Node x = args[0];
    Node y = args[1];
    Node t = nm->mkNode(Kind::NONLINEAR_MULT, x, y);
    Node a = args[2];
    Node b = args[3];
    int sgn = args[4].getConst<Rational>().getNumerator().sgn();
    Assert(sgn == -1 || sgn == 1);
    Node tplane = nm->mkNode(Kind::SUB,
                             nm->mkNode(Kind::ADD,
                                        nm->mkNode(Kind::MULT, b, x),
                                        nm->mkNode(Kind::MULT, a, y)),
                             nm->mkNode(Kind::MULT, a, b));
    return nm->mkNode(
        Kind::EQUAL,
        nm->mkNode(sgn == -1 ? Kind::LEQ : Kind::GEQ, t, tplane),
        nm->mkNode(
            Kind::OR,
            nm->mkNode(Kind::AND,
                       nm->mkNode(Kind::LEQ, x, a),
                       nm->mkNode(sgn == -1 ? Kind::GEQ : Kind::LEQ, y, b)),
            nm->mkNode(Kind::AND,
                       nm->mkNode(Kind::GEQ, x, a),
                       nm->mkNode(sgn == -1 ? Kind::LEQ : Kind::GEQ, y, b))));
  }
  else if (id == ProofRule::MACRO_ARITH_NL_COMPARISON
           || id == ProofRule::MACRO_ARITH_NL_ABS_COMPARISON)
  {
    Assert(args.size() == 1);
    bool isAbs = (id == ProofRule::MACRO_ARITH_NL_ABS_COMPARISON);
    // decompose the conclusion first
    std::vector<Node> cprod[2];
    // note we treat the conclusion as a singleton if there is exactly one
    // premise.
    Kind conck = ArithNlCompareProofGenerator::decomposeCompareLit(
        args[0], isAbs, cprod[0], cprod[1], children.size()==1);
    if (conck == Kind::UNDEFINED_KIND)
    {
      return Node::null();
    }
    if (cprod[0].size() != cprod[1].size())
    {
      return Node::null();
    }
    Kind k = Kind::EQUAL;
    size_t cindex = 0;
    bool allZeroGuards = true;
    for (const Node& c : children)
    {
      std::vector<Node> eprod[2];
      Kind ck = c.getKind();
      Node zeroGuard;
      Node lit = c;
      if (ck == Kind::AND)
      {
        zeroGuard = ArithNlCompareProofGenerator::isDisequalZero(c[1]);
        // it may be a disequality with zero
        if (c.getNumChildren() == 2 && !zeroGuard.isNull())
        {
          lit = c[0];
        }
        else
        {
          return Node::null();
        }
      }
      ck = ArithNlCompareProofGenerator::decomposeCompareLit(
          lit, isAbs, eprod[0], eprod[1]);
      if (eprod[0].size() > 1 || eprod[1].size() > 1)
      {
        return Node::null();
      }
      // guarded zero disequality should be for LHS
      if (!zeroGuard.isNull() && (eprod[0].empty() || zeroGuard != eprod[0][0]))
      {
        return Node::null();
      }
      if (ck == Kind::UNDEFINED_KIND)
      {
        return Node::null();
      }
      // check if we have guarded for zero
      if (ck != Kind::LT && ck != Kind::GT && zeroGuard.isNull())
      {
        allZeroGuards = false;
      }
      // combine the implied relation
      k = ArithNlCompareProofGenerator::combineRelation(k, ck);
      if (k == Kind::UNDEFINED_KIND)
      {
        return Node::null();
      }
      if (cindex >= cprod[0].size())
      {
        return Node::null();
      }
      // check that the corresponding factor is the same
      size_t exponent = 0;
      for (size_t j = 0; j < 2; j++)
      {
        const Node& cf = cprod[j][cindex];
        if (eprod[j].empty())
        {
          // factor of conclusion must be one
          if (!cf.isConst() || !cf.getConst<Rational>().isOne())
          {
            return Node::null();
          }
          continue;
        }
        const Node& ef = eprod[j][0];
        size_t exponentj = 0;
        if (ef == cf)
        {
          exponentj = 1;
        }
        else if (cf.getKind() == Kind::NONLINEAR_MULT)
        {
          for (const Node& ccf : cf)
          {
            if (ccf != ef)
            {
              return Node::null();
            }
          }
          exponentj = cf.getNumChildren();
        }
        if (exponent == 0)
        {
          exponent = exponentj;
        }
        else if (exponent != exponentj)
        {
          // exponents don't match
          return Node::null();
        }
      }
      cindex++;
    }
    if (conck != k)
    {
      // conclusion does not match the implied relation
      return Node::null();
    }
    return args[0];
  }
  return Node::null();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
