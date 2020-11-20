/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of NlExt proof checker
 **/

#include "theory/arith/nl/ext/proof_checker.h"

#include "expr/sequence.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

void ExtProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ARITH_MULT_SIGN, this);
  pc->registerChecker(PfRule::ARITH_MULT_POS, this);
  pc->registerChecker(PfRule::ARITH_MULT_NEG, this);
}

Node ExtProofRuleChecker::checkInternal(PfRule id,
                                        const std::vector<Node>& children,
                                        const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  auto zero = nm->mkConst<Rational>(0);
  auto one = nm->mkConst<Rational>(1);
  auto mone = nm->mkConst<Rational>(-1);
  auto pi = nm->mkNullaryOperator(nm->realType(), Kind::PI);
  auto mpi = nm->mkNode(Kind::MULT, mone, pi);
  Trace("nl-ext-checker") << "Checking " << id << std::endl;
  for (const auto& c : children)
  {
    Trace("nl-ext-checker") << "\t" << c << std::endl;
  }
  if (id == PfRule::ARITH_MULT_SIGN)
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
      auto it = exps.find(v);
      if (it == exps.end())
      {
        exps.emplace(v, 1);
      }
      else
      {
        ++it->second;
      }
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
  else if (id == PfRule::ARITH_MULT_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 3);
    Node mult = args[0];
    Node orig = args[1];
    Kind rel = args[2].getKind();
    Assert(rel == Kind::EQUAL || rel == Kind::DISTINCT || rel == Kind::LT
           || rel == Kind::LEQ || rel == Kind::GT || rel == Kind::GEQ);
    Node lhs = args[2][0];
    Node rhs = args[2][1];
    return Rewriter::rewrite(nm->mkNode(
        Kind::IMPLIES,
        nm->mkAnd(std::vector<Node>{nm->mkNode(Kind::GT, mult, zero), orig}),
        nm->mkNode(rel,
                   nm->mkNode(Kind::MULT, mult, lhs),
                   nm->mkNode(Kind::MULT, mult, rhs))));
  }
  else if (id == PfRule::ARITH_MULT_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 3);
    Node mult = args[0];
    Node orig = args[1];
    Kind rel = args[2].getKind();
    Assert(rel == Kind::EQUAL || rel == Kind::DISTINCT || rel == Kind::LT
           || rel == Kind::LEQ || rel == Kind::GT || rel == Kind::GEQ);
    Kind rel_inv = reverseRelationKind(rel);
    Node lhs = args[2][0];
    Node rhs = args[2][1];
    return Rewriter::rewrite(nm->mkNode(
        Kind::IMPLIES,
        nm->mkAnd(std::vector<Node>{nm->mkNode(Kind::LT, mult, zero), orig}),
        nm->mkNode(rel_inv,
                   nm->mkNode(Kind::MULT, mult, lhs),
                   nm->mkNode(Kind::MULT, mult, rhs))));
  }
  return Node::null();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
