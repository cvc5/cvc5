/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

void ExtProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ARITH_MULT_SIGN, this);
  pc->registerChecker(PfRule::ARITH_MULT_TANGENT, this);
}

Node ExtProofRuleChecker::checkInternal(PfRule id,
                                        const std::vector<Node>& children,
                                        const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
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
  else if (id == PfRule::ARITH_MULT_TANGENT)
  {
    Assert(children.empty());
    Assert(args.size() == 6);
    Assert(args[0].getType().isRealOrInt());
    Assert(args[1].getType().isRealOrInt());
    Assert(args[2].getType().isRealOrInt());
    Assert(args[3].getType().isRealOrInt());
    Assert(args[4].getType().isRealOrInt());
    Assert(args[5].isConst() && args[5].getConst<Rational>().isIntegral());
    Node t = args[0];
    Node x = args[1];
    Node y = args[2];
    Node a = args[3];
    Node b = args[4];
    int sgn = args[5].getConst<Rational>().getNumerator().sgn();
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
  return Node::null();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
