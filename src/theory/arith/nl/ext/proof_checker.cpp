/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  pc->registerChecker(ProofRule::ARITH_MULT_ABS_COMPARISON, this);
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
    Assert(args.size() == 2);
    Node mon = args[1];
    std::map<Node, int> exps;
    std::vector<Node> premise;
    if (args[0].getKind() == Kind::AND)
    {
      premise.insert(premise.end(), args[0].begin(), args[0].end());
    }
    else
    {
      premise.push_back(args[0]);
    }
    Assert(mon.getKind() == Kind::MULT
           || mon.getKind() == Kind::NONLINEAR_MULT);
    std::vector<Node> vars;
    for (const auto& v : mon)
    {
      if (vars.empty() || v != vars.back())
      {
        vars.push_back(v);
      }
      exps[v]++;
    }
    // unique variables must equal the number of given premises
    if (vars.size() != premise.size())
    {
      return Node::null();
    }
    std::map<Node, int> signs;
    for (size_t i = 0, nprem = premise.size(); i < nprem; i++)
    {
      const Node& f = premise[i];
      if (f.getKind() == Kind::NOT)
      {
        // variables must be in order
        if (f[0][0] != vars[i])
        {
          return Node::null();
        }
        Assert(f[0].getKind() == Kind::EQUAL);
        Assert(f[0][1].isConst() && f[0][1].getConst<Rational>().isZero());
        Assert(signs.find(f[0][0]) == signs.end());
        signs.emplace(f[0][0], 0);
        continue;
      }
      // variables must be in order
      if (f[0] != vars[i])
      {
        return Node::null();
      }
      Assert(f.getKind() == Kind::LT || f.getKind() == Kind::GT);
      Assert(f[1].isConst() && f[1].getConst<Rational>().isZero());
      Assert(signs.find(f[0]) == signs.end());
      signs.emplace(f[0], f.getKind() == Kind::LT ? -1 : 1);
    }
    int sign = 1;
    for (const auto& ve : exps)
    {
      auto sit = signs.find(ve.first);
      Assert(sit != signs.end());
      if (ve.second % 2 == 0)
      {
        Assert(sit->second == 0);
      }
      else
      {
        Assert(sit->second != 0);
        sign *= sit->second;
      }
    }
    Node zero = nm->mkConstRealOrInt(mon.getType(), Rational(0));
    switch (sign)
    {
      case -1:
        return nm->mkNode(
            Kind::IMPLIES, nm->mkAnd(premise), nm->mkNode(Kind::LT, mon, zero));
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
    Assert(args[4].isConst() && args[4].getType().isBoolean());
    Node x = args[0];
    Node y = args[1];
    Node t = nm->mkNode(Kind::NONLINEAR_MULT, x, y);
    Node a = args[2];
    Node b = args[3];
    int sgn = args[4].getConst<bool>() ? 1 : -1;
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
  else if (id == ProofRule::ARITH_MULT_ABS_COMPARISON)
  {
    Assert(!children.empty());
    Assert(args.empty());
    // the conclusion kind is kind of the first premise
    Kind k = children[0].getKind();
    std::vector<Node> concProd[2];
    for (size_t cindex = 0, nchildren = children.size(); cindex < nchildren;
         cindex++)
    {
      const Node& c = children[cindex];
      Kind ck = c.getKind();
      Node zeroGuard;
      Node lit = c;
      if (ck == Kind::AND)
      {
        zeroGuard = ArithNlCompareProofGenerator::isDisequalZero(c[1]);
        // it should be a disequality with zero
        if (c.getNumChildren() == 2 && !zeroGuard.isNull())
        {
          lit = c[0];
        }
        else
        {
          return Node::null();
        }
      }
      ck = lit.getKind();
      if (k == Kind::EQUAL)
      {
        // should be an equality
        if (ck != Kind::EQUAL)
        {
          return Node::null();
        }
      }
      else if (k == Kind::GT)
      {
        if (ck != Kind::GT)
        {
          // if an equality, needs a disequal to zero guard
          if (ck == Kind::EQUAL)
          {
            // guarded zero disequality should be for LHS
            if (zeroGuard.isNull() || lit[0].getKind() != Kind::ABS
                || zeroGuard != lit[0][0])
            {
              return Node::null();
            }
          }
          else
          {
            return Node::null();
          }
        }
      }
      else
      {
        return Node::null();
      }
      Assert(ck == Kind::EQUAL || ck == Kind::GT);
      if (lit[0].getKind() != Kind::ABS || lit[1].getKind() != Kind::ABS)
      {
        return Node::null();
      }
      // add to the product
      for (size_t j = 0; j < 2; j++)
      {
        if (lit[j][0].isConst())
        {
          if (!lit[j][0].getConst<Rational>().isOne())
          {
            return Node::null();
          }
          size_t jj = 1 - j;
          if (lit[jj][0].isConst())
          {
            return Node::null();
          }
          // always ensure type matches
          Node one = nm->mkConstRealOrInt(lit[jj][0].getType(), Rational(1));
          concProd[j].emplace_back(one);
          continue;
        }
        concProd[j].emplace_back(lit[j][0]);
      }
    }
    Node lhs = ArithNlCompareProofGenerator::mkProduct(nm, concProd[0]);
    Node rhs = ArithNlCompareProofGenerator::mkProduct(nm, concProd[1]);
    return ArithNlCompareProofGenerator::mkLit(nm, k, lhs, rhs);
  }
  return Node::null();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
