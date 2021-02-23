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
  pc->registerChecker(PfRule::ARITH_MULT_POS, this);
  pc->registerChecker(PfRule::ARITH_MULT_NEG, this);
  pc->registerChecker(PfRule::ARITH_MULT_TANGENT, this);
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
  if (id == PfRule::ARITH_MULT_POS)
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
    Kind rel_inv = (rel == Kind::DISTINCT ? rel : reverseRelationKind(rel));
    Node lhs = args[2][0];
    Node rhs = args[2][1];
    return Rewriter::rewrite(nm->mkNode(
        Kind::IMPLIES,
        nm->mkAnd(std::vector<Node>{nm->mkNode(Kind::LT, mult, zero), orig}),
        nm->mkNode(rel_inv,
                   nm->mkNode(Kind::MULT, mult, lhs),
                   nm->mkNode(Kind::MULT, mult, rhs))));
  }
  else if (id == PfRule::ARITH_MULT_TANGENT)
  {
    Assert(children.empty());
    Assert(args.size() == 6);
    Assert(args[0].getType().isReal());
    Assert(args[1].getType().isReal());
    Assert(args[2].getType().isReal());
    Assert(args[3].getType().isReal());
    Assert(args[4].getType().isReal());
    Assert(args[5].isConst() && args[5].getKind() == Kind::CONST_RATIONAL
           && args[5].getConst<Rational>().isIntegral());
    Node t = args[0];
    Node x = args[1];
    Node y = args[2];
    Node a = args[3];
    Node b = args[4];
    int sgn = args[5].getConst<Rational>().getNumerator().sgn();
    Assert(sgn == -1 || sgn == 1);
    Node tplane = nm->mkNode(Kind::MINUS,
                             nm->mkNode(Kind::PLUS,
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
}  // namespace CVC4
