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
  if (id == PfRule::ARITH_MULT_TANGENT)
  {
    Assert(children.empty());
    Assert(args.size() == 5);
    Assert(args[0].getType().isReal());
    Assert(args[1].getType().isReal());
    Assert(args[2].getType().isReal());
    Assert(args[3].getType().isReal());
    Assert(args[4].isConst() && args[4].getKind() == Kind::CONST_RATIONAL
           && args[4].getConst<Rational>().isIntegral());
    Node x = args[0];
    Node y = args[1];
    Node a = args[2];
    Node b = args[3];
    std::uint64_t i =
        args[4].getConst<Rational>().getNumerator().toUnsignedInt();
    Node tplane = nm->mkNode(Kind::MINUS,
                             nm->mkNode(Kind::PLUS,
                                        nm->mkNode(Kind::MULT, b, x),
                                        nm->mkNode(Kind::MULT, a, y)),
                             nm->mkNode(Kind::MULT, a, b));
    return nm->mkOr(std::vector<Node>{
        nm->mkNode(i == 0 || i == 3 ? Kind::GEQ : Kind::LEQ, x, a).negate(),
        nm->mkNode(i == 1 || i == 3 ? Kind::GEQ : Kind::LEQ, y, b).negate(),
        nm->mkNode(i == 2 || i == 3 ? Kind::GEQ : Kind::LEQ,
                   nm->mkNode(Kind::NONLINEAR_MULT, x, y),
                   tplane)
    });
  }
  return Node::null();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
