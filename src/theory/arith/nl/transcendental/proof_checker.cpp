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
 ** \brief Implementation of proof checker for transcendentals
 **/

#include "theory/arith/nl/transcendental/proof_checker.h"

#include "expr/sequence.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/transcendental/taylor_generator.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

void TranscendentalProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::ARITH_TRANS_SINE_SHIFT, this);
}

Node TranscendentalProofRuleChecker::checkInternal(
    PfRule id, const std::vector<Node>& children, const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  auto zero = nm->mkConst<Rational>(0);
  auto one = nm->mkConst<Rational>(1);
  auto mone = nm->mkConst<Rational>(-1);
  auto pi = nm->mkNullaryOperator(nm->realType(), Kind::PI);
  auto mpi = nm->mkNode(Kind::MULT, mone, pi);
  Trace("nl-trans-checker") << "Checking " << id << std::endl;
  for (const auto& c : children)
  {
    Trace("nl-trans-checker") << "\t" << c << std::endl;
  }
  if (id == PfRule::ARITH_TRANS_SINE_SHIFT)
  {
    Assert(children.empty());
    Assert(args.size() == 3);
    const auto& x = args[0];
    const auto& y = args[1];
    const auto& s = args[2];
    return nm->mkAnd(std::vector<Node>{
        nm->mkAnd(std::vector<Node>{
            nm->mkNode(Kind::GEQ, y, nm->mkNode(Kind::MULT, mone, pi)),
            nm->mkNode(Kind::LEQ, y, pi)}),
        nm->mkNode(
            Kind::ITE,
            nm->mkAnd(std::vector<Node>{
                nm->mkNode(Kind::GEQ, x, nm->mkNode(Kind::MULT, mone, pi)),
                nm->mkNode(Kind::LEQ, x, pi),
            }),
            x.eqNode(y),
            x.eqNode(nm->mkNode(
                Kind::PLUS,
                y,
                nm->mkNode(Kind::MULT, nm->mkConst<Rational>(2), s, pi)))),
        nm->mkNode(Kind::SINE, y).eqNode(nm->mkNode(Kind::SINE, x))});
  }
  return Node::null();
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
