/*********************                                                        */
/*! \file bv_eager_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Paul Meng, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Eager bit-blasting solver.
 **
 ** Eager bit-blasting solver.
 **/

#include "theory/bv/bv_eager_solver.h"
#include "options/bv_options.h"
#include "proof/bitvector_proof.h"
#include "theory/bv/bitblaster_template.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace bv {

EagerBitblastSolver::EagerBitblastSolver(TheoryBV* bv)
    : d_assertionSet(),
      d_bitblaster(nullptr),
      d_aigBitblaster(nullptr),
      d_useAig(options::bitvectorAig()),
      d_bv(bv),
      d_bvp(nullptr) {}

EagerBitblastSolver::~EagerBitblastSolver() {
  if (d_useAig) {
    Assert(d_bitblaster == nullptr);
    delete d_aigBitblaster;
  } else {
    Assert(d_aigBitblaster == nullptr);
    delete d_bitblaster;
  }
}

void EagerBitblastSolver::turnOffAig() {
  Assert(d_aigBitblaster == nullptr && d_bitblaster == nullptr);
  d_useAig = false;
}

void EagerBitblastSolver::initialize() {
  Assert(!isInitialized());
  if (d_useAig) {
#ifdef CVC4_USE_ABC
    d_aigBitblaster = new AigBitblaster();
#else
    Unreachable();
#endif
  } else {
    d_bitblaster = new EagerBitblaster(d_bv);
    THEORY_PROOF(if (d_bvp) {
      d_bitblaster->setProofLog(d_bvp);
      d_bvp->setBitblaster(d_bitblaster);
    });
  }
}

bool EagerBitblastSolver::isInitialized() {
  const bool init = d_aigBitblaster != nullptr || d_bitblaster != nullptr;
  Assert(!init || !d_useAig || d_aigBitblaster);
  Assert(!init || d_useAig || d_bitblaster);
  return init;
}

void EagerBitblastSolver::assertFormula(TNode formula) {
  d_bv->spendResource(1);
  Assert(isInitialized());
  Debug("bitvector-eager") << "EagerBitblastSolver::assertFormula " << formula
                           << "\n";
  d_assertionSet.insert(formula);
  // ensures all atoms are bit-blasted and converted to AIG
  if (d_useAig) {
#ifdef CVC4_USE_ABC
    d_aigBitblaster->bbFormula(formula);
#else
    Unreachable();
#endif
  } else {
    d_bitblaster->bbFormula(formula);
  }
}

bool EagerBitblastSolver::checkSat() {
  Assert(isInitialized());
  if (d_assertionSet.empty()) {
    return true;
  }

  if (d_useAig) {
#ifdef CVC4_USE_ABC
    const std::vector<TNode> assertions = {d_assertionSet.begin(),
                                           d_assertionSet.end()};
    Assert(!assertions.empty());

    Node query = utils::mkAnd(assertions);
    return d_aigBitblaster->solve(query);
#else
    Unreachable();
#endif
  }

  return d_bitblaster->solve();
}

bool EagerBitblastSolver::hasAssertions(const std::vector<TNode>& formulas) {
  Assert(isInitialized());
  if (formulas.size() != d_assertionSet.size()) return false;
  for (unsigned i = 0; i < formulas.size(); ++i) {
    Assert(formulas[i].getKind() == kind::BITVECTOR_EAGER_ATOM);
    TNode formula = formulas[i][0];
    if (d_assertionSet.find(formula) == d_assertionSet.end()) return false;
  }
  return true;
}

bool EagerBitblastSolver::collectModelInfo(TheoryModel* m, bool fullModel)
{
  AlwaysAssert(!d_useAig && d_bitblaster);
  return d_bitblaster->collectModelInfo(m, fullModel);
}

void EagerBitblastSolver::setProofLog(BitVectorProof* bvp) { d_bvp = bvp; }

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
