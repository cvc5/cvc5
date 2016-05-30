/*********************                                                        */
/*! \file bv_eager_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Eager bit-blasting solver. 
 **
 ** Eager bit-blasting solver.
 **/

#include "options/bv_options.h"
#include "theory/bv/bitblaster_template.h"
#include "proof/bitvector_proof.h"
#include "theory/bv/bv_eager_solver.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

EagerBitblastSolver::EagerBitblastSolver(TheoryBV* bv)
  : d_assertionSet()
  , d_bitblaster(NULL)
  , d_aigBitblaster(NULL)
  , d_useAig(options::bitvectorAig())
  , d_bv(bv)
{}

EagerBitblastSolver::~EagerBitblastSolver() {
  if (d_useAig) {
    Assert (d_bitblaster == NULL); 
    delete d_aigBitblaster;
  }
  else {
    Assert (d_aigBitblaster == NULL); 
    delete d_bitblaster;
  }
}

void EagerBitblastSolver::turnOffAig() {
  Assert (d_aigBitblaster == NULL &&
          d_bitblaster == NULL);
  d_useAig = false;
}

void EagerBitblastSolver::initialize() {
  Assert(!isInitialized());
  if (d_useAig) {
    d_aigBitblaster = new AigBitblaster();
  } else {
    d_bitblaster = new EagerBitblaster(d_bv);
    THEORY_PROOF(
      if( d_bvp ){
        d_bitblaster->setProofLog( d_bvp );
        d_bvp->setBitblaster(d_bitblaster);
      }
    );
  }
}

bool EagerBitblastSolver::isInitialized() {
  bool init = d_aigBitblaster != NULL || d_bitblaster != NULL;
  if (init) {
    Assert (!d_useAig || d_aigBitblaster);
    Assert (d_useAig || d_bitblaster);
  }
  return init;
}

void EagerBitblastSolver::assertFormula(TNode formula) {
  d_bv->spendResource(1);
  Assert (isInitialized());
  Debug("bitvector-eager") << "EagerBitblastSolver::assertFormula "<< formula <<"\n"; 
  d_assertionSet.insert(formula);
  //ensures all atoms are bit-blasted and converted to AIG
  if (d_useAig) 
    d_aigBitblaster->bbFormula(formula);
  else
    d_bitblaster->bbFormula(formula);
}

bool EagerBitblastSolver::checkSat() {
  Assert (isInitialized());
  std::vector<TNode> assertions; 
  for (AssertionSet::const_iterator it = d_assertionSet.begin(); it != d_assertionSet.end(); ++it) {
    assertions.push_back(*it); 
  }
  if (!assertions.size())
    return true;
  
  if (d_useAig) {
    Node query = utils::mkAnd(assertions); 
    return d_aigBitblaster->solve(query);
  }
  
  return d_bitblaster->solve(); 
}

bool EagerBitblastSolver::hasAssertions(const std::vector<TNode> &formulas) {
  Assert (isInitialized());
  if (formulas.size() != d_assertionSet.size())
    return false; 
  for (unsigned i = 0; i < formulas.size(); ++i) {
    Assert (formulas[i].getKind() == kind::BITVECTOR_EAGER_ATOM);
    TNode formula = formulas[i][0];
    if (d_assertionSet.find(formula) == d_assertionSet.end())
      return false; 
  }
  return true; 
}

void EagerBitblastSolver::collectModelInfo(TheoryModel* m, bool fullModel) {
  AlwaysAssert(!d_useAig && d_bitblaster);
  d_bitblaster->collectModelInfo(m, fullModel); 
}

void EagerBitblastSolver::setProofLog( BitVectorProof * bvp ) {
  d_bvp = bvp;
}
