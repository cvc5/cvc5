/*********************                                                        */
/*! \file bv_eager_solver.h
 ** \verbatim
 ** Original author: Liana Hadarean 
 ** Major contributors: none
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Eager bit-blasting solver. 
 **
 ** Eager bit-blasting solver.
 **/

#include "theory/bv/bv_eager_solver.h"
#include "theory/bv/bitblaster_template.h"
#include "theory/bv/eager_bitblaster.h"
#include "theory/bv/aig_bitblaster.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

EagerBitblastSolver::EagerBitblastSolver()
  : d_assertionSet()
  , d_bitblaster(NULL)
  , d_aigBitblaster(NULL)
{
  if (options::bitvectorAig()) {
    d_aigBitblaster = new AigBitblaster(); 
  } else {
    d_bitblaster = new EagerBitblaster();
  }
}

EagerBitblastSolver::~EagerBitblastSolver() {
  if (options::bitvectorAig()) {
    Assert (d_bitblaster == NULL); 
    delete d_aigBitblaster;
  }
  else {
    Assert (d_aigBitblaster == NULL); 
    delete d_bitblaster;
  }
}

void EagerBitblastSolver::assertFormula(TNode formula) {
  Debug("bitvector-eager") << "EagerBitblastSolver::assertFormula "<< formula <<"\n"; 
  d_assertionSet.insert(formula);
  //ensures all atoms are bit-blasted and converted to AIG
  if (options::bitvectorAig()) 
    d_aigBitblaster->bbFormula(formula);
  else
    d_bitblaster->bbFormula(formula);
}

bool EagerBitblastSolver::checkSat() {
  std::vector<TNode> assertions; 
  for (AssertionSet::const_iterator it = d_assertionSet.begin(); it != d_assertionSet.end(); ++it) {
    assertions.push_back(*it); 
  }
  Assert (assertions.size());
  if (options::bitvectorAig()) {
    Node query = utils::mkAnd(assertions); 
    return d_aigBitblaster->solve(query);
  }
  
  return d_bitblaster->solve(); 
}

bool EagerBitblastSolver::hasAssertions(const std::vector<TNode> &formulas) {
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
