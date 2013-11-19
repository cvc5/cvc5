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

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

EagerBitblastSolver::EagerBitblastSolver()
  : d_assertionSet()
{
  // prop::BVSatSolverInterface* satSolver = prop::SatSolverFactory::createMinisat(new context::Context(), "eager");
  // MinisatEmptyNotify* notify = new MinisatEmptyNotify();
  // satSolver->setNotify(notify);
  //d_aigSimplifer = new AigSimplifier(satSolver);
  //d_bitblaster = new AigBitblaster(d_aigSimplifer);
  d_bitblaster = new EagerBitblaster(); 
}

EagerBitblastSolver::~EagerBitblastSolver() {
  // delete d_aigSimplifer; 
  delete d_bitblaster; 
}

void EagerBitblastSolver::assertFormula(TNode formula) {
  Debug("bitvector-eager") << "EagerBitblastSolver::assertFormula "<< formula <<"\n"; 
  d_assertionSet.insert(formula);
  //ensures all atoms are bit-blasted and converted to AIG
  d_bitblaster->bbFormula(formula);
}

bool EagerBitblastSolver::checkSat() {
  std::vector<TNode> assertions; 
  for (AssertionSet::const_iterator it = d_assertionSet.begin(); it != d_assertionSet.end(); ++it) {
    assertions.push_back(*it); 
  }
  Assert (assertions.size());

  // Node query = utils::mkAnd(assertions);
  // Debug("bitvector-eager") << "EagerBitblastSolver::checkSat "<< query <<"\n"; 
  // d_aigSimplifer->setOutput(query); 
  // d_aigSimplifer->simplifyAig();
  // d_aigSimplifer->convertToCnfAndAssert(); 
  // return d_aigSimplifer->solve(); 
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
