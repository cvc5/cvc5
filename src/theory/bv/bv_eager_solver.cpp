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

#include "theory/bv/bitblaster.h"
#include "theory/bv/bv_eager_solver.h"
#include "theory/bv/bitblast_strategies.h"
#include "theory/theory_registrar.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/options.h"
#include "theory/bv/aig.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_factory.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

namespace CVC4 {
namespace theory {
namespace bv {

/** Dummy class to pass to Minisat constructor */
class MinisatEmptyNotify : public prop::BVSatSolverInterface::Notify {
public:
  MinisatEmptyNotify() {}
  bool notify(prop::SatLiteral lit) { return true; }
  void notify(prop::SatClause& clause) { }
  void safePoint() {}
};



class EagerBitblaster : public Bitblaster {

  // sat solver used for bitblasting and associated CnfStream
  prop::BVSatSolverInterface*        d_satSolver;
  prop::CnfStream*                   d_cnfStream;

public:
  void addAtom(TNode atom);
  void storeVariable(TNode node) {} // not implemented for the eager solver
  void bbTerm(TNode node, Bits&  bits);
  void bbAtom(TNode node);
  void bbFormula(TNode formula);
  
  EagerBitblaster(); 
  ~EagerBitblaster();
  bool assertToSat(TNode node, bool propagate = true);
  bool solve(); 
};

class BitblastingRegistrar: public prop::Registrar {
  EagerBitblaster* d_bitblaster; 
public:
  BitblastingRegistrar(EagerBitblaster* bb)
    : d_bitblaster(bb)
  {}
  void preRegister(Node n) {
    d_bitblaster->bbAtom(n); 
  };

};/* class Registrar */


}
}
}

EagerBitblaster::EagerBitblaster()
  : Bitblaster()
{
  d_satSolver = prop::SatSolverFactory::createMinisat(new context::Context(), "eager");
  d_cnfStream = new prop::TseitinCnfStream(d_satSolver, new BitblastingRegistrar(this), new context::Context());
  
  MinisatEmptyNotify* notify = new MinisatEmptyNotify();
  d_satSolver->setNotify(notify);
}

EagerBitblaster::~EagerBitblaster() {
  delete d_cnfStream;
  delete d_satSolver;
}

void EagerBitblaster::bbFormula(TNode node) {
  d_cnfStream->convertAndAssert(node, false, false); 
}

/**
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 *
 */
void EagerBitblaster::bbAtom(TNode node) {
  node = node.getKind() == kind::NOT?  node[0] : node;
  if (node.getKind() == kind::BITVECTOR_BITOF)
    return; 
  if (hasBBAtom(node)) {
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb = normalized.getKind() != kind::CONST_BOOLEAN ?
      Rewriter::rewrite(d_atomBBStrategies[normalized.getKind()](normalized, this)) :
      normalized;
  // asserting that the atom is true iff the definition holds
  Node atom_definition = mkNode(kind::IFF, node, atom_bb);

  Assert (options::bitvectorNewEagerBitblast());
  storeBBAtom(node);
  d_cnfStream->convertAndAssert(atom_definition, false, false);
}

void EagerBitblaster::bbTerm(TNode node, Bits& bits) {
  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";

  d_termBBStrategies[node.getKind()] (node, bits, this);

  Assert (bits.size() == utils::getSize(node));

  storeBBTerm(node, bits);
}


/**
 * Calls the solve method for the Sat Solver.
 *
 * @return true for sat, and false for unsat
 */

bool EagerBitblaster::solve() {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "EagerBitblaster::solve(). \n";
  }
  Debug("bitvector") << "EagerBitblaster::solve(). \n"; 
  return prop::SAT_VALUE_TRUE == d_satSolver->solve();
}


EagerBitblastSolver::EagerBitblastSolver()
  : d_assertionSet()
{
  prop::BVSatSolverInterface* satSolver = prop::SatSolverFactory::createMinisat(new context::Context(), "eager");
  MinisatEmptyNotify* notify = new MinisatEmptyNotify();
  satSolver->setNotify(notify);
  d_aigSimplifer = new AigSimplifier(satSolver);
  d_bitblaster = new AigBitblaster(d_aigSimplifer);
}

EagerBitblastSolver::~EagerBitblastSolver() {
  delete d_aigSimplifer; 
  delete d_bitblaster; 
}

void EagerBitblastSolver::assertFormula(TNode formula) {
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
  // negate it due to ABC's cnf conversion?
  Node query = utils::mkNode(kind::NOT, utils::mkAnd(assertions)); 
  d_aigSimplifer->setOutput(query); 
  d_aigSimplifer->simplifyAig();
  d_aigSimplifer->convertToCnfAndAssert(); 
  return d_aigSimplifer->solve(); 
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
