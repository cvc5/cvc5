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


class EagerBitblaster : public Bitblaster {

  /** Dummy class to pass to Minisat constructor */
  class MinisatEmptyNotify : public prop::BVSatSolverInterface::Notify {
  public:
    MinisatEmptyNotify() {}
    bool notify(prop::SatLiteral lit) { return true; }
    void notify(prop::SatClause& clause) { }
    void safePoint() {}
  };


  typedef __gnu_cxx::hash_map <Node, Bits, TNodeHashFunction>  TermDefMap;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction>        AtomSet;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction>        VarSet;

  typedef void   (*TermBBStrategy) (TNode, Bits&, Bitblaster*);
  typedef Node   (*AtomBBStrategy) (TNode, Bitblaster*);

  // sat solver used for bitblasting and associated CnfStream
  prop::BVSatSolverInterface*        d_satSolver;
  prop::CnfStream*                   d_cnfStream;

  // caches and mappings
  TermDefMap                   d_termCache;
  AtomSet                      d_bitblastedAtoms;
  VarSet                       d_variables;

  /// helper methods
public:
  bool          hasBBAtom(TNode node) const;
  private:
  bool          hasBBTerm(TNode node) const;
  void          getBBTerm(TNode node, Bits& bits) const;

  /// function tables for the various bitblasting strategies indexed by node kind
  TermBBStrategy d_termBBStrategies[kind::LAST_KIND];
  AtomBBStrategy d_atomBBStrategies[kind::LAST_KIND];

  // helper methods to initialize function tables
  void initAtomBBStrategies();
  void initTermBBStrategies();

  void addAtom(TNode atom);
  // division is bitblasted in terms of constraints
  // so it needs to use private bitblaster interface
  void bbUdiv(TNode node, Bits& bits);
  void bbUrem(TNode node, Bits& bits);
public:
  void storeVariable(TNode node) {} // not implemented for the eager solver
  void cacheTermDef(TNode node, Bits def); // public so we can cache remainder for division
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

EagerBitblaster::EagerBitblaster() :
    d_termCache(),
    d_bitblastedAtoms()
  {
    d_satSolver = prop::SatSolverFactory::createMinisat(new context::Context(), "eager");
    d_cnfStream = new prop::TseitinCnfStream(d_satSolver, new BitblastingRegistrar(this), new context::Context());

    MinisatEmptyNotify* notify = new MinisatEmptyNotify();
    d_satSolver->setNotify(notify);
    // initializing the bit-blasting strategies
    initAtomBBStrategies();
    initTermBBStrategies();
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
  
  d_cnfStream->convertAndAssert(atom_definition, false, false);
  d_bitblastedAtoms.insert(node);
}

void EagerBitblaster::bbTerm(TNode node, Bits& bits) {
  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node <<"\n";

  d_termBBStrategies[node.getKind()] (node, bits, this);

  Assert (bits.size() == utils::getSize(node));

  cacheTermDef(node, bits);
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


/// Helper methods


void EagerBitblaster::initAtomBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_atomBBStrategies[i] = UndefinedAtomBBStrategy;
  }

  /// setting default bb strategies for atoms
  d_atomBBStrategies [ kind::EQUAL ]           = DefaultEqBB;
  d_atomBBStrategies [ kind::BITVECTOR_ULT ]   = DefaultUltBB;
  d_atomBBStrategies [ kind::BITVECTOR_ULE ]   = DefaultUleBB;
  d_atomBBStrategies [ kind::BITVECTOR_UGT ]   = DefaultUgtBB;
  d_atomBBStrategies [ kind::BITVECTOR_UGE ]   = DefaultUgeBB;
  d_atomBBStrategies [ kind::BITVECTOR_SLT ]   = DefaultSltBB;
  d_atomBBStrategies [ kind::BITVECTOR_SLE ]   = DefaultSleBB;
  d_atomBBStrategies [ kind::BITVECTOR_SGT ]   = DefaultSgtBB;
  d_atomBBStrategies [ kind::BITVECTOR_SGE ]   = DefaultSgeBB;

}

void EagerBitblaster::initTermBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_termBBStrategies[i] = DefaultVarBB;
  }

  /// setting default bb strategies for terms:
  d_termBBStrategies [ kind::CONST_BITVECTOR ]        = DefaultConstBB;
  d_termBBStrategies [ kind::BITVECTOR_NOT ]          = DefaultNotBB;
  d_termBBStrategies [ kind::BITVECTOR_CONCAT ]       = DefaultConcatBB;
  d_termBBStrategies [ kind::BITVECTOR_AND ]          = DefaultAndBB;
  d_termBBStrategies [ kind::BITVECTOR_OR ]           = DefaultOrBB;
  d_termBBStrategies [ kind::BITVECTOR_XOR ]          = DefaultXorBB;
  d_termBBStrategies [ kind::BITVECTOR_XNOR ]         = DefaultXnorBB;
  d_termBBStrategies [ kind::BITVECTOR_NAND ]         = DefaultNandBB ;
  d_termBBStrategies [ kind::BITVECTOR_NOR ]          = DefaultNorBB;
  d_termBBStrategies [ kind::BITVECTOR_COMP ]         = DefaultCompBB ;
  d_termBBStrategies [ kind::BITVECTOR_MULT ]         = DefaultMultBB;
  d_termBBStrategies [ kind::BITVECTOR_PLUS ]         = DefaultPlusBB;
  d_termBBStrategies [ kind::BITVECTOR_SUB ]          = DefaultSubBB;
  d_termBBStrategies [ kind::BITVECTOR_NEG ]          = DefaultNegBB;
  d_termBBStrategies [ kind::BITVECTOR_UDIV ]         = UndefinedTermBBStrategy;
  d_termBBStrategies [ kind::BITVECTOR_UREM ]         = UndefinedTermBBStrategy;
  d_termBBStrategies [ kind::BITVECTOR_UDIV_TOTAL ]   = DefaultUdivBB;
  d_termBBStrategies [ kind::BITVECTOR_UREM_TOTAL ]   = DefaultUremBB;
  d_termBBStrategies [ kind::BITVECTOR_SDIV ]         = UndefinedTermBBStrategy;
  d_termBBStrategies [ kind::BITVECTOR_SREM ]         = UndefinedTermBBStrategy;
  d_termBBStrategies [ kind::BITVECTOR_SMOD ]         = UndefinedTermBBStrategy;
  d_termBBStrategies [ kind::BITVECTOR_SHL ]          = DefaultShlBB;
  d_termBBStrategies [ kind::BITVECTOR_LSHR ]         = DefaultLshrBB;
  d_termBBStrategies [ kind::BITVECTOR_ASHR ]         = DefaultAshrBB;
  d_termBBStrategies [ kind::BITVECTOR_EXTRACT ]      = DefaultExtractBB;
  d_termBBStrategies [ kind::BITVECTOR_REPEAT ]       = DefaultRepeatBB;
  d_termBBStrategies [ kind::BITVECTOR_ZERO_EXTEND ]  = DefaultZeroExtendBB;
  d_termBBStrategies [ kind::BITVECTOR_SIGN_EXTEND ]  = DefaultSignExtendBB;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_RIGHT ] = DefaultRotateRightBB;
  d_termBBStrategies [ kind::BITVECTOR_ROTATE_LEFT ]  = DefaultRotateLeftBB;

}

bool EagerBitblaster::hasBBAtom(TNode atom) const {
  return d_bitblastedAtoms.find(atom) != d_bitblastedAtoms.end();
}

void EagerBitblaster::cacheTermDef(TNode term, Bits def) {
  Assert (d_termCache.find(term) == d_termCache.end());
  d_termCache[term] = def;
}

bool EagerBitblaster::hasBBTerm(TNode node) const {
  return d_termCache.find(node) != d_termCache.end();
}

void EagerBitblaster::getBBTerm(TNode node, Bits& bits) const {
  Assert (hasBBTerm(node));
  bits = d_termCache.find(node)->second;
}


EagerBitblastSolver::EagerBitblastSolver()
  : d_bitblaster(new EagerBitblaster())
  , d_assertionSet()
{}

EagerBitblastSolver::~EagerBitblastSolver() {
  delete d_bitblaster; 
}

void EagerBitblastSolver::assertFormula(TNode formula) {
  d_assertionSet.insert(formula);
  d_bitblaster->bbFormula(formula); 
}

bool EagerBitblastSolver::checkSat() {
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
