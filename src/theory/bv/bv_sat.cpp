/*********************                                                        */
/*! \file bv_sat.cpp
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** 
 **/

#include "bv_sat.h"
#include "theory_bv_utils.h"
#include "theory/rewriter.h"
#include "prop/cnf_stream.h"
#include "prop/sat_module.h"

using namespace std;

using namespace CVC4::theory::bv::utils;
using namespace CVC4::context; 
using namespace CVC4::prop;

namespace CVC4 {
namespace theory {
namespace bv{


std::string toString(Bits&  bits) {
  ostringstream os; 
  for (int i = bits.size() - 1; i >= 0; --i) {
    TNode bit = bits[i];
    if (bit.getKind() == kind::CONST_BOOLEAN) {
      os << (bit.getConst<bool>() ? "1" : "0");
    } else {
      os << bit<< " ";   
    }
  }
  os <<"\n";
  
  return os.str(); 
}
/////// Bitblaster 

Bitblaster::Bitblaster(context::Context* c) :
    d_termCache(),
    d_bitblastedAtoms(),
    d_assertedAtoms(c),
    d_statistics()
  {
    d_satSolver = prop::SatSolverFactory::createMinisat();
    d_cnfStream = new TseitinCnfStream(d_satSolver, new NullRegistrar());

    // initializing the bit-blasting strategies
    initAtomBBStrategies(); 
    initTermBBStrategies(); 
  }

Bitblaster::~Bitblaster() {
  delete d_cnfStream;
  delete d_satSolver; 
}


/** 
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 * 
 */
void Bitblaster::bbAtom(TNode node) {
  if (hasBBAtom(node)) {
    return; 
  }

  // the bitblasted definition of the atom
  Node atom_bb = d_atomBBStrategies[node.getKind()](node, this);
  // asserting that the atom is true iff the definition holds
  Node atom_definition = mkNode(kind::IFF, node, atom_bb);
  // do boolean simplifications if possible
  Node rewritten = Rewriter::rewrite(atom_definition);
  d_cnfStream->convertAndAssert(rewritten, true, false);
  d_bitblastedAtoms.insert(node); 
}


void Bitblaster::bbTerm(TNode node, Bits& bits) {
  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  d_termBBStrategies[node.getKind()] (node, bits,this);
  
  Assert (bits.size() == utils::getSize(node)); 
  cacheTermDef(node, bits); 
}

/// Public methods

/** 
 * Called from preregistration bitblasts the node
 * 
 * @param node 
 * 
 * @return 
 */
void Bitblaster::bitblast(TNode node) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_bitblastTimer);

  /// strip the not
  if (node.getKind() == kind::NOT) {
    node = node[0];
  }
  
  if (node.getKind() == kind::EQUAL ||
      node.getKind() == kind::BITVECTOR_ULT ||
      node.getKind() == kind::BITVECTOR_SLT ||
      node.getKind() == kind::BITVECTOR_ULE || 
      node.getKind() == kind::BITVECTOR_SLE )
    {
      bbAtom(node); 
    }
  else if (node.getKind() == kind::BITVECTOR_UGT ||
           node.getKind() == kind::BITVECTOR_UGE ||
           node.getKind() == kind::BITVECTOR_SGT ||
           node.getKind() == kind::BITVECTOR_SGE )
    {
      Unhandled(node.getKind()); 
    }
  else
    {
      Bits bits;
      bbTerm(node, bits); 
    }
}

/** 
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be aserted
 * 
 */
 
void Bitblaster::assertToSat(TNode lit) {
  // strip the not
  TNode atom; 
  if (lit.getKind() == kind::NOT) {
    atom = lit[0]; 
  } else {
    atom = lit; 
  }
  
  Assert (hasBBAtom(atom)); 
  SatLiteral markerLit = d_cnfStream->getLiteral(atom);

  if(lit.getKind() == kind::NOT) {
    markerLit = ~markerLit;
  }
  
  Debug("bitvector-bb") << "TheoryBV::Bitblaster::assertToSat asserting node: " << atom <<"\n";
  Debug("bitvector-bb") << "TheoryBV::Bitblaster::assertToSat with literal:   " << markerLit << "\n";  

  d_assertedAtoms.push_back(markerLit);
}

/** 
 * Calls the solve method for the Sat Solver. 
 * passing it the marker literals to be asserted
 * 
 * @return true for sat, and false for unsat
 */
 
bool Bitblaster::solve() {
  return SatValTrue == d_satSolver->solve(d_assertedAtoms); 
}

void Bitblaster::getConflict(std::vector<TNode>& conflict) {
  SatClause conflictClause;
  d_satSolver->getUnsatCore(conflictClause);
  
  for (unsigned i = 0; i < conflictClause.size(); i++) {
    SatLiteral lit = conflictClause[i]; 
    TNode atom = d_cnfStream->getNode(lit);
    Node  not_atom; 
    if (atom.getKind() == kind::NOT) {
      not_atom = atom[0];
    } else {
      not_atom = NodeManager::currentNM()->mkNode(kind::NOT, atom); 
    }
    conflict.push_back(not_atom); 
  }
}


/// Helper methods


void Bitblaster::initAtomBBStrategies() {
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

void Bitblaster::initTermBBStrategies() {
  for (int i = 0 ; i < kind::LAST_KIND; ++i ) {
    d_termBBStrategies[i] = UndefinedTermBBStrategy; 
  }
  
  /// setting default bb strategies for terms:
  d_termBBStrategies [ kind::VARIABLE ]               = DefaultVarBB;
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
  d_termBBStrategies [ kind::BITVECTOR_UDIV ]         = DefaultUdivBB;
  d_termBBStrategies [ kind::BITVECTOR_UREM ]         = DefaultUremBB;
  d_termBBStrategies [ kind::BITVECTOR_SDIV ]         = DefaultSdivBB;
  d_termBBStrategies [ kind::BITVECTOR_SREM ]         = DefaultSremBB;
  d_termBBStrategies [ kind::BITVECTOR_SMOD ]         = DefaultSmodBB;
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
 
bool Bitblaster::hasBBAtom(TNode atom) {
  return d_bitblastedAtoms.find(atom) != d_bitblastedAtoms.end();
}

void Bitblaster::cacheTermDef(TNode term, Bits def) {
  Assert (d_termCache.find(term) == d_termCache.end());
  d_termCache[term] = def; 
}

bool Bitblaster::hasBBTerm(TNode node) {
  return d_termCache.find(node) != d_termCache.end(); 
}

void Bitblaster::getBBTerm(TNode node, Bits& bits) {
  
  Assert (hasBBTerm(node)); 
  // copy?
  bits = d_termCache[node]; 
}

Bitblaster::Statistics::Statistics() :
  d_numTermClauses("theory::bv::NumberOfTermSatClauses", 0),
  d_numAtomClauses("theory::bv::NumberOfAtomSatClauses", 0), 
  d_bitblastTimer("theory::bv::BitblastTimer")
{
  StatisticsRegistry::registerStat(&d_numTermClauses);
  StatisticsRegistry::registerStat(&d_numAtomClauses);
  StatisticsRegistry::registerStat(&d_bitblastTimer);
}


Bitblaster::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermClauses);
  StatisticsRegistry::unregisterStat(&d_numAtomClauses);
  StatisticsRegistry::unregisterStat(&d_bitblastTimer);
}




} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/
