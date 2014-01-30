/*********************                                                        */
/*! \file eager_bitblaster.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): lianah
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief 
 **
 ** Bitblaster for the lazy bv solver. 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EAGER__BITBLASTER_H
#define __CVC4__EAGER__BITBLASTER_H


#include "bitblaster_template.h"
#include "theory/theory_registrar.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/options.h"

namespace CVC4 {
namespace theory {
namespace bv {


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

EagerBitblaster::EagerBitblaster()
  : TBitblaster<Node>()
  , d_bbAtoms()
{
  d_satSolver = prop::SatSolverFactory::createMinisat(new context::Context(), "EagerBitblaster");
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
  Node atom_definition = utils::mkNode(kind::IFF, node, atom_bb);

  Assert (options::bitvectorEagerBitblast());
  storeBBAtom(node, atom_definition);
  d_cnfStream->convertAndAssert(atom_definition, false, false);
}

void EagerBitblaster::storeBBAtom(TNode atom, Node atom_bb) {
  // no need to store the definition for the lazy bit-blaster
  d_bbAtoms.insert(atom); 
}

bool EagerBitblaster::hasBBAtom(TNode atom) const {
  return d_bbAtoms.find(atom) != d_bbAtoms.end(); 
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

void EagerBitblaster::makeVariable(TNode var, Bits& bits) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    bits.push_back(utils::mkBitOf(var, i)); 
  }
}

Node EagerBitblaster::getBBAtom(TNode node) const {
  return node; 
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
  // TODO: clear some memory
  // if (something) {
  //   NodeManager* nm= NodeManager::currentNM();
  //   Rewriter::garbageCollect();
  //   nm->reclaimZombiesUntil(options::zombieHuntThreshold());
  // }
  return prop::SAT_VALUE_TRUE == d_satSolver->solve();
}


} /*bv namespace */
} /* theory namespace */
} /* CVC4 namespace*/



#endif
