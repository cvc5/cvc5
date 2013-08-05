/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for CnfProofs.
 **
 ** A manager for CnfProofs.
 **
 **
 **/

#ifndef __CVC4__CNF_PROOF_H
#define __CVC4__CNF_PROOF_H

#include "cvc4_private.h"
#include "util/proof.h"
#include "proof/sat_proof.h"

#include <ext/hash_set>
#include <ext/hash_map>
#include <iostream>

namespace CVC4 {
namespace prop {
  class CnfStream;
}

class CnfProof;

class AtomIterator {
  CnfProof& d_cnf;
  ProofManager::var_iterator d_it;

public:
  AtomIterator(CnfProof& cnf, const ProofManager::var_iterator& it)
    : d_cnf(cnf), d_it(it)
  {}
  inline Expr operator*();
  AtomIterator& operator++() { ++d_it; return *this; }
  AtomIterator operator++(int) { AtomIterator x = *this; ++d_it; return x; }
  bool operator==(const AtomIterator& it) const { return &d_cnf == &it.d_cnf && d_it == it.d_it; }
  bool operator!=(const AtomIterator& it) const { return !(*this == it); }
};/* class AtomIterator */

class CnfProof {
protected:
  CVC4::prop::CnfStream* d_cnfStream;
  Expr getAtom(prop::SatVariable var);
  friend class AtomIterator;
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream);

  typedef AtomIterator iterator;
  virtual iterator begin_atom_mapping() = 0;
  virtual iterator end_atom_mapping() = 0;

  virtual void printAtomMapping(std::ostream& os, std::ostream& paren) = 0;
  virtual void printClauses(std::ostream& os, std::ostream& paren) = 0;
  virtual ~CnfProof();
};

class LFSCCnfProof : public CnfProof {
  void printInputClauses(std::ostream& os, std::ostream& paren);
  void printTheoryLemmas(std::ostream& os, std::ostream& paren);
  void printClause(const prop::SatClause& clause, std::ostream& os, std::ostream& paren);

public:
  LFSCCnfProof(CVC4::prop::CnfStream* cnfStream)
    : CnfProof(cnfStream)
  {}

  virtual iterator begin_atom_mapping();
  virtual iterator end_atom_mapping();

  virtual void printAtomMapping(std::ostream& os, std::ostream& paren);
  virtual void printClauses(std::ostream& os, std::ostream& paren);
};

inline Expr AtomIterator::operator*() {
  return d_cnf.getAtom(*d_it);
}

} /* CVC4 namespace */

#endif /* __CVC4__CNF_PROOF_H */
