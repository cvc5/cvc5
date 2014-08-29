/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
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

typedef __gnu_cxx::hash_map < ClauseId, const prop::SatClause* > IdToClause;
typedef __gnu_cxx::hash_map<Expr, prop::SatVariable, ExprHashFunction > ExprToSatVar;
typedef __gnu_cxx::hash_map<prop::SatVariable, Expr> SatVarToExpr;

class CnfProof {
protected:
  CVC4::prop::CnfStream* d_cnfStream;
  ExprToSatVar d_atomToSatVar;
  SatVarToExpr d_satVarToAtom;
  IdToClause d_inputClauses;
  
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream);

  typedef IdToClause::const_iterator clause_iterator;
  clause_iterator begin_input_clauses() const { return d_inputClauses.begin(); }
  clause_iterator end_input_clauses() const { return d_inputClauses.end(); }
  void addInputClause(ClauseId id, const prop::SatClause* clause); 

  typedef ExprToSatVar::const_iterator atom_iterator;
  atom_iterator begin_atoms() { return d_atomToSatVar.begin(); }
  atom_iterator end_atoms() { return d_atomToSatVar.end(); }
  Expr getAtom(prop::SatVariable var);
  
  virtual void printAtomMapping(std::ostream& os, std::ostream& paren) = 0;
  virtual void printClauses(std::ostream& os, std::ostream& paren) = 0;
  virtual ~CnfProof();
};

class LFSCCnfProof : public CnfProof {
  void printInputClauses(std::ostream& os, std::ostream& paren);

public:
  LFSCCnfProof(CVC4::prop::CnfStream* cnfStream)
    : CnfProof(cnfStream)
  {}

  // virtual iterator begin_atom_mapping();
  // virtual iterator end_atom_mapping();

  virtual void printAtomMapping(std::ostream& os, std::ostream& paren);
  virtual void printClauses(std::ostream& os, std::ostream& paren);
  static void printClause(const prop::SatClause& clause, std::ostream& os, std::ostream& paren);
};


// inline Expr AtomIterator::operator*() {
//   return d_cnf.getAtom(*d_it);
// }

} /* CVC4 namespace */

#endif /* __CVC4__CNF_PROOF_H */
