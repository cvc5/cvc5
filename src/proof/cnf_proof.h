/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters, Andrew Reynolds
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

#include "cvc4_private.h"

#ifndef __CVC4__CNF_PROOF_H
#define __CVC4__CNF_PROOF_H

#include <ext/hash_map>
#include <ext/hash_set>
#include <iosfwd>

#include "proof/sat_proof.h"
#include "util/proof.h"

namespace CVC4 {
namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class CnfProof;

class CnfProof {
protected:
  CVC4::prop::CnfStream* d_cnfStream;
  VarSet d_atomsDeclared;
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream);

  Expr getAtom(prop::SatVariable var);
  Expr getAssertion(uint64_t id);
  prop::SatLiteral getLiteral(TNode atom);

  virtual void printClauses(std::ostream& os, std::ostream& paren) = 0;
  virtual ~CnfProof();
};/* class CnfProof */

class LFSCCnfProof : public CnfProof {
  void printPreprocess(std::ostream& os, std::ostream& paren);
  void printInputClauses(std::ostream& os, std::ostream& paren);
  void printTheoryLemmas(std::ostream& os, std::ostream& paren);
  void printClause(const prop::SatClause& clause, std::ostream& os, std::ostream& paren);
  virtual void printAtomMapping(const prop::SatClause* clause, std::ostream& os, std::ostream& paren);

  Expr clauseToExpr( const prop::SatClause& clause,
                     std::map< Expr, unsigned >& childIndex,
                     std::map< Expr, bool >& childPol );
 
public:
  LFSCCnfProof(CVC4::prop::CnfStream* cnfStream)
    : CnfProof(cnfStream)
  {}

  virtual void printClauses(std::ostream& os, std::ostream& paren);
};/* class LFSCCnfProof */

} /* CVC4 namespace */

#endif /* __CVC4__CNF_PROOF_H */
