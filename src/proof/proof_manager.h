/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A manager for Proofs
 **
 ** A manager for Proofs.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF_MANAGER_H
#define CVC4__PROOF_MANAGER_H

#include <iosfwd>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "proof/clause_id.h"
#include "util/statistics_registry.h"

namespace CVC4 {

// forward declarations
namespace Minisat {
  class Solver;
}/* Minisat namespace */

namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class SmtEngine;

template <class Solver> class TSatProof;
typedef TSatProof< CVC4::Minisat::Solver> CoreSatProof;

class CnfProof;

typedef TSatProof<CVC4::Minisat::Solver> CoreSatProof;

namespace prop {
  typedef uint64_t SatVariable;
  class SatLiteral;
  typedef std::vector<SatLiteral> SatClause;
}/* CVC4::prop namespace */

typedef std::unordered_map<ClauseId, prop::SatClause*> IdToSatClause;
typedef context::CDHashSet<Expr, ExprHashFunction> CDExprSet;
typedef context::CDHashMap<Node, std::vector<Node>, NodeHashFunction> CDNodeToNodes;
typedef std::unordered_set<ClauseId> IdHashSet;

class ProofManager {
  context::Context* d_context;

  std::unique_ptr<CoreSatProof> d_satProof;
  std::unique_ptr<CnfProof> d_cnfProof;

  // information that will need to be shared across proofs
  CDExprSet    d_inputCoreFormulas;
  CDExprSet    d_outputCoreFormulas;

  int d_nextId;

  CDNodeToNodes d_deps;

public:
 ProofManager(context::Context* context);
 ~ProofManager();

 static ProofManager* currentPM();

 // initialization
 void initSatProof(Minisat::Solver* solver);
 void initCnfProof(CVC4::prop::CnfStream* cnfStream, context::Context* ctx);

 // getting various proofs
 static CoreSatProof* getSatProof();
 static CnfProof* getCnfProof();

 /** Public unsat core methods **/
 void addCoreAssertion(Expr formula);

 void addDependence(TNode n, TNode dep);
 void addUnsatCore(Expr formula);

 // trace dependences back to unsat core
 void traceDeps(TNode n, CDExprSet* coreAssertions);
 void traceUnsatCore();

 typedef CDExprSet::const_iterator output_core_iterator;

 output_core_iterator begin_unsat_core() const
 {
   return d_outputCoreFormulas.begin();
 }
 output_core_iterator end_unsat_core() const
 {
   return d_outputCoreFormulas.end();
 }
 size_t size_unsat_core() const { return d_outputCoreFormulas.size(); }
 std::vector<Expr> extractUnsatCore();

 bool unsatCoreAvailable() const;
 void getLemmasInUnsatCore(std::vector<Node>& lemmas);

 int nextId() { return d_nextId++; }

private:
 void constructSatProof();

};/* class ProofManager */

}/* CVC4 namespace */



#endif /* CVC4__PROOF_MANAGER_H */
