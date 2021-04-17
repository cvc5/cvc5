/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A manager for Proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF_MANAGER_H
#define CVC5__PROOF_MANAGER_H

#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "proof/clause_id.h"

namespace cvc5 {

// forward declarations
namespace Minisat {
  class Solver;
}/* Minisat namespace */

namespace prop {
  class CnfStream;
  }  // namespace prop

class SmtEngine;

template <class Solver> class TSatProof;
typedef TSatProof<cvc5::Minisat::Solver> CoreSatProof;

class CnfProof;

typedef TSatProof<cvc5::Minisat::Solver> CoreSatProof;

namespace prop {
  typedef uint64_t SatVariable;
  class SatLiteral;
  typedef std::vector<SatLiteral> SatClause;
  }  // namespace prop

typedef std::unordered_map<ClauseId, prop::SatClause*> IdToSatClause;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;
typedef context::CDHashMap<Node, std::vector<Node>, NodeHashFunction> CDNodeToNodes;
typedef std::unordered_set<ClauseId> IdHashSet;

class ProofManager {
  context::Context* d_context;

  std::unique_ptr<CoreSatProof> d_satProof;
  std::unique_ptr<CnfProof> d_cnfProof;

  // information that will need to be shared across proofs
  CDNodeSet d_inputCoreFormulas;
  CDNodeSet d_outputCoreFormulas;

  int d_nextId;

  CDNodeToNodes d_deps;

public:
 ProofManager(context::Context* context);
 ~ProofManager();

 static ProofManager* currentPM();

 // initialization
 void initSatProof(Minisat::Solver* solver);
 void initCnfProof(cvc5::prop::CnfStream* cnfStream, context::Context* ctx);

 // getting various proofs
 static CoreSatProof* getSatProof();
 static CnfProof* getCnfProof();

 /** Public unsat core methods **/
 void addCoreAssertion(Node formula);

 void addDependence(TNode n, TNode dep);
 void addUnsatCore(Node formula);

 // trace dependences back to unsat core
 void traceDeps(TNode n, CDNodeSet* coreAssertions);
 void traceUnsatCore();

 typedef CDNodeSet::const_iterator output_core_iterator;

 output_core_iterator begin_unsat_core() const
 {
   return d_outputCoreFormulas.begin();
 }
 output_core_iterator end_unsat_core() const
 {
   return d_outputCoreFormulas.end();
 }
 size_t size_unsat_core() const { return d_outputCoreFormulas.size(); }
 std::vector<Node> extractUnsatCore();

 bool unsatCoreAvailable() const;
 void getLemmasInUnsatCore(std::vector<Node>& lemmas);

 int nextId() { return d_nextId++; }

private:
 void constructSatProof();

};/* class ProofManager */

}  // namespace cvc5

#endif /* CVC5__PROOF_MANAGER_H */
