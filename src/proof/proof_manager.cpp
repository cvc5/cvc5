/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "proof/proof_manager.h"

#include "base/check.h"
#include "context/context.h"
#include "expr/node_visitor.h"
#include "options/bv_options.h"
#include "options/smt_options.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/sat_proof_implementation.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/valuation.h"
#include "util/hash.h"

namespace CVC4 {

ProofManager::ProofManager(context::Context* context)
    : d_context(context),
      d_satProof(nullptr),
      d_cnfProof(nullptr),
      d_inputCoreFormulas(context),
      d_outputCoreFormulas(context),
      d_nextId(0),
      d_deps(context)
{
}

ProofManager::~ProofManager() {}

ProofManager* ProofManager::currentPM() {
  return smt::currentProofManager();
}

CoreSatProof* ProofManager::getSatProof()
{
  Assert(currentPM()->d_satProof);
  return currentPM()->d_satProof.get();
}

CnfProof* ProofManager::getCnfProof()
{
  Assert(currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof.get();
}

void ProofManager::initSatProof(Minisat::Solver* solver)
{
  // Destroy old instance before initializing new one to avoid issues with
  // registering stats
  d_satProof.reset();
  d_satProof.reset(new CoreSatProof(solver, d_context, ""));
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream,
                                context::Context* ctx)
{
  Assert(d_satProof != nullptr);

  d_cnfProof.reset(new CnfProof(cnfStream, ctx, ""));

  // true and false have to be setup in a special way
  Node true_node = NodeManager::currentNM()->mkConst<bool>(true);
  Node false_node = NodeManager::currentNM()->mkConst<bool>(false).notNode();

  d_cnfProof->pushCurrentAssertion(true_node);
  d_cnfProof->registerConvertedClause(d_satProof->getTrueUnit());
  d_cnfProof->popCurrentAssertion();

  d_cnfProof->pushCurrentAssertion(false_node);
  d_cnfProof->registerConvertedClause(d_satProof->getFalseUnit());
  d_cnfProof->popCurrentAssertion();
}


void ProofManager::traceDeps(TNode n, CDExprSet* coreAssertions) {
  Debug("cores") << "trace deps " << n << std::endl;
  if ((n.isConst() && n == NodeManager::currentNM()->mkConst<bool>(true)) ||
      (n.getKind() == kind::NOT && n[0] == NodeManager::currentNM()->mkConst<bool>(false))) {
    return;
  }
  if(d_inputCoreFormulas.find(n.toExpr()) != d_inputCoreFormulas.end()) {
    // originating formula was in core set
    Debug("cores") << " -- IN INPUT CORE LIST!" << std::endl;
    coreAssertions->insert(n.toExpr());
  } else {
    Debug("cores") << " -- NOT IN INPUT CORE LIST!" << std::endl;
    if(d_deps.find(n) == d_deps.end()) {
      InternalError()
          << "Cannot trace dependence information back to input assertion:\n`"
          << n << "'";
    }
    Assert(d_deps.find(n) != d_deps.end());
    std::vector<Node> deps = (*d_deps.find(n)).second;

    for(std::vector<Node>::const_iterator i = deps.begin(); i != deps.end(); ++i) {
      Debug("cores") << " + tracing deps: " << n << " -deps-on- " << *i << std::endl;
      if( !(*i).isNull() ){
        traceDeps(*i, coreAssertions);
      }
    }
  }
}

void ProofManager::traceUnsatCore() {
  Assert(options::unsatCores());
  d_satProof->refreshProof();
  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_satProof->collectClausesUsed(used_inputs,
                                 used_lemmas);

  // At this point, there should be no assertions without a clause id
  Assert(d_cnfProof->isAssertionStackEmpty());

  IdToSatClause::const_iterator it = used_inputs.begin();
  for(; it != used_inputs.end(); ++it) {
    Node node = d_cnfProof->getAssertionForClause(it->first);

    Debug("cores") << "core input assertion " << node << "\n";
    // trace dependences back to actual assertions
    // (this adds them to the unsat core)
    traceDeps(node, &d_outputCoreFormulas);
  }
}

bool ProofManager::unsatCoreAvailable() const {
  return d_satProof->derivedEmptyClause();
}

std::vector<Expr> ProofManager::extractUnsatCore() {
  std::vector<Expr> result;
  output_core_iterator it = begin_unsat_core();
  output_core_iterator end = end_unsat_core();
  while ( it != end ) {
    result.push_back(*it);
    ++it;
  }
  return result;
}

void ProofManager::constructSatProof()
{
  if (!d_satProof->proofConstructed())
  {
    d_satProof->constructProof();
  }
}

void ProofManager::getLemmasInUnsatCore(std::vector<Node>& lemmas)
{
  Assert(options::unsatCores())
      << "Cannot compute unsat core when proofs are off";
  Assert(unsatCoreAvailable())
      << "Cannot get unsat core at this time. Mabye the input is SAT?";
  constructSatProof();
  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_satProof->collectClausesUsed(used_inputs, used_lemmas);
  Debug("pf::lemmasUnsatCore") << "Retrieving all lemmas in unsat core\n";
  IdToSatClause::const_iterator it;
  for (it = used_lemmas.begin(); it != used_lemmas.end(); ++it)
  {
    Node lemma = d_cnfProof->getAssertionForClause(it->first);
    Debug("pf::lemmasUnsatCore") << "Retrieved lemma " << lemma << "\n";
    lemmas.push_back(lemma);
  }
}

void ProofManager::addCoreAssertion(Expr formula) {
  Debug("cores") << "assert: " << formula << std::endl;
  d_deps[Node::fromExpr(formula)]; // empty vector of deps
  d_inputCoreFormulas.insert(formula);
}

void ProofManager::addDependence(TNode n, TNode dep) {
  if(dep != n) {
    Debug("cores") << "dep: " << n << " : " << dep << std::endl;
    if( !dep.isNull() && d_deps.find(dep) == d_deps.end()) {
      Debug("cores") << "WHERE DID " << dep << " come from ??" << std::endl;
    }
    std::vector<Node> deps = d_deps[n].get();
    deps.push_back(dep);
    d_deps[n].set(deps);
  }
}

void ProofManager::addUnsatCore(Expr formula) {
  Assert(d_inputCoreFormulas.find(formula) != d_inputCoreFormulas.end());
  d_outputCoreFormulas.insert(formula);
}

} /* CVC4  namespace */
