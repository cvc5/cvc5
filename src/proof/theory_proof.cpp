/*********************                                                        */
/*! \file theory_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Liana Hadarean, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "proof/theory_proof.h"

#include "base/check.h"
#include "context/context.h"
#include "expr/node_visitor.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/arith_proof.h"
#include "proof/array_proof.h"
#include "proof/clausal_bitvector_proof.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/proof_manager.h"
#include "proof/proof_output_channel.h"
#include "proof/proof_utils.h"
#include "proof/resolution_bitvector_proof.h"
#include "proof/sat_proof.h"
#include "proof/simplify_boolean_node.h"
#include "proof/uf_proof.h"
#include "prop/sat_solver_types.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"
#include "theory/output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/theory_uf.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/proof.h"

namespace CVC4 {

using proof::LfscResolutionBitVectorProof;
using proof::ResolutionBitVectorProof;

unsigned CVC4::ProofLetCount::counter = 0;
static unsigned LET_COUNT = 1;

TheoryProofEngine::TheoryProofEngine()
  : d_registrationCache()
  , d_theoryProofTable()
{
  d_theoryProofTable[theory::THEORY_BOOL] = new LFSCBooleanProof(this);
}

TheoryProofEngine::~TheoryProofEngine() {
  TheoryProofTable::iterator it = d_theoryProofTable.begin();
  TheoryProofTable::iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    delete it->second;
  }
}

void TheoryProofEngine::registerTheory(theory::Theory* th) {
  if (th) {
    theory::TheoryId id = th->getId();
    if(d_theoryProofTable.find(id) == d_theoryProofTable.end()) {

      Trace("pf::tp") << "TheoryProofEngine::registerTheory: " << id << std::endl;

      if (id == theory::THEORY_UF) {
        d_theoryProofTable[id] = new LFSCUFProof((theory::uf::TheoryUF*)th, this);
        return;
      }

      if (id == theory::THEORY_BV) {
        auto thBv = static_cast<theory::bv::TheoryBV*>(th);
        if (options::bitblastMode() == options::BitblastMode::EAGER
            && options::bvSatSolver() == options::SatSolverMode::CRYPTOMINISAT)
        {
          proof::BitVectorProof* bvp = nullptr;
          switch (options::bvProofFormat())
          {
            case options::BvProofFormat::DRAT:
            {
              bvp = new proof::LfscDratBitVectorProof(thBv, this);
              break;
            }
            case options::BvProofFormat::LRAT:
            {
              bvp = new proof::LfscLratBitVectorProof(thBv, this);
              break;
            }
            case options::BvProofFormat::ER:
            {
              bvp = new proof::LfscErBitVectorProof(thBv, this);
              break;
            }
            default:
            {
              Unreachable() << "Invalid BvProofFormat";
            }
          };
          d_theoryProofTable[id] = bvp;
        }
        else
        {
          proof::BitVectorProof* bvp =
              new proof::LfscResolutionBitVectorProof(thBv, this);
          d_theoryProofTable[id] = bvp;
        }
        return;
      }

      if (id == theory::THEORY_ARRAYS) {
        d_theoryProofTable[id] = new LFSCArrayProof((theory::arrays::TheoryArrays*)th, this);
        return;
      }

      if (id == theory::THEORY_ARITH) {
        d_theoryProofTable[id] = new LFSCArithProof((theory::arith::TheoryArith*)th, this);
        return;
      }

      // TODO other theories
    }
  }
}

void TheoryProofEngine::finishRegisterTheory(theory::Theory* th) {
  if (th) {
    theory::TheoryId id = th->getId();
    if (id == theory::THEORY_BV) {
      theory::bv::TheoryBV* bv_th = static_cast<theory::bv::TheoryBV*>(th);
      Assert(d_theoryProofTable.find(id) != d_theoryProofTable.end());
      proof::BitVectorProof* bvp =
          static_cast<proof::BitVectorProof*>(d_theoryProofTable[id]);
      bv_th->setProofLog(bvp);
      return;
    }
  }
}

TheoryProof* TheoryProofEngine::getTheoryProof(theory::TheoryId id) {
  // The UF theory handles queries for the Builtin theory.
  if (id == theory::THEORY_BUILTIN) {
    Debug("pf::tp") << "TheoryProofEngine::getTheoryProof: BUILTIN --> UF" << std::endl;
    id = theory::THEORY_UF;
  }

  if (d_theoryProofTable.find(id) == d_theoryProofTable.end()) {
    InternalError()
        << "Error! Proofs not yet supported for the following theory: " << id
        << std::endl;
  }

  return d_theoryProofTable[id];
}

void TheoryProofEngine::markTermForFutureRegistration(Expr term, theory::TheoryId id) {
  d_exprToTheoryIds[term].insert(id);
}

void TheoryProofEngine::printConstantDisequalityProof(std::ostream& os, Expr c1, Expr c2, const ProofLetMap &globalLetMap) {
  Assert(c1.isConst());
  Assert(c2.isConst());

  Assert(theory::Theory::theoryOf(c1) == theory::Theory::theoryOf(c2));
  getTheoryProof(theory::Theory::theoryOf(c1))->printConstantDisequalityProof(os, c1, c2, globalLetMap);
}

void TheoryProofEngine::printTheoryTerm(Expr term,
                                        std::ostream& os,
                                        const ProofLetMap& map,
                                        TypeNode expectedType)
{
  this->printTheoryTermAsType(term, os, map, expectedType);
}

TypeNode TheoryProofEngine::equalityType(const Expr& left, const Expr& right)
{
  // Ask the two theories what they think..
  TypeNode leftType = getTheoryProof(theory::Theory::theoryOf(left))->equalityType(left, right);
  TypeNode rightType = getTheoryProof(theory::Theory::theoryOf(right))->equalityType(left, right);

  // Error if the disagree.
  Assert(leftType.isNull() || rightType.isNull() || leftType == rightType)
    << "TheoryProofEngine::equalityType(" << left << ", " << right << "):" << std::endl
    << "theories disagree about the type of an equality:" << std::endl
    << "\tleft: " << leftType << std::endl
    << "\tright:" << rightType;

  return leftType.isNull() ? rightType : leftType;
}

void TheoryProofEngine::registerTerm(Expr term) {
  Debug("pf::tp::register") << "TheoryProofEngine::registerTerm: registering term: " << term << std::endl;

  if (d_registrationCache.count(term)) {
    return;
  }

  Debug("pf::tp::register") << "TheoryProofEngine::registerTerm: registering NEW term: " << term << std::endl;

  theory::TheoryId theory_id = theory::Theory::theoryOf(term);

  Debug("pf::tp::register") << "Term's theory( " << term << " ) = " << theory_id << std::endl;

  // don't need to register boolean terms
  if (theory_id == theory::THEORY_BUILTIN ||
      term.getKind() == kind::ITE) {
    for (unsigned i = 0; i < term.getNumChildren(); ++i) {
      registerTerm(term[i]);
    }
    d_registrationCache.insert(term);
    return;
  }

  if (!supportedTheory(theory_id)) return;

  // Register the term with its owner theory
  getTheoryProof(theory_id)->registerTerm(term);

  // A special case: the array theory needs to know of every skolem, even if
  // it belongs to another theory (e.g., a BV skolem)
  if (ProofManager::getSkolemizationManager()->isSkolem(term) && theory_id != theory::THEORY_ARRAYS) {
    Debug("pf::tp::register") << "TheoryProofEngine::registerTerm: registering a non-array skolem: " << term << std::endl;
    getTheoryProof(theory::THEORY_ARRAYS)->registerTerm(term);
  }

  d_registrationCache.insert(term);
}

theory::TheoryId TheoryProofEngine::getTheoryForLemma(const prop::SatClause* clause) {
  ProofManager* pm = ProofManager::currentPM();

  std::set<Node> nodes;
  for(unsigned i = 0; i < clause->size(); ++i) {
    prop::SatLiteral lit = (*clause)[i];
    Node node = pm->getCnfProof()->getAtom(lit.getSatVariable());
    Expr atom = node.toExpr();
    if (atom.isConst()) {
      Assert(atom == utils::mkTrue());
      continue;
    }

    nodes.insert(lit.isNegated() ? node.notNode() : node);
  }

  // Ensure that the lemma is in the database.
  Assert(pm->getCnfProof()->haveProofRecipe(nodes));
  return pm->getCnfProof()->getProofRecipe(nodes).getTheory();
}

void LFSCTheoryProofEngine::bind(Expr term, ProofLetMap& map, Bindings& let_order) {
  ProofLetMap::iterator it = map.find(term);
  if (it != map.end()) {
    ProofLetCount& count = it->second;
    count.increment();
    return;
  }
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    bind(term[i], map, let_order);
  }
  unsigned new_id = ProofLetCount::newId();
  map[term] = ProofLetCount(new_id);
  let_order.push_back(LetOrderElement(term, new_id));
}

void LFSCTheoryProofEngine::printLetTerm(Expr term, std::ostream& os) {
  ProofLetMap map;
  Bindings let_order;
  bind(term, map, let_order);
  std::ostringstream paren;
  for (unsigned i = 0; i < let_order.size(); ++i) {
    Expr current_expr = let_order[i].expr;
    unsigned let_id = let_order[i].id;
    ProofLetMap::const_iterator it = map.find(current_expr);
    Assert(it != map.end());
    unsigned let_count = it->second.count;
    Assert(let_count);
    // skip terms that only appear once
    if (let_count <= LET_COUNT) {
      continue;
    }

    os << "(@ let" <<let_id << " ";
    printTheoryTerm(current_expr, os, map);
    paren <<")";
  }
  unsigned last_let_id = let_order.back().id;
  Expr last = let_order.back().expr;
  unsigned last_count = map.find(last)->second.count;
  if (last_count <= LET_COUNT) {
    printTheoryTerm(last, os, map);
  }
  else {
    os << " let" << last_let_id;
  }
  os << paren.str();
}

void LFSCTheoryProofEngine::printTheoryTermAsType(Expr term,
                                                  std::ostream& os,
                                                  const ProofLetMap& map,
                                                  TypeNode expectedType)
{
  theory::TheoryId theory_id = theory::Theory::theoryOf(term);

  // boolean terms and ITEs are special because they
  // are common to all theories
  if (theory_id == theory::THEORY_BUILTIN ||
      term.getKind() == kind::ITE ||
      term.getKind() == kind::EQUAL) {
    printCoreTerm(term, os, map, expectedType);
    return;
  }
  // dispatch to proper theory
  getTheoryProof(theory_id)->printOwnedTerm(term, os, map, expectedType);
}

void LFSCTheoryProofEngine::printSort(Type type, std::ostream& os) {
  if (type.isSort()) {
    getTheoryProof(theory::THEORY_UF)->printOwnedSort(type, os);
    return;
  }
  if (type.isBitVector()) {
    getTheoryProof(theory::THEORY_BV)->printOwnedSort(type, os);
    return;
  }

  if (type.isArray()) {
    getTheoryProof(theory::THEORY_ARRAYS)->printOwnedSort(type, os);
    return;
  }

  if (type.isInteger() || type.isReal()) {
    getTheoryProof(theory::THEORY_ARITH)->printOwnedSort(type, os);
    return;
  }

  if (type.isBoolean()) {
    getTheoryProof(theory::THEORY_BOOL)->printOwnedSort(type, os);
    return;
  }

  Unreachable();
}

void LFSCTheoryProofEngine::performExtraRegistrations() {
  ExprToTheoryIds::const_iterator it;
  for (it = d_exprToTheoryIds.begin(); it != d_exprToTheoryIds.end(); ++it) {
    if (d_registrationCache.count(it->first)) { // Only register if the term appeared
      TheoryIdSet::const_iterator theoryIt;
      for (theoryIt = it->second.begin(); theoryIt != it->second.end(); ++theoryIt) {
        Debug("pf::tp") << "\tExtra registration of term " << it->first
                        << " with theory: " << *theoryIt << std::endl;
        Assert(supportedTheory(*theoryIt));
        getTheoryProof(*theoryIt)->registerTerm(it->first);
      }
    }
  }
}

void LFSCTheoryProofEngine::registerTermsFromAssertions() {
  ProofManager::assertions_iterator it = ProofManager::currentPM()->begin_assertions();
  ProofManager::assertions_iterator end = ProofManager::currentPM()->end_assertions();

  for(; it != end; ++it) {
    registerTerm(*it);
  }

  performExtraRegistrations();
}

void LFSCTheoryProofEngine::printAssertions(std::ostream& os, std::ostream& paren) {
  Debug("pf::tp") << "LFSCTheoryProofEngine::printAssertions called" << std::endl << std::endl;

  ProofManager::assertions_iterator it = ProofManager::currentPM()->begin_assertions();
  ProofManager::assertions_iterator end = ProofManager::currentPM()->end_assertions();

  for (; it != end; ++it) {
    Debug("pf::tp") << "printAssertions: assertion is: " << *it << std::endl;
    os << "(% " << ProofManager::currentPM()->getInputFormulaName(*it) << " (th_holds ";

    // Assertions appear before the global let map, so we use a dummpMap to avoid letification here.
    ProofLetMap dummyMap;

    bool convertFromBool = (it->getType().isBoolean() && printsAsBool(*it));
    if (convertFromBool) os << "(p_app ";
    printBoundTerm(*it, os, dummyMap);
    if (convertFromBool) os << ")";

    os << ")\n";
    paren << ")";
  }

  Debug("pf::tp") << "LFSCTheoryProofEngine::printAssertions done" << std::endl << std::endl;
}

void LFSCTheoryProofEngine::printLemmaRewrites(NodePairSet& rewrites,
                                               std::ostream& os,
                                               std::ostream& paren) {
  Debug("pf::tp") << "LFSCTheoryProofEngine::printLemmaRewrites called" << std::endl << std::endl;

  NodePairSet::const_iterator it;

  for (it = rewrites.begin(); it != rewrites.end(); ++it) {
    Debug("pf::tp") << "printLemmaRewrites: " << it->first << " --> " << it->second << std::endl;

    Node n1 = it->first;
    Node n2 = it->second;
    Assert(n1.toExpr() == utils::mkFalse()
           || theory::Theory::theoryOf(n1) == theory::Theory::theoryOf(n2));

    std::ostringstream rewriteRule;
    rewriteRule << ".lrr" << d_assertionToRewrite.size();

    os << "(th_let_pf _ ";
    getTheoryProof(theory::Theory::theoryOf(n1))->printRewriteProof(os, n1, n2);
    os << "(\\ " << rewriteRule.str() << "\n";

    d_assertionToRewrite[it->first] = rewriteRule.str();
    Debug("pf::tp") << "d_assertionToRewrite[" << it->first << "] = " << rewriteRule.str() << std::endl;
    paren << "))";
  }

  Debug("pf::tp") << "LFSCTheoryProofEngine::printLemmaRewrites done" << std::endl << std::endl;
}

void LFSCTheoryProofEngine::printSortDeclarations(std::ostream& os, std::ostream& paren) {
  Debug("pf::tp") << "LFSCTheoryProofEngine::printSortDeclarations called" << std::endl << std::endl;

  TheoryProofTable::const_iterator it = d_theoryProofTable.begin();
  TheoryProofTable::const_iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    it->second->printSortDeclarations(os, paren);
  }

  Debug("pf::tp") << "LFSCTheoryProofEngine::printSortDeclarations done" << std::endl << std::endl;
}

void LFSCTheoryProofEngine::printTermDeclarations(std::ostream& os, std::ostream& paren) {
  Debug("pf::tp") << "LFSCTheoryProofEngine::printTermDeclarations called" << std::endl << std::endl;

  TheoryProofTable::const_iterator it = d_theoryProofTable.begin();
  TheoryProofTable::const_iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    it->second->printTermDeclarations(os, paren);
  }

  Debug("pf::tp") << "LFSCTheoryProofEngine::printTermDeclarations done" << std::endl << std::endl;
}

void LFSCTheoryProofEngine::printDeferredDeclarations(std::ostream& os, std::ostream& paren) {
  Debug("pf::tp") << "LFSCTheoryProofEngine::printDeferredDeclarations called" << std::endl;

  TheoryProofTable::const_iterator it = d_theoryProofTable.begin();
  TheoryProofTable::const_iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    it->second->printDeferredDeclarations(os, paren);
  }
}

void LFSCTheoryProofEngine::printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) {
  Debug("pf::tp") << "LFSCTheoryProofEngine::printAliasingDeclarations called" << std::endl;

  TheoryProofTable::const_iterator it = d_theoryProofTable.begin();
  TheoryProofTable::const_iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    it->second->printAliasingDeclarations(os, paren, globalLetMap);
  }
}

void LFSCTheoryProofEngine::dumpTheoryLemmas(const IdToSatClause& lemmas) {
  Debug("pf::dumpLemmas") << "Dumping ALL theory lemmas" << std::endl << std::endl;

  ProofManager* pm = ProofManager::currentPM();
  for (IdToSatClause::const_iterator it = lemmas.begin(); it != lemmas.end(); ++it) {
    ClauseId id = it->first;
    Debug("pf::dumpLemmas") << "**** \tLemma ID = " << id << std::endl;
    const prop::SatClause* clause = it->second;
    std::set<Node> nodes;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Node node = pm->getCnfProof()->getAtom(lit.getSatVariable());
      if (node.isConst()) {
        Assert(node.toExpr() == utils::mkTrue());
        continue;
      }
      nodes.insert(lit.isNegated() ? node.notNode() : node);
    }

    LemmaProofRecipe recipe = pm->getCnfProof()->getProofRecipe(nodes);
    recipe.dump("pf::dumpLemmas");
  }

  Debug("pf::dumpLemmas") << "Theory lemma printing DONE" << std::endl << std::endl;
}

// TODO: this function should be moved into the BV prover.
void LFSCTheoryProofEngine::finalizeBvConflicts(const IdToSatClause& lemmas, std::ostream& os) {
  // BitVector theory is special case: must know all conflicts needed
  // ahead of time for resolution proof lemmas
  std::vector<Expr> bv_lemmas;

  for (IdToSatClause::const_iterator it = lemmas.begin(); it != lemmas.end(); ++it) {
    const prop::SatClause* clause = it->second;

    std::vector<Expr> conflict;
    std::set<Node> conflictNodes;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Node node = ProofManager::currentPM()->getCnfProof()->getAtom(lit.getSatVariable());
      Expr atom = node.toExpr();

      // The literals (true) and (not false) are omitted from conflicts
      if (atom.isConst()) {
        Assert(atom == utils::mkTrue()
               || (atom == utils::mkFalse() && lit.isNegated()));
        continue;
      }

      Expr expr_lit = lit.isNegated() ? atom.notExpr() : atom;
      conflict.push_back(expr_lit);
      conflictNodes.insert(lit.isNegated() ? node.notNode() : node);
    }

    LemmaProofRecipe recipe = ProofManager::currentPM()->getCnfProof()->getProofRecipe(conflictNodes);

    unsigned numberOfSteps = recipe.getNumSteps();

    prop::SatClause currentClause = *clause;
    std::vector<Expr> currentClauseExpr = conflict;

    for (unsigned i = 0; i < numberOfSteps; ++i) {
      const LemmaProofRecipe::ProofStep* currentStep = recipe.getStep(i);

      if (currentStep->getTheory() != theory::THEORY_BV) {
        continue;
      }

      // If any rewrites took place, we need to update the conflict clause accordingly
      std::set<Node> missingAssertions = recipe.getMissingAssertionsForStep(i);
      std::map<Node, Node> explanationToMissingAssertion;
      std::set<Node>::iterator assertionIt;
      for (assertionIt = missingAssertions.begin();
           assertionIt != missingAssertions.end();
           ++assertionIt) {
        Node negated = (*assertionIt).negate();
        explanationToMissingAssertion[recipe.getExplanation(negated)] = negated;
      }

      currentClause = *clause;
      currentClauseExpr = conflict;

      for (unsigned j = 0; j < i; ++j) {
        // Literals already used in previous steps need to be negated
        Node previousLiteralNode = recipe.getStep(j)->getLiteral();

        // If this literal is the result of a rewrite, we need to translate it
        if (explanationToMissingAssertion.find(previousLiteralNode) !=
            explanationToMissingAssertion.end()) {
          previousLiteralNode = explanationToMissingAssertion[previousLiteralNode];
        }

        Node previousLiteralNodeNegated = previousLiteralNode.negate();
        prop::SatLiteral previousLiteralNegated =
          ProofManager::currentPM()->getCnfProof()->getLiteral(previousLiteralNodeNegated);

        currentClause.push_back(previousLiteralNegated);
        currentClauseExpr.push_back(previousLiteralNodeNegated.toExpr());
      }

      // If we're in the final step, the last literal is Null and should not be added.
      // Otherwise, the current literal does NOT need to be negated
      Node currentLiteralNode = currentStep->getLiteral();

      if (currentLiteralNode != Node()) {
        prop::SatLiteral currentLiteral =
          ProofManager::currentPM()->getCnfProof()->getLiteral(currentLiteralNode);

        currentClause.push_back(currentLiteral);
        currentClauseExpr.push_back(currentLiteralNode.toExpr());
      }

      bv_lemmas.push_back(utils::mkSortedExpr(kind::OR, currentClauseExpr));
    }
  }

  proof::BitVectorProof* bv = ProofManager::getBitVectorProof();
  bv->finalizeConflicts(bv_lemmas);
}

void LFSCTheoryProofEngine::printTheoryLemmas(const IdToSatClause& lemmas,
                                              std::ostream& os,
                                              std::ostream& paren,
                                              ProofLetMap& map) {
  os << " ;; Theory Lemmas \n";
  Debug("pf::tp") << "LFSCTheoryProofEngine::printTheoryLemmas: starting" << std::endl;

  if (Debug.isOn("pf::dumpLemmas")) {
    dumpTheoryLemmas(lemmas);
  }

  //  finalizeBvConflicts(lemmas, os, paren, map);
  ProofManager::getBitVectorProof()->printBBDeclarationAndCnf(os, paren, map);

  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    Assert(lemmas.size() == 1);
    // nothing more to do (no combination with eager so far)
    return;
  }

  ProofManager* pm = ProofManager::currentPM();
  Debug("pf::tp") << "LFSCTheoryProofEngine::printTheoryLemmas: printing lemmas..." << std::endl;

  for (IdToSatClause::const_iterator it = lemmas.begin(); it != lemmas.end(); ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;

    Debug("pf::tp") << "LFSCTheoryProofEngine::printTheoryLemmas: printing lemma. ID = "
                    << id << std::endl;

    std::vector<Expr> clause_expr;
    std::set<Node> clause_expr_nodes;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Node node = pm->getCnfProof()->getAtom(lit.getSatVariable());
      Expr atom = node.toExpr();
      if (atom.isConst()) {
        Assert(atom == utils::mkTrue());
        continue;
      }
      Expr expr_lit = lit.isNegated() ? atom.notExpr(): atom;
      clause_expr.push_back(expr_lit);
      clause_expr_nodes.insert(lit.isNegated() ? node.notNode() : node);
    }

    LemmaProofRecipe recipe = pm->getCnfProof()->getProofRecipe(clause_expr_nodes);

    if (recipe.simpleLemma()) {
      // In a simple lemma, there will be no propositional resolution in the end

      Debug("pf::tp") << "Simple lemma" << std::endl;
      // Printing the clause as it appears in resolution proof
      os << "(satlem _ _ ";
      std::ostringstream clause_paren;
      pm->getCnfProof()->printClause(*clause, os, clause_paren);

      // Find and handle missing assertions, due to rewrites
      std::set<Node> missingAssertions = recipe.getMissingAssertionsForStep(0);
      if (!missingAssertions.empty()) {
        Debug("pf::tp") << "Have missing assertions for this simple lemma!" << std::endl;
      }

      std::set<Node>::const_iterator missingAssertion;
      for (missingAssertion = missingAssertions.begin();
           missingAssertion != missingAssertions.end();
           ++missingAssertion) {

        Debug("pf::tp") << "Working on missing assertion: " << *missingAssertion << std::endl;
        Assert(recipe.wasRewritten(missingAssertion->negate()));
        Node explanation = recipe.getExplanation(missingAssertion->negate()).negate();
        Debug("pf::tp") << "Found explanation: " << explanation << std::endl;

        // We have a missing assertion.
        //     rewriteIt->first is the assertion after the rewrite (the explanation),
        //     rewriteIt->second is the original assertion that needs to be fed into the theory.

        bool found = false;
        unsigned k;
        for (k = 0; k < clause_expr.size(); ++k) {
          if (clause_expr[k] == explanation.toExpr()) {
            found = true;
            break;
          }
        }

        AlwaysAssert(found);
        Debug("pf::tp") << "Replacing theory assertion "
                        << clause_expr[k]
                        << " with "
                        << *missingAssertion
                        << std::endl;

        clause_expr[k] = missingAssertion->toExpr();

        std::ostringstream rewritten;

        if (missingAssertion->getKind() == kind::NOT && (*missingAssertion)[0].toExpr() == utils::mkFalse()) {
          rewritten << "(or_elim_2 _ _ ";
          rewritten << "(not_not_intro _ ";
          rewritten << pm->getLitName(explanation);
          rewritten << ") (iff_elim_2 _ _ ";
          rewritten << d_assertionToRewrite[missingAssertion->negate()];
          rewritten << "))";
        }
        else {
          rewritten << "(or_elim_1 _ _ ";
          rewritten << "(not_not_intro _ ";
          rewritten << pm->getLitName(explanation);
          rewritten << ") (iff_elim_1 _ _ ";
          rewritten << d_assertionToRewrite[missingAssertion->negate()];
          rewritten << "))";
        }

        Debug("pf::tp") << "Setting a rewrite filter for this proof: " << std::endl
                        << pm->getLitName(*missingAssertion) << " --> " << rewritten.str()
                        << ", explanation = " << explanation
                        << std::endl << std::endl;

        pm->addRewriteFilter(pm->getLitName(*missingAssertion), rewritten.str());
      }

      // Query the appropriate theory for a proof of this clause
      theory::TheoryId theory_id = getTheoryForLemma(clause);
      Debug("pf::tp") << "Get theory lemma from " << theory_id << "..." << std::endl;
      getTheoryProof(theory_id)->printTheoryLemmaProof(clause_expr, os, paren, map);

      // Turn rewrite filter OFF
      pm->clearRewriteFilters();

      Debug("pf::tp") << "Get theory lemma from " << theory_id << "... DONE!" << std::endl;
      os << clause_paren.str();
      os << "( \\ " << pm->getLemmaClauseName(id) <<"\n";
      paren << "))";
    } else { // This is a composite lemma

      unsigned numberOfSteps = recipe.getNumSteps();
      prop::SatClause currentClause = *clause;
      std::vector<Expr> currentClauseExpr = clause_expr;

      for (unsigned i = 0; i < numberOfSteps; ++i) {
        const LemmaProofRecipe::ProofStep* currentStep = recipe.getStep(i);

        currentClause = *clause;
        currentClauseExpr = clause_expr;

        for (unsigned j = 0; j < i; ++j) {
          // Literals already used in previous steps need to be negated
          Node previousLiteralNode = recipe.getStep(j)->getLiteral();
          Node previousLiteralNodeNegated = previousLiteralNode.negate();
          prop::SatLiteral previousLiteralNegated =
            ProofManager::currentPM()->getCnfProof()->getLiteral(previousLiteralNodeNegated);
          currentClause.push_back(previousLiteralNegated);
          currentClauseExpr.push_back(previousLiteralNodeNegated.toExpr());
        }

        // If the current literal is NULL, can ignore (final step)
        // Otherwise, the current literal does NOT need to be negated
        Node currentLiteralNode = currentStep->getLiteral();
        if (currentLiteralNode != Node()) {
          prop::SatLiteral currentLiteral =
            ProofManager::currentPM()->getCnfProof()->getLiteral(currentLiteralNode);

          currentClause.push_back(currentLiteral);
          currentClauseExpr.push_back(currentLiteralNode.toExpr());
        }

        os << "(satlem _ _ ";
        std::ostringstream clause_paren;

        pm->getCnfProof()->printClause(currentClause, os, clause_paren);

        // query appropriate theory for proof of clause
        theory::TheoryId theory_id = currentStep->getTheory();
        Debug("pf::tp") << "Get theory lemma from " << theory_id << "..." << std::endl;

        std::set<Node> missingAssertions = recipe.getMissingAssertionsForStep(i);
        if (!missingAssertions.empty()) {
          Debug("pf::tp") << "Have missing assertions for this step!" << std::endl;
        }

        // Turn rewrite filter ON
        std::set<Node>::const_iterator missingAssertion;
        for (missingAssertion = missingAssertions.begin();
             missingAssertion != missingAssertions.end();
             ++missingAssertion) {

          Debug("pf::tp") << "Working on missing assertion: " << *missingAssertion << std::endl;

          Assert(recipe.wasRewritten(missingAssertion->negate()));
          Node explanation = recipe.getExplanation(missingAssertion->negate()).negate();

          Debug("pf::tp") << "Found explanation: " << explanation << std::endl;

          // We have a missing assertion.
          //     rewriteIt->first is the assertion after the rewrite (the explanation),
          //     rewriteIt->second is the original assertion that needs to be fed into the theory.

          bool found = false;
          unsigned k;
          for (k = 0; k < currentClauseExpr.size(); ++k) {
            if (currentClauseExpr[k] == explanation.toExpr()) {
              found = true;
              break;
            }
          }

          AlwaysAssert(found);

          Debug("pf::tp") << "Replacing theory assertion "
                          << currentClauseExpr[k]
                          << " with "
                          << *missingAssertion
                          << std::endl;

          currentClauseExpr[k] = missingAssertion->toExpr();

          std::ostringstream rewritten;

          if (missingAssertion->getKind() == kind::NOT && (*missingAssertion)[0].toExpr() == utils::mkFalse()) {
            rewritten << "(or_elim_2 _ _ ";
            rewritten << "(not_not_intro _ ";
            rewritten << pm->getLitName(explanation);
            rewritten << ") (iff_elim_2 _ _ ";
            rewritten << d_assertionToRewrite[missingAssertion->negate()];
            rewritten << "))";
          }
          else {
            rewritten << "(or_elim_1 _ _ ";
            rewritten << "(not_not_intro _ ";
            rewritten << pm->getLitName(explanation);
            rewritten << ") (iff_elim_1 _ _ ";
            rewritten << d_assertionToRewrite[missingAssertion->negate()];
            rewritten << "))";
          }

          Debug("pf::tp") << "Setting a rewrite filter for this proof: " << std::endl
                          << pm->getLitName(*missingAssertion) << " --> " << rewritten.str()
                          << "explanation = " << explanation
                          << std::endl << std::endl;

          pm->addRewriteFilter(pm->getLitName(*missingAssertion), rewritten.str());
        }

        getTheoryProof(theory_id)->printTheoryLemmaProof(currentClauseExpr, os, paren, map);

        // Turn rewrite filter OFF
        pm->clearRewriteFilters();

        Debug("pf::tp") << "Get theory lemma from " << theory_id << "... DONE!" << std::endl;
        os << clause_paren.str();
        os << "( \\ " << pm->getLemmaClauseName(id) << "s" << i <<"\n";
        paren << "))";
      }

      Assert(numberOfSteps >= 2);

      os << "(satlem_simplify _ _ _ ";
      for (unsigned i = 0; i < numberOfSteps - 1; ++i) {
        // Resolve step i with step i + 1
        if (recipe.getStep(i)->getLiteral().getKind() == kind::NOT) {
          os << "(Q _ _ ";
        } else {
          os << "(R _ _ ";
        }

        os << pm->getLemmaClauseName(id) << "s" << i;
        os << " ";
      }

      os << pm->getLemmaClauseName(id) << "s" << numberOfSteps - 1 << " ";

      prop::SatLiteral v;
      for (int i = numberOfSteps - 2; i >= 0; --i) {
        v = ProofManager::currentPM()->getCnfProof()->getLiteral(recipe.getStep(i)->getLiteral());
        os << ProofManager::getVarName(v.getSatVariable(), "") << ") ";
      }

      os << "( \\ " << pm->getLemmaClauseName(id) << "\n";
      paren << "))";
    }
  }
}

void LFSCTheoryProofEngine::printBoundTermAsType(Expr term,
                                                 std::ostream& os,
                                                 const ProofLetMap& map,
                                                 TypeNode expectedType)
{
  Debug("pf::tp") << "LFSCTheoryProofEngine::printBoundTerm( " << term << " ) " << std::endl;

  // Since let-abbreviated terms are abbreviated with their default type, only
  // use the let map if there is no expectedType or the expectedType matches
  // the default.
  if (expectedType.isNull()
      || TypeNode::fromType(term.getType()) == expectedType)
  {
    ProofLetMap::const_iterator it = map.find(term);
    if (it != map.end())
    {
      unsigned id = it->second.id;
      unsigned count = it->second.count;

      if (count > LET_COUNT)
      {
        os << "let" << id;
        Debug("pf::tp::letmap") << "Using let map for " << term << std::endl;
        return;
      }
    }
  }
  Debug("pf::tp::letmap") << "Skipping let map for " << term << std::endl;

  printTheoryTerm(term, os, map, expectedType);
}

void LFSCTheoryProofEngine::printBoundFormula(Expr term,
                                              std::ostream& os,
                                              const ProofLetMap& map)
{
  Assert(term.getType().isBoolean() or term.getType().isPredicate());
  bool wrapWithBoolToPred = term.getType().isBoolean() and printsAsBool(term);
  if (wrapWithBoolToPred)
  {
    os << "(p_app ";
  }
  printBoundTerm(term, os, map);
  if (wrapWithBoolToPred)
  {
    os << ")";
  }
}

void LFSCTheoryProofEngine::printCoreTerm(Expr term,
                                          std::ostream& os,
                                          const ProofLetMap& map,
                                          TypeNode expectedType)
{
  if (term.isVariable()) {
    os << ProofManager::sanitize(term);
    return;
  }

  Kind k = term.getKind();

  switch(k) {
  case kind::ITE: {
    TypeNode armType = expectedType.isNull()
                           ? TypeNode::fromType(term.getType())
                           : expectedType;
    bool useFormulaType = term.getType().isBoolean();
    Assert(term[1].getType().isSubtypeOf(term.getType()));
    Assert(term[2].getType().isSubtypeOf(term.getType()));
    os << (useFormulaType ? "(ifte " : "(ite _ ");

    printBoundFormula(term[0], os, map);
    os << " ";
    if (useFormulaType)
    {
      printBoundFormula(term[1], os, map);
    }
    else
    {
      printBoundTerm(term[1], os, map, armType);
    }
    os << " ";
    if (useFormulaType)
    {
      printBoundFormula(term[2], os, map);
    }
    else
    {
      printBoundTerm(term[2], os, map, armType);
    }
    os << ")";
    return;
  }

  case kind::EQUAL: {
    bool booleanCase = term[0].getType().isBoolean();
    TypeNode armType = equalityType(term[0], term[1]);

    os << "(";
    if (booleanCase) {
      os << "iff ";
    } else {
      os << "= ";
      printSort(term[0].getType(), os);
      os << " ";
    }

    if (booleanCase && printsAsBool(term[0])) os << "(p_app ";
    printBoundTerm(term[0], os, map, armType);
    if (booleanCase && printsAsBool(term[0])) os << ")";

    os << " ";

    if (booleanCase && printsAsBool(term[1])) os << "(p_app ";
    printBoundTerm(term[1], os, map, armType);
    if (booleanCase && printsAsBool(term[1])) os << ") ";
    os << ")";

    return;
  }

  case kind::DISTINCT:
  {
    // Distinct nodes can have any number of chidlren.
    Assert(term.getNumChildren() >= 2);
    TypeNode armType = equalityType(term[0], term[1]);

    if (term.getNumChildren() == 2) {
      os << "(not (= ";
      printSort(term[0].getType(), os);
      os << " ";
      printBoundTerm(term[0], os, map, armType);
      os << " ";
      printBoundTerm(term[1], os, map, armType);
      os << "))";
    } else {
      unsigned numOfPairs = term.getNumChildren() * (term.getNumChildren() - 1) / 2;
      for (unsigned i = 1; i < numOfPairs; ++i) {
        os << "(and ";
      }

      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        for (unsigned j = i + 1; j < term.getNumChildren(); ++j) {
          armType = equalityType(term[i], term[j]);
          if ((i != 0) || (j != 1)) {
            os << "(not (= ";
            printSort(term[0].getType(), os);
            os << " ";
            printBoundTerm(term[i], os, map, armType);
            os << " ";
            printBoundTerm(term[j], os, map, armType);
            os << ")))";
          } else {
            os << "(not (= ";
            printSort(term[0].getType(), os);
            os << " ";
            printBoundTerm(term[0], os, map, armType);
            os << " ";
            printBoundTerm(term[1], os, map, armType);
            os << "))";
          }
        }
      }
    }
    return;
  }

  default: Unhandled() << k;
  }
}

void TheoryProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                        std::ostream& os,
                                        std::ostream& paren,
                                        const ProofLetMap& map) {
  // Default method for replaying proofs: assert (negated) literals back to a fresh copy of the theory
  Assert(d_theory != NULL);

  context::UserContext fakeContext;
  ProofOutputChannel oc;
  theory::Valuation v(NULL);
  //make new copy of theory
  theory::Theory* th;
  Trace("pf::tp") << ";; Print theory lemma proof, theory id = " << d_theory->getId() << std::endl;

  if (d_theory->getId()==theory::THEORY_UF) {
    th = new theory::uf::TheoryUF(&fakeContext,
                                  &fakeContext,
                                  oc,
                                  v,
                                  ProofManager::currentPM()->getLogicInfo(),
                                  nullptr,
                                  "replay::");
  } else if (d_theory->getId()==theory::THEORY_ARRAYS) {
    th = new theory::arrays::TheoryArrays(
        &fakeContext,
        &fakeContext,
        oc,
        v,
        ProofManager::currentPM()->getLogicInfo(),
        nullptr,
        "replay::");
  } else if (d_theory->getId() == theory::THEORY_ARITH) {
    Trace("theory-proof-debug") << "Arith proofs currently not supported. Use 'trust'" << std::endl;
    os << " (clausify_false trust)";
    return;
  } else {
    InternalError() << "can't generate theory-proof for "
                    << ProofManager::currentPM()->getLogic();
  }
  // must perform initialization on the theory
  if (th != nullptr)
  {
    // finish init, standalone version
    th->finishInitStandalone();
  }

  Debug("pf::tp") << "TheoryProof::printTheoryLemmaProof - calling th->ProduceProofs()" << std::endl;
  th->produceProofs();
  Debug("pf::tp") << "TheoryProof::printTheoryLemmaProof - th->ProduceProofs() DONE" << std::endl;

  MyPreRegisterVisitor preRegVisitor(th);
  for (unsigned i=0; i<lemma.size(); i++) {
    Node strippedLit = (lemma[i].getKind() == kind::NOT) ? lemma[i][0] : lemma[i];
    if (strippedLit.getKind() == kind::EQUAL ||
        d_theory->getId() == theory::Theory::theoryOf(strippedLit)) {
      Node lit = Node::fromExpr( lemma[i] ).negate();
      Trace("pf::tp") << "; preregistering and asserting " << lit << std::endl;
      NodeVisitor<MyPreRegisterVisitor>::run(preRegVisitor, lit);
      th->assertFact(lit, false);
    }
  }

  Debug("pf::tp") << "TheoryProof::printTheoryLemmaProof - calling th->check()" << std::endl;
  th->check(theory::Theory::EFFORT_FULL);
  Debug("pf::tp") << "TheoryProof::printTheoryLemmaProof - th->check() DONE" << std::endl;

  if(!oc.hasConflict()) {
    Trace("pf::tp") << "; conflict is null" << std::endl;
    Node lastLemma  = oc.getLastLemma();
    Assert(!lastLemma.isNull());
    Trace("pf::tp") << "; ++ but got lemma: " << lastLemma << std::endl;

    if (lastLemma.getKind() == kind::OR) {
      Debug("pf::tp") << "OR lemma. Negating each child separately" << std::endl;
      for (unsigned i = 0; i < lastLemma.getNumChildren(); ++i) {
        if (lastLemma[i].getKind() == kind::NOT) {
          Trace("pf::tp") << ";     asserting fact: " << lastLemma[i][0] << std::endl;
          th->assertFact(lastLemma[i][0], false);
        }
        else {
          Trace("pf::tp") << ";     asserting fact: " << lastLemma[i].notNode() << std::endl;
          th->assertFact(lastLemma[i].notNode(), false);
        }
      }
    } else {
      Unreachable();

      Assert(oc.getLastLemma().getKind() == kind::NOT);
      Debug("pf::tp") << "NOT lemma" << std::endl;
      Trace("pf::tp") << ";     asserting fact: " << oc.getLastLemma()[0]
                      << std::endl;
      th->assertFact(oc.getLastLemma()[0], false);
    }

    // Trace("pf::tp") << "; ++ but got lemma: " << oc.d_lemma << std::endl;
    // Trace("pf::tp") << "; asserting " << oc.d_lemma[1].negate() << std::endl;
    // th->assertFact(oc.d_lemma[1].negate(), false);

    //
    th->check(theory::Theory::EFFORT_FULL);
  } else {
    Debug("pf::tp") << "Calling   oc.d_proof->toStream(os)" << std::endl;
    oc.getConflictProof().toStream(os, map);
    Debug("pf::tp") << "Calling   oc.d_proof->toStream(os) -- DONE!" << std::endl;
  }

  Debug("pf::tp") << "About to delete the theory solver used for proving the lemma... " << std::endl;
  delete th;
  Debug("pf::tp") << "About to delete the theory solver used for proving the lemma: DONE! " << std::endl;
}

bool TheoryProofEngine::supportedTheory(theory::TheoryId id) {
  return (id == theory::THEORY_ARRAYS ||
          id == theory::THEORY_ARITH ||
          id == theory::THEORY_BV ||
          id == theory::THEORY_UF ||
          id == theory::THEORY_BOOL);
}

bool TheoryProofEngine::printsAsBool(const Node &n) {
  if (!n.getType().isBoolean()) {
    return false;
  }

  theory::TheoryId theory_id = theory::Theory::theoryOf(n);
  return getTheoryProof(theory_id)->printsAsBool(n);
}

BooleanProof::BooleanProof(TheoryProofEngine* proofEngine)
  : TheoryProof(NULL, proofEngine)
{}

void BooleanProof::registerTerm(Expr term) {
  Assert(term.getType().isBoolean());

  if (term.isVariable() && d_declarations.find(term) == d_declarations.end()) {
    d_declarations.insert(term);
    return;
  }
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    d_proofEngine->registerTerm(term[i]);
  }
}

theory::TheoryId BooleanProof::getTheoryId() { return theory::THEORY_BOOL; }
void LFSCBooleanProof::printConstantDisequalityProof(std::ostream& os, Expr c1, Expr c2, const ProofLetMap &globalLetMap) {
  Node falseNode = NodeManager::currentNM()->mkConst(false);
  Node trueNode = NodeManager::currentNM()->mkConst(true);

  Assert(c1 == falseNode.toExpr() || c1 == trueNode.toExpr());
  Assert(c2 == falseNode.toExpr() || c2 == trueNode.toExpr());
  Assert(c1 != c2);

  if (c1 == trueNode.toExpr())
    os << "t_t_neq_f";
  else
    os << "(negsymm _ _ _ t_t_neq_f)";
}

void LFSCBooleanProof::printOwnedTermAsType(Expr term,
                                            std::ostream& os,
                                            const ProofLetMap& map,
                                            TypeNode expectedType)
{
  Assert(term.getType().isBoolean());
  if (term.isVariable()) {
    os << ProofManager::sanitize(term);
    return;
  }

  Kind k = term.getKind();
  switch(k) {
  case kind::OR:
  case kind::AND:
    if (options::lfscLetification() && term.getNumChildren() > 2) {
      // If letification is on, the entire term is probably a let expression.
      // However, we need to transform it from (and a b c) into (and a (and b c)) form first.
      Node currentExpression = term[term.getNumChildren() - 1];
      for (int i = term.getNumChildren() - 2; i >= 0; --i) {
        NodeBuilder<> builder(k);
        builder << term[i];
        builder << currentExpression.toExpr();
        currentExpression = builder;
      }

      // The let map should already have the current expression.
      ProofLetMap::const_iterator it = map.find(currentExpression.toExpr());
      if (it != map.end()) {
        unsigned id = it->second.id;
        unsigned count = it->second.count;

        if (count > LET_COUNT) {
          os << "let" << id;
          break;
        }
      }
    }

    // If letification is off or there were 2 children, same treatment as the other cases.
    CVC4_FALLTHROUGH;
  case kind::XOR:
  case kind::IMPLIES:
  case kind::NOT:
    // print the Boolean operators
    os << "(" << utils::toLFSCKind(k);
    if(term.getNumChildren() > 2) {
      // LFSC doesn't allow declarations with variable numbers of
      // arguments, so we have to flatten these N-ary versions.
      std::ostringstream paren;
      os << " ";
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {

        if (printsAsBool(term[i])) os << "(p_app ";
        d_proofEngine->printBoundTerm(term[i], os, map);
        if (printsAsBool(term[i])) os << ")";

        os << " ";
        if(i < term.getNumChildren() - 2) {
          os << "(" << utils::toLFSCKind(k) << " ";
          paren << ")";
        }
      }
      os << paren.str() << ")";
    } else {
      // this is for binary and unary operators
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        os << " ";
        if (printsAsBool(term[i])) os << "(p_app ";
        d_proofEngine->printBoundTerm(term[i], os, map);
        if (printsAsBool(term[i])) os << ")";
      }
      os << ")";
    }
    return;

  case kind::CONST_BOOLEAN:
    os << (term.getConst<bool>() ? "true" : "false");
    return;

  default: Unhandled() << k;
  }
}

void LFSCBooleanProof::printOwnedSort(Type type, std::ostream& os) {
  Assert(type.isBoolean());
  os << "Bool";
}

void LFSCBooleanProof::printSortDeclarations(std::ostream& os, std::ostream& paren) {
  // Nothing to do here at this point.
}

void LFSCBooleanProof::printTermDeclarations(std::ostream& os, std::ostream& paren) {
  for (ExprSet::const_iterator it = d_declarations.begin(); it != d_declarations.end(); ++it) {
    Expr term = *it;

    os << "(% " << ProofManager::sanitize(term) << " (term ";
    printSort(term.getType(), os);
    os <<")\n";
    paren <<")";
  }
}

void LFSCBooleanProof::printDeferredDeclarations(std::ostream& os, std::ostream& paren) {
  // Nothing to do here at this point.
}

void LFSCBooleanProof::printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) {
  // Nothing to do here at this point.
}

void LFSCBooleanProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                             std::ostream& os,
                                             std::ostream& paren,
                                             const ProofLetMap& map) {
  Unreachable() << "No boolean lemmas yet!";
}

bool LFSCBooleanProof::printsAsBool(const Node &n)
{
  Kind k = n.getKind();
  switch (k) {
  case kind::BOOLEAN_TERM_VARIABLE:
  case kind::VARIABLE:
    return true;

  default:
    return false;
  }
}

void TheoryProof::printConstantDisequalityProof(std::ostream& os, Expr c1, Expr c2, const ProofLetMap &globalLetMap) {
  // By default, we just print a trust statement. Specific theories can implement
  // better proofs.

  os << "(trust_f (not (= _ ";
  d_proofEngine->printBoundTerm(c1, os, globalLetMap);
  os << " ";
  d_proofEngine->printBoundTerm(c2, os, globalLetMap);
  os << ")))";
}

void TheoryProof::printRewriteProof(std::ostream& os, const Node &n1, const Node &n2) {
  // This is the default for a rewrite proof: just a trust statement.
  ProofLetMap emptyMap;
  os << "(trust_f (iff ";
  d_proofEngine->printBoundTerm(n1.toExpr(), os, emptyMap);
  os << " ";
  d_proofEngine->printBoundTerm(n2.toExpr(), os, emptyMap);
  os << "))";
}

void TheoryProof::printOwnedTerm(Expr term,
                                 std::ostream& os,
                                 const ProofLetMap& map,
                                 TypeNode expectedType)
{
  this->printOwnedTermAsType(term, os, map, expectedType);
}

TypeNode TheoryProof::equalityType(const Expr& left, const Expr& right)
{
  Assert(left.getType() == right.getType())
    << "TheoryProof::equalityType(" << left << ", " << right << "):" << std::endl
    << "types disagree:" << std::endl
    << "\tleft: " << left.getType() << std::endl
    << "\tright:" << right.getType();
  return TypeNode::fromType(left.getType());
}

bool TheoryProof::match(TNode n1, TNode n2)
{
  theory::TheoryId theoryId = this->getTheoryId();
  ProofManager* pm = ProofManager::currentPM();
  bool ufProof = (theoryId == theory::THEORY_UF);
  Debug(ufProof ? "pf::uf" : "mgd") << "match " << n1 << " " << n2 << std::endl;
  if (pm->hasOp(n1))
  {
    n1 = pm->lookupOp(n1);
  }
  if (pm->hasOp(n2))
  {
    n2 = pm->lookupOp(n2);
  }
  Debug(ufProof ? "pf::uf" : "mgd") << "+ match " << n1 << " " << n2
                                    << std::endl;
  if (!ufProof)
  {
    Debug("pf::array") << "+ match: step 1" << std::endl;
  }
  if (n1 == n2)
  {
    return true;
  }

  if (n1.getType().isFunction() && n2.hasOperator())
  {
    if (pm->hasOp(n2.getOperator()))
    {
      return n1 == pm->lookupOp(n2.getOperator());
    }
    else
    {
      return n1 == n2.getOperator();
    }
  }

  if (n2.getType().isFunction() && n1.hasOperator())
  {
    if (pm->hasOp(n1.getOperator()))
    {
      return n2 == pm->lookupOp(n1.getOperator());
    }
    else
    {
      return n2 == n1.getOperator();
    }
  }

  if (n1.hasOperator() && n2.hasOperator()
      && n1.getOperator() != n2.getOperator())
  {
    if (ufProof
        || !((n1.getKind() == kind::SELECT
              && n2.getKind() == kind::PARTIAL_SELECT_0)
             || (n1.getKind() == kind::SELECT
                 && n2.getKind() == kind::PARTIAL_SELECT_1)
             || (n1.getKind() == kind::PARTIAL_SELECT_1
                 && n2.getKind() == kind::SELECT)
             || (n1.getKind() == kind::PARTIAL_SELECT_1
                 && n2.getKind() == kind::PARTIAL_SELECT_0)
             || (n1.getKind() == kind::PARTIAL_SELECT_0
                 && n2.getKind() == kind::SELECT)
             || (n1.getKind() == kind::PARTIAL_SELECT_0
                 && n2.getKind() == kind::PARTIAL_SELECT_1)))
    {
      return false;
    }
  }

  for (size_t i = 0; i < n1.getNumChildren() && i < n2.getNumChildren(); ++i)
  {
    if (n1[i] != n2[i])
    {
      return false;
    }
  }

  return true;
}

int TheoryProof::assertAndPrint(
    const theory::eq::EqProof& pf,
    const ProofLetMap& map,
    std::shared_ptr<theory::eq::EqProof> subTrans,
    theory::eq::EqProof::PrettyPrinter* pPrettyPrinter)
{
  theory::TheoryId theoryId = getTheoryId();
  int neg = -1;
  Assert(theoryId == theory::THEORY_UF || theoryId == theory::THEORY_ARRAYS);
  bool ufProof = (theoryId == theory::THEORY_UF);
  std::string theoryName = theory::getStatsPrefix(theoryId);
  pf.debug_print(("pf::" + theoryName).c_str(), 0, pPrettyPrinter);
  Debug("pf::" + theoryName) << std::endl;

  Assert(pf.d_id == theory::eq::MERGED_THROUGH_TRANS);
  Assert(!pf.d_node.isNull());
  Assert(pf.d_children.size() >= 2);

  subTrans->d_id = theory::eq::MERGED_THROUGH_TRANS;
  subTrans->d_node = pf.d_node;

  size_t i = 0;
  while (i < pf.d_children.size())
  {
    // special treatment for uf and not for array
    if (ufProof
        || pf.d_children[i]->d_id != theory::eq::MERGED_THROUGH_CONGRUENCE)
    {
      pf.d_children[i]->d_node = simplifyBooleanNode(pf.d_children[i]->d_node);
    }

    // Look for the negative clause, with which we will form a contradiction.
    if (!pf.d_children[i]->d_node.isNull()
        && pf.d_children[i]->d_node.getKind() == kind::NOT)
    {
      Assert(neg < 0);
      (neg) = i;
      ++i;
    }

    // Handle congruence closures over equalities.
    else if (pf.d_children[i]->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE
             && pf.d_children[i]->d_node.isNull())
    {
      Debug("pf::" + theoryName) << "Handling congruence over equalities"
                                 << std::endl;

      // Gather the sequence of consecutive congruence closures.
      std::vector<std::shared_ptr<const theory::eq::EqProof>>
          congruenceClosures;
      unsigned count;
      Debug("pf::" + theoryName) << "Collecting congruence sequence"
                                 << std::endl;
      for (count = 0; i + count < pf.d_children.size()
                      && pf.d_children[i + count]->d_id
                             == theory::eq::MERGED_THROUGH_CONGRUENCE
                      && pf.d_children[i + count]->d_node.isNull();
           ++count)
      {
        Debug("pf::" + theoryName) << "Found a congruence: " << std::endl;
        pf.d_children[i + count]->debug_print(
            ("pf::" + theoryName).c_str(), 0, pPrettyPrinter);
        congruenceClosures.push_back(pf.d_children[i + count]);
      }

      Debug("pf::" + theoryName)
          << "Total number of congruences found: " << congruenceClosures.size()
          << std::endl;

      // Determine if the "target" of the congruence sequence appears right
      // before or right after the sequence.
      bool targetAppearsBefore = true;
      bool targetAppearsAfter = true;

      if ((i == 0) || (i == 1 && neg == 0))
      {
        Debug("pf::" + theoryName) << "Target does not appear before"
                                   << std::endl;
        targetAppearsBefore = false;
      }

      if ((i + count >= pf.d_children.size())
          || (!pf.d_children[i + count]->d_node.isNull()
              && pf.d_children[i + count]->d_node.getKind() == kind::NOT))
      {
        Debug("pf::" + theoryName) << "Target does not appear after"
                                   << std::endl;
        targetAppearsAfter = false;
      }

      // Flow changes between uf and array
      if (ufProof)
      {
        // Assert that we have precisely at least one possible clause.
        Assert(targetAppearsBefore || targetAppearsAfter);

        // If both are valid, assume the one after the sequence is correct
        if (targetAppearsAfter && targetAppearsBefore)
        {
          targetAppearsBefore = false;
        }
      }
      else
      {  // not a uf proof
        // Assert that we have precisely one target clause.
        Assert(targetAppearsBefore != targetAppearsAfter);
      }

      // Begin breaking up the congruences and ordering the equalities
      // correctly.
      std::vector<std::shared_ptr<theory::eq::EqProof>> orderedEqualities;

      // Insert target clause first.
      if (targetAppearsBefore)
      {
        orderedEqualities.push_back(pf.d_children[i - 1]);
        // The target has already been added to subTrans; remove it.
        subTrans->d_children.pop_back();
      }
      else
      {
        orderedEqualities.push_back(pf.d_children[i + count]);
      }

      // Start with the congruence closure closest to the target clause, and
      // work our way back/forward.
      if (targetAppearsBefore)
      {
        for (unsigned j = 0; j < count; ++j)
        {
          if (pf.d_children[i + j]->d_children[0]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(orderedEqualities.begin(),
                                     pf.d_children[i + j]->d_children[0]);
          if (pf.d_children[i + j]->d_children[1]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(orderedEqualities.end(),
                                     pf.d_children[i + j]->d_children[1]);
        }
      }
      else
      {
        for (unsigned j = 0; j < count; ++j)
        {
          if (pf.d_children[i + count - 1 - j]->d_children[0]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(
                orderedEqualities.begin(),
                pf.d_children[i + count - 1 - j]->d_children[0]);
          if (pf.d_children[i + count - 1 - j]->d_children[1]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(
                orderedEqualities.end(),
                pf.d_children[i + count - 1 - j]->d_children[1]);
        }
      }

      // Copy the result into the main transitivity proof.
      subTrans->d_children.insert(subTrans->d_children.end(),
                                  orderedEqualities.begin(),
                                  orderedEqualities.end());

      // Increase i to skip over the children that have been processed.
      i += count;
      if (targetAppearsAfter)
      {
        ++i;
      }
    }

    // Else, just copy the child proof as is
    else
    {
      subTrans->d_children.push_back(pf.d_children[i]);
      ++i;
    }
  }

  bool disequalityFound = (neg >= 0);
  if (!disequalityFound)
  {
    Debug("pf::" + theoryName)
        << "A disequality was NOT found. UNSAT due to merged constants"
        << std::endl;
    Debug("pf::" + theoryName) << "Proof for: " << pf.d_node << std::endl;
    Assert(pf.d_node.getKind() == kind::EQUAL);
    Assert(pf.d_node.getNumChildren() == 2);
    Assert(pf.d_node[0].isConst() && pf.d_node[1].isConst());
  }
  return neg;
}

std::pair<Node, Node> TheoryProof::identicalEqualitiesPrinterHelper(
    bool evenLengthSequence,
    bool sequenceOver,
    const theory::eq::EqProof& pf,
    const ProofLetMap& map,
    const std::string subproofStr,
    std::stringstream* outStream,
    Node n,
    Node nodeAfterEqualitySequence)
{
  theory::TheoryId theoryId = getTheoryId();
  Assert(theoryId == theory::THEORY_UF || theoryId == theory::THEORY_ARRAYS);
  bool ufProof = (theoryId == theory::THEORY_UF);
  std::string theoryName = theory::getStatsPrefix(theoryId);
  if (evenLengthSequence)
  {
    // If the length is even, we need to apply transitivity for the "correct"
    // hand of the equality.

    Debug("pf::" + theoryName) << "Equality sequence of even length"
                               << std::endl;
    Debug("pf::" + theoryName) << "n1 is: " << n << std::endl;
    Debug("pf::" + theoryName) << "pf-d_node is: " << pf.d_node << std::endl;
    Debug("pf::" + theoryName) << "Next node is: " << nodeAfterEqualitySequence
                               << std::endl;

    (*outStream) << "(trans _ _ _ _ ";

    // If the sequence is at the very end of the transitivity proof, use
    // pf.d_node to guide us.
    if (!sequenceOver)
    {
      if (match(n[0], pf.d_node[0]))
      {
        n = n[0].eqNode(n[0]);
        (*outStream) << subproofStr << " (symm _ _ _ " << subproofStr << ")";
      }
      else if (match(n[1], pf.d_node[1]))
      {
        n = n[1].eqNode(n[1]);
        (*outStream) << " (symm _ _ _ " << subproofStr << ")" << subproofStr;
      }
      else
      {
        Debug("pf::" + theoryName) << "Error: identical equalities over, but "
                                      "hands don't match what we're proving."
                                   << std::endl;
        Assert(false);
      }
    }
    else
    {
      // We have a "next node". Use it to guide us.
      if (!ufProof && nodeAfterEqualitySequence.getKind() == kind::NOT)
      {
        nodeAfterEqualitySequence = nodeAfterEqualitySequence[0];
      }

      Assert(nodeAfterEqualitySequence.getKind() == kind::EQUAL);

      if ((n[0] == nodeAfterEqualitySequence[0])
          || (n[0] == nodeAfterEqualitySequence[1]))
      {
        // Eliminate n[1]
        (*outStream) << subproofStr << " (symm _ _ _ " << subproofStr << ")";
        n = n[0].eqNode(n[0]);
      }
      else if ((n[1] == nodeAfterEqualitySequence[0])
               || (n[1] == nodeAfterEqualitySequence[1]))
      {
        // Eliminate n[0]
        (*outStream) << " (symm _ _ _ " << subproofStr << ")" << subproofStr;
        n = n[1].eqNode(n[1]);
      }
      else
      {
        Debug("pf::" + theoryName) << "Error: even length sequence, but I "
                                      "don't know which hand to keep!"
                                   << std::endl;
        Assert(false);
      }
    }

    (*outStream) << ")";
  }
  else
  {
    Debug("pf::" + theoryName) << "Equality sequence length is odd!"
                               << std::endl;
    (*outStream).str(subproofStr);
  }

  Debug("pf::" + theoryName) << "Have proven: " << n << std::endl;
  return std::make_pair<Node&, Node&>(n, nodeAfterEqualitySequence);
}

} /* namespace CVC4 */
