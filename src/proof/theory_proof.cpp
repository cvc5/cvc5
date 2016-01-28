/*********************                                                        */
/*! \file theory_proof.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "base/cvc4_assert.h"
#include "context/context.h"
#include "options/bv_options.h"
#include "proof/array_proof.h"
#include "proof/bitvector_proof.h"
#include "proof/cnf_proof.h"
#include "proof/cnf_proof.h"
#include "proof/proof_manager.h"
#include "proof/proof_utils.h"
#include "proof/sat_proof.h"
#include "proof/theory_proof.h"
#include "proof/uf_proof.h"
#include "prop/sat_solver_types.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt_util/node_visitor.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"
#include "theory/output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/proof.h"


namespace CVC4 {

unsigned CVC4::LetCount::counter = 0;
static unsigned LET_COUNT = 1;

//for proof replay
class ProofOutputChannel : public theory::OutputChannel {
public:
  Node d_conflict;
  Proof* d_proof;
  Node d_lemma;

  ProofOutputChannel() : d_conflict(), d_proof(NULL) {}

  void conflict(TNode n, Proof* pf) throw() {
    Trace("theory-proof-debug") << "; CONFLICT: " << n << std::endl;
    Assert(d_conflict.isNull());
    Assert(!n.isNull());
    d_conflict = n;
    Assert(pf != NULL);
    d_proof = pf;
  }
  bool propagate(TNode x) throw() {
    Trace("theory-proof-debug") << "got a propagation: " << x << std::endl;
    return true;
  }
  theory::LemmaStatus lemma(TNode n, ProofRule rule, bool, bool, bool) throw() {
    Trace("theory-proof-debug") << "new lemma: " << n << std::endl;
    d_lemma = n;
    return theory::LemmaStatus(TNode::null(), 0);
  }
  theory::LemmaStatus splitLemma(TNode, bool) throw() {
    AlwaysAssert(false);
    return theory::LemmaStatus(TNode::null(), 0);
  }
  void requirePhase(TNode n, bool b) throw() {
    Trace("theory-proof-debug") << "requirePhase " << n << " " << b << std::endl;
  }
  bool flipDecision() throw() {
    AlwaysAssert(false);
    return false;
  }
  void setIncomplete() throw() {
    AlwaysAssert(false);
  }
};/* class ProofOutputChannel */

//for proof replay
class MyPreRegisterVisitor { 
  theory::Theory* d_theory;
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> d_visited;
public:
  typedef void return_type;
  MyPreRegisterVisitor(theory::Theory* theory)
  : d_theory(theory)
  , d_visited()
  {}
  bool alreadyVisited(TNode current, TNode parent) { return d_visited.find(current) != d_visited.end(); }
  void visit(TNode current, TNode parent) {
    if(theory::Theory::theoryOf(current) == d_theory->getId()) {
      //Trace("theory-proof-debug") << "preregister " << current << std::endl;
      d_theory->preRegisterTerm(current);
      d_visited.insert(current);
    }
  }
  void start(TNode node) { }
  void done(TNode node) { }
}; /* class MyPreRegisterVisitor */

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
  if( th ){
    theory::TheoryId id = th->getId();
    if(d_theoryProofTable.find(id) == d_theoryProofTable.end()) {

      Trace("theory-proof-debug") << "; register theory " << id << std::endl;

      if (id == theory::THEORY_UF) {
        d_theoryProofTable[id] = new LFSCUFProof((theory::uf::TheoryUF*)th, this);
        return;
      }

      if (id == theory::THEORY_BV) {
        BitVectorProof * bvp = new LFSCBitVectorProof((theory::bv::TheoryBV*)th, this);
        d_theoryProofTable[id] = bvp;
        ((theory::bv::TheoryBV*)th)->setProofLog( bvp );
        return;
      }
      if (id == theory::THEORY_ARRAY) {
        d_theoryProofTable[id] = new LFSCArrayProof((theory::arrays::TheoryArrays*)th, this);
        return;
      }
    // TODO other theories
    }
  }
}

TheoryProof* TheoryProofEngine::getTheoryProof(theory::TheoryId id) {
  Assert (d_theoryProofTable.find(id) != d_theoryProofTable.end());
  return d_theoryProofTable[id];
}

void TheoryProofEngine::registerTerm(Expr term) {
  if (d_registrationCache.count(term)) {
    return;
  }

  theory::TheoryId theory_id = theory::Theory::theoryOf(term);

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
      
  getTheoryProof(theory_id)->registerTerm(term);
  d_registrationCache.insert(term);
}

theory::TheoryId TheoryProofEngine::getTheoryForLemma(ClauseId id) {
  // TODO: now CNF proof has a map from formula to proof rule
  // that should be checked to figure out what theory is responsible for this
  ProofManager* pm = ProofManager::currentPM();

  if (pm->getLogic() == "QF_UF") return theory::THEORY_UF;
  if (pm->getLogic() == "QF_BV") return theory::THEORY_BV;
  if (pm->getLogic() == "ALL_SUPPORTED") return theory::THEORY_BV;
  Unreachable();
}

void LFSCTheoryProofEngine::bind(Expr term, LetMap& map, Bindings& let_order) {
  LetMap::iterator it = map.find(term);
  if (it != map.end()) {
    LetCount& count = it->second;
    count.increment();
    return;
  }
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    bind(term[i], map, let_order);
  }
  unsigned new_id = LetCount::newId();
  map[term] = LetCount(new_id);
  let_order.push_back(LetOrderElement(term, new_id));
}

void LFSCTheoryProofEngine::printLetTerm(Expr term, std::ostream& os) {
  LetMap map;
  Bindings let_order;
  bind(term, map, let_order);
  std::ostringstream paren;
  for (unsigned i = 0; i < let_order.size(); ++i) {
    Expr current_expr = let_order[i].expr;
    unsigned let_id = let_order[i].id;
    LetMap::const_iterator it = map.find(current_expr);
    Assert (it != map.end());
    unsigned let_count = it->second.count;
    Assert(let_count);
    // skip terms that only appear once
    if (let_count <= LET_COUNT) {
      continue;
    }

    os << "(@ let"<<let_id << " ";
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
    os << " let"<< last_let_id;
  }
  os << paren.str();
}


void LFSCTheoryProofEngine::printTheoryTerm(Expr term, std::ostream& os, const LetMap& map) {
  theory::TheoryId theory_id = theory::Theory::theoryOf(term);
  // boolean terms and ITEs are special because they
  // are common to all theories
  if (theory_id == theory::THEORY_BUILTIN ||
      term.getKind() == kind::ITE ||
      term.getKind() == kind::EQUAL) {
    printCoreTerm(term, os, map);
    return;
  }
  // dispatch to proper theory
  getTheoryProof(theory_id)->printTerm(term, os, map);
}

void LFSCTheoryProofEngine::printSort(Type type, std::ostream& os) {
  if (type.isSort()) {
    getTheoryProof(theory::THEORY_UF)->printSort(type, os);
    return;
  }
  if (type.isBitVector()) {
    getTheoryProof(theory::THEORY_BV)->printSort(type, os);
    return;
  }

  if (type.isArray()) {
    getTheoryProof(theory::THEORY_ARRAY)->printSort(type, os);
    return;
  }
  Unreachable();
}

void LFSCTheoryProofEngine::printAssertions(std::ostream& os, std::ostream& paren) {
  unsigned counter = 0;
  ProofManager::assertions_iterator it = ProofManager::currentPM()->begin_assertions();
  ProofManager::assertions_iterator end = ProofManager::currentPM()->end_assertions();

  // collect declarations first
  for(; it != end; ++it) {
    registerTerm(*it);
  }
  printDeclarations(os, paren);

  it = ProofManager::currentPM()->begin_assertions();
  for (; it != end; ++it) {
    // FIXME: merge this with counter
    os << "(% A" << counter++ << " (th_holds ";
    printLetTerm(*it,  os);
    os << ")\n";
    paren << ")";
  }
  //store map between assertion and counter
  // ProofManager::currentPM()->setAssertion( *it );
}

void LFSCTheoryProofEngine::printDeclarations(std::ostream& os, std::ostream& paren) {
  TheoryProofTable::const_iterator it = d_theoryProofTable.begin();
  TheoryProofTable::const_iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    it->second->printDeclarations(os, paren);
  }
}

void LFSCTheoryProofEngine::printTheoryLemmas(const IdToSatClause& lemmas,
                                              std::ostream& os,
                                              std::ostream& paren) {
  os << " ;; Theory Lemmas \n";
  ProofManager* pm = ProofManager::currentPM();
  IdToSatClause::const_iterator it = lemmas.begin();
  IdToSatClause::const_iterator end = lemmas.end();

  // BitVector theory is special case: must know all
  // conflicts needed ahead of time for resolution
  // proof lemmas
  std::vector<Expr> bv_lemmas;
  for (; it != end; ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;

    theory::TheoryId theory_id = getTheoryForLemma(id);
    if (theory_id != theory::THEORY_BV) continue;

    std::vector<Expr> conflict;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Expr atom = pm->getCnfProof()->getAtom(lit.getSatVariable()).toExpr();
      if (atom.isConst()) {
        Assert (atom == utils::mkTrue() ||
                (atom == utils::mkFalse() && lit.isNegated()));
        continue;
      }
      Expr expr_lit = lit.isNegated() ? atom.notExpr() : atom;
      conflict.push_back(expr_lit);
    }
    bv_lemmas.push_back(utils::mkSortedExpr(kind::OR, conflict));
  }
  // FIXME: ugly, move into bit-vector proof by adding lemma
  // queue inside each theory_proof
  BitVectorProof* bv = ProofManager::getBitVectorProof();
  bv->finalizeConflicts(bv_lemmas);

  bv->printResolutionProof(os, paren);

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    Assert (lemmas.size() == 1);
    // nothing more to do (no combination with eager so far)
    return;
  }

  it = lemmas.begin();

  for (; it != end; ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;
    // printing clause as it appears in resolution proof
    os << "(satlem _ _ ";
    std::ostringstream clause_paren;
    pm->getCnfProof()->printClause(*clause, os, clause_paren);

    std::vector<Expr> clause_expr;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Expr atom = pm->getCnfProof()->getAtom(lit.getSatVariable()).toExpr();
      if (atom.isConst()) {
        Assert (atom == utils::mkTrue());
        continue;
      }
      Expr expr_lit = lit.isNegated() ? atom.notExpr(): atom;
      clause_expr.push_back(expr_lit);
    }

    // query appropriate theory for proof of clause
    theory::TheoryId theory_id = getTheoryForLemma(id);
    Debug("theory-proof-debug") << ";; Get theory lemma from " << theory_id << "..." << std::endl;
    getTheoryProof(theory_id)->printTheoryLemmaProof(clause_expr, os, paren);
    // os << " (clausify_false trust)";
    os << clause_paren.str();
    os << "( \\ " << pm->getLemmaClauseName(id) <<"\n";
    paren << "))";
  }
}

void LFSCTheoryProofEngine::printBoundTerm(Expr term, std::ostream& os, const LetMap& map) {
  LetMap::const_iterator it = map.find(term);
  Assert (it != map.end());
  unsigned id = it->second.id;
  unsigned count = it->second.count;
  if (count > LET_COUNT) {
    os <<"let"<<id;
    return;
  }
  printTheoryTerm(term, os,  map);
}

void LFSCTheoryProofEngine::printCoreTerm(Expr term, std::ostream& os, const LetMap& map) {
  if (term.isVariable()) {
    os << ProofManager::sanitize(term);
    return;
  }

  Kind k = term.getKind();

  switch(k) {
  case kind::ITE:
    os << (term.getType().isBoolean() ? "(ifte ": "(ite _ ");

    printBoundTerm(term[0], os, map);
    os << " ";
    printBoundTerm(term[1], os, map);
    os << " ";
    printBoundTerm(term[2], os, map);
    os << ")";
    return;

  case kind::EQUAL:
    os << "(";
    os << "= ";
    printSort(term[0].getType(), os);
    printBoundTerm(term[0], os, map);
    os << " ";
    printBoundTerm(term[1], os, map);
    os << ")";
    return;

  case kind::DISTINCT:
    // Distinct nodes can have any number of chidlren.
    Assert (term.getNumChildren() >= 2);

    if (term.getNumChildren() == 2) {
      os << "(not (= ";
      printSort(term[0].getType(), os);
      printBoundTerm(term[0], os, map);
      os << " ";
      printBoundTerm(term[1], os, map);
      os << "))";
    } else {
      unsigned numOfPairs = term.getNumChildren() * (term.getNumChildren() - 1) / 2;
      for (unsigned i = 1; i < numOfPairs; ++i) {
        os << "(and ";
      }

      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        for (unsigned j = i + 1; j < term.getNumChildren(); ++j) {
          if ((i != 0) || (j != 1)) {
            os << "(not (= ";
            printSort(term[0].getType(), os);
            printBoundTerm(term[i], os, map);
            os << " ";
            printBoundTerm(term[j], os, map);
            os << ")))";
          } else {
            os << "(not (= ";
            printSort(term[0].getType(), os);
            printBoundTerm(term[0], os, map);
            os << " ";
            printBoundTerm(term[1], os, map);
            os << "))";
          }
        }
      }
    }

    return;

  case kind::CHAIN: {
    // LFSC doesn't allow declarations with variable numbers of
    // arguments, so we have to flatten chained operators, like =.
    Kind op = term.getOperator().getConst<Chain>().getOperator();
    size_t n = term.getNumChildren();
    std::ostringstream paren;
    for(size_t i = 1; i < n; ++i) {
      if(i + 1 < n) {
        os << "(" << utils::toLFSCKind(kind::AND) << " ";
        paren << ")";
      }
      os << "(" << utils::toLFSCKind(op) << " ";
      printBoundTerm(term[i - 1], os, map);
      os << " ";
      printBoundTerm(term[i], os, map);
      os << ")";
      if(i + 1 < n) {
        os << " ";
      }
    }
    os << paren.str();
    return;
  }

  default:
    Unhandled(k);
  }

}

void TheoryProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren) {
  //default method for replaying proofs: assert (negated) literals back to a fresh copy of the theory
  Assert( d_theory!=NULL );
  context::UserContext fakeContext;
  ProofOutputChannel oc;
  theory::Valuation v(NULL);
  //make new copy of theory
  theory::Theory* th;
  Trace("theory-proof-debug") << ";; Print theory lemma proof, theory id = " << d_theory->getId() << std::endl;
  if(d_theory->getId()==theory::THEORY_UF) {
    th = new theory::uf::TheoryUF(&fakeContext, &fakeContext, oc, v,
                                  ProofManager::currentPM()->getLogicInfo(),
                                  "replay::");
  } else if(d_theory->getId()==theory::THEORY_ARRAY) {
    th = new theory::arrays::TheoryArrays(&fakeContext, &fakeContext, oc, v,
                                          ProofManager::currentPM()->getLogicInfo(),
                                          "replay::");
  } else {
    InternalError(std::string("can't generate theory-proof for ") + ProofManager::currentPM()->getLogic());
  }
  th->produceProofs();
  MyPreRegisterVisitor preRegVisitor(th);
  for( unsigned i=0; i<lemma.size(); i++ ){
    Node lit = Node::fromExpr( lemma[i] ).negate();
    Trace("theory-proof-debug") << "; preregistering and asserting " << lit << std::endl;
    NodeVisitor<MyPreRegisterVisitor>::run(preRegVisitor, lit);
    th->assertFact(lit, false);
  }
  th->check(theory::Theory::EFFORT_FULL);
  if(oc.d_conflict.isNull()) {
    Trace("theory-proof-debug") << "; conflict is null" << std::endl;
    Assert(!oc.d_lemma.isNull());
    Trace("theory-proof-debug") << "; ++ but got lemma: " << oc.d_lemma << std::endl;
    Trace("theory-proof-debug") << "; asserting " << oc.d_lemma[1].negate() << std::endl;
    th->assertFact(oc.d_lemma[1].negate(), false);
    th->check(theory::Theory::EFFORT_FULL);
  }
  oc.d_proof->toStream(os);
  delete th;
}

bool TheoryProofEngine::supportedTheory(theory::TheoryId id) {
  return (id == theory::THEORY_ARRAY ||
          id == theory::THEORY_BV ||
          id == theory::THEORY_UF ||
          id == theory::THEORY_BOOL);
}

BooleanProof::BooleanProof(TheoryProofEngine* proofEngine)
  : TheoryProof(NULL, proofEngine)
{}

void BooleanProof::registerTerm(Expr term) {
  Assert (term.getType().isBoolean());

  if (term.isVariable() && d_declarations.find(term) == d_declarations.end()) {
    d_declarations.insert(term);
    return;
  }
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    d_proofEngine->registerTerm(term[i]);
  }
}

void LFSCBooleanProof::printTerm(Expr term, std::ostream& os, const LetMap& map) {
  Assert (term.getType().isBoolean());
  if (term.isVariable()) {
    os << "(p_app " << ProofManager::sanitize(term) <<")";
    return;
  }

  Kind k = term.getKind();
  switch(k) {
  case kind::OR:
  case kind::AND:
  case kind::XOR:
  case kind::IFF:
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
        d_proofEngine->printBoundTerm(term[i], os, map);
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
        d_proofEngine->printBoundTerm(term[i], os, map);
      }
      os << ")";
    }
    return;

  case kind::CONST_BOOLEAN:
    os << (term.getConst<bool>() ? "true" : "false");
    return;

  default:
    Unhandled(k);
  }

}

void LFSCBooleanProof::printSort(Type type, std::ostream& os) {
  Assert (type.isBoolean());
  os << "Bool";
}
void LFSCBooleanProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  for (ExprSet::const_iterator it = d_declarations.begin(); it != d_declarations.end(); ++it) {
    Expr term = *it;

    os << "(% " << ProofManager::sanitize(term) << " (term ";
    printSort(term.getType(), os);
    os <<")\n";
    paren <<")";
  }
}

void LFSCBooleanProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                             std::ostream& os,
                                             std::ostream& paren) {
  Unreachable("No boolean lemmas yet!");
}

} /* namespace CVC4 */
