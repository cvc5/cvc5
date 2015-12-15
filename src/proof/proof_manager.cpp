/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Andrew Reynolds
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

#include "proof/proof_manager.h"

#include "base/cvc4_assert.h"
#include "context/context.h"
#include "proof/cnf_proof.h"
#include "proof/sat_proof.h"
#include "proof/theory_proof.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt_util/node_visitor.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/proof.h"

namespace CVC4 {

std::string append(const std::string& str, uint64_t num) {
  std::ostringstream os;
  os << str << num;
  return os.str();
}

ProofManager::ProofManager(ProofFormat format):
  d_satProof(NULL),
  d_cnfProof(NULL),
  d_theoryProof(NULL),
  d_inputClauses(),
  d_theoryLemmas(),
  d_theoryPropagations(),
  d_inputFormulas(),
  d_inputCoreFormulas(),
  d_outputCoreFormulas(),
  d_nextId(0),
  d_fullProof(NULL),
  d_format(format),
  d_deps(),
  d_assertion_counter(1)
{
}

ProofManager::~ProofManager() {
  delete d_satProof;
  delete d_cnfProof;
  delete d_theoryProof;
  delete d_fullProof;

  for(IdToClause::iterator it = d_inputClauses.begin();
      it != d_inputClauses.end();
      ++it) {
    delete it->second;
  }

  for(OrderedIdToClause::iterator it = d_theoryLemmas.begin();
      it != d_theoryLemmas.end();
      ++it) {
    delete it->second;
  }

  // FIXME: memory leak because there are deleted theory lemmas that
  // were not used in the SatProof
}

ProofManager* ProofManager::currentPM() {
  return smt::currentProofManager();
}

Proof* ProofManager::getProof(SmtEngine* smt) {
  if (currentPM()->d_fullProof != NULL) {
    return currentPM()->d_fullProof;
  }
  Assert (currentPM()->d_format == LFSC);

  currentPM()->d_fullProof = new LFSCProof(smt,
                                           (LFSCSatProof*)getSatProof(),
                                           (LFSCCnfProof*)getCnfProof(),
                                           (LFSCTheoryProof*)getTheoryProof());
  return currentPM()->d_fullProof;
}

SatProof* ProofManager::getSatProof() {
  Assert (currentPM()->d_satProof);
  return currentPM()->d_satProof;
}

CnfProof* ProofManager::getCnfProof() {
  Assert (currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof;
}

TheoryProof* ProofManager::getTheoryProof() {
  //Assert (currentPM()->d_theoryProof);
  return currentPM()->d_theoryProof;
}

void ProofManager::initSatProof(Minisat::Solver* solver) {
  Assert (currentPM()->d_satProof == NULL);
  Assert(currentPM()->d_format == LFSC);
  currentPM()->d_satProof = new LFSCSatProof(solver);
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream) {
  Assert (currentPM()->d_cnfProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_cnfProof = new LFSCCnfProof(cnfStream);
}

void ProofManager::initTheoryProof() {
  Assert (currentPM()->d_theoryProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_theoryProof = new LFSCTheoryProof();
}

std::string ProofManager::getInputClauseName(ClauseId id) { return append("pb", id); }
std::string ProofManager::getLemmaName(ClauseId id) { return append("lem", id); }
std::string ProofManager::getLemmaClauseName(ClauseId id) { return append("lemc", id); }
std::string ProofManager::getLearntClauseName(ClauseId id) { return append("cl", id); }
std::string ProofManager::getVarName(prop::SatVariable var) { return append("var", var); }
std::string ProofManager::getAtomName(prop::SatVariable var) { return append("atom", var); }
std::string ProofManager::getLitName(prop::SatLiteral lit) { return append("lit", lit.toInt()); }

std::string ProofManager::getAtomName(TNode atom) {
  prop::SatLiteral lit = currentPM()->d_cnfProof->getLiteral(atom);
  Assert(!lit.isNegated());
  return getAtomName(lit.getSatVariable());
}
std::string ProofManager::getLitName(TNode lit) {
  return getLitName(currentPM()->d_cnfProof->getLiteral(lit));
}

void ProofManager::traceDeps(TNode n) {
  Debug("cores") << "trace deps " << n << std::endl;
  if(d_inputCoreFormulas.find(n.toExpr()) != d_inputCoreFormulas.end()) {
    // originating formula was in core set
    Debug("cores") << " -- IN INPUT CORE LIST!" << std::endl;
    d_outputCoreFormulas.insert(n.toExpr());
  } else {
    Debug("cores") << " -- NOT IN INPUT CORE LIST!" << std::endl;
    if(d_deps.find(n) == d_deps.end()) {
      InternalError("Cannot trace dependence information back to input assertion:\n`%s'", n.toString().c_str());
    }
    Assert(d_deps.find(n) != d_deps.end());
    std::vector<Node> deps = (*d_deps.find(n)).second;
    for(std::vector<Node>::const_iterator i = deps.begin(); i != deps.end(); ++i) {
      Debug("cores") << " + tracing deps: " << n << " -deps-on- " << *i << std::endl;
      if( !(*i).isNull() ){
        traceDeps(*i);
      }
    }
  }
}

void ProofManager::addClause(ClauseId id, const prop::SatClause* clause, ClauseKind kind) {
  /*for (unsigned i = 0; i < clause->size(); ++i) {
    prop::SatLiteral lit = clause->operator[](i);
    d_propVars.insert(lit.getSatVariable());
  }*/
  if (kind == INPUT) {
    Debug("cores") << "; Add to inputClauses " << id << std::endl;
    d_inputClauses.insert(std::make_pair(id, clause));
    Assert(d_satProof->d_inputClauses.find(id) != d_satProof->d_inputClauses.end());
    Debug("cores") << "; core id is " << d_satProof->d_inputClauses[id] << std::endl;
    if(d_satProof->d_inputClauses[id] == uint64_t(-1)) {
      Debug("cores") << "; + constant unit (true or false)" << std::endl;
    } else if(options::unsatCores()) {
      Expr e = d_cnfProof->getAssertion(d_satProof->d_inputClauses[id] & 0xffffffff);
      Debug("cores") << "; core input assertion from CnfStream is " << e << std::endl;
      Debug("cores") << "; with proof rule " << ((d_satProof->d_inputClauses[id] & 0xffffffff00000000llu) >> 32) << std::endl;
      // Invalid proof rules are currently used for parts of CVC4 that don't
      // support proofs (these are e.g. unproven theory lemmas) or don't need
      // proofs (e.g. split lemmas).  We can ignore these safely when
      // constructing unsat cores.
      if(((d_satProof->d_inputClauses[id] & 0xffffffff00000000llu) >> 32) != RULE_INVALID) {
        // trace dependences back to actual assertions
        traceDeps(Node::fromExpr(e));
      }
    }
  } else {
    Assert(kind == THEORY_LEMMA);
    d_theoryLemmas.insert(std::make_pair(id, clause));
  }
}

void ProofManager::addAssertion(Expr formula, bool inUnsatCore) {
  Debug("cores") << "assert: " << formula << std::endl;
  d_inputFormulas.insert(formula);
  d_deps[Node::fromExpr(formula)]; // empty vector of deps
  if(inUnsatCore || options::dumpUnsatCores() || options::checkUnsatCores()) {
    Debug("cores") << "adding to input core forms: " << formula << std::endl;
    d_inputCoreFormulas.insert(formula);
  }
}

void ProofManager::addDependence(TNode n, TNode dep) {
  if(dep != n) {
    Debug("cores") << "dep: " << n << " : " << dep << std::endl;
    if( !dep.isNull() && d_deps.find(dep) == d_deps.end()) {
      Debug("cores") << "WHERE DID " << dep << " come from ??" << std::endl;
    }
    //Assert(d_deps.find(dep) != d_deps.end());
    d_deps[n].push_back(dep);
  }
}

void ProofManager::addUnsatCore(Expr formula) {
  Assert (d_inputCoreFormulas.find(formula) != d_inputCoreFormulas.end());
  d_outputCoreFormulas.insert(formula);
}

void ProofManager::setLogic(const LogicInfo& logic) {
  d_logic = logic;
}

void ProofManager::printProof(std::ostream& os, TNode n) {
  // no proofs here yet
}

void ProofManager::setCnfDep( Expr child, Expr parent ) {
  Debug("cores") << "CNF dep : " << child << " : " << parent << std::endl;
  d_cnf_dep[child] = parent;
}

Expr ProofManager::getFormulaForClauseId( ClauseId id ) {
  std::map< ClauseId, Expr >::const_iterator it = d_clause_id_to_assertion.find( id );
  if( it!=d_clause_id_to_assertion.end() ){
    return it->second;
  }else{
    Node ret;
    return ret.toExpr();
  }
}

ProofRule ProofManager::getProofRuleForClauseId( ClauseId id ) {
  std::map< ClauseId, ProofRule >::const_iterator it = d_clause_id_to_rule.find( id );
  if( it!=d_clause_id_to_rule.end() ){
    return it->second;
  }else{
    return RULE_INVALID;
  }
}

void ProofManager::setAssertion( Expr e ) {
  d_assertion_to_id[e] = d_assertion_counter;
  d_assertion_counter++;
}

// if this function returns true, writes to out a proof of e based on input assertions
bool ProofManager::isInputAssertion( Expr e, std::ostream& out ) {
  std::map< Expr, unsigned >::iterator itp = d_assertion_to_id.find( e );
  if( itp==d_assertion_to_id.end() ){
    //check if deduced by CNF
    std::map< Expr, Expr >::iterator itd = d_cnf_dep.find( e );
    if( itd!=d_cnf_dep.end() ){
      Expr parent = itd->second;
      //check if parent is an input assertion
      std::stringstream out_parent;
      if( isInputAssertion( parent, out_parent ) ){
        if( parent.getKind()==kind::AND || ( parent.getKind()==kind::NOT && ( parent[0].getKind()==kind::IMPLIES || parent[0].getKind()==kind::OR ) ) ){
          Expr parent_base = parent.getKind()==kind::NOT ? parent[0] : parent;
          Expr e_base = e.getKind()==kind::NOT ? e[0] : e;
          bool e_pol = e.getKind()!=kind::NOT;
          for( unsigned i=0; i<parent_base.getNumChildren(); i++ ){
            Expr child_base = parent_base[i].getKind()==kind::NOT ? parent_base[i][0] : parent_base[i];
            bool child_pol = parent_base[i].getKind()!=kind::NOT;
            if( parent_base.getKind()==kind::IMPLIES && i==0 ){
              child_pol = !child_pol;
            }
            if( e_base==child_base && (e_pol==child_pol)==(parent_base.getKind()==kind::AND) ){
              bool elimNn = ( ( parent_base.getKind()==kind::OR || ( parent_base.getKind()==kind::IMPLIES && i==1 ) ) && e_pol );
              if( elimNn ){
                out << "(not_not_elim _ ";
              }
              std::stringstream out_paren;
              if( i+1<parent_base.getNumChildren() ){
                out << "(and_elim_1 _ _ ";
                if( parent_base.getKind()==kind::OR || parent_base.getKind()==kind::IMPLIES  ){
                  out << "(not_" << ( parent_base.getKind()==kind::OR ? "or" : "impl" ) << "_elim _ _ ";
                  out_paren << ")";
                }
                out_paren << ")";
              }
              for( unsigned j=0; j<i; j++ ){
                out << "(and_elim_2 _ _ ";
                if( parent_base.getKind()==kind::OR || parent_base.getKind()==kind::IMPLIES ){
                  out << "(not_" << ( parent_base.getKind()==kind::OR ? "or" : "impl" ) << "_elim _ _ ";
                  out_paren << ")";
                }
                out_paren << ")";
              }
              out << out_parent.str();
              out << out_paren.str();
              if( elimNn ){
                out << ")";
              }
              return true;
            }
          }
        }else{
          Trace("cnf-pf-debug") << "; isInputAssertion : parent of " << e << " is not correct type (" << parent << ")" << std::endl;
        }
      }else{
        Trace("cnf-pf-debug") << "; isInputAssertion : parent of " << e << " is not input" << std::endl;
      }
    }else{
      Trace("cnf-pf-debug") << "; isInputAssertion : " << e << " has no parent" << std::endl;
    }
    return false;
  }else{
    out << "A" << itp->second;
    return true;
  }
}

void ProofManager::setRegisteringFormula( Node n, ProofRule proof_id ) {
  Trace("cnf-pf-debug") << "; set registering formula " << n << " proof rule = " << proof_id << std::endl;
  d_registering_assertion = n;
  d_registering_rule = proof_id;
}

void ProofManager::setRegisteredClauseId( ClauseId id ) {
  Trace("cnf-pf-debug") << "; set register clause id " << id << " " << d_registering_assertion << std::endl;
  if( !d_registering_assertion.isNull() ){
     d_clause_id_to_assertion[id] = d_registering_assertion.toExpr();
     d_clause_id_to_rule[id] = d_registering_rule;
     setRegisteringFormula( Node::null(), RULE_INVALID );
  }
}

LFSCProof::LFSCProof(SmtEngine* smtEngine, LFSCSatProof* sat, LFSCCnfProof* cnf, LFSCTheoryProof* theory)
  : d_satProof(sat)
  , d_cnfProof(cnf)
  , d_theoryProof(theory)
  , d_smtEngine(smtEngine)
{
  d_satProof->constructProof();
}

void LFSCProof::toStream(std::ostream& out) {
  smt::SmtScope scope(d_smtEngine);
  std::ostringstream paren;
  out << "(check\n";
  out << " ;; Declarations\n";
  if (d_theoryProof == NULL) {
    d_theoryProof = new LFSCTheoryProof();
  }
  /*for(LFSCCnfProof::iterator i = d_cnfProof->begin_atom_mapping();
      i != d_cnfProof->end_atom_mapping();
      ++i) {
    d_theoryProof->addDeclaration(*i);
  }*/
  d_theoryProof->printAssertions(out, paren);
  out << " ;; Proof of empty clause follows\n";
  out << "(: (holds cln)\n";
  d_cnfProof->printClauses(out, paren);
  d_satProof->printResolutions(out, paren);
  paren <<")))\n;;";
  out << paren.str();
  out << "\n";
}

} /* CVC4  namespace */
