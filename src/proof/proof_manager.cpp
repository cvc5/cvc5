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
#include "util/proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/cnf_proof.h"
#include "proof/theory_proof.h"
#include "proof/bitvector_proof.h"
#include "proof/rewriter_proof.h"
#include "proof/proof_utils.h"

#include "util/cvc4_assert.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/output_channel.h"
#include "theory/valuation.h"
#include "util/node_visitor.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/equality_engine.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/options.h"
#include "context/context.h"
#include "util/hash.h"

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
  //  d_inputClauses(),
  //  d_theoryLemmas(),
  //  d_theoryPropagations(),
  d_inputFormulas(), 
  d_inputCoreFormulas(),
  d_outputCoreFormulas(),
  //  d_nextId(0),
  d_fullProof(NULL),
  d_format(format),
  d_deps()
  //  d_assertion_counter(1)
{
}

ProofManager::~ProofManager() {
  delete d_satProof;
  delete d_cnfProof;
  //  delete d_rewriterProof;
  delete d_theoryProof;
  delete d_fullProof;

  // for(IdToSatClause::iterator it = d_inputClauses.begin();
  //     it != d_inputClauses.end();
  //     ++it) {
  //   delete it->second;
  // }

  // for(OrderedIdToSatClause::iterator it = d_theoryLemmas.begin();
  //     it != d_theoryLemmas.end();
  //     ++it) {
  //   delete it->second;
  // }

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
                                           (LFSCCoreSatProof*)getSatProof(),
                                           (LFSCCnfProof*)getCnfProof(),
                                           //                                           (LFSCRewriterProof*)getRewriterProof(),
                                           (LFSCTheoryProofEngine*)getTheoryProofEngine());
  return currentPM()->d_fullProof;
}

CoreSatProof* ProofManager::getSatProof() {
  Assert (currentPM()->d_satProof);
  return currentPM()->d_satProof;
}

CnfProof* ProofManager::getCnfProof() {
  Assert (currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof;
}
RewriterProof* ProofManager::getRewriterProof() {
  Unreachable();
  return NULL;
  // Assert (options::proof());
  // if (currentPM()->d_rewriterProof == NULL) {
  //   Assert (currentPM()->d_format == LFSC);
  //   currentPM()->d_rewriterProof = new LFSCRewriterProof();
  // }
  // return currentPM()->d_rewriterProof;
}

TheoryProofEngine* ProofManager::getTheoryProofEngine() {
  Assert (options::proof());
  Assert (currentPM()->d_theoryProof != NULL);
  return currentPM()->d_theoryProof;
}

UFProof* ProofManager::getUfProof() {
  Assert (options::proof());
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_UF);
  return (UFProof*)pf; 
}
BitVectorProof* ProofManager::getBitVectorProof() {
  Assert (options::proof());
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_BV);
  return (BitVectorProof*)pf; 
}

ArrayProof* ProofManager::getArrayProof() {
  Assert (options::proof());
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_ARRAY);
  return (ArrayProof*)pf; 
}

void ProofManager::initSatProof(Minisat::Solver* solver) {
  Assert (currentPM()->d_satProof == NULL);
  Assert(currentPM()->d_format == LFSC);
  currentPM()->d_satProof = new LFSCCoreSatProof(solver, "");
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream,
                                context::Context* ctx) {
  ProofManager* pm = currentPM();
  Assert (pm->d_cnfProof == NULL);
  Assert (pm->d_format == LFSC);
  CnfProof* cnf = new LFSCCnfProof(cnfStream, ctx, "");
  pm->d_cnfProof = cnf;
  Assert(pm-> d_satProof != NULL);
  pm->d_satProof->setCnfProof(cnf);

  // true and false have to be setup in a special way
  Node true_node = NodeManager::currentNM()->mkConst<bool>(true);
  Node false_node = NodeManager::currentNM()->mkConst<bool>(false).notNode();

  pm->d_cnfProof->pushCurrentAssertion(true_node);
  pm->d_cnfProof->pushCurrentDefinition(true_node);
  pm->d_cnfProof->registerConvertedClause(pm->d_satProof->getTrueUnit());
  //pm->d_cnfProof->setClauseFact(pm->d_satProof->getTrueUnit(), true_node);
  pm->d_cnfProof->popCurrentAssertion();
  pm->d_cnfProof->popCurrentDefinition();

  pm->d_cnfProof->pushCurrentAssertion(false_node);
  pm->d_cnfProof->pushCurrentDefinition(false_node);
  pm->d_cnfProof->registerConvertedClause(pm->d_satProof->getFalseUnit());
  //pm->d_cnfProof->setClauseFact(pm->d_satProof->getFalseUnit(), false_node);
  pm->d_cnfProof->popCurrentAssertion();
  pm->d_cnfProof->popCurrentDefinition();
  
}

void ProofManager::initTheoryProofEngine() {
  Assert (currentPM()->d_theoryProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_theoryProof = new LFSCTheoryProofEngine();
}

std::string ProofManager::getInputClauseName(ClauseId id,
                                             const std::string& prefix) {
  return append(prefix+".pb", id);
}
std::string ProofManager::getLemmaClauseName(ClauseId id,
                                             const std::string& prefix) {
  return append(prefix+".lemc", id);
}
  std::string ProofManager::getLemmaName(ClauseId id,
					 const std::string& prefix) {
  return append(prefix+"lem", id);
}
  
std::string ProofManager::getLearntClauseName(ClauseId id,
                                              const std::string& prefix) {
  return append(prefix+".cl", id);
}
std::string ProofManager::getVarName(prop::SatVariable var,
                                     const std::string& prefix) {
  return append(prefix+".v", var);
}
std::string ProofManager::getAtomName(prop::SatVariable var,
                                      const std::string& prefix) {
  return append(prefix+".a", var);
}
std::string ProofManager::getLitName(prop::SatLiteral lit,
                                     const std::string& prefix) {
  return append(prefix+".l", lit.toInt());
}


std::string ProofManager::getPreprocessedAssertionName(Node node,
                                                       const std::string& prefix) {
  node = node.getKind() == kind::BITVECTOR_EAGER_ATOM ? node[0] : node;
  //std::cout <<std::endl << "id" << node.getId() << " " << node <<std::endl;
  return append(prefix+".PA", node.getId());
}
std::string ProofManager::getAssertionName(Node node,
                                           const std::string& prefix) {
  return append(prefix+".A", node.getId());
}

// void ProofManager::addTheoryLemma(ClauseId id,
//                                   const prop::SatClause* clause,
//                                   ClauseKind kind) {
//   Assert (d_theoryLemmas.find(id) == d_theoryLemmas.end()); 
//   d_theoryLemmas.insert(std::make_pair(id, clause));
//   d_cnfProof->collectAtoms(clause);
// }
  
std::string ProofManager::getAtomName(TNode atom,
                                      const std::string& prefix) {
  prop::SatLiteral lit = currentPM()->d_cnfProof->getLiteral(atom);
  Assert(!lit.isNegated());
  return getAtomName(lit.getSatVariable(), prefix);
}
std::string ProofManager::getLitName(TNode lit,
                                     const std::string& prefix) {
  return getLitName(currentPM()->d_cnfProof->getLiteral(lit), prefix);
}

void ProofManager::traceDeps(TNode n) {
  Debug("cores") << "trace deps " << n << std::endl;
  if ((n.isConst() && n == NodeManager::currentNM()->mkConst<bool>(true)) ||
      (n.getKind() == kind::NOT && n[0] == NodeManager::currentNM()->mkConst<bool>(false))) {
    return;
  }
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

void ProofManager::traceUnsatCore() {
  Assert (options::unsatCores());
  
  d_satProof->constructProof();
  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_satProof->collectClausesUsed(used_inputs,
                                 used_lemmas);
  IdToSatClause::const_iterator it = used_inputs.begin();
  for(; it != used_inputs.end(); ++it) {
    Node node = d_cnfProof->getAssertionForClause(it->first);
    ProofRule rule = d_cnfProof->getProofRule(node);
    
    Debug("cores") << "core input assertion " << node << std::endl;
    Debug("cores") << "with proof rule " << rule << std::endl;
    if (rule == RULE_TSEITIN ||
        rule == RULE_GIVEN) {
      // trace dependences back to actual assertions
      // (this adds them to the unsat core)
      traceDeps(node);
    }
  }
}

void ProofManager::addAssertion(Expr formula) {
  Debug("proof:pm") << "assert: " << formula << std::endl;
  d_inputFormulas.insert(formula);
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

// void ProofManager::addTheoryLemma(ClauseId id,
//                                   const prop::SatClause* clause,
//                                   ClauseKind kind) {
//   Assert (d_theoryLemmas.find(id) == d_theoryLemmas.end()); 
//   d_theoryLemmas.insert(std::make_pair(id, clause));
//   d_cnfProof->collectAtoms(clause);
// }


// void ProofManager::printProof(std::ostream& os, TNode n) {
//   // no proofs here yet
// }

// void ProofManager::setCnfDep( Expr child, Expr parent ) {
//   Debug("cores") << "CNF dep : " << child << " : " << parent << std::endl;
//   d_cnf_dep[child] = parent;
// }

// Expr ProofManager::getFormulaForClauseId( ClauseId id ) {
//   std::map< ClauseId, Expr >::const_iterator it = d_clause_id_to_assertion.find( id );
//   if( it!=d_clause_id_to_assertion.end() ){
//     return it->second;
//   }else{
//     Node ret;
//     return ret.toExpr();
//   }
// }

// ProofRule ProofManager::getProofRuleForClauseId( ClauseId id ) {
//   std::map< ClauseId, ProofRule >::const_iterator it = d_clause_id_to_rule.find( id );
//   if( it!=d_clause_id_to_rule.end() ){
//     return it->second;
//   }else{
//     return RULE_INVALID;
//   }
// }

// void ProofManager::setAssertion( Expr e ) {
//   d_assertion_to_id[e] = d_assertion_counter;
//   d_assertion_counter++;
// }
// this is the case when the cnf stream asserts a top-level fact and converts it (convertAndAssert)
// the expression e is a top-level fact that has been proven from other assertions e.g. the assertion
// was a ^ b and e is a (similarly negation over disjunction)

// if this function returns true, writes to out a proof of e based on input assertions

// void ProofManager::setRegisteringFormula( Node n, ProofRule proof_id ) {
//   d_registering_assertion = n;
//   d_registering_rule = proof_id;
// }

// void ProofManager::setRegisteredClauseId( ClauseId id ) {
//   Trace("cnf-pf-debug") << "set register clause id " << id << " " << d_registering_assertion << std::endl;
//   if( !d_registering_assertion.isNull() ){
//      d_clause_id_to_assertion[id] = d_registering_assertion.toExpr();
//      d_clause_id_to_rule[id] = d_registering_rule;
//      setRegisteringFormula( Node::null(), RULE_INVALID );
//   }
// }

LFSCProof::LFSCProof(SmtEngine* smtEngine,
                     LFSCCoreSatProof* sat,
                     LFSCCnfProof* cnf,
                     //               LFSCRewriterProof* rwr,
                     LFSCTheoryProofEngine* theory)
  : d_satProof(sat)
  , d_cnfProof(cnf)
    //  , d_rewriterProof(rwr)    
  , d_theoryProof(theory)
  , d_smtEngine(smtEngine)
{}

void LFSCProof::toStream(std::ostream& out) {
  d_satProof->constructProof();

  // collecting leaf clauses in resolution proof
  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_satProof->collectClausesUsed(used_inputs,
                                 used_lemmas);

  // collecting assertions that lead to the clauses being asserted
  NodeSet used_assertions;
  d_cnfProof->collectAssertionsForClauses(used_inputs, used_assertions);

  NodeSet atoms;
  // collects the atoms in the clauses
  d_cnfProof->collectAtomsForClauses(used_inputs, atoms);
  d_cnfProof->collectAtomsForClauses(used_lemmas, atoms);

  // collects the atoms in the assertions
  for (NodeSet::const_iterator it = used_assertions.begin();
       it != used_assertions.end(); ++it) {
    utils::collectAtoms(*it, atoms);
  }
  
  if (Debug.isOn("proof:pm")) {
    // std::cout << NodeManager::currentNM(); 
    Debug("proof:pm") << "LFSCProof::Used assertions: "<< std::endl;
    for(NodeSet::const_iterator it = used_assertions.begin(); it != used_assertions.end(); ++it) {
      Debug("proof:pm") << "   " << *it << std::endl;
    }
    
    // NodeSet lemmas;
    // d_cnfProof->collectAssertionsForClauses(used_lemmas, lemmas);

    // Debug("proof:pm") << "LFSCProof::Used lemmas: "<< std::endl;
    // for(NodeSet::const_iterator it = lemmas.begin(); it != lemmas.end(); ++it) {
    //   Debug("proof:pm") << "   " << *it << std::endl;
    // }

    Debug("proof:pm") << "LFSCProof::Used atoms: "<< std::endl;
    for(NodeSet::const_iterator it = atoms.begin(); it != atoms.end(); ++it) {
      Debug("proof:pm") << "   " << *it << std::endl;
    }
  }

  
  
  smt::SmtScope scope(d_smtEngine);
  std::ostringstream paren;
  out << "(check\n";
  out << " ;; Declarations\n";
  
  // declare the theory atoms
  NodeSet::const_iterator it = atoms.begin();
  NodeSet::const_iterator end = atoms.end();
  for(; it != end; ++it) {
    d_theoryProof->registerTerm((*it).toExpr());
  }
  // print out all the original assertions
  d_theoryProof->printAssertions(out, paren);
  // d_rewriterProof->printRewrittenAssertios(out, paren);


  out << "(: (holds cln)\n";

  // print trust that input assertions are their preprocessed form
  printPreprocessedAssertions(used_assertions, out, paren);

  // print mapping between theory atoms and internal SAT variables
  d_cnfProof->printAtomMapping(atoms, out, paren);

  IdToSatClause::const_iterator cl_it = used_inputs.begin();
  // print CNF conversion proof for each clause
  for (; cl_it != used_inputs.end(); ++cl_it) {
    d_cnfProof->printCnfProofForClause(cl_it->first, cl_it->second, out, paren);
  }

  // FIXME: for now assume all theory lemmas are in CNF form so
  // distinguish between them and inputs
  // print theory lemmas for resolution proof
  d_theoryProof->printTheoryLemmas(used_lemmas, out, paren);

  
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    // priunt actual resolution proof
    // d_satProof->printResolutions(out, paren);
    ProofManager::getBitVectorProof()->getSatProof()->printResolutionEmptyClause(out, paren);
    paren <<")))\n;;";
    out << paren.str();
    out << "\n";
  } else {
    // priunt actual resolution proof
    d_satProof->printResolutions(out, paren);
    d_satProof->printResolutionEmptyClause(out, paren);
    paren <<")))\n;;";
    out << paren.str();
    out << "\n";
  }
}

void LFSCProof::printPreprocessedAssertions(const NodeSet& assertions,
                                            std::ostream& os,
                                            std::ostream& paren) {
  os << " ;; Preprocessing \n";
  NodeSet::const_iterator it = assertions.begin();
  NodeSet::const_iterator end = assertions.end();
  
  for (; it != end; ++it) {
    os << "(th_let_pf _ ";
    
    //TODO
    os << "(trust_f ";
    ProofManager::currentPM()->getTheoryProofEngine()->printLetTerm((*it).toExpr(), os);
    os << ") ";
    
    os << "(\\ "<< ProofManager::getPreprocessedAssertionName(*it, "") << "\n";
    paren << "))";

  }
}


// void LFSCProof::toStream(std::ostream& out) {
//   smt::SmtScope scope(d_smtEngine);
//   std::ostringstream paren;
//   out << "(check\n";
//   out << " ;; Declarations\n";

//   // declare the theory atoms
//   CnfProof::atom_iterator begin = d_cnfProof->begin_atoms();
//   CnfProof::atom_iterator end = d_cnfProof->end_atoms();
//   for(CnfProof::atom_iterator it = begin; it != end; ++it) {
//     d_theoryProof->registerTerm(it->first);
//   }
//   // print out the assertions
//   d_theoryProof->printAssertions(out, paren);
//   // d_rewriterProof->printRewrittenAssertios(out, paren);
  
//   out << "(: (holds cln)\n";
//   // print mapping between theory atoms and internal SAT variables
//   d_cnfProof->printAtomMapping(out, paren);
//   d_cnfProof->printClauses(out, paren);
//   // print theory lemmas for resolution proof
//   d_theoryProof->printTheoryLemmas(out, paren);
//   // priunt actual resolution proof
//   d_satProof->printResolutions(out, paren);
//   d_satProof->printResolutionEmptyClause(out, paren);
//   paren <<")))\n;;";
//   out << paren.str();
//   out << "\n";
// }

} /* CVC4  namespace */
