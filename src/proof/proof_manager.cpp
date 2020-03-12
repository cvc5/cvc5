/*********************                                                        */
/*! \file proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Liana Hadarean, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "proof/proof_manager.h"

#include "base/check.h"
#include "context/context.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/proof_utils.h"
#include "proof/resolution_bitvector_proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/theory_proof.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
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

std::string nodeSetToString(const std::set<Node>& nodes) {
  std::ostringstream os;
  std::set<Node>::const_iterator it;
  for (it = nodes.begin(); it != nodes.end(); ++it) {
    os << *it << " ";
  }
  return os.str();
}

std::string append(const std::string& str, uint64_t num) {
  std::ostringstream os;
  os << str << num;
  return os.str();
}

ProofManager::ProofManager(context::Context* context, ProofFormat format)
    : d_context(context),
      d_satProof(NULL),
      d_cnfProof(NULL),
      d_theoryProof(NULL),
      d_inputFormulas(),
      d_inputCoreFormulas(context),
      d_outputCoreFormulas(context),
      d_nextId(0),
      d_fullProof(),
      d_format(format),
      d_deps(context)
{
}

ProofManager::~ProofManager() {
  if (d_satProof) delete d_satProof;
  if (d_cnfProof) delete d_cnfProof;
  if (d_theoryProof) delete d_theoryProof;
}

ProofManager* ProofManager::currentPM() {
  return smt::currentProofManager();
}
const Proof& ProofManager::getProof(SmtEngine* smt)
{
  if (!currentPM()->d_fullProof)
  {
    Assert(currentPM()->d_format == LFSC);
    currentPM()->d_fullProof.reset(new LFSCProof(
        smt,
        static_cast<CoreSatProof*>(getSatProof()),
        static_cast<LFSCCnfProof*>(getCnfProof()),
        static_cast<LFSCTheoryProofEngine*>(getTheoryProofEngine())));
  }
  return *(currentPM()->d_fullProof);
}

CoreSatProof* ProofManager::getSatProof() {
  Assert(currentPM()->d_satProof);
  return currentPM()->d_satProof;
}

CnfProof* ProofManager::getCnfProof() {
  Assert(currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof;
}

TheoryProofEngine* ProofManager::getTheoryProofEngine() {
  Assert(currentPM()->d_theoryProof != NULL);
  return currentPM()->d_theoryProof;
}

UFProof* ProofManager::getUfProof() {
  Assert(options::proof());
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_UF);
  return (UFProof*)pf;
}

proof::ResolutionBitVectorProof* ProofManager::getBitVectorProof()
{
  Assert(options::proof());
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_BV);
  return static_cast<proof::ResolutionBitVectorProof*>(pf);
}

ArrayProof* ProofManager::getArrayProof() {
  Assert(options::proof());
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_ARRAYS);
  return (ArrayProof*)pf;
}

ArithProof* ProofManager::getArithProof() {
  Assert(options::proof());
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_ARITH);
  return (ArithProof*)pf;
}

SkolemizationManager* ProofManager::getSkolemizationManager() {
  Assert(options::proof() || options::unsatCores());
  return &(currentPM()->d_skolemizationManager);
}

void ProofManager::initSatProof(Minisat::Solver* solver) {
  Assert(currentPM()->d_satProof == NULL);
  Assert(currentPM()->d_format == LFSC);
  currentPM()->d_satProof = new CoreSatProof(solver, d_context, "");
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream,
                                context::Context* ctx) {
  ProofManager* pm = currentPM();
  Assert(pm->d_satProof != NULL);
  Assert(pm->d_cnfProof == NULL);
  Assert(pm->d_format == LFSC);
  CnfProof* cnf = new LFSCCnfProof(cnfStream, ctx, "");
  pm->d_cnfProof = cnf;

  // true and false have to be setup in a special way
  Node true_node = NodeManager::currentNM()->mkConst<bool>(true);
  Node false_node = NodeManager::currentNM()->mkConst<bool>(false).notNode();

  pm->d_cnfProof->pushCurrentAssertion(true_node);
  pm->d_cnfProof->pushCurrentDefinition(true_node);
  pm->d_cnfProof->registerConvertedClause(pm->d_satProof->getTrueUnit());
  pm->d_cnfProof->popCurrentAssertion();
  pm->d_cnfProof->popCurrentDefinition();

  pm->d_cnfProof->pushCurrentAssertion(false_node);
  pm->d_cnfProof->pushCurrentDefinition(false_node);
  pm->d_cnfProof->registerConvertedClause(pm->d_satProof->getFalseUnit());
  pm->d_cnfProof->popCurrentAssertion();
  pm->d_cnfProof->popCurrentDefinition();

}

void ProofManager::initTheoryProofEngine() {
  Assert(currentPM()->d_theoryProof == NULL);
  Assert(currentPM()->d_format == LFSC);
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

std::string ProofManager::getLemmaName(ClauseId id, const std::string& prefix) {
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
  if (currentPM()->d_assertionFilters.find(node) != currentPM()->d_assertionFilters.end()) {
    return currentPM()->d_assertionFilters[node];
  }

  node = node.getKind() == kind::BITVECTOR_EAGER_ATOM ? node[0] : node;
  return append(prefix+".PA", node.getId());
}
std::string ProofManager::getAssertionName(Node node,
                                           const std::string& prefix) {
  return append(prefix+".A", node.getId());
}
std::string ProofManager::getInputFormulaName(const Expr& expr) {
  return currentPM()->d_inputFormulaToName[expr];
}

std::string ProofManager::getAtomName(TNode atom,
                                      const std::string& prefix) {
  prop::SatLiteral lit = currentPM()->d_cnfProof->getLiteral(atom);
  Assert(!lit.isNegated());
  return getAtomName(lit.getSatVariable(), prefix);
}

std::string ProofManager::getLitName(TNode lit,
                                     const std::string& prefix) {
  std::string litName = getLitName(currentPM()->d_cnfProof->getLiteral(lit), prefix);
  if (currentPM()->d_rewriteFilters.find(litName) != currentPM()->d_rewriteFilters.end()) {
    return currentPM()->d_rewriteFilters[litName];
  }

  return litName;
}

bool ProofManager::hasLitName(TNode lit) {
  return currentPM()->d_cnfProof->hasLiteral(lit);
}

std::string ProofManager::sanitize(TNode node) {
  Assert(node.isVar() || node.isConst());

  std::string name = node.toString();
  if (node.isVar()) {
    std::replace(name.begin(), name.end(), ' ', '_');
  } else if (node.isConst()) {
    name.erase(std::remove(name.begin(), name.end(), '('), name.end());
    name.erase(std::remove(name.begin(), name.end(), ')'), name.end());
    name.erase(std::remove(name.begin(), name.end(), ' '), name.end());
    name = "const" + name;
  }

  return name;
}

void ProofManager::traceDeps(TNode n, ExprSet* coreAssertions) {
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
      if (options::allowEmptyDependencies()) {
        Debug("cores") << " -- Could not track cause assertion. Failing silently." << std::endl;
        return;
      }
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
      if (options::allowEmptyDependencies()) {
        Debug("cores") << " -- Could not track cause assertion. Failing silently." << std::endl;
        return;
      }
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
    ProofRule rule = d_cnfProof->getProofRule(node);

    Debug("cores") << "core input assertion " << node << std::endl;
    Debug("cores") << "with proof rule " << rule << std::endl;
    if (rule == RULE_TSEITIN ||
        rule == RULE_GIVEN) {
      // trace dependences back to actual assertions
      // (this adds them to the unsat core)
      traceDeps(node, &d_outputCoreFormulas);
    }
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

void ProofManager::constructSatProof() {
  if (!d_satProof->proofConstructed()) {
    d_satProof->constructProof();
  }
}

void ProofManager::getLemmasInUnsatCore(theory::TheoryId theory, std::vector<Node> &lemmas) {
  Assert(PROOF_ON()) << "Cannot compute unsat core when proofs are off";
  Assert(unsatCoreAvailable())
      << "Cannot get unsat core at this time. Mabye the input is SAT?";

  constructSatProof();

  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_satProof->collectClausesUsed(used_inputs, used_lemmas);

  IdToSatClause::const_iterator it;
  std::set<Node> seen;

  Debug("pf::lemmasUnsatCore") << "Dumping all lemmas in unsat core" << std::endl;
  for (it = used_lemmas.begin(); it != used_lemmas.end(); ++it) {
    std::set<Node> lemma = satClauseToNodeSet(it->second);
    Debug("pf::lemmasUnsatCore") << nodeSetToString(lemma);

    // TODO: we should be able to drop the "haveProofRecipe" check.
    // however, there are some rewrite issues with the arith solver, resulting
    // in non-registered recipes. For now we assume no one is requesting arith lemmas.
    LemmaProofRecipe recipe;
    if (!getCnfProof()->haveProofRecipe(lemma)) {
      Debug("pf::lemmasUnsatCore") << "\t[no recipe]" << std::endl;
      continue;
    }

    recipe = getCnfProof()->getProofRecipe(lemma);
    Debug("pf::lemmasUnsatCore") << "\t[owner = " << recipe.getTheory()
                                 << ", original = " << recipe.getOriginalLemma() << "]" << std::endl;
    if (recipe.simpleLemma() && recipe.getTheory() == theory && seen.find(recipe.getOriginalLemma()) == seen.end()) {
      lemmas.push_back(recipe.getOriginalLemma());
      seen.insert(recipe.getOriginalLemma());
    }
  }
}

std::set<Node> ProofManager::satClauseToNodeSet(prop::SatClause* clause) {
  std::set<Node> result;
  for (unsigned i = 0; i < clause->size(); ++i) {
    prop::SatLiteral lit = (*clause)[i];
    Node node = getCnfProof()->getAtom(lit.getSatVariable());
    Expr atom = node.toExpr();
    if (atom != utils::mkTrue())
      result.insert(lit.isNegated() ? node.notNode() : node);
  }

  return result;
}

Node ProofManager::getWeakestImplicantInUnsatCore(Node lemma) {
  Assert(PROOF_ON()) << "Cannot compute unsat core when proofs are off";
  Assert(unsatCoreAvailable())
      << "Cannot get unsat core at this time. Mabye the input is SAT?";

  // If we're doing aggressive minimization, work on all lemmas, not just conjunctions.
  if (!options::aggressiveCoreMin() && (lemma.getKind() != kind::AND))
    return lemma;

  constructSatProof();

  NodeBuilder<> builder(kind::AND);

  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  d_satProof->collectClausesUsed(used_inputs, used_lemmas);

  IdToSatClause::const_iterator it;
  std::set<Node>::iterator lemmaIt;

  if (!options::aggressiveCoreMin()) {
    for (it = used_lemmas.begin(); it != used_lemmas.end(); ++it) {
      std::set<Node> currentLemma = satClauseToNodeSet(it->second);

      // TODO: we should be able to drop the "haveProofRecipe" check.
      // however, there are some rewrite issues with the arith solver, resulting
      // in non-registered recipes. For now we assume no one is requesting arith lemmas.
      LemmaProofRecipe recipe;
      if (!getCnfProof()->haveProofRecipe(currentLemma))
        continue;

      recipe = getCnfProof()->getProofRecipe(currentLemma);
      if (recipe.getOriginalLemma() == lemma) {
        for (lemmaIt = currentLemma.begin(); lemmaIt != currentLemma.end(); ++lemmaIt) {
          builder << *lemmaIt;

          // Check that each conjunct appears in the original lemma.
          bool found = false;
          for (unsigned i = 0; i < lemma.getNumChildren(); ++i) {
            if (lemma[i] == *lemmaIt)
              found = true;
          }

          if (!found)
            return lemma;
        }
      }
    }
  } else {
    // Aggressive mode
    for (it = used_lemmas.begin(); it != used_lemmas.end(); ++it) {
      std::set<Node> currentLemma = satClauseToNodeSet(it->second);

      // TODO: we should be able to drop the "haveProofRecipe" check.
      // however, there are some rewrite issues with the arith solver, resulting
      // in non-registered recipes. For now we assume no one is requesting arith lemmas.
      LemmaProofRecipe recipe;
      if (!getCnfProof()->haveProofRecipe(currentLemma))
        continue;

      recipe = getCnfProof()->getProofRecipe(currentLemma);
      if (recipe.getOriginalLemma() == lemma) {
        NodeBuilder<> disjunction(kind::OR);
        for (lemmaIt = currentLemma.begin(); lemmaIt != currentLemma.end(); ++lemmaIt) {
          disjunction << *lemmaIt;
        }

        Node conjunct = (disjunction.getNumChildren() == 1) ? disjunction[0] : disjunction;
        builder << conjunct;
      }
    }
  }

  AlwaysAssert(builder.getNumChildren() != 0);

  if (builder.getNumChildren() == 1)
    return builder[0];

  return builder;
}

void ProofManager::addAssertion(Expr formula) {
  Debug("proof:pm") << "assert: " << formula << std::endl;
  d_inputFormulas.insert(formula);
  std::ostringstream name;
  name << "A" << d_inputFormulaToName.size();
  d_inputFormulaToName[formula] = name.str();
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

void ProofManager::addAssertionFilter(const Node& node, const std::string& rewritten) {
  d_assertionFilters[node] = rewritten;
}

void ProofManager::setLogic(const LogicInfo& logic) {
  d_logic = logic;
}

LFSCProof::LFSCProof(SmtEngine* smtEngine,
                     CoreSatProof* sat,
                     LFSCCnfProof* cnf,
                     LFSCTheoryProofEngine* theory)
    : d_satProof(sat),
      d_cnfProof(cnf),
      d_theoryProof(theory),
      d_smtEngine(smtEngine)
{}

void LFSCProof::toStream(std::ostream& out, const ProofLetMap& map) const
{
  Unreachable();
}

void LFSCProof::toStream(std::ostream& out) const
{
  TimerStat::CodeTimer proofProductionTimer(
      ProofManager::currentPM()->getStats().d_proofProductionTime);

  IdToSatClause used_lemmas;
  IdToSatClause used_inputs;
  std::set<Node> atoms;
  NodePairSet rewrites;
  NodeSet used_assertions;

  {
    CodeTimer skeletonProofTimer{
        ProofManager::currentPM()->getStats().d_skeletonProofTraceTime};
    Assert(!d_satProof->proofConstructed());

    // Here we give our SAT solver a chance to flesh out the resolution proof.
    // It proves bottom from a set of clauses.
    d_satProof->constructProof();

    // We ask the SAT solver which clauses are used in that proof.
    // For a resolution proof, these are the leaves of the tree.
    d_satProof->collectClausesUsed(used_inputs, used_lemmas);

    IdToSatClause::iterator it2;
    Debug("pf::pm") << std::endl << "Used inputs: " << std::endl;
    for (it2 = used_inputs.begin(); it2 != used_inputs.end(); ++it2)
    {
      Debug("pf::pm") << "\t input = " << *(it2->second) << std::endl;
    }
    Debug("pf::pm") << std::endl;

    Debug("pf::pm") << std::endl << "Used lemmas: " << std::endl;
    for (it2 = used_lemmas.begin(); it2 != used_lemmas.end(); ++it2)
    {
      std::vector<Expr> clause_expr;
      for (unsigned i = 0; i < it2->second->size(); ++i)
      {
        prop::SatLiteral lit = (*(it2->second))[i];
        Expr atom = d_cnfProof->getAtom(lit.getSatVariable()).toExpr();
        if (atom.isConst())
        {
          Assert(atom == utils::mkTrue());
          continue;
        }
        Expr expr_lit = lit.isNegated() ? atom.notExpr() : atom;
        clause_expr.push_back(expr_lit);
      }

      Debug("pf::pm") << "\t lemma " << it2->first << " = " << *(it2->second)
                      << std::endl;
      Debug("pf::pm") << "\t";
      for (unsigned i = 0; i < clause_expr.size(); ++i)
      {
        Debug("pf::pm") << clause_expr[i] << " ";
      }
      Debug("pf::pm") << std::endl;
    }
    Debug("pf::pm") << std::endl;

    // collecting assertions that lead to the clauses being asserted
    d_cnfProof->collectAssertionsForClauses(used_inputs, used_assertions);

    NodeSet::iterator it3;
    Debug("pf::pm") << std::endl << "Used assertions: " << std::endl;
    for (it3 = used_assertions.begin(); it3 != used_assertions.end(); ++it3)
      Debug("pf::pm") << "\t assertion = " << *it3 << std::endl;

    // collects the atoms in the clauses
    d_cnfProof->collectAtomsAndRewritesForLemmas(used_lemmas, atoms, rewrites);

    if (!rewrites.empty())
    {
      Debug("pf::pm") << std::endl << "Rewrites used in lemmas: " << std::endl;
      NodePairSet::const_iterator rewriteIt;
      for (rewriteIt = rewrites.begin(); rewriteIt != rewrites.end();
           ++rewriteIt)
      {
        Debug("pf::pm") << "\t" << rewriteIt->first << " --> "
                        << rewriteIt->second << std::endl;
      }
      Debug("pf::pm") << std::endl << "Rewrite printing done" << std::endl;
    }
    else
    {
      Debug("pf::pm") << "No rewrites in lemmas found" << std::endl;
    }

    // The derived/unrewritten atoms may not have CNF literals required later
    // on. If they don't, add them.
    std::set<Node>::const_iterator it;
    for (it = atoms.begin(); it != atoms.end(); ++it)
    {
      Debug("pf::pm") << "Ensure literal for atom: " << *it << std::endl;
      if (!d_cnfProof->hasLiteral(*it))
      {
        // For arithmetic: these literals are not normalized, causing an error
        // in Arith.
        if (theory::Theory::theoryOf(*it) == theory::THEORY_ARITH)
        {
          d_cnfProof->ensureLiteral(
              *it,
              true);  // This disables preregistration with the theory solver.
        }
        else
        {
          d_cnfProof->ensureLiteral(
              *it);  // Normal method, with theory solver preregisteration.
        }
      }
    }

    // From the clauses, compute the atoms (atomic theory predicates in
    // assertions and lemmas).
    d_cnfProof->collectAtomsForClauses(used_inputs, atoms);
    d_cnfProof->collectAtomsForClauses(used_lemmas, atoms);

    // collects the atoms in the assertions
    for (TNode used_assertion : used_assertions)
    {
      utils::collectAtoms(used_assertion, atoms);
    }

    std::set<Node>::iterator atomIt;
    Debug("pf::pm") << std::endl
                    << "Dumping atoms from lemmas, inputs and assertions: "
                    << std::endl
                    << std::endl;
    for (atomIt = atoms.begin(); atomIt != atoms.end(); ++atomIt)
    {
      Debug("pf::pm") << "\tAtom: " << *atomIt << std::endl;
    }
  }

  smt::SmtScope scope(d_smtEngine);
  ProofLetMap globalLetMap;
  std::ostringstream paren;
  {
    CodeTimer declTimer{
        ProofManager::currentPM()->getStats().d_proofDeclarationsTime};
    out << "(check\n";
    paren << ")";
    out << " ;; Declarations\n";

    // declare the theory atoms
    Debug("pf::pm") << "LFSCProof::toStream: registering terms:" << std::endl;
    for (std::set<Node>::const_iterator it = atoms.begin(); it != atoms.end(); ++it)
    {
      Debug("pf::pm") << "\tTerm: " << (*it).toExpr() << std::endl;
      d_theoryProof->registerTerm((*it).toExpr());
    }

    Debug("pf::pm") << std::endl
                    << "Term registration done!" << std::endl
                    << std::endl;

    Debug("pf::pm") << std::endl
                    << "LFSCProof::toStream: starting to print assertions"
                    << std::endl;

    // print out all the original assertions
    d_theoryProof->registerTermsFromAssertions();
    d_theoryProof->printSortDeclarations(out, paren);
    d_theoryProof->printTermDeclarations(out, paren);
    d_theoryProof->printAssertions(out, paren);

    Debug("pf::pm") << std::endl
                    << "LFSCProof::toStream: print assertions DONE"
                    << std::endl;

    out << "(: (holds cln)\n\n";
    paren << ")";

    // Have the theory proofs print deferred declarations, e.g. for skolem
    // variables.
    out << " ;; Printing deferred declarations \n\n";
    d_theoryProof->printDeferredDeclarations(out, paren);

    out << "\n ;; Printing the global let map";
    d_theoryProof->finalizeBvConflicts(used_lemmas, out);
    ProofManager::getBitVectorProof()->calculateAtomsInBitblastingProof();
    if (options::lfscLetification())
    {
      ProofManager::currentPM()->printGlobalLetMap(
          atoms, globalLetMap, out, paren);
    }

    out << " ;; Printing aliasing declarations \n\n";
    d_theoryProof->printAliasingDeclarations(out, paren, globalLetMap);

    out << " ;; Rewrites for Lemmas \n";
    d_theoryProof->printLemmaRewrites(rewrites, out, paren);

    // print trust that input assertions are their preprocessed form
    printPreprocessedAssertions(used_assertions, out, paren, globalLetMap);
  }

  {
    CodeTimer cnfProofTimer{
        ProofManager::currentPM()->getStats().d_cnfProofTime};
    // print mapping between theory atoms and internal SAT variables
    out << ";; Printing mapping from preprocessed assertions into atoms \n";
    d_cnfProof->printAtomMapping(atoms, out, paren, globalLetMap);

    Debug("pf::pm") << std::endl
                    << "Printing cnf proof for clauses" << std::endl;

    IdToSatClause::const_iterator cl_it = used_inputs.begin();
    // print CNF conversion proof for each clause
    for (; cl_it != used_inputs.end(); ++cl_it)
    {
      d_cnfProof->printCnfProofForClause(
          cl_it->first, cl_it->second, out, paren);
    }
  }

  {
    CodeTimer theoryLemmaTimer{
        ProofManager::currentPM()->getStats().d_theoryLemmaTime};
    Debug("pf::pm") << std::endl
                    << "Printing cnf proof for clauses DONE" << std::endl;

    Debug("pf::pm") << "Proof manager: printing theory lemmas" << std::endl;
    d_theoryProof->printTheoryLemmas(used_lemmas, out, paren, globalLetMap);
    Debug("pf::pm") << "Proof manager: printing theory lemmas DONE!"
                    << std::endl;
  }

  {
    CodeTimer finalProofTimer{
        ProofManager::currentPM()->getStats().d_finalProofTime};
    out << ";; Printing final unsat proof \n";
    if (options::bitblastMode() == options::BitblastMode::EAGER
        && ProofManager::getBitVectorProof())
    {
      ProofManager::getBitVectorProof()->printEmptyClauseProof(out, paren);
    }
    else
    {
      // print actual resolution proof
      proof::LFSCProofPrinter::printResolutions(d_satProof, out, paren);
      proof::LFSCProofPrinter::printResolutionEmptyClause(
          d_satProof, out, paren);
    }
  }

  out << paren.str();
  out << "\n;;\n";
}

void LFSCProof::printPreprocessedAssertions(const NodeSet& assertions,
                                            std::ostream& os,
                                            std::ostream& paren,
                                            ProofLetMap& globalLetMap) const
{
  os << "\n ;; In the preprocessor we trust \n";
  NodeSet::const_iterator it = assertions.begin();
  NodeSet::const_iterator end = assertions.end();

  Debug("pf::pm") << "LFSCProof::printPreprocessedAssertions starting" << std::endl;

  if (options::fewerPreprocessingHoles()) {
    // Check for assertions that did not get rewritten, and update the printing filter.
    checkUnrewrittenAssertion(assertions);

    // For the remaining assertions, bind them to input assertions.
    for (; it != end; ++it) {
      // Rewrite preprocessing step if it cannot be eliminated
      if (!ProofManager::currentPM()->have_input_assertion((*it).toExpr())) {
        os << "(th_let_pf _ (trust_f (iff ";

        Expr inputAssertion;

        if (((*it).isConst() && *it == NodeManager::currentNM()->mkConst<bool>(true)) ||
            ((*it).getKind() == kind::NOT && (*it)[0] == NodeManager::currentNM()->mkConst<bool>(false))) {
          inputAssertion = NodeManager::currentNM()->mkConst<bool>(true).toExpr();
        } else {
          // Figure out which input assertion led to this assertion
          ExprSet inputAssertions;
          ProofManager::currentPM()->traceDeps(*it, &inputAssertions);

          Debug("pf::pm") << "Original assertions for " << *it << " are: " << std::endl;

          ProofManager::assertions_iterator assertionIt;
          for (assertionIt = inputAssertions.begin(); assertionIt != inputAssertions.end(); ++assertionIt) {
            Debug("pf::pm") << "\t" << *assertionIt << std::endl;
          }

          if (inputAssertions.size() == 0) {
            Debug("pf::pm") << "LFSCProof::printPreprocessedAssertions: Count NOT find the assertion that caused this PA. Picking an arbitrary one..." << std::endl;
            // For now just use the first assertion...
            inputAssertion = *(ProofManager::currentPM()->begin_assertions());
          } else {
            if (inputAssertions.size() != 1) {
              Debug("pf::pm") << "LFSCProof::printPreprocessedAssertions: Attention: more than one original assertion was found. Picking just one." << std::endl;
            }
            inputAssertion = *inputAssertions.begin();
          }
        }

        if (!ProofManager::currentPM()->have_input_assertion(inputAssertion)) {
          // The thing returned by traceDeps does not appear in the input assertions...
          Debug("pf::pm") << "LFSCProof::printPreprocessedAssertions: Count NOT find the assertion that caused this PA. Picking an arbitrary one..." << std::endl;
          // For now just use the first assertion...
          inputAssertion = *(ProofManager::currentPM()->begin_assertions());
        }

        Debug("pf::pm") << "Original assertion for " << *it
                        << " is: "
                        << inputAssertion
                        << ", AKA "
                        << ProofManager::currentPM()->getInputFormulaName(inputAssertion)
                        << std::endl;

        ProofManager::currentPM()->getTheoryProofEngine()->printTheoryTerm(inputAssertion, os, globalLetMap);
        os << " ";
        ProofManager::currentPM()->printTrustedTerm(*it, os, globalLetMap);
        os << "))";
        os << "(\\ "<< ProofManager::getPreprocessedAssertionName(*it, "") << "\n";
        paren << "))";

        std::ostringstream rewritten;

        rewritten << "(or_elim_1 _ _ ";
        rewritten << "(not_not_intro _ ";
        rewritten << ProofManager::currentPM()->getInputFormulaName(inputAssertion);
        rewritten << ") (iff_elim_1 _ _ ";
        rewritten << ProofManager::getPreprocessedAssertionName(*it, "");
        rewritten << "))";

        ProofManager::currentPM()->addAssertionFilter(*it, rewritten.str());
      }
    }
  } else {
    for (; it != end; ++it) {
      os << "(th_let_pf _ ";

      //TODO
      os << "(trust_f ";
      ProofManager::currentPM()->printTrustedTerm(*it, os, globalLetMap);
      os << ") ";

      os << "(\\ "<< ProofManager::getPreprocessedAssertionName(*it, "") << "\n";
      paren << "))";
    }
  }

  os << "\n";
}

void LFSCProof::checkUnrewrittenAssertion(const NodeSet& rewrites) const
{
  Debug("pf::pm") << "LFSCProof::checkUnrewrittenAssertion starting" << std::endl;

  NodeSet::const_iterator rewrite;
  for (rewrite = rewrites.begin(); rewrite != rewrites.end(); ++rewrite) {
    Debug("pf::pm") << "LFSCProof::checkUnrewrittenAssertion: handling " << *rewrite << std::endl;
    if (ProofManager::currentPM()->have_input_assertion((*rewrite).toExpr())) {
      Assert(
          ProofManager::currentPM()->have_input_assertion((*rewrite).toExpr()));
      Debug("pf::pm") << "LFSCProof::checkUnrewrittenAssertion: this assertion was NOT rewritten!" << std::endl
                      << "\tAdding filter: "
                      << ProofManager::getPreprocessedAssertionName(*rewrite, "")
                      << " --> "
                      << ProofManager::currentPM()->getInputFormulaName((*rewrite).toExpr())
                      << std::endl;
      ProofManager::currentPM()->addAssertionFilter(*rewrite,
        ProofManager::currentPM()->getInputFormulaName((*rewrite).toExpr()));
    } else {
      Debug("pf::pm") << "LFSCProof::checkUnrewrittenAssertion: this assertion WAS rewritten! " << *rewrite << std::endl;
    }
  }
}

//---from Morgan---

bool ProofManager::hasOp(TNode n) const {
  return d_bops.find(n) != d_bops.end();
}

Node ProofManager::lookupOp(TNode n) const {
  std::map<Node, Node>::const_iterator i = d_bops.find(n);
  Assert(i != d_bops.end());
  return (*i).second;
}

Node ProofManager::mkOp(TNode n) {
  Trace("mgd-pm-mkop") << "MkOp : " << n << " " << n.getKind() << std::endl;
  if(n.getKind() != kind::BUILTIN) {
    return n;
  }

  Node& op = d_ops[n];
  if(op.isNull()) {
    Assert((n.getConst<Kind>() == kind::SELECT)
           || (n.getConst<Kind>() == kind::STORE));

    Debug("mgd-pm-mkop") << "making an op for " << n << "\n";

    std::stringstream ss;
    ss << n;
    std::string s = ss.str();
    Debug("mgd-pm-mkop") << " : " << s << std::endl;
    std::vector<TypeNode> v;
    v.push_back(NodeManager::currentNM()->integerType());
    if(n.getConst<Kind>() == kind::SELECT) {
      v.push_back(NodeManager::currentNM()->integerType());
      v.push_back(NodeManager::currentNM()->integerType());
    } else if(n.getConst<Kind>() == kind::STORE) {
      v.push_back(NodeManager::currentNM()->integerType());
      v.push_back(NodeManager::currentNM()->integerType());
      v.push_back(NodeManager::currentNM()->integerType());
    }
    TypeNode type = NodeManager::currentNM()->mkFunctionType(v);
    Debug("mgd-pm-mkop") << "typenode is: " << type << "\n";
    op = NodeManager::currentNM()->mkSkolem(s, type, " ignore", NodeManager::SKOLEM_NO_NOTIFY);
    d_bops[op] = n;
  }
  Debug("mgd-pm-mkop") << "returning the op: " << op << "\n";
  return op;
}
//---end from Morgan---

bool ProofManager::wasPrinted(const Type& type) const {
  return d_printedTypes.find(type) != d_printedTypes.end();
}

void ProofManager::markPrinted(const Type& type) {
  d_printedTypes.insert(type);
}

void ProofManager::addRewriteFilter(const std::string &original, const std::string &substitute) {
  d_rewriteFilters[original] = substitute;
}

bool ProofManager::haveRewriteFilter(TNode lit) {
  std::string litName = getLitName(currentPM()->d_cnfProof->getLiteral(lit));
  return d_rewriteFilters.find(litName) != d_rewriteFilters.end();
}

void ProofManager::clearRewriteFilters() {
  d_rewriteFilters.clear();
}

std::ostream& operator<<(std::ostream& out, CVC4::ProofRule k) {
  switch(k) {
  case RULE_GIVEN:
    out << "RULE_GIVEN";
    break;
  case RULE_DERIVED:
    out << "RULE_DERIVED";
    break;
  case RULE_RECONSTRUCT:
    out << "RULE_RECONSTRUCT";
    break;
  case RULE_TRUST:
    out << "RULE_TRUST";
    break;
  case RULE_INVALID:
    out << "RULE_INVALID";
    break;
  case RULE_CONFLICT:
    out << "RULE_CONFLICT";
    break;
  case RULE_TSEITIN:
    out << "RULE_TSEITIN";
    break;
  case RULE_SPLIT:
    out << "RULE_SPLIT";
    break;
  case RULE_ARRAYS_EXT:
    out << "RULE_ARRAYS";
    break;
  case RULE_ARRAYS_ROW:
    out << "RULE_ARRAYS";
    break;
  default:
    out << "ProofRule Unknown! [" << unsigned(k) << "]";
  }

  return out;
}

void ProofManager::registerRewrite(unsigned ruleId, Node original, Node result){
  Assert(currentPM()->d_theoryProof != NULL);
  currentPM()->d_rewriteLog.push_back(RewriteLogEntry(ruleId, original, result));
}

void ProofManager::clearRewriteLog() {
  Assert(currentPM()->d_theoryProof != NULL);
  currentPM()->d_rewriteLog.clear();
}

std::vector<RewriteLogEntry> ProofManager::getRewriteLog() {
  return currentPM()->d_rewriteLog;
}

void ProofManager::dumpRewriteLog() const {
  Debug("pf::rr") << "Dumpign rewrite log:" << std::endl;

  for (unsigned i = 0; i < d_rewriteLog.size(); ++i) {
    Debug("pf::rr") << "\tRule " << d_rewriteLog[i].getRuleId()
                    << ": "
                    << d_rewriteLog[i].getOriginal()
                    << " --> "
                    << d_rewriteLog[i].getResult() << std::endl;
  }
}

void bind(Expr term, ProofLetMap& map, Bindings& letOrder) {
  ProofLetMap::iterator it = map.find(term);
  if (it != map.end())
    return;

  for (unsigned i = 0; i < term.getNumChildren(); ++i)
    bind(term[i], map, letOrder);

  // Special case: chain operators. If we have and(a,b,c), it will be prineted as and(a,and(b,c)).
  // The subterm and(b,c) may repeat elsewhere, so we need to bind it, too.
  Kind k = term.getKind();
  if (((k == kind::OR) || (k == kind::AND)) && term.getNumChildren() > 2) {
    Node currentExpression = term[term.getNumChildren() - 1];
    for (int i = term.getNumChildren() - 2; i >= 0; --i) {
      NodeBuilder<> builder(k);
      builder << term[i];
      builder << currentExpression.toExpr();
      currentExpression = builder;
      bind(currentExpression.toExpr(), map, letOrder);
    }
  } else {
    unsigned newId = ProofLetCount::newId();
    ProofLetCount letCount(newId);
    map[term] = letCount;
    letOrder.push_back(LetOrderElement(term, newId));
  }
}

void ProofManager::printGlobalLetMap(std::set<Node>& atoms,
                                     ProofLetMap& letMap,
                                     std::ostream& out,
                                     std::ostringstream& paren) {
  Bindings letOrder;
  std::set<Node>::const_iterator atom;
  for (atom = atoms.begin(); atom != atoms.end(); ++atom) {
    bind(atom->toExpr(), letMap, letOrder);
  }

  // TODO: give each theory a chance to add atoms. For now, just query BV directly...
  const std::set<Node>* additionalAtoms = ProofManager::getBitVectorProof()->getAtomsInBitblastingProof();
  for (atom = additionalAtoms->begin(); atom != additionalAtoms->end(); ++atom) {
    bind(atom->toExpr(), letMap, letOrder);
  }

  for (unsigned i = 0; i < letOrder.size(); ++i) {
    Expr currentExpr = letOrder[i].expr;
    unsigned letId = letOrder[i].id;
    ProofLetMap::iterator it = letMap.find(currentExpr);
    Assert(it != letMap.end());
    out << "\n(@ let" << letId << " ";
    d_theoryProof->printBoundTerm(currentExpr, out, letMap);
    paren << ")";
    it->second.increment();
  }

  out << std::endl << std::endl;
}

void ProofManager::ensureLiteral(Node node) {
  d_cnfProof->ensureLiteral(node);
}
void ProofManager::printTrustedTerm(Node term,
                                    std::ostream& os,
                                    ProofLetMap& globalLetMap)
{
  TheoryProofEngine* tpe = ProofManager::currentPM()->getTheoryProofEngine();
  if (tpe->printsAsBool(term)) os << "(p_app ";
  tpe->printTheoryTerm(term.toExpr(), os, globalLetMap);
  if (tpe->printsAsBool(term)) os << ")";
}

ProofManager::ProofManagerStatistics::ProofManagerStatistics()
    : d_proofProductionTime("proof::ProofManager::proofProductionTime"),
      d_theoryLemmaTime(
          "proof::ProofManager::proofProduction::theoryLemmaTime"),
      d_skeletonProofTraceTime(
          "proof::ProofManager::proofProduction::skeletonProofTraceTime"),
      d_proofDeclarationsTime(
          "proof::ProofManager::proofProduction::proofDeclarationsTime"),
      d_cnfProofTime("proof::ProofManager::proofProduction::cnfProofTime"),
      d_finalProofTime("proof::ProofManager::proofProduction::finalProofTime")
{
  smtStatisticsRegistry()->registerStat(&d_proofProductionTime);
  smtStatisticsRegistry()->registerStat(&d_theoryLemmaTime);
  smtStatisticsRegistry()->registerStat(&d_skeletonProofTraceTime);
  smtStatisticsRegistry()->registerStat(&d_proofDeclarationsTime);
  smtStatisticsRegistry()->registerStat(&d_cnfProofTime);
  smtStatisticsRegistry()->registerStat(&d_finalProofTime);
}

ProofManager::ProofManagerStatistics::~ProofManagerStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_proofProductionTime);
  smtStatisticsRegistry()->unregisterStat(&d_theoryLemmaTime);
  smtStatisticsRegistry()->unregisterStat(&d_skeletonProofTraceTime);
  smtStatisticsRegistry()->unregisterStat(&d_proofDeclarationsTime);
  smtStatisticsRegistry()->unregisterStat(&d_cnfProofTime);
  smtStatisticsRegistry()->unregisterStat(&d_finalProofTime);
}

} /* CVC4  namespace */
