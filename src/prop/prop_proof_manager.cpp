/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the proof manager for the PropPfManager.
 */

#include "prop/prop_proof_manager.h"

#include "expr/skolem_manager.h"
#include "options/main_options.h"
#include "printer/printer.h"
#include "proof/proof_ensure_closed.h"
#include "proof/proof_node_algorithm.h"
#include "proof/theory_proof_step_buffer.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/sat_proof_manager.h"
#include "prop/prop_proof_manager.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "smt/env.h"
#include "util/string.h"

namespace cvc5::internal {
namespace prop {

PropPfManager::PropPfManager(Env& env,
                             CDCLTSatSolver* satSolver,
                             CnfStream& cnf,
                             const context::CDList<Node>& assumptions)
    : EnvObj(env),
      d_propProofs(userContext()),
      // Since the ProofCnfStream performs no equality reasoning, there is no
      // need to automatically add symmetry steps. Note that it is *safer* to
      // forbid this, since adding symmetry steps when proof nodes are being
      // updated may inadvertently generate cyclic proofs.
      //
      // This can happen for example if the proof cnf stream has a generator for
      // (= a b), whose proof depends on symmetry applied to (= b a). It does
      // not have a generator for (= b a). However if asked for a proof of the
      // fact (= b a) (after having expanded the proof of (= a b)), since it has
      // no genarotor for (= b a), a proof (= b a) can be generated via symmetry
      // on the proof of (= a b). As a result the assumption (= b a) would be
      // assigned a proof with assumption (= b a). This breakes the invariant of
      // the proof node manager of no cyclic proofs if the ASSUMPTION proof node
      // of both the assumption (= b a) we are asking the proof for and the
      // assumption (= b a) in the proof of (= a b) are the same.
      d_proof(
          env, nullptr, userContext(), "ProofCnfStream::LazyCDProof", false),
      d_pfpp(new ProofPostprocess(env, &d_proof)),
      d_pfCnfStream(env, cnf, this),
      d_satSolver(satSolver),
      d_assertions(userContext()),
      d_cnfStream(cnf),
      d_assumptions(assumptions),
      d_inputClauses(userContext()),
      d_lemmaClauses(userContext()),
      d_satPm(nullptr)
{
  // add trivial assumption. This is so that we can check the that the prop
  // engine's proof is closed, as the SAT solver's refutation proof may use True
  // as an assumption even when True is not given as an assumption. An example
  // is when a propagated literal has an empty explanation (i.e., it is a valid
  // literal), which leads to adding True as its explanation, since for creating
  // a learned clause we need at least two literals.
  d_assertions.push_back(nodeManager()->mkConst(true));
}

void PropPfManager::ensureLiteral(TNode n) { d_pfCnfStream.ensureLiteral(n); }

void PropPfManager::convertAndAssert(theory::InferenceId id,
                                     TNode node,
                                     bool negated,
                                     bool removable,
                                     bool input,
                                     ProofGenerator* pg)
{
  d_pfCnfStream.convertAndAssert(node, negated, removable, input, pg);
  // if input, register the assertion in the proof manager
  if (input)
  {
    d_assertions.push_back(node);
  }
}

void PropPfManager::registerAssertion(Node assertion)
{
  d_assertions.push_back(assertion);
}

void PropPfManager::checkProof(const context::CDList<Node>& assertions)
{
  Trace("sat-proof") << "PropPfManager::checkProof: Checking if resolution "
                        "proof of false is closed\n";
  std::shared_ptr<ProofNode> conflictProof = getProof(false);
  Assert(conflictProof);
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  // add given assertions d_assertions
  for (const Node& assertion : assertions)
  {
    d_assertions.push_back(assertion);
  }
  std::vector<Node> avec{d_assertions.begin(), d_assertions.end()};
  pfnEnsureClosedWrt(options(),
                     conflictProof.get(),
                     avec,
                     "sat-proof",
                     "PropPfManager::checkProof");
}

std::vector<Node> PropPfManager::getUnsatCoreLemmas()
{
  std::vector<Node> usedLemmas;
  std::vector<Node> allLemmas = getLemmaClauses();
  // compute the unsat core clauses, as below
  std::vector<Node> ucc = getUnsatCoreClauses();
  Trace("prop-pf") << "Compute unsat core lemmas from " << ucc.size()
                   << " clauses (of " << allLemmas.size() << " lemmas)"
                   << std::endl;
  Trace("prop-pf") << "lemmas: " << allLemmas << std::endl;
  Trace("prop-pf") << "uc: " << ucc << std::endl;
  // filter to only those corresponding to lemmas
  for (const Node& lemma : allLemmas)
  {
    if (std::find(ucc.begin(), ucc.end(), lemma) != ucc.end())
    {
      usedLemmas.push_back(lemma);
    }
  }
  return usedLemmas;
}

std::vector<Node> PropPfManager::getMinimizedAssumptions()
{
  std::vector<Node> minAssumptions;
  std::vector<SatLiteral> unsatAssumptions;
  d_satSolver->getUnsatAssumptions(unsatAssumptions);
  for (const Node& nc : d_assumptions)
  {
    if (nc.isConst())
    {
      if (nc.getConst<bool>())
      {
        // never include true
        continue;
      }
      minAssumptions.clear();
      minAssumptions.push_back(nc);
      return minAssumptions;
    }
    else if (d_pfCnfStream.hasLiteral(nc))
    {
      SatLiteral il = d_pfCnfStream.getLiteral(nc);
      if (std::find(unsatAssumptions.begin(), unsatAssumptions.end(), il)
          == unsatAssumptions.end())
      {
        continue;
      }
    }
    else
    {
      Assert(false) << "Missing literal for assumption " << nc;
    }
    minAssumptions.push_back(nc);
  }
  return minAssumptions;
}

std::vector<Node> PropPfManager::getUnsatCoreClauses(std::ostream* outDimacs)
{
  std::vector<Node> uc;
  // if it has a proof
  std::shared_ptr<ProofNode> satPf = d_satSolver->getProof();
  if (satPf != nullptr)
  {
    // then, get the proof *without* connecting the CNF
    expr::getFreeAssumptions(satPf.get(), uc);
    if (outDimacs != nullptr)
    {
      std::vector<Node> auxUnits = computeAuxiliaryUnits(uc);
      d_pfCnfStream.dumpDimacs(*outDimacs, uc, auxUnits);
      // include the auxiliary units if any
      uc.insert(uc.end(), auxUnits.begin(), auxUnits.end());
    }
    return uc;
  }
  // otherwise we need to compute it
  // as a minor optimization, we use only minimized assumptions
  std::vector<Node> minAssumptions = getMinimizedAssumptions();
  std::unordered_set<Node> cset(minAssumptions.begin(), minAssumptions.end());
  std::vector<Node> inputs = getInputClauses();
  std::vector<Node> lemmas = getLemmaClauses();
  cset.insert(inputs.begin(), inputs.end());
  cset.insert(lemmas.begin(), lemmas.end());
  if (!reproveUnsatCore(cset, uc, outDimacs))
  {
    // otherwise, must include all
    return getLemmaClauses();
  }
  return uc;
}

bool PropPfManager::reproveUnsatCore(const std::unordered_set<Node>& cset,
                                     std::vector<Node>& uc,
                                     std::ostream* outDimacs)
{
  std::unique_ptr<CDCLTSatSolver> csm(SatSolverFactory::createCadical(
      d_env, statisticsRegistry(), d_env.getResourceManager(), ""));
  NullRegistrar nreg;
  context::Context nctx;
  CnfStream csms(d_env, csm.get(), &nreg, &nctx);
  Trace("cnf-input-min") << "Get literals..." << std::endl;
  std::vector<SatLiteral> csma;
  std::map<SatLiteral, Node> litToNode;
  std::map<SatLiteral, Node> litToNodeAbs;
  NodeManager* nm = NodeManager::currentNM();
  TypeNode bt = nm->booleanType();
  TypeNode ft = nm->mkFunctionType({bt}, bt);
  SkolemManager* skm = nm->getSkolemManager();
  // Function used to ensure that subformulas are not treated by CNF below.
  Node litOf = skm->mkDummySkolem("litOf", ft);
  for (const Node& c : cset)
  {
    Node ca = c;
    std::vector<SatLiteral> satClause;
    std::vector<Node> lits;
    if (c.getKind() == Kind::OR)
    {
      lits.insert(lits.end(), c.begin(), c.end());
    }
    else
    {
      lits.push_back(c);
    }
    // For each literal l in the current clause, if it has Boolean
    // substructure, we replace it with (litOf l), which will be treated as a
    // literal. We do this since we require that the clause be treated
    // verbatim by the SAT solver, otherwise the unsat core will not include
    // the necessary clauses (e.g. it will skip those corresponding to CNF
    // conversion).
    std::vector<Node> cls;
    bool childChanged = false;
    for (const Node& cl : lits)
    {
      bool negated = cl.getKind() == Kind::NOT;
      Node cla = negated ? cl[0] : cl;
      if (d_env.theoryOf(cla) == theory::THEORY_BOOL && !cla.isVar())
      {
        Node k = nm->mkNode(Kind::APPLY_UF, {litOf, cla});
        cls.push_back(negated ? k.notNode() : k);
        childChanged = true;
      }
      else
      {
        cls.push_back(cl);
      }
    }
    if (childChanged)
    {
      ca = nm->mkOr(cls);
    }
    Trace("cnf-input-min-assert") << "Assert: " << ca << std::endl;
    csms.ensureLiteral(ca);
    SatLiteral lit = csms.getLiteral(ca);
    csma.emplace_back(lit);
    litToNode[lit] = c;
    litToNodeAbs[lit] = ca;
  }
  Trace("cnf-input-min") << "Solve under " << csma.size() << " assumptions..."
                         << std::endl;
  SatValue res = csm->solve(csma);
  bool success = false;
  if (res == SAT_VALUE_FALSE)
  {
    // we successfully reproved the input
    Trace("cnf-input-min") << "...got unsat" << std::endl;
    std::vector<SatLiteral> uassumptions;
    csm->getUnsatAssumptions(uassumptions);
    Trace("cnf-input-min") << "...#unsat assumptions=" << uassumptions.size()
                           << std::endl;
    std::vector<Node> aclauses;
    for (const SatLiteral& lit : uassumptions)
    {
      Assert(litToNode.find(lit) != litToNode.end());
      Trace("cnf-input-min-result")
          << "assert: " << litToNode[lit] << std::endl;
      uc.emplace_back(litToNode[lit]);
      aclauses.emplace_back(litToNodeAbs[lit]);
    }
    if (outDimacs)
    {
      // dump using the CNF stream we created above
      csms.dumpDimacs(*outDimacs, aclauses);
    }
    success = true;
  }
  // should never happen, if it does, we revert to the entire input
  Trace("cnf-input-min") << "...got sat" << std::endl;
  Assert(success) << "Failed to minimize DIMACS";
  return success;
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getProofLeaves(
    modes::ProofComponent pc)
{
  Trace("sat-proof") << "PropPfManager::getProofLeaves: Getting " << pc
                     << " component proofs\n";
  std::vector<Node> fassumps;
  Assert(pc == modes::ProofComponent::THEORY_LEMMAS
         || pc == modes::ProofComponent::PREPROCESS);
  std::vector<std::shared_ptr<ProofNode>> pfs =
      pc == modes::ProofComponent::THEORY_LEMMAS ? getLemmaClausesProofs()
                                                 : getInputClausesProofs();
  std::shared_ptr<ProofNode> satPf = getProof(false);
  std::vector<Node> satLeaves;
  expr::getFreeAssumptions(satPf.get(), satLeaves);
  std::vector<std::shared_ptr<ProofNode>> usedPfs;
  for (const std::shared_ptr<ProofNode>& pf : pfs)
  {
    Node proven = pf->getResult();
    if (std::find(satLeaves.begin(), satLeaves.end(), proven) != satLeaves.end())
    {
      usedPfs.push_back(pf);
    }
  }
  return usedPfs;
}

std::shared_ptr<ProofNode> PropPfManager::getProof(bool connectCnf)
{
  auto it = d_propProofs.find(connectCnf);
  if (it != d_propProofs.end())
  {
    return it->second;
  }
  // retrieve the SAT solver's refutation proof
  Trace("sat-proof") << "PropPfManager::getProof: Getting proof of false\n";

  // get the proof based on the proof mode
  options::PropProofMode pmode = options().proof.propProofMode;
  std::shared_ptr<ProofNode> conflictProof;
  if (pmode == options::PropProofMode::PROOF)
  {
    // take proof from SAT solver as is
    conflictProof = d_satSolver->getProof();
  }
  else
  {
    // set up a proof and get the internal proof
    CDProof cdp(d_env);
    getProofInternal(&cdp);
    Node falsen = NodeManager::currentNM()->mkConst(false);
    conflictProof = cdp.getProofFor(falsen);
  }

  Assert(conflictProof);
  if (TraceIsOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: initial free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
    Trace("sat-proof")
        << "PropPfManager::getProof: Connecting with CNF proof\n";
  }
  if (!connectCnf)
  {
    d_propProofs[connectCnf] = conflictProof;
    return conflictProof;
  }
  // Must clone if we are using the original proof, since we don't want to
  // modify the original SAT proof.
  if (pmode == options::PropProofMode::PROOF)
  {
    conflictProof = conflictProof->clone();
  }
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  if (TraceIsOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: new free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof") << "PropPfManager::getProof: assertions are:\n";
    for (const Node& a : d_assertions)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
  }
  d_propProofs[connectCnf] = conflictProof;
  return conflictProof;
}

Node PropPfManager::normalizeAndRegister(TNode clauseNode,
                                         bool input,
                                         bool doNormalize)
{
  Node normClauseNode = clauseNode;
  if (doNormalize)
  {
    TheoryProofStepBuffer psb;
    normClauseNode = psb.factorReorderElimDoubleNeg(clauseNode);
    const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
    for (const std::pair<Node, ProofStep>& step : steps)
    {
      d_proof.addStep(step.first, step.second);
    }
  }
  if (TraceIsOn("cnf") && normClauseNode != clauseNode)
  {
    Trace("cnf") << push
                 << "ProofCnfStream::normalizeAndRegister: steps to normalized "
                 << normClauseNode << "\n"
                 << pop;
  }
  Trace("cnf-input") << "New clause: " << normClauseNode << " " << input
                     << std::endl;
  if (input)
  {
    d_inputClauses.insert(normClauseNode);
  }
  else
  {
    d_lemmaClauses.insert(normClauseNode);
  }
  if (d_satPm)
  {
    d_satPm->registerSatAssumptions({normClauseNode});
  }
  return normClauseNode;
}

LazyCDProof* PropPfManager::getCnfProof() { return &d_proof; }

void PropPfManager::getProofInternal(CDProof* cdp)
{
  // This method is called when the SAT solver did not generate a fully self
  // contained ProofNode proving false. This method adds a step to cdp
  // based on a set of computed assumptions, possibly relying on the internal
  // proof.
  NodeManager* nm = NodeManager::currentNM();
  Node falsen = nm->mkConst(false);
  std::vector<Node> clauses;
  // deduplicate assumptions
  Trace("cnf-input") << "#assumptions=" << d_assumptions.size() << std::endl;
  std::vector<Node> minAssumptions = getMinimizedAssumptions();
  if (minAssumptions.size() == 1 && minAssumptions[0] == falsen)
  {
    // if false exists, no proof is necessary
    return;
  }
  std::unordered_set<Node> cset(minAssumptions.begin(), minAssumptions.end());
  Trace("cnf-input") << "#assumptions (min)=" << cset.size() << std::endl;
  std::vector<Node> inputs = getInputClauses();
  Trace("cnf-input") << "#input=" << inputs.size() << std::endl;
  std::vector<Node> lemmas = getLemmaClauses();
  Trace("cnf-input") << "#lemmas=" << lemmas.size() << std::endl;
  cset.insert(inputs.begin(), inputs.end());
  cset.insert(lemmas.begin(), lemmas.end());

  // Otherwise, we will dump a DIMACS. The proof further depends on the
  // mode, which we handle below.
  std::stringstream dinputFile;
  dinputFile << options().driver.filename << ".drat_input.cnf";
  // the stream which stores the DIMACS of the computed clauses
  std::fstream dout(dinputFile.str(), std::ios::out);
  options::PropProofMode pmode = options().proof.propProofMode;
  // minimize only if SAT_EXTERNAL_PROVE and satProofMinDimacs is true.
  bool minimal = (pmode == options::PropProofMode::SAT_EXTERNAL_PROVE
                  && options().proof.satProofMinDimacs);
  // go back and minimize assumptions if minimal is true
  bool computedClauses = false;
  if (minimal)
  {
    // get the unsat core clauses
    std::shared_ptr<ProofNode> satPf = d_satSolver->getProof();
    if (satPf != nullptr)
    {
      clauses = getUnsatCoreClauses(&dout);
      computedClauses = true;
    }
    else if (reproveUnsatCore(cset, clauses, &dout))
    {
      computedClauses = true;
    }
    else
    {
      // failed to reprove
    }
  }
  // if we did not minimize, just include all
  if (!computedClauses)
  {
    // if no minimization is necessary, just include all
    clauses.insert(clauses.end(), cset.begin(), cset.end());
    std::vector<Node> auxUnits = computeAuxiliaryUnits(clauses);
    d_pfCnfStream.dumpDimacs(dout, clauses, auxUnits);
    // include the auxiliary units if any
    clauses.insert(clauses.end(), auxUnits.begin(), auxUnits.end());
  }
  // construct the proof
  std::vector<Node> args;
  Node dfile = nm->mkConst(String(dinputFile.str()));
  args.push_back(dfile);
  ProofRule r = ProofRule::UNKNOWN;
  if (pmode == options::PropProofMode::SKETCH)
  {
    // if sketch, get the rule and arguments from the SAT solver.
    std::pair<ProofRule, std::vector<Node>> sk = d_satSolver->getProofSketch();
    r = sk.first;
    args.insert(args.end(), sk.second.begin(), sk.second.end());
  }
  else if (pmode == options::PropProofMode::SAT_EXTERNAL_PROVE)
  {
    // if SAT_EXTERNAL_PROVE, the rule is fixed and there are no additional
    // arguments.
    r = ProofRule::SAT_EXTERNAL_PROVE;
  }
  else
  {
    Assert(false) << "Unknown proof mode " << pmode;
  }
  // use the rule, clauses and arguments we computed above
  cdp->addStep(falsen, r, clauses, args);
}

std::vector<Node> PropPfManager::computeAuxiliaryUnits(
    const std::vector<Node>& clauses)
{
  std::vector<Node> auxUnits;
  for (const Node& c : clauses)
  {
    if (c.getKind() != Kind::OR)
    {
      continue;
    }
    // Determine if any OR child occurs as a top level clause. If so, it may
    // be relevant to include this as a unit clause.
    for (const Node& l : c)
    {
      const Node& atom = l.getKind() == Kind::NOT ? l[0] : l;
      if (atom.getKind() == Kind::OR
          && std::find(clauses.begin(), clauses.end(), atom) != clauses.end()
          && std::find(auxUnits.begin(), auxUnits.end(), atom)
                 == auxUnits.end())
      {
        auxUnits.push_back(atom);
      }
    }
  }
  return auxUnits;
}

std::vector<Node> PropPfManager::getInputClauses()
{
  std::vector<Node> cls;
  for (const Node& c : d_inputClauses)
  {
    cls.push_back(c);
  }
  return cls;
}

std::vector<Node> PropPfManager::getLemmaClauses()
{
  std::vector<Node> cls;
  for (const Node& c : d_lemmaClauses)
  {
    cls.push_back(c);
  }
  return cls;
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getInputClausesProofs()
{
  std::vector<std::shared_ptr<ProofNode>> pfs;
  for (const Node& a : d_inputClauses)
  {
    pfs.push_back(d_proof.getProofFor(a));
  }
  return pfs;
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getLemmaClausesProofs()
{
  std::vector<std::shared_ptr<ProofNode>> pfs;
  for (const Node& a : d_lemmaClauses)
  {
    pfs.push_back(d_proof.getProofFor(a));
  }
  return pfs;
}

void PropPfManager::notifyExplainedPropagation(TrustNode trn)
{
  Node proven = trn.getProven();
  // If we are not producing proofs in the theory engine there is no need to
  // keep track in d_proof of the clausification. We still need however to let
  // the SAT proof manager know that this clause is an assumption.
  bool proofLogging = trn.getGenerator() != nullptr;
  Trace("cnf")
      << "PropPfManager::notifyExplainedPropagation: proven explanation"
      << proven << ", proofLogging=" << proofLogging << "\n";
  if (proofLogging)
  {
    Assert(trn.getGenerator()->getProofFor(proven)->isClosed());
    Trace("cnf-steps") << proven << " by explainPropagation "
                       << trn.identifyGenerator() << std::endl;
    d_proof.addLazyStep(proven,
                        trn.getGenerator(),
                        TrustId::NONE,
                        true,
                        "PropPfManager::notifyExplainedPropagation");
  }
  // since the propagation is added directly to the SAT solver via theoryProxy,
  // do the transformation of the lemma E1 ^ ... ^ En => P into CNF here
  NodeManager* nm = nodeManager();
  Node clauseImpliesElim;
  if (proofLogging)
  {
    clauseImpliesElim = nm->mkNode(Kind::OR, proven[0].notNode(), proven[1]);
    Trace("cnf") << "PropPfManager::notifyExplainedPropagation: adding "
                 << ProofRule::IMPLIES_ELIM << " rule to conclude "
                 << clauseImpliesElim << "\n";
    d_proof.addStep(clauseImpliesElim, ProofRule::IMPLIES_ELIM, {proven}, {});
  }
  Node clauseExp;
  // need to eliminate AND
  if (proven[0].getKind() == Kind::AND)
  {
    std::vector<Node> disjunctsAndNeg{proven[0]};
    std::vector<Node> disjunctsRes;
    for (unsigned i = 0, size = proven[0].getNumChildren(); i < size; ++i)
    {
      disjunctsAndNeg.push_back(proven[0][i].notNode());
      disjunctsRes.push_back(proven[0][i].notNode());
    }
    disjunctsRes.push_back(proven[1]);
    clauseExp = nm->mkNode(Kind::OR, disjunctsRes);
    if (proofLogging)
    {
      // add proof steps to convert into clause
      Node clauseAndNeg = nm->mkNode(Kind::OR, disjunctsAndNeg);
      d_proof.addStep(clauseAndNeg, ProofRule::CNF_AND_NEG, {}, {proven[0]});
      d_proof.addStep(clauseExp,
                      ProofRule::RESOLUTION,
                      {clauseAndNeg, clauseImpliesElim},
                      {nm->mkConst(true), proven[0]});
    }
  }
  else
  {
    clauseExp = nm->mkNode(Kind::OR, proven[0].notNode(), proven[1]);
  }
  d_currPropagationProcessed = normalizeAndRegister(clauseExp, false);
  // If we are not logging the clausification, we need to add the clause, as *it
  // will be saved in the SAT solver* (i.e., as clauseExp), as closed step in
  // the d_proof, so that there are no non-input assumptions.
  if (!proofLogging)
  {
    d_proof.addTrustedStep(clauseExp, TrustId::THEORY_LEMMA, {}, {clauseExp});
  }
}

Node PropPfManager::getLastExplainedPropagation() const
{
  return d_currPropagationProcessed;
}

void PropPfManager::resetLastExplainedPropagation()
{
  d_currPropagationProcessed = Node::null();
}

}  // namespace prop
}  // namespace cvc5::internal
