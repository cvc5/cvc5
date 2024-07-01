/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the unsat core manager of SolverEngine.
 */

#include "unsat_core_manager.h"

#include <sstream>

#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "printer/printer.h"
#include "proof/proof.h"
#include "proof/proof_node_algorithm.h"
#include "prop/prop_engine.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/print_benchmark.h"
#include "smt/set_defaults.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {
namespace smt {

UnsatCoreManager::UnsatCoreManager(Env& env, SmtSolver& slv, PfManager& pfm)
    : EnvObj(env), d_slv(slv), d_pfm(pfm)
{
}

std::vector<Node> UnsatCoreManager::getUnsatCore(bool isInternal)
{
  prop::PropEngine* pe = d_slv.getPropEngine();
  Assert(pe != nullptr);
  // first get the unsat core from the prop engine
  std::vector<Node> pcore;
  pe->getUnsatCore(pcore);
  // convert to input
  return convertPreprocessedToInput(pcore, isInternal);
}

std::vector<Node> UnsatCoreManager::getUnsatCoreLemmas(bool isInternal)
{
  prop::PropEngine* pe = d_slv.getPropEngine();
  Assert(pe != nullptr);
  std::vector<Node> coreLemmas = pe->getUnsatCoreLemmas();
  // output benchmark if specified
  if (!isInternal)
  {
    if (isOutputOn(OutputTag::UNSAT_CORE_LEMMAS_BENCHMARK))
    {
      // also must compute the unsat core of input
      std::vector<Node> core = getUnsatCore(true);
      std::vector<Node> coreAsserts;
      std::vector<Node> coreDefs;
      partitionUnsatCore(core, coreDefs, coreAsserts);
      coreAsserts.insert(
          coreAsserts.end(), coreLemmas.begin(), coreLemmas.end());
      std::stringstream ss;
      smt::PrintBenchmark pb(Printer::getPrinter(ss));
      pb.printBenchmark(
          ss, logicInfo().getLogicString(), coreDefs, coreAsserts);
      output(OutputTag::UNSAT_CORE_LEMMAS_BENCHMARK) << ";; unsat core + lemmas" << std::endl;
      output(OutputTag::UNSAT_CORE_LEMMAS_BENCHMARK) << ss.str();
      output(OutputTag::UNSAT_CORE_LEMMAS_BENCHMARK) << ";; end unsat core + lemmas" << std::endl;
    }
  }
  return coreLemmas;
}

void UnsatCoreManager::getUnsatCoreInternal(std::shared_ptr<ProofNode> pfn,
                                            std::vector<Node>& core,
                                            bool isInternal)
{
  const Assertions& as = d_slv.getAssertions();
  Trace("unsat-core") << "UCManager::getUnsatCore: final proof: " << *pfn.get()
                      << "\n";
  Assert(pfn->getRule() == ProofRule::SCOPE);
  std::vector<Node> fassumps;
  expr::getFreeAssumptions(pfn->getChildren()[0].get(), fassumps);
  Trace("unsat-core") << "UCManager::getUnsatCore: free assumptions: "
                      << fassumps << "\n";
  const context::CDList<Node>& al = as.getAssertionList();
  std::set<Node> coreSet;
  for (const Node& a : al)
  {
    Trace("unsat-core") << "is assertion " << a << " there?\n";
    if (std::find(fassumps.begin(), fassumps.end(), a) != fassumps.end())
    {
      Trace("unsat-core") << "\tyes\n";
      coreSet.insert(a);
    }
  }
  core.insert(core.end(), coreSet.begin(), coreSet.end());
  if (TraceIsOn("unsat-core"))
  {
    Trace("unsat-core") << "UCManager::getUnsatCore():\n";
    for (const Node& n : core)
    {
      Trace("unsat-core") << "- " << n << "\n";
    }
  }
  // reduce it if specified
  if (options().smt.minimalUnsatCores)
  {
    core = reduceUnsatCore(as, core);
  }
  // don't postprocess if this was an internal call
  if (isInternal)
  {
    return;
  }
  // output benchmark if specified
  if (isOutputOn(OutputTag::UNSAT_CORE_BENCHMARK))
  {
    std::vector<Node> coreAsserts;
    std::vector<Node> coreDefs;
    partitionUnsatCore(core, coreDefs, coreAsserts);
    std::stringstream ss;
    smt::PrintBenchmark pb(Printer::getPrinter(ss));
    pb.printBenchmark(ss, logicInfo().getLogicString(), coreDefs, coreAsserts);
    output(OutputTag::UNSAT_CORE_BENCHMARK) << ";; unsat core" << std::endl;
    output(OutputTag::UNSAT_CORE_BENCHMARK) << ss.str();
    output(OutputTag::UNSAT_CORE_BENCHMARK) << ";; end unsat core" << std::endl;
  }
}

void UnsatCoreManager::getRelevantQuantTermVectors(
    std::map<Node, InstantiationList>& insts,
    std::map<Node, std::vector<Node>>& sks,
    bool getDebugInfo)
{
  // note that we don't have to connect the SAT proof to the input assertions,
  // and preprocessing proofs don't impact what instantiations are used
  prop::PropEngine* pe = d_slv.getPropEngine();
  Assert(pe != nullptr);
  std::shared_ptr<ProofNode> pfn = pe->getProof();
  Assert(pfn != nullptr);
  NodeManager* nm = nodeManager();
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::map<Node, InstantiationList>::iterator itq;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pfn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur.get());
    if (it != visited.end())
    {
      continue;
    }
    visited[cur.get()] = true;
    const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
    ProofRule r = cur->getRule();
    if (r == ProofRule::INSTANTIATE)
    {
      Node tlist = cur->getArguments()[0];
      Assert(cs.size() == 1);
      Node q = cs[0]->getResult();
      std::vector<Node> instTerms(tlist.begin(), tlist.end());
      Assert(instTerms.size() == q[0].getNumChildren());
      // the instantiation is a prefix of the arguments up to the number of
      // variables
      itq = insts.find(q);
      if (itq == insts.end())
      {
        insts[q].initialize(q);
        itq = insts.find(q);
      }
      itq->second.d_inst.push_back(InstantiationVec(instTerms));
      if (getDebugInfo)
      {
        const std::vector<Node>& args = cur->getArguments();
        std::vector<Node> extraArgs(args.begin() + 1, args.end());
        if (extraArgs.size() >= 1)
        {
          getInferenceId(extraArgs[0], itq->second.d_inst.back().d_id);
        }
        if (extraArgs.size() >= 2)
        {
          itq->second.d_inst.back().d_pfArg = extraArgs[1];
        }
      }
    }
    else if (r == ProofRule::SKOLEMIZE)
    {
      Node q = cur->getChildren()[0]->getResult();
      Node exists;
      if (q.getKind() == Kind::NOT && q.getKind() == Kind::FORALL)
      {
        std::vector<Node> echildren(q[0].begin(), q[0].end());
        echildren[1] = echildren[1].notNode();
        exists = nm->mkNode(Kind::EXISTS, echildren);
      }
      else if (q.getKind() == Kind::EXISTS)
      {
        exists = q;
      }
      if (!exists.isNull())
      {
        sks[q] = theory::quantifiers::Skolemize::getSkolemConstants(exists);
      }
    }
    for (const std::shared_ptr<ProofNode>& cp : cs)
    {
      visit.push_back(cp);
    }
  } while (!visit.empty());
}

std::vector<Node> UnsatCoreManager::reduceUnsatCore(
    const Assertions& as, const std::vector<Node>& core)
{
  Assert(options().smt.produceUnsatCores)
      << "cannot reduce unsat core if unsat cores are turned off";

  d_env.verbose(1) << "SolverEngine::reduceUnsatCore(): reducing unsat core"
                   << std::endl;
  std::unordered_set<Node> removed;
  std::unordered_set<Node> adefs = as.getCurrentAssertionListDefitions();
  for (const Node& skip : core)
  {
    std::unique_ptr<SolverEngine> coreChecker;
    theory::initializeSubsolver(coreChecker, d_env);
    coreChecker->setLogic(logicInfo());
    // disable all proof options
    SetDefaults::disableChecking(coreChecker->getOptions());
    // add to removed set?
    removed.insert(skip);
    // assert everything to the subsolver
    theory::assertToSubsolver(*coreChecker.get(), core, adefs, removed);
    Result r;
    try
    {
      r = coreChecker->checkSat();
    }
    catch (...)
    {
      throw;
    }

    if (r.getStatus() != Result::UNSAT)
    {
      removed.erase(skip);
      if (r.isUnknown())
      {
        d_env.warning()
            << "SolverEngine::reduceUnsatCore(): could not reduce unsat core "
               "due to "
               "unknown result.";
      }
    }
  }

  if (removed.empty())
  {
    return core;
  }
  std::vector<Node> newUcAssertions;
  for (const Node& n : core)
  {
    if (removed.find(n) == removed.end())
    {
      newUcAssertions.push_back(n);
    }
  }
  return newUcAssertions;
}

void UnsatCoreManager::partitionUnsatCore(const std::vector<Node>& core,
                                          std::vector<Node>& coreDefs,
                                          std::vector<Node>& coreAsserts)
{
  const Assertions& as = d_slv.getAssertions();
  std::unordered_set<Node> defs = as.getCurrentAssertionListDefitions();
  for (const Node& c : core)
  {
    if (defs.find(c) != defs.end())
    {
      coreDefs.push_back(c);
    }
    else
    {
      coreAsserts.push_back(c);
    }
  }
}

std::vector<Node> UnsatCoreManager::convertPreprocessedToInput(
    const std::vector<Node>& ppa, bool isInternal)
{
  std::vector<Node> core;
  CDProof cdp(d_env);
  Node fnode = nodeManager()->mkConst(false);
  cdp.addStep(fnode, ProofRule::SAT_REFUTATION, ppa, {});
  std::shared_ptr<ProofNode> pepf = cdp.getProofFor(fnode);
  Assert(pepf != nullptr);
  std::shared_ptr<ProofNode> pfn =
      d_pfm.connectProofToAssertions(pepf, d_slv, ProofScopeMode::UNIFIED);
  getUnsatCoreInternal(pfn, core, isInternal);
  return core;
}

}  // namespace smt
}  // namespace cvc5::internal
