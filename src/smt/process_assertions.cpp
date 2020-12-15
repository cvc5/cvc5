/*********************                                                        */
/*! \file process_assertions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Yoni Zohar, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of module for processing assertions for an SMT engine.
 **/

#include "smt/process_assertions.h"

#include <stack>
#include <utility>

#include "expr/node_manager_attributes.h"
#include "options/arith_options.h"
#include "options/base_options.h"
#include "options/bv_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "printer/printer.h"
#include "smt/defined_function.h"
#include "smt/dump.h"
#include "smt/smt_engine.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"

using namespace CVC4::preprocessing;
using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

/** Useful for counting the number of recursive calls. */
class ScopeCounter
{
 public:
  ScopeCounter(unsigned& d) : d_depth(d) { ++d_depth; }
  ~ScopeCounter() { --d_depth; }

 private:
  unsigned& d_depth;
};

ProcessAssertions::ProcessAssertions(SmtEngine& smt,
                                     ExpandDefs& exDefs,
                                     ResourceManager& rm,
                                     SmtEngineStatistics& stats)
    : d_smt(smt),
      d_exDefs(exDefs),
      d_resourceManager(rm),
      d_smtStats(stats),
      d_preprocessingPassContext(nullptr)
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

ProcessAssertions::~ProcessAssertions()
{
}

void ProcessAssertions::finishInit(PreprocessingPassContext* pc)
{
  Assert(d_preprocessingPassContext == nullptr);
  d_preprocessingPassContext = pc;

  PreprocessingPassRegistry& ppReg = PreprocessingPassRegistry::getInstance();
  // TODO: this will likely change when we add support for actually assembling
  // preprocessing pipelines. For now, we just create an instance of each
  // available preprocessing pass.
  std::vector<std::string> passNames = ppReg.getAvailablePasses();
  for (const std::string& passName : passNames)
  {
    d_passes[passName].reset(
        ppReg.createPass(d_preprocessingPassContext, passName));
  }
}

void ProcessAssertions::cleanup() { d_passes.clear(); }

void ProcessAssertions::spendResource(ResourceManager::Resource r)
{
  d_resourceManager.spendResource(r);
}

bool ProcessAssertions::apply(Assertions& as)
{
  AssertionPipeline& assertions = as.getAssertionPipeline();
  Assert(d_preprocessingPassContext != nullptr);
  // Dump the assertions
  dumpAssertions("pre-everything", assertions);

  Trace("smt-proc") << "ProcessAssertions::processAssertions() begin" << endl;
  Trace("smt") << "ProcessAssertions::processAssertions()" << endl;

  Debug("smt") << "#Assertions : " << assertions.size() << endl;
  Debug("smt") << "#Assumptions: " << assertions.getNumAssumptions() << endl;

  if (assertions.size() == 0)
  {
    // nothing to do
    return true;
  }

  if (options::bvGaussElim())
  {
    d_passes["bv-gauss"]->apply(&assertions);
  }

  // Add dummy assertion in last position - to be used as a
  // placeholder for any new assertions to get added
  assertions.push_back(d_true);
  // any assertions added beyond realAssertionsEnd must NOT affect the
  // equisatisfiability
  assertions.updateRealAssertionsEnd();

  // Assertions are NOT guaranteed to be rewritten by this point

  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : pre-definition-expansion"
      << endl;
  dumpAssertions("pre-definition-expansion", assertions);
  // Expand definitions, which replaces defined functions with their definition
  // and does beta reduction. Notice we pass true as the second argument since
  // we do not want to call theories to expand definitions here, since we want
  // to give the opportunity to rewrite/preprocess terms before expansion.
  d_exDefs.expandAssertions(assertions, true);
  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : post-definition-expansion"
      << endl;
  dumpAssertions("post-definition-expansion", assertions);

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  if (options::globalNegate())
  {
    // global negation of the formula
    d_passes["global-negate"]->apply(&assertions);
    as.flipGlobalNegated();
  }

  if (options::nlExtPurify())
  {
    d_passes["nl-ext-purify"]->apply(&assertions);
  }

  if (options::solveRealAsInt())
  {
    d_passes["real-to-int"]->apply(&assertions);
  }

  if (options::solveIntAsBV() > 0)
  {
    d_passes["int-to-bv"]->apply(&assertions);
  }

  if (options::ackermann())
  {
    d_passes["ackermann"]->apply(&assertions);
  }

  if (options::bvAbstraction())
  {
    d_passes["bv-abstraction"]->apply(&assertions);
  }

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  bool noConflict = true;

  if (options::extRewPrep())
  {
    d_passes["ext-rew-pre"]->apply(&assertions);
  }

  // Unconstrained simplification
  if (options::unconstrainedSimp())
  {
    d_passes["rewrite"]->apply(&assertions);
    d_passes["unconstrained-simplifier"]->apply(&assertions);
  }

  if (options::bvIntroducePow2())
  {
    d_passes["bv-intro-pow2"]->apply(&assertions);
  }

  // Lift bit-vectors of size 1 to bool
  if (options::bitvectorToBool())
  {
    d_passes["bv-to-bool"]->apply(&assertions);
  }
  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    d_passes["bv-to-int"]->apply(&assertions);
    // after running bv-to-int, we need to immediately run
    // theory-preprocess and ite-removal so that newlly created
    // terms and assertions are normalized (e.g., div is expanded).
    d_passes["theory-preprocess"]->apply(&assertions);
  }

  // Since this pass is not robust for the information tracking necessary for
  // unsat cores, it's only applied if we are not doing unsat core computation
  if (!options::unsatCores())
  {
    d_passes["apply-substs"]->apply(&assertions);
  }

  // Assertions MUST BE guaranteed to be rewritten by this point
  d_passes["rewrite"]->apply(&assertions);

  // Convert non-top-level Booleans to bit-vectors of size 1
  if (options::boolToBitvector() != options::BoolToBVMode::OFF)
  {
    d_passes["bool-to-bv"]->apply(&assertions);
  }
  if (options::sepPreSkolemEmp())
  {
    d_passes["sep-skolem-emp"]->apply(&assertions);
  }

  if (d_smt.getLogicInfo().isQuantified())
  {
    // remove rewrite rules, apply pre-skolemization to existential quantifiers
    d_passes["quantifiers-preprocess"]->apply(&assertions);
    if (options::macrosQuant())
    {
      // quantifiers macro expansion
      d_passes["quantifier-macros"]->apply(&assertions);
    }

    // fmf-fun : assume admissible functions, applying preprocessing reduction
    // to FMF
    if (options::fmfFunWellDefined())
    {
      d_passes["fun-def-fmf"]->apply(&assertions);
    }
  }

  if (options::sortInference() || options::ufssFairnessMonotone())
  {
    d_passes["sort-inference"]->apply(&assertions);
  }

  if (options::pbRewrites())
  {
    d_passes["pseudo-boolean-processor"]->apply(&assertions);
  }

  // rephrasing normal inputs as sygus problems
  if (!d_smt.isInternalSubsolver())
  {
    if (options::sygusInference())
    {
      d_passes["sygus-infer"]->apply(&assertions);
    }
    else if (options::sygusRewSynthInput())
    {
      // do candidate rewrite rule synthesis
      d_passes["synth-rr"]->apply(&assertions);
    }
  }

  Trace("smt-proc") << "ProcessAssertions::processAssertions() : pre-simplify"
                    << endl;
  dumpAssertions("pre-simplify", assertions);
  Chat() << "simplifying assertions..." << endl;
  noConflict = simplifyAssertions(assertions);
  if (!noConflict)
  {
    ++(d_smtStats.d_simplifiedToFalse);
  }
  Trace("smt-proc") << "ProcessAssertions::processAssertions() : post-simplify"
                    << endl;
  dumpAssertions("post-simplify", assertions);

  if (options::doStaticLearning())
  {
    d_passes["static-learning"]->apply(&assertions);
  }
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  {
    d_smtStats.d_numAssertionsPre += assertions.size();
    d_passes["ite-removal"]->apply(&assertions);
    // This is needed because when solving incrementally, removeITEs may
    // introduce skolems that were solved for earlier and thus appear in the
    // substitution map.
    d_passes["apply-substs"]->apply(&assertions);
    d_smtStats.d_numAssertionsPost += assertions.size();
  }

  dumpAssertions("pre-repeat-simplify", assertions);
  if (options::repeatSimp())
  {
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : pre-repeat-simplify"
        << endl;
    Chat() << "re-simplifying assertions..." << endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions(assertions);
    if (noConflict)
    {
      // Need to fix up assertion list to maintain invariants:
      // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be
      // the order in which these variables were introduced during ite removal.
      // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr
      // mapped to by sk.

      // cache for expression traversal
      unordered_map<Node, bool, NodeHashFunction> cache;

      IteSkolemMap& iskMap = assertions.getIteSkolemMap();
      // First, find all skolems that appear in the substitution map - their
      // associated iteExpr will need to be moved to the main assertion set
      set<TNode> skolemSet;
      SubstitutionMap& top_level_substs =
          d_preprocessingPassContext->getTopLevelSubstitutions().get();
      SubstitutionMap::iterator pos = top_level_substs.begin();
      for (; pos != top_level_substs.end(); ++pos)
      {
        collectSkolems(iskMap, (*pos).first, skolemSet, cache);
        collectSkolems(iskMap, (*pos).second, skolemSet, cache);
      }
      // We need to ensure:
      // 1. iteExpr has the form (ite cond (sk = t) (sk = e))
      // 2. if some sk' in Sk appears in cond, t, or e, then sk' <_sk sk
      // If either of these is violated, we must add iteExpr as a proper
      // assertion
      IteSkolemMap::iterator it = iskMap.begin();
      IteSkolemMap::iterator iend = iskMap.end();
      std::vector<Node> newConj;
      vector<TNode> toErase;
      for (; it != iend; ++it)
      {
        if (skolemSet.find((*it).first) == skolemSet.end())
        {
          TNode iteExpr = assertions[(*it).second];
          if (iteExpr.getKind() == ITE && iteExpr[1].getKind() == EQUAL
              && iteExpr[1][0] == (*it).first && iteExpr[2].getKind() == EQUAL
              && iteExpr[2][0] == (*it).first)
          {
            cache.clear();
            bool bad =
                checkForBadSkolems(iskMap, iteExpr[0], (*it).first, cache);
            bad = bad
                  || checkForBadSkolems(
                         iskMap, iteExpr[1][1], (*it).first, cache);
            bad = bad
                  || checkForBadSkolems(
                         iskMap, iteExpr[2][1], (*it).first, cache);
            if (!bad)
            {
              continue;
            }
          }
        }
        // Move this iteExpr into the main assertions
        newConj.push_back(assertions[(*it).second]);
        assertions.replace((*it).second, d_true);
        toErase.push_back((*it).first);
      }
      if (!newConj.empty())
      {
        while (!toErase.empty())
        {
          iskMap.erase(toErase.back());
          toErase.pop_back();
        }
        size_t index = assertions.getRealAssertionsEnd() - 1;
        Node newAssertion = NodeManager::currentNM()->mkAnd(newConj);
        assertions.conjoin(index, newAssertion);
      }
      // TODO(b/1256): For some reason this is needed for some benchmarks, such
      // as
      // QF_AUFBV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_remove_at.il.dwp.smt2
      d_passes["ite-removal"]->apply(&assertions);
      d_passes["apply-substs"]->apply(&assertions);
    }
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : post-repeat-simplify"
        << endl;
  }
  dumpAssertions("post-repeat-simplify", assertions);

  if (options::ufHo())
  {
    d_passes["ho-elim"]->apply(&assertions);
  }

  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  Debug("smt") << "ProcessAssertions::processAssertions() POST SIMPLIFICATION"
               << endl;
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  d_passes["theory-preprocess"]->apply(&assertions);
  // Must remove ITEs again since theory preprocessing may introduce them.
  // Notice that we alternatively could ensure that the theory-preprocess
  // pass above calls TheoryPreprocess::preprocess instead of
  // TheoryPreprocess::theoryPreprocess, as the former also does ITE removal.
  d_passes["ite-removal"]->apply(&assertions);

  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    d_passes["bv-eager-atoms"]->apply(&assertions);
  }

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() end" << endl;
  dumpAssertions("post-everything", assertions);

  return noConflict;
}

// returns false if simplification led to "false"
bool ProcessAssertions::simplifyAssertions(AssertionPipeline& assertions)
{
  spendResource(ResourceManager::Resource::PreprocessStep);
  try
  {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

    if (options::simplificationMode() != options::SimplificationMode::NONE)
    {
      if (!options::unsatCores())
      {
        // Perform non-clausal simplification
        PreprocessingPassResult res =
            d_passes["non-clausal-simp"]->apply(&assertions);
        if (res == PreprocessingPassResult::CONFLICT)
        {
          return false;
        }
      }

      // We piggy-back off of the BackEdgesMap in the CircuitPropagator to
      // do the miplib trick.
      if (  // check that option is on
          options::arithMLTrick() &&
          // only useful in arith
          d_smt.getLogicInfo().isTheoryEnabled(THEORY_ARITH) &&
          // we add new assertions and need this (in practice, this
          // restriction only disables miplib processing during
          // re-simplification, which we don't expect to be useful anyway)
          assertions.getRealAssertionsEnd() == assertions.size())
      {
        d_passes["miplib-trick"]->apply(&assertions);
      }
      else
      {
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "skipping miplib pseudobooleans pass..." << endl;
      }
    }

    Debug("smt") << " assertions     : " << assertions.size() << endl;

    // Theory preprocessing
    bool doEarlyTheoryPp = !options::arithRewriteEq();
    if (doEarlyTheoryPp)
    {
      d_passes["theory-preprocess"]->apply(&assertions);
    }

    // ITE simplification
    if (options::doITESimp()
        && (d_simplifyAssertionsDepth <= 1 || options::doITESimpOnRepeat()))
    {
      PreprocessingPassResult res = d_passes["ite-simp"]->apply(&assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        Chat() << "...ITE simplification found unsat..." << endl;
        return false;
      }
    }

    Debug("smt") << " assertions     : " << assertions.size() << endl;

    // Unconstrained simplification
    if (options::unconstrainedSimp())
    {
      d_passes["unconstrained-simplifier"]->apply(&assertions);
    }

    if (options::repeatSimp()
        && options::simplificationMode() != options::SimplificationMode::NONE
        && !options::unsatCores())
    {
      PreprocessingPassResult res =
          d_passes["non-clausal-simp"]->apply(&assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", assertions);
    Trace("smt") << "POST repeatSimp" << endl;
    Debug("smt") << " assertions     : " << assertions.size() << endl;
  }
  catch (TypeCheckingExceptionPrivate& tcep)
  {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    InternalError()
        << "A bad expression was produced.  Original exception follows:\n"
        << tcep;
  }
  return true;
}

void ProcessAssertions::dumpAssertions(const char* key,
                                       const AssertionPipeline& assertionList)
{
  if (Dump.isOn("assertions") && Dump.isOn(string("assertions:") + key))
  {
    // Push the simplified assertions to the dump output stream
    for (unsigned i = 0; i < assertionList.size(); ++i)
    {
      TNode n = assertionList[i];
      d_smt.getOutputManager().getPrinter().toStreamCmdAssert(
          d_smt.getOutputManager().getDumpOut(), n);
    }
  }
}

void ProcessAssertions::collectSkolems(
    IteSkolemMap& iskMap,
    TNode n,
    set<TNode>& skolemSet,
    unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end())
  {
    return;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0)
  {
    if (iskMap.find(n) != iskMap.end())
    {
      skolemSet.insert(n);
    }
    cache[n] = true;
    return;
  }

  size_t k = 0;
  for (; k < sz; ++k)
  {
    collectSkolems(iskMap, n[k], skolemSet, cache);
  }
  cache[n] = true;
}

bool ProcessAssertions::checkForBadSkolems(
    IteSkolemMap& iskMap,
    TNode n,
    TNode skolem,
    unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end())
  {
    return (*it).second;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0)
  {
    IteSkolemMap::iterator iit = iskMap.find(n);
    bool bad = false;
    if (iit != iskMap.end())
    {
      if (!((*iit).first < n))
      {
        bad = true;
      }
    }
    cache[n] = bad;
    return bad;
  }

  size_t k = 0;
  for (; k < sz; ++k)
  {
    if (checkForBadSkolems(iskMap, n[k], skolem, cache))
    {
      cache[n] = true;
      return true;
    }
  }

  cache[n] = false;
  return false;
}

}  // namespace smt
}  // namespace CVC4
