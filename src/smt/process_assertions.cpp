/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for processing assertions for an SMT engine.
 */

#include "smt/process_assertions.h"

#include <utility>

#include "expr/node_manager_attributes.h"
#include "options/arith_options.h"
#include "options/base_options.h"
#include "options/bv_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "printer/printer.h"
#include "smt/assertions.h"
#include "smt/dump.h"
#include "smt/expand_definitions.h"
#include "smt/print_benchmark.h"
#include "smt/solver_engine_stats.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace cvc5::preprocessing;
using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
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

ProcessAssertions::ProcessAssertions(Env& env, SolverEngineStatistics& stats)
    : EnvObj(env), d_slvStats(stats), d_preprocessingPassContext(nullptr)
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

ProcessAssertions::~ProcessAssertions()
{
}

void ProcessAssertions::finishInit(PreprocessingPassContext* pc)
{
  // note that we may be replacing a stale preprocessing pass context here
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

void ProcessAssertions::spendResource(Resource r)
{
  resourceManager()->spendResource(r);
}

bool ProcessAssertions::apply(Assertions& as)
{
  // must first refresh the assertions, in the case global declarations is true
  as.refresh();
  AssertionPipeline& assertions = as.getAssertionPipeline();
  Assert(d_preprocessingPassContext != nullptr);
  // Dump the assertions
  dumpAssertions("pre-everything", as);

  Trace("smt-proc") << "ProcessAssertions::processAssertions() begin" << endl;
  Trace("smt") << "ProcessAssertions::processAssertions()" << endl;

  Debug("smt") << "#Assertions : " << assertions.size() << endl;
  Debug("smt") << "#Assumptions: " << assertions.getNumAssumptions() << endl;

  if (assertions.size() == 0)
  {
    // nothing to do
    return true;
  }

  if (options().bv.bvGaussElim)
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
  dumpAssertions("pre-definition-expansion", as);
  // Apply substitutions first. If we are non-incremental, this has only the
  // effect of replacing defined functions with their definitions.
  // We do not call theory-specific expand definitions here, since we want
  // to give the opportunity to rewrite/preprocess terms before expansion.
  d_passes["apply-substs"]->apply(&assertions);
  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : post-definition-expansion"
      << endl;
  dumpAssertions("post-definition-expansion", as);

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  if (options().quantifiers.globalNegate)
  {
    // global negation of the formula
    d_passes["global-negate"]->apply(&assertions);
    as.flipGlobalNegated();
  }

  if (options().arith.nlExtPurify)
  {
    d_passes["nl-ext-purify"]->apply(&assertions);
  }

  if (options().smt.solveRealAsInt)
  {
    d_passes["real-to-int"]->apply(&assertions);
  }

  if (options().smt.solveIntAsBV > 0)
  {
    d_passes["int-to-bv"]->apply(&assertions);
  }

  if (options().smt.ackermann)
  {
    d_passes["ackermann"]->apply(&assertions);
  }

  if (options().bv.bvAbstraction)
  {
    d_passes["bv-abstraction"]->apply(&assertions);
  }

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  bool noConflict = true;

  if (options().smt.extRewPrep)
  {
    d_passes["ext-rew-pre"]->apply(&assertions);
  }

  // Unconstrained simplification
  if (options().smt.unconstrainedSimp)
  {
    d_passes["rewrite"]->apply(&assertions);
    d_passes["unconstrained-simplifier"]->apply(&assertions);
  }

  if (options().bv.bvIntroducePow2)
  {
    d_passes["bv-intro-pow2"]->apply(&assertions);
  }

  // Lift bit-vectors of size 1 to bool
  if (options().bv.bitvectorToBool)
  {
    d_passes["bv-to-bool"]->apply(&assertions);
  }
  if (options().smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    d_passes["bv-to-int"]->apply(&assertions);
  }
  if (options().smt.foreignTheoryRewrite)
  {
    d_passes["foreign-theory-rewrite"]->apply(&assertions);
  }

  // Since this pass is not robust for the information tracking necessary for
  // unsat cores, it's only applied if we are not doing unsat core computation
  d_passes["apply-substs"]->apply(&assertions);

  // Assertions MUST BE guaranteed to be rewritten by this point
  d_passes["rewrite"]->apply(&assertions);

  // Convert non-top-level Booleans to bit-vectors of size 1
  if (options().bv.boolToBitvector != options::BoolToBVMode::OFF)
  {
    d_passes["bool-to-bv"]->apply(&assertions);
  }
  if (options().sep.sepPreSkolemEmp)
  {
    d_passes["sep-skolem-emp"]->apply(&assertions);
  }

  if (logicInfo().isQuantified())
  {
    // remove rewrite rules, apply pre-skolemization to existential quantifiers
    d_passes["quantifiers-preprocess"]->apply(&assertions);

    // fmf-fun : assume admissible functions, applying preprocessing reduction
    // to FMF
    if (options().quantifiers.fmfFunWellDefined)
    {
      d_passes["fun-def-fmf"]->apply(&assertions);
    }
  }
  if (!options().strings.stringLazyPreproc)
  {
    d_passes["strings-eager-pp"]->apply(&assertions);
  }
  if (options().smt.sortInference || options().uf.ufssFairnessMonotone)
  {
    d_passes["sort-inference"]->apply(&assertions);
  }

  if (options().arith.pbRewrites)
  {
    d_passes["pseudo-boolean-processor"]->apply(&assertions);
  }

  // rephrasing normal inputs as sygus problems
  if (options().quantifiers.sygusInference)
  {
    d_passes["sygus-infer"]->apply(&assertions);
  }
  else if (options().quantifiers.sygusRewSynthInput)
  {
    // do candidate rewrite rule synthesis
    d_passes["synth-rr"]->apply(&assertions);
  }

  Trace("smt-proc") << "ProcessAssertions::processAssertions() : pre-simplify"
                    << endl;
  dumpAssertions("pre-simplify", as);
  Chat() << "simplifying assertions..." << endl;
  noConflict = simplifyAssertions(as);
  if (!noConflict)
  {
    ++(d_slvStats.d_simplifiedToFalse);
  }
  Trace("smt-proc") << "ProcessAssertions::processAssertions() : post-simplify"
                    << endl;
  dumpAssertions("post-simplify", as);

  if (options().smt.doStaticLearning)
  {
    d_passes["static-learning"]->apply(&assertions);
  }
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  if (options().smt.learnedRewrite)
  {
    d_passes["learned-rewrite"]->apply(&assertions);
  }

  if (options().smt.earlyIteRemoval)
  {
    d_slvStats.d_numAssertionsPre += assertions.size();
    d_passes["ite-removal"]->apply(&assertions);
    // This is needed because when solving incrementally, removeITEs may
    // introduce skolems that were solved for earlier and thus appear in the
    // substitution map.
    d_passes["apply-substs"]->apply(&assertions);
    d_slvStats.d_numAssertionsPost += assertions.size();
  }

  dumpAssertions("pre-repeat-simplify", as);
  if (options().smt.repeatSimp)
  {
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : pre-repeat-simplify"
        << endl;
    Chat() << "re-simplifying assertions..." << endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions(as);
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : post-repeat-simplify"
        << endl;
  }
  dumpAssertions("post-repeat-simplify", as);

  if (logicInfo().isHigherOrder())
  {
    d_passes["ho-elim"]->apply(&assertions);
  }
  
  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  Debug("smt") << "ProcessAssertions::processAssertions() POST SIMPLIFICATION"
               << endl;
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  // ensure rewritten
  d_passes["rewrite"]->apply(&assertions);
  // rewrite equalities based on theory-specific rewriting
  d_passes["theory-rewrite-eq"]->apply(&assertions);
  // apply theory preprocess, which includes ITE removal
  d_passes["theory-preprocess"]->apply(&assertions);
  // notice that we do not apply substitutions as a last step here, since
  // the range of substitutions is not theory-preprocessed.

  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    d_passes["bv-eager-atoms"]->apply(&assertions);
  }

  Trace("smt-proc") << "ProcessAssertions::apply() end" << endl;
  dumpAssertions("post-everything", as);

  return noConflict;
}

// returns false if simplification led to "false"
bool ProcessAssertions::simplifyAssertions(Assertions& as)
{
  spendResource(Resource::PreprocessStep);
  try
  {
    AssertionPipeline& assertions = as.getAssertionPipeline();
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "ProcessAssertions::simplify()" << endl;

    if (options().smt.simplificationMode != options::SimplificationMode::NONE)
    {
      // Perform non-clausal simplification
      PreprocessingPassResult res =
          d_passes["non-clausal-simp"]->apply(&assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        return false;
      }

      // We piggy-back off of the BackEdgesMap in the CircuitPropagator to
      // do the miplib trick.
      if (  // check that option is on
          options().arith.arithMLTrick &&
          // only useful in arith
          logicInfo().isTheoryEnabled(THEORY_ARITH) &&
          // we add new assertions and need this (in practice, this
          // restriction only disables miplib processing during
          // re-simplification, which we don't expect to be useful anyway)
          assertions.getRealAssertionsEnd() == assertions.size())
      {
        d_passes["miplib-trick"]->apply(&assertions);
      }
      else
      {
        Trace("simplify") << "ProcessAssertions::simplify(): "
                          << "skipping miplib pseudobooleans pass..." << endl;
      }
    }

    Debug("smt") << " assertions     : " << assertions.size() << endl;

    // ITE simplification
    if (options().smt.doITESimp
        && (d_simplifyAssertionsDepth <= 1 || options().smt.doITESimpOnRepeat))
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
    if (options().smt.unconstrainedSimp)
    {
      d_passes["unconstrained-simplifier"]->apply(&assertions);
    }

    if (options().smt.repeatSimp
        && options().smt.simplificationMode
               != options::SimplificationMode::NONE)
    {
      PreprocessingPassResult res =
          d_passes["non-clausal-simp"]->apply(&assertions);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", as);
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

void ProcessAssertions::dumpAssertions(const char* key, Assertions& as)
{
  if (Dump.isOn("assertions") && Dump.isOn(string("assertions:") + key))
  {
    const AssertionPipeline& assertionList = as.getAssertionPipeline();
    // Push the simplified assertions to the dump output stream
    for (unsigned i = 0; i < assertionList.size(); ++i)
    {
      TNode n = assertionList[i];
      d_env.getPrinter().toStreamCmdAssert(d_env.getDumpOut(), n);
    }
  }
}

}  // namespace smt
}  // namespace cvc5
