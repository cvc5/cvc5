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
#include "preprocessing/preprocessing_pass_registry.h"
#include "printer/printer.h"
#include "smt/assertions.h"
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
  dumpAssertions("assertions::pre-everything", as);
  Trace("assertions::pre-everything") << std::endl;

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
    applyPass("bv-gauss", as);
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
  // Apply substitutions first. If we are non-incremental, this has only the
  // effect of replacing defined functions with their definitions.
  // We do not call theory-specific expand definitions here, since we want
  // to give the opportunity to rewrite/preprocess terms before expansion.
  applyPass("apply-substs", as);
  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : post-definition-expansion"
      << endl;

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  if (options().quantifiers.globalNegate)
  {
    // global negation of the formula
    applyPass("global-negate", as);
    as.flipGlobalNegated();
  }

  if (options().arith.nlExtPurify)
  {
    applyPass("nl-ext-purify", as);
  }

  if (options().smt.solveRealAsInt)
  {
    applyPass("real-to-int", as);
  }

  if (options().smt.solveIntAsBV > 0)
  {
    applyPass("int-to-bv", as);
  }

  if (options().smt.ackermann)
  {
    applyPass("ackermann", as);
  }

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  bool noConflict = true;

  if (options().smt.extRewPrep != options::ExtRewPrepMode::OFF)
  {
    applyPass("ext-rew-pre", as);
  }

  // Unconstrained simplification
  if (options().smt.unconstrainedSimp)
  {
    applyPass("rewrite", as);
    applyPass("unconstrained-simplifier", as);
  }

  if (options().bv.bvIntroducePow2)
  {
    applyPass("bv-intro-pow2", as);
  }

  // Lift bit-vectors of size 1 to bool
  if (options().bv.bitvectorToBool)
  {
    applyPass("bv-to-bool", as);
  }
  if (options().smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    applyPass("bv-to-int", as);
  }
  if (options().smt.foreignTheoryRewrite)
  {
    applyPass("foreign-theory-rewrite", as);
  }

  // Assertions MUST BE guaranteed to be rewritten by this point
  applyPass("rewrite", as);

  // Convert non-top-level Booleans to bit-vectors of size 1
  if (options().bv.boolToBitvector != options::BoolToBVMode::OFF)
  {
    applyPass("bool-to-bv", as);
  }
  if (options().sep.sepPreSkolemEmp)
  {
    applyPass("sep-skolem-emp", as);
  }

  if (logicInfo().isQuantified())
  {
    // remove rewrite rules, apply pre-skolemization to existential quantifiers
    applyPass("quantifiers-preprocess", as);

    // fmf-fun : assume admissible functions, applying preprocessing reduction
    // to FMF
    if (options().quantifiers.fmfFunWellDefined)
    {
      applyPass("fun-def-fmf", as);
    }
  }
  if (!options().strings.stringLazyPreproc)
  {
    applyPass("strings-eager-pp", as);
    // needed since strings eager preprocessing may reintroduce skolems that
    // were already solved for in incremental mode
    applyPass("apply-substs", as);
  }
  if (options().smt.sortInference || options().uf.ufssFairnessMonotone)
  {
    applyPass("sort-inference", as);
  }

  if (options().arith.pbRewrites)
  {
    applyPass("pseudo-boolean-processor", as);
  }

  // rephrasing normal inputs as sygus problems
  if (options().quantifiers.sygusInference)
  {
    applyPass("sygus-infer", as);
  }
  else if (options().quantifiers.sygusRewSynthInput)
  {
    // do candidate rewrite rule synthesis
    applyPass("synth-rr", as);
  }

  Trace("smt-proc") << "ProcessAssertions::processAssertions() : pre-simplify"
                    << endl;
  dumpAssertions("assertions::pre-simplify", as);
  Trace("assertions::pre-simplify") << std::endl;
  verbose(2) << "simplifying assertions..." << std::endl;
  noConflict = simplifyAssertions(as);
  if (!noConflict)
  {
    ++(d_slvStats.d_simplifiedToFalse);
  }
  Trace("smt-proc") << "ProcessAssertions::processAssertions() : post-simplify"
                    << endl;
  dumpAssertions("assertions::post-simplify", as);
  Trace("assertions::post-simplify") << std::endl;

  if (options().smt.doStaticLearning)
  {
    applyPass("static-learning", as);
  }
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  if (options().smt.learnedRewrite)
  {
    applyPass("learned-rewrite", as);
  }

  if (options().smt.earlyIteRemoval)
  {
    d_slvStats.d_numAssertionsPre += assertions.size();
    applyPass("ite-removal", as);
    // This is needed because when solving incrementally, removeITEs may
    // introduce skolems that were solved for earlier and thus appear in the
    // substitution map.
    applyPass("apply-substs", as);
    d_slvStats.d_numAssertionsPost += assertions.size();
  }

  dumpAssertions("assertions::pre-repeat-simplify", as);
  Trace("assertions::pre-repeat-simplify") << std::endl;
  if (options().smt.repeatSimp)
  {
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : pre-repeat-simplify"
        << endl;
    verbose(2) << "re-simplifying assertions..." << std::endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions(as);
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : post-repeat-simplify"
        << endl;
  }
  dumpAssertions("assertions::post-repeat-simplify", as);
  Trace("assertions::post-repeat-simplify") << std::endl;

  if (logicInfo().isHigherOrder())
  {
    applyPass("ho-elim", as);
  }
  
  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  Debug("smt") << " assertions     : " << assertions.size() << endl;

  Debug("smt") << "ProcessAssertions::processAssertions() POST SIMPLIFICATION"
               << endl;
  Debug("smt") << " assertions     : " << assertions.size() << endl;

  // ensure rewritten
  applyPass("rewrite", as);
  // rewrite equalities based on theory-specific rewriting
  applyPass("theory-rewrite-eq", as);
  // apply theory preprocess, which includes ITE removal
  applyPass("theory-preprocess", as);
  // notice that we do not apply substitutions as a last step here, since
  // the range of substitutions is not theory-preprocessed.

  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    applyPass("bv-eager-atoms", as);
  }

  Trace("smt-proc") << "ProcessAssertions::apply() end" << endl;
  dumpAssertions("assertions::post-everything", as);
  Trace("assertions::post-everything") << std::endl;
  if (isOutputOn(OutputTag::POST_ASSERTS))
  {
    std::ostream& outPA = d_env.output(OutputTag::POST_ASSERTS);
    outPA << ";; post-asserts start" << std::endl;
    dumpAssertionsToStream(outPA, as);
    outPA << ";; post-asserts end" << std::endl;
  }

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
      PreprocessingPassResult res = applyPass("non-clausal-simp", as);
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
        applyPass("miplib-trick", as);
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
      PreprocessingPassResult res = applyPass("ite-simp", as);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        verbose(2) << "...ITE simplification found unsat..." << std::endl;
        return false;
      }
    }

    Debug("smt") << " assertions     : " << assertions.size() << endl;

    // Unconstrained simplification
    if (options().smt.unconstrainedSimp)
    {
      applyPass("unconstrained-simplifier", as);
    }

    if (options().smt.repeatSimp
        && options().smt.simplificationMode
               != options::SimplificationMode::NONE)
    {
      PreprocessingPassResult res = applyPass("non-clausal-simp", as);
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

void ProcessAssertions::dumpAssertions(const std::string& key, Assertions& as)
{
  bool isTraceOn = Trace.isOn(key);
  if (!isTraceOn)
  {
    return;
  }
  std::stringstream ss;
  dumpAssertionsToStream(ss, as);
  Trace(key) << ";;; " << key << " start" << std::endl;
  Trace(key) << ss.str();
  Trace(key) << ";;; " << key << " end " << std::endl;
}

void ProcessAssertions::dumpAssertionsToStream(std::ostream& os, Assertions& as)
{
  PrintBenchmark pb(&d_env.getPrinter());
  std::vector<Node> assertions;
  // Notice that the following list covers define-fun and define-fun-rec
  // from input. The former does not impact the assertions since define-fun are
  // added as top-level substitutions. The latter do get added to the list
  // of assertions. Since we are interested in printing the result of
  // preprocessed quantified formulas corresponding to recursive function
  // definitions and not the original definitions, we discard the latter
  // in the loop below.
  //
  // In summary, this means that define-fun-rec are expanded to
  // (declare-fun ...) + (assert (forall ...)) in the printing below, whereas
  // define-fun are preserved.
  const context::CDList<Node>& asld = as.getAssertionListDefinitions();
  std::vector<Node> defs;
  for (const Node& d : asld)
  {
    if (d.getKind() != FORALL)
    {
      defs.push_back(d);
    }
  }
  AssertionPipeline& ap = as.getAssertionPipeline();
  for (size_t i = 0, size = ap.size(); i < size; i++)
  {
    assertions.push_back(ap[i]);
  }
  pb.printBenchmark(os, logicInfo().getLogicString(), defs, assertions);
}

PreprocessingPassResult ProcessAssertions::applyPass(const std::string& pname,
                                                     Assertions& as)
{
  dumpAssertions("assertions::pre-" + pname, as);
  AssertionPipeline& assertions = as.getAssertionPipeline();
  PreprocessingPassResult res = d_passes[pname]->apply(&assertions);
  dumpAssertions("assertions::post-" + pname, as);
  return res;
}

}  // namespace smt
}  // namespace cvc5
