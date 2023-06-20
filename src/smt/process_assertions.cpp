/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for processing assertions for an SMT engine.
 */

#include "smt/process_assertions.h"

#include <utility>

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
#include "smt/print_benchmark.h"
#include "smt/solver_engine_stats.h"
#include "theory/logic_info.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace cvc5::internal::preprocessing;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
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

bool ProcessAssertions::apply(AssertionPipeline& ap)
{
  Assert(d_preprocessingPassContext != nullptr);
  // Dump the assertions
  dumpAssertions("assertions::pre-everything", ap);
  Trace("assertions::pre-everything") << std::endl;
  if (isOutputOn(OutputTag::PRE_ASSERTS))
  {
    std::ostream& outPA = d_env.output(OutputTag::PRE_ASSERTS);
    outPA << ";; pre-asserts start" << std::endl;
    dumpAssertionsToStream(outPA, ap);
    outPA << ";; pre-asserts end" << std::endl;
  }

  Trace("smt-proc") << "ProcessAssertions::processAssertions() begin" << endl;
  Trace("smt") << "ProcessAssertions::processAssertions()" << endl;

  Trace("smt") << "#Assertions : " << ap.size() << endl;

  if (ap.size() == 0)
  {
    // nothing to do
    return true;
  }

  if (options().bv.bvGaussElim)
  {
    applyPass("bv-gauss", ap);
  }

  // Add dummy assertion in last position - to be used as a
  // placeholder for any new assertions to get added
  ap.push_back(d_true);

  // Assertions are NOT guaranteed to be rewritten by this point

  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : pre-definition-expansion"
      << endl;
  // Apply substitutions first. If we are non-incremental, this has only the
  // effect of replacing defined functions with their definitions.
  // We do not call theory-specific expand definitions here, since we want
  // to give the opportunity to rewrite/preprocess terms before expansion.
  applyPass("apply-substs", ap);
  Trace("smt-proc")
      << "ProcessAssertions::processAssertions() : post-definition-expansion"
      << endl;

  Trace("smt") << " assertions     : " << ap.size() << endl;

  if (options().quantifiers.globalNegate)
  {
    // global negation of the formula
    applyPass("global-negate", ap);
  }

  if (options().arith.nlExtPurify)
  {
    applyPass("nl-ext-purify", ap);
  }

  if (options().smt.solveRealAsInt)
  {
    applyPass("real-to-int", ap);
  }

  if (options().smt.solveIntAsBV > 0)
  {
    applyPass("int-to-bv", ap);
  }

  if (options().smt.ackermann)
  {
    applyPass("ackermann", ap);
  }

  Trace("smt") << " assertions     : " << ap.size() << endl;

  bool noConflict = true;

  if (options().smt.extRewPrep != options::ExtRewPrepMode::OFF)
  {
    applyPass("ext-rew-pre", ap);
  }

  // Unconstrained simplification
  if (options().smt.unconstrainedSimp)
  {
    applyPass("rewrite", ap);
    applyPass("unconstrained-simplifier", ap);
  }

  if (options().bv.bvIntroducePow2)
  {
    applyPass("bv-intro-pow2", ap);
  }

  // Lift bit-vectors of size 1 to bool
  if (options().bv.bitvectorToBool)
  {
    applyPass("bv-to-bool", ap);
  }
  if (options().smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    applyPass("bv-to-int", ap);
  }
  if (options().smt.foreignTheoryRewrite)
  {
    applyPass("foreign-theory-rewrite", ap);
  }

  // Assertions MUST BE guaranteed to be rewritten by this point
  applyPass("rewrite", ap);

  // Convert non-top-level Booleans to bit-vectors of size 1
  if (options().bv.boolToBitvector != options::BoolToBVMode::OFF)
  {
    applyPass("bool-to-bv", ap);
  }
  if (options().sep.sepPreSkolemEmp)
  {
    applyPass("sep-skolem-emp", ap);
  }

  if (logicInfo().isQuantified())
  {
    // remove rewrite rules, apply pre-skolemization to existential quantifiers
    applyPass("quantifiers-preprocess", ap);

    // fmf-fun : assume admissible functions, applying preprocessing reduction
    // to FMF
    if (options().quantifiers.fmfFunWellDefined)
    {
      applyPass("fun-def-fmf", ap);
    }
  }
  if (!options().strings.stringLazyPreproc)
  {
    applyPass("strings-eager-pp", ap);
    // needed since strings eager preprocessing may reintroduce skolems that
    // were already solved for in incremental mode
    applyPass("apply-substs", ap);
  }
  if (options().smt.sortInference || options().uf.ufssFairnessMonotone)
  {
    applyPass("sort-inference", ap);
  }

  if (options().arith.pbRewrites)
  {
    applyPass("pseudo-boolean-processor", ap);
  }

  // rephrasing normal inputs as sygus problems
  if (options().quantifiers.sygusInference)
  {
    applyPass("sygus-infer", ap);
  }

  Trace("smt-proc") << "ProcessAssertions::processAssertions() : pre-simplify"
                    << endl;
  dumpAssertions("assertions::pre-simplify", ap);
  Trace("assertions::pre-simplify") << std::endl;
  verbose(2) << "simplifying assertions..." << std::endl;
  noConflict = simplifyAssertions(ap);
  if (!noConflict)
  {
    ++(d_slvStats.d_simplifiedToFalse);
  }
  Trace("smt-proc") << "ProcessAssertions::processAssertions() : post-simplify"
                    << endl;
  dumpAssertions("assertions::post-simplify", ap);
  Trace("assertions::post-simplify") << std::endl;

  if (options().smt.staticLearning)
  {
    applyPass("static-learning", ap);
  }
  Trace("smt") << " assertions     : " << ap.size() << endl;

  if (options().smt.learnedRewrite)
  {
    applyPass("learned-rewrite", ap);
  }

  if (options().smt.earlyIteRemoval)
  {
    d_slvStats.d_numAssertionsPre += ap.size();
    applyPass("ite-removal", ap);
    // This is needed because when solving incrementally, removeITEs may
    // introduce skolems that were solved for earlier and thus appear in the
    // substitution map.
    applyPass("apply-substs", ap);
    d_slvStats.d_numAssertionsPost += ap.size();
  }

  if (options().smt.repeatSimp)
  {
    dumpAssertions("assertions::pre-repeat-simplify", ap);
    Trace("assertions::pre-repeat-simplify") << std::endl;
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : pre-repeat-simplify"
        << endl;
    verbose(2) << "re-simplifying assertions..." << std::endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions(ap);
    Trace("smt-proc")
        << "ProcessAssertions::processAssertions() : post-repeat-simplify"
        << endl;
    dumpAssertions("assertions::post-repeat-simplify", ap);
    Trace("assertions::post-repeat-simplify") << std::endl;
  }

  if (logicInfo().isHigherOrder())
  {
    applyPass("ho-elim", ap);
  }
  
  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  Trace("smt") << " assertions     : " << ap.size() << endl;

  Trace("smt") << "ProcessAssertions::processAssertions() POST SIMPLIFICATION"
               << endl;
  Trace("smt") << " assertions     : " << ap.size() << endl;

  // ensure rewritten
  applyPass("rewrite", ap);

  // Note the two passes below are very similar. Ideally, they could be
  // done in a single traversal, e.g. do both static (ppStaticRewrite) and
  // normal (ppRewrite) in one pass. However, we do theory-preprocess
  // separately since it is cached in TheoryPreprocessor, which is subsequently
  // used for theory preprocessing lemmas as well, whereas a combined
  // pass could not be used for this purpose.

  // rewrite terms based on static theory-specific rewriting
  applyPass("static-rewrite", ap);
  // apply theory preprocess, which includes ITE removal
  applyPass("theory-preprocess", ap);
  // notice that we do not apply substitutions as a last step here, since
  // the range of substitutions is not theory-preprocessed.

  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    applyPass("bv-eager-atoms", ap);
  }

  Trace("smt-proc") << "ProcessAssertions::apply() end" << endl;
  dumpAssertions("assertions::post-everything", ap);
  Trace("assertions::post-everything") << std::endl;
  if (isOutputOn(OutputTag::POST_ASSERTS))
  {
    std::ostream& outPA = d_env.output(OutputTag::POST_ASSERTS);
    outPA << ";; post-asserts start" << std::endl;
    dumpAssertionsToStream(outPA, ap);
    outPA << ";; post-asserts end" << std::endl;
  }

  return noConflict;
}

// returns false if simplification led to "false"
bool ProcessAssertions::simplifyAssertions(AssertionPipeline& ap)
{
  spendResource(Resource::PreprocessStep);
  try
  {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "ProcessAssertions::simplify()" << endl;

    if (options().smt.simplificationMode != options::SimplificationMode::NONE)
    {
      // Perform non-clausal simplification
      PreprocessingPassResult res = applyPass("non-clausal-simp", ap);
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
          // disables miplib processing during re-simplification, which we don't
          // expect to be useful
          d_simplifyAssertionsDepth <= 1)
      {
        applyPass("miplib-trick", ap);
      }
      else
      {
        Trace("simplify") << "ProcessAssertions::simplify(): "
                          << "skipping miplib pseudobooleans pass..." << endl;
      }
    }

    Trace("smt") << " assertions     : " << ap.size() << endl;

    // ITE simplification
    if (options().smt.doITESimp
        && (d_simplifyAssertionsDepth <= 1 || options().smt.doITESimpOnRepeat))
    {
      PreprocessingPassResult res = applyPass("ite-simp", ap);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        verbose(2) << "...ITE simplification found unsat..." << std::endl;
        return false;
      }
    }

    Trace("smt") << " assertions     : " << ap.size() << endl;

    // Unconstrained simplification
    if (options().smt.unconstrainedSimp)
    {
      applyPass("unconstrained-simplifier", ap);
    }

    if (options().smt.repeatSimp
        && options().smt.simplificationMode
               != options::SimplificationMode::NONE)
    {
      PreprocessingPassResult res = applyPass("non-clausal-simp", ap);
      if (res == PreprocessingPassResult::CONFLICT)
      {
        return false;
      }
    }
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

void ProcessAssertions::dumpAssertions(const std::string& key,
                                       const AssertionPipeline& ap)
{
  bool isTraceOn = TraceIsOn(key);
  if (!isTraceOn)
  {
    return;
  }
  std::stringstream ss;
  dumpAssertionsToStream(ss, ap);
  Trace(key) << ";;; " << key << " start" << std::endl;
  Trace(key) << ss.str();
  Trace(key) << ";;; " << key << " end " << std::endl;
}

void ProcessAssertions::dumpAssertionsToStream(std::ostream& os,
                                               const AssertionPipeline& ap)
{
  PrintBenchmark pb(Printer::getPrinter(os));
  std::vector<Node> assertions;
  // Notice that users may define ordinary and recursive functions. The latter
  // get added to the list of assertions as quantified formulas. Since we are
  // interested in printing the result of preprocessed quantified formulas
  // corresponding to recursive function definitions and not the original
  // definitions, we do not explicitly record recursive function definitions.
  //
  // Furthermore, we may have eliminated user variables from the preprocessed
  // input, often via solving an equality (= x t) and adding x -> t to the
  // top-level substitutions. We include these in the output as well. Note that
  // ordinary define-fun are also included in this substitution.
  //
  // In summary, this means that define-fun-rec are expanded to
  // (declare-fun ...) + (assert (forall ...)) in the printing below, whereas
  // define-fun are preserved. Further inferred top-level substitutions are
  // also printed as define-fun.
  std::vector<Node> defs;
  const theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
  const std::unordered_map<Node, Node>& ss = sm.getSubstitutions();
  for (const std::pair<const Node, Node>& s : ss)
  {
    defs.push_back(s.first.eqNode(s.second));
  }
  for (size_t i = 0, size = ap.size(); i < size; i++)
  {
    assertions.push_back(ap[i]);
  }
  pb.printBenchmark(os, logicInfo().getLogicString(), defs, assertions);
}

PreprocessingPassResult ProcessAssertions::applyPass(const std::string& pname,
                                                     AssertionPipeline& ap)
{
  dumpAssertions("assertions::pre-" + pname, ap);
  PreprocessingPassResult res = d_passes[pname]->apply(&ap);
  dumpAssertions("assertions::post-" + pname, ap);
  return res;
}

}  // namespace smt
}  // namespace cvc5::internal
