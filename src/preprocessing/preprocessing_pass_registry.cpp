/*********************                                                        */
/*! \file preprocessing_pass_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Yoni Zohar, Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass registry
 **
 ** This file defines the classes PreprocessingPassRegistry, which keeps track
 ** of the available preprocessing passes.
 **/

#include "preprocessing/preprocessing_pass_registry.h"

#include <algorithm>
#include <utility>

#include "base/check.h"
#include "base/map_util.h"
#include "base/output.h"
#include "preprocessing/passes/ackermann.h"
#include "preprocessing/passes/apply_substs.h"
#include "preprocessing/passes/bool_to_bv.h"
#include "preprocessing/passes/bv_abstraction.h"
#include "preprocessing/passes/bv_eager_atoms.h"
#include "preprocessing/passes/bv_gauss.h"
#include "preprocessing/passes/bv_intro_pow2.h"
#include "preprocessing/passes/bv_to_bool.h"
#include "preprocessing/passes/bv_to_int.h"
#include "preprocessing/passes/extended_rewriter_pass.h"
#include "preprocessing/passes/global_negate.h"
#include "preprocessing/passes/ho_elim.h"
#include "preprocessing/passes/int_to_bv.h"
#include "preprocessing/passes/ite_removal.h"
#include "preprocessing/passes/ite_simp.h"
#include "preprocessing/passes/miplib_trick.h"
#include "preprocessing/passes/nl_ext_purify.h"
#include "preprocessing/passes/non_clausal_simp.h"
#include "preprocessing/passes/pseudo_boolean_processor.h"
#include "preprocessing/passes/quantifier_macros.h"
#include "preprocessing/passes/quantifiers_preprocess.h"
#include "preprocessing/passes/real_to_int.h"
#include "preprocessing/passes/rewrite.h"
#include "preprocessing/passes/sep_skolem_emp.h"
#include "preprocessing/passes/sort_infer.h"
#include "preprocessing/passes/static_learning.h"
#include "preprocessing/passes/sygus_inference.h"
#include "preprocessing/passes/synth_rew_rules.h"
#include "preprocessing/passes/theory_preprocess.h"
#include "preprocessing/passes/unconstrained_simplifier.h"
#include "preprocessing/preprocessing_pass.h"

namespace CVC4 {
namespace preprocessing {

using namespace CVC4::preprocessing::passes;

PreprocessingPassRegistry& PreprocessingPassRegistry::getInstance()
{
  static PreprocessingPassRegistry* ppReg = new PreprocessingPassRegistry();
  return *ppReg;
}

void PreprocessingPassRegistry::registerPassInfo(
    const std::string& name,
    std::function<PreprocessingPass*(PreprocessingPassContext*)> ctor)
{
  AlwaysAssert(!ContainsKey(d_ppInfo, name));
  d_ppInfo[name] = ctor;
}

PreprocessingPass* PreprocessingPassRegistry::createPass(
    PreprocessingPassContext* ppCtx, const std::string& name)
{
  return d_ppInfo[name](ppCtx);
}

std::vector<std::string> PreprocessingPassRegistry::getAvailablePasses()
{
  std::vector<std::string> passes;
  for (const auto& info : d_ppInfo)
  {
    passes.push_back(info.first);
  }
  std::sort(passes.begin(), passes.end());
  return passes;
}

bool PreprocessingPassRegistry::hasPass(const std::string& name)
{
  return d_ppInfo.find(name) != d_ppInfo.end();
}

namespace {

/**
 * This method is stored by the `PreprocessingPassRegistry` and used to create
 * a new instance of the preprocessing pass T.
 *
 * @param ppCtx The preprocessing pass context passed to the constructor of
 *              the preprocessing pass
 */
template <class T>
PreprocessingPass* callCtor(PreprocessingPassContext* ppCtx)
{
  return new T(ppCtx);
}

}  // namespace

PreprocessingPassRegistry::PreprocessingPassRegistry()
{
  registerPassInfo("apply-substs", callCtor<ApplySubsts>);
  registerPassInfo("bv-gauss", callCtor<BVGauss>);
  registerPassInfo("static-learning", callCtor<StaticLearning>);
  registerPassInfo("ite-simp", callCtor<ITESimp>);
  registerPassInfo("global-negate", callCtor<GlobalNegate>);
  registerPassInfo("int-to-bv", callCtor<IntToBV>);
  registerPassInfo("bv-to-int", callCtor<BVToInt>);
  registerPassInfo("synth-rr", callCtor<SynthRewRulesPass>);
  registerPassInfo("real-to-int", callCtor<RealToInt>);
  registerPassInfo("sygus-infer", callCtor<SygusInference>);
  registerPassInfo("bv-to-bool", callCtor<BVToBool>);
  registerPassInfo("bv-intro-pow2", callCtor<BvIntroPow2>);
  registerPassInfo("sort-inference", callCtor<SortInferencePass>);
  registerPassInfo("sep-skolem-emp", callCtor<SepSkolemEmp>);
  registerPassInfo("rewrite", callCtor<Rewrite>);
  registerPassInfo("bv-abstraction", callCtor<BvAbstraction>);
  registerPassInfo("bv-eager-atoms", callCtor<BvEagerAtoms>);
  registerPassInfo("pseudo-boolean-processor",
                   callCtor<PseudoBooleanProcessor>);
  registerPassInfo("unconstrained-simplifier",
                   callCtor<UnconstrainedSimplifier>);
  registerPassInfo("quantifiers-preprocess", callCtor<QuantifiersPreprocess>);
  registerPassInfo("ite-removal", callCtor<IteRemoval>);
  registerPassInfo("miplib-trick", callCtor<MipLibTrick>);
  registerPassInfo("non-clausal-simp", callCtor<NonClausalSimp>);
  registerPassInfo("ackermann", callCtor<Ackermann>);
  registerPassInfo("ext-rew-pre", callCtor<ExtRewPre>);
  registerPassInfo("theory-preprocess", callCtor<TheoryPreprocess>);
  registerPassInfo("quantifier-macros", callCtor<QuantifierMacros>);
  registerPassInfo("nl-ext-purify", callCtor<NlExtPurify>);
  registerPassInfo("bool-to-bv", callCtor<BoolToBV>);
  registerPassInfo("ho-elim", callCtor<HoElim>);
}

}  // namespace preprocessing
}  // namespace CVC4
