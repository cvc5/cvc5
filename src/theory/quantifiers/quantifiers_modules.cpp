/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for initializing the modules of quantifiers engine.
 */

#include "theory/quantifiers/quantifiers_modules.h"

#include "options/quantifiers_options.h"
#include "options/strings_options.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantifiersModules::QuantifiersModules()
    : d_rel_dom(nullptr),
      d_alpha_equiv(nullptr),
      d_inst_engine(nullptr),
      d_model_engine(nullptr),
      d_bint(nullptr),
      d_qcf(nullptr),
      d_sg_gen(nullptr),
      d_synth_e(nullptr),
      d_fs(nullptr),
      d_ipool(nullptr),
      d_i_cbqi(nullptr),
      d_qsplit(nullptr),
      d_sygus_inst(nullptr)
{
}
QuantifiersModules::~QuantifiersModules() {}
void QuantifiersModules::initialize(Env& env,
                                    QuantifiersState& qs,
                                    QuantifiersInferenceManager& qim,
                                    QuantifiersRegistry& qr,
                                    TermRegistry& tr,
                                    QModelBuilder* builder,
                                    std::vector<QuantifiersModule*>& modules)
{
  // add quantifiers modules
  const Options& options = env.getOptions();
  if (options.quantifiers.conflictBasedInst)
  {
    d_qcf.reset(new QuantConflictFind(env, qs, qim, qr, tr));
    modules.push_back(d_qcf.get());
  }
  if (options.quantifiers.conjectureGen)
  {
    d_sg_gen.reset(new ConjectureGenerator(env, qs, qim, qr, tr));
    modules.push_back(d_sg_gen.get());
  }
  if (options.quantifiers.eMatching)
  {
    d_inst_engine.reset(new InstantiationEngine(env, qs, qim, qr, tr));
    modules.push_back(d_inst_engine.get());
  }
  if (options.quantifiers.cegqi)
  {
    d_i_cbqi.reset(new InstStrategyCegqi(env, qs, qim, qr, tr));
    modules.push_back(d_i_cbqi.get());
    qim.getInstantiate()->addRewriter(d_i_cbqi->getInstRewriter());
  }
  if (options.quantifiers.sygus)
  {
    d_synth_e.reset(new SynthEngine(env, qs, qim, qr, tr));
    modules.push_back(d_synth_e.get());
  }
  // bounded integer instantiation is used when the user requests it via
  // fmfBound, or if strings are enabled.
  if (options.quantifiers.fmfBound || options.strings.stringExp)
  {
    d_bint.reset(new BoundedIntegers(env, qs, qim, qr, tr));
    modules.push_back(d_bint.get());
  }

  if (options.quantifiers.finiteModelFind || options.quantifiers.fmfBound
      || options.strings.stringExp)
  {
    d_model_engine.reset(new ModelEngine(env, qs, qim, qr, tr, builder));
    modules.push_back(d_model_engine.get());
  }
  if (options.quantifiers.quantDynamicSplit != options::QuantDSplitMode::NONE)
  {
    d_qsplit.reset(new QuantDSplit(env, qs, qim, qr, tr));
    modules.push_back(d_qsplit.get());
  }
  if (options.quantifiers.quantAlphaEquiv)
  {
    d_alpha_equiv.reset(new AlphaEquivalence(env));
  }
  // full saturation : instantiate from relevant domain, then arbitrary terms
  if (options.quantifiers.enumInst || options.quantifiers.enumInstInterleave)
  {
    d_rel_dom.reset(new RelevantDomain(env, qs, qr, tr));
    d_fs.reset(new InstStrategyEnum(env, qs, qim, qr, tr, d_rel_dom.get()));
    modules.push_back(d_fs.get());
  }
  if (options.quantifiers.poolInst)
  {
    d_ipool.reset(new InstStrategyPool(env, qs, qim, qr, tr));
    modules.push_back(d_ipool.get());
  }
  if (options.quantifiers.sygusInst)
  {
    d_sygus_inst.reset(new SygusInst(env, qs, qim, qr, tr));
    modules.push_back(d_sygus_inst.get());
  }
  if (options.quantifiers.mbqi)
  {
    d_mbqi.reset(new InstStrategyMbqi(env, qs, qim, qr, tr));
    modules.push_back(d_mbqi.get());
  }
  if (options.quantifiers.oracles)
  {
    d_oracleEngine.reset(new OracleEngine(env, qs, qim, qr, tr));
    modules.push_back(d_oracleEngine.get());
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
