/*********************                                                        */
/*! \file quantifiers_modules.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Class for initializing the modules of quantifiers engine
 **/

#include "theory/quantifiers/quantifiers_modules.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
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
      d_i_cbqi(nullptr),
      d_qsplit(nullptr),
      d_anti_skolem(nullptr),
      d_sygus_inst(nullptr)
{
}
QuantifiersModules::~QuantifiersModules() {}
void QuantifiersModules::initialize(QuantifiersEngine* qe,
                                    context::Context* c,
                                    std::vector<QuantifiersModule*>& modules)
{
  // add quantifiers modules
  if (options::quantConflictFind())
  {
    d_qcf.reset(new quantifiers::QuantConflictFind(qe, c));
    modules.push_back(d_qcf.get());
  }
  if (options::conjectureGen())
  {
    d_sg_gen.reset(new quantifiers::ConjectureGenerator(qe, c));
    modules.push_back(d_sg_gen.get());
  }
  if (!options::finiteModelFind() || options::fmfInstEngine())
  {
    d_inst_engine.reset(new quantifiers::InstantiationEngine(qe));
    modules.push_back(d_inst_engine.get());
  }
  if (options::cegqi())
  {
    d_i_cbqi.reset(new quantifiers::InstStrategyCegqi(qe));
    modules.push_back(d_i_cbqi.get());
    qe->getInstantiate()->addRewriter(d_i_cbqi->getInstRewriter());
  }
  if (options::sygus())
  {
    d_synth_e.reset(new quantifiers::SynthEngine(qe, c));
    modules.push_back(d_synth_e.get());
  }
  // finite model finding
  if (options::fmfBound())
  {
    d_bint.reset(new quantifiers::BoundedIntegers(c, qe));
    modules.push_back(d_bint.get());
  }
  if (options::finiteModelFind() || options::fmfBound())
  {
    d_model_engine.reset(new quantifiers::ModelEngine(c, qe));
    modules.push_back(d_model_engine.get());
  }
  if (options::quantDynamicSplit() != options::QuantDSplitMode::NONE)
  {
    d_qsplit.reset(new quantifiers::QuantDSplit(qe, c));
    modules.push_back(d_qsplit.get());
  }
  if (options::quantAntiSkolem())
  {
    d_anti_skolem.reset(new quantifiers::QuantAntiSkolem(qe));
    modules.push_back(d_anti_skolem.get());
  }
  if (options::quantAlphaEquiv())
  {
    d_alpha_equiv.reset(new quantifiers::AlphaEquivalence(qe));
  }
  // full saturation : instantiate from relevant domain, then arbitrary terms
  if (options::fullSaturateQuant() || options::fullSaturateInterleave())
  {
    d_rel_dom.reset(new quantifiers::RelevantDomain(qe));
    d_fs.reset(new quantifiers::InstStrategyEnum(qe, d_rel_dom.get()));
    modules.push_back(d_fs.get());
  }
  if (options::sygusInst())
  {
    d_sygus_inst.reset(new quantifiers::SygusInst(qe));
    modules.push_back(d_sygus_inst.get());
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
