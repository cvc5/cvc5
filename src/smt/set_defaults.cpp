/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of setting default options.
 */

#include "smt/set_defaults.h"

#include <sstream>

#include "base/output.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/bags_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_options.h"
#include "options/ff_options.h"
#include "options/fp_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/parallel_options.h"
#include "options/parser_options.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/prop_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/sets_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "smt/logic_exception.h"
#include "theory/theory.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

/**
 * Set domain.optName to value due to reason. Notify if value changes.
 * Note this macro should be used if the value is concrete.
 */
#define SET_AND_NOTIFY(domain, optName, value, reason)                      \
  if (opts.write_##domain().optName != value)                               \
  {                                                                         \
    notifyModifyOption(options::domain::longName::optName, #value, reason); \
    opts.write_##domain().optName = value;                                  \
  }
/**
 * Set domain.optName to value due to reason. Notify if value changes.
 *
 * Note this macro should be used if the value passed to the macro is not
 * concrete (i.e., stored in a variable).
 */
#define SET_AND_NOTIFY_VAL_SYM(domain, optName, value, reason)    \
  if (opts.write_##domain().optName != value)                     \
  {                                                               \
    std::stringstream sstmp;                                      \
    sstmp << value;                                               \
    notifyModifyOption(                                           \
        options::domain::longName::optName, sstmp.str(), reason); \
    opts.write_##domain().optName = value;                        \
  }
/**
 * Set domain.optName to value due to reason if the option was not already set
 * by the user. Notify if value changes.
 * Note this macro should be used if the value is concrete.
 */
#define SET_AND_NOTIFY_IF_NOT_USER(domain, optName, value, reason)          \
  if (!opts.write_##domain().optName##WasSetByUser                          \
      && opts.write_##domain().optName != value)                            \
  {                                                                         \
    notifyModifyOption(options::domain::longName::optName, #value, reason); \
    opts.write_##domain().optName = value;                                  \
  }
/**
 * Set domain.optName to value due to reason if the option was not already set
 * by the user. Notify if value changes.
 */
#define SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(domain, optName, value, reason) \
  if (!opts.write_##domain().optName##WasSetByUser                         \
      && opts.write_##domain().optName != value)                           \
  {                                                                        \
    std::stringstream sstmp;                                               \
    sstmp << value;                                                        \
    notifyModifyOption(                                                    \
        options::domain::longName::optName, sstmp.str(), reason);          \
    opts.write_##domain().optName = value;                                 \
  }

SetDefaults::SetDefaults(Env& env, bool isInternalSubsolver)
    : EnvObj(env), d_isInternalSubsolver(isInternalSubsolver)
{
}

void SetDefaults::setDefaults(LogicInfo& logic, Options& opts)
{
  // initial changes that are independent of logic, and may impact the logic
  setDefaultsPre(opts);
  // now, finalize the logic
  finalizeLogic(logic, opts);
  // further changes to options based on the logic
  setDefaultsPost(logic, opts);
}

void SetDefaults::setDefaultsPre(Options& opts)
{
  // safe options
  if (options().base.safeOptions)
  {
    // all "experimental" theories that are enabled by default should be
    // disabled here
    SET_AND_NOTIFY_IF_NOT_USER(uf, hoExp, false, "safe options");
    SET_AND_NOTIFY_IF_NOT_USER(arith, arithExp, false, "safe options");
    SET_AND_NOTIFY_IF_NOT_USER(sep, sepExp, false, "safe options");
    SET_AND_NOTIFY_IF_NOT_USER(bags, bagsExp, false, "safe options");
    SET_AND_NOTIFY_IF_NOT_USER(ff, ffExp, false, "safe options");
    // these are disabled by default but are listed here in case they are
    // enabled by default later
    SET_AND_NOTIFY_IF_NOT_USER(fp, fpExp, false, "safe options");
    SET_AND_NOTIFY_IF_NOT_USER(sets, setsExp, false, "safe options");
  }
  // implied options
  if (opts.smt.debugCheckModels)
  {
    SET_AND_NOTIFY(smt, checkModels, true, "debugCheckModels");
  }
  if (opts.smt.checkModels || opts.driver.dumpModels)
  {
    SET_AND_NOTIFY(smt, produceModels, true, "check or dump models");
  }
  if (opts.smt.checkModels)
  {
    SET_AND_NOTIFY(smt, produceAssignments, true, "checkModels");
  }
  // unsat cores and proofs shenanigans
  if (opts.driver.dumpDifficulty)
  {
    SET_AND_NOTIFY(smt, produceDifficulty, true, "dumpDifficulty");
  }
  if (opts.smt.checkUnsatCores || opts.driver.dumpUnsatCores
      || opts.driver.dumpUnsatCoresLemmas || opts.smt.unsatAssumptions
      || opts.smt.minimalUnsatCores
      || opts.smt.unsatCoresMode != options::UnsatCoresMode::OFF)
  {
    SET_AND_NOTIFY(
        smt, produceUnsatCores, true, "option requiring unsat cores");
  }
  if (opts.smt.produceUnsatCores
      && opts.smt.unsatCoresMode == options::UnsatCoresMode::OFF)
  {
    SET_AND_NOTIFY(smt,
                   unsatCoresMode,
                   options::UnsatCoresMode::ASSUMPTIONS,
                   "enabling unsat cores");
  }
  if (opts.proof.checkProofSteps)
  {
    SET_AND_NOTIFY(smt, checkProofs, true, "check-proof-steps");
    // maximize the granularity
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
        proof,
        proofGranularityMode,
        options::ProofGranularityMode::DSL_REWRITE,
        "check-proof-steps");
  }
  // if check-proofs, dump-proofs, dump-unsat-cores-lemmas, or proof-mode=full,
  // then proofs being fully enabled is implied
  if (opts.smt.checkProofs || opts.driver.dumpProofs
      || opts.driver.dumpUnsatCoresLemmas
      || opts.smt.proofMode == options::ProofMode::FULL
      || opts.smt.proofMode == options::ProofMode::FULL_STRICT)
  {
    SET_AND_NOTIFY(smt, produceProofs, true, "option requiring proofs");
  }

  // this check assumes the user has requested *full* proofs
  if (opts.smt.produceProofs)
  {
    // if the user requested proofs, proof mode is (at least) full
    if (opts.smt.proofMode < options::ProofMode::FULL)
    {
      SET_AND_NOTIFY_IF_NOT_USER(
          smt, proofMode, options::ProofMode::FULL, "enabling proofs");
    }
    // Default granularity is theory rewrite if we are intentionally using
    // proofs, otherwise it is MACRO (e.g. if produce unsat cores is true)
    if (!opts.proof.proofGranularityModeWasSetByUser
        && opts.proof.proofGranularityMode
               < options::ProofGranularityMode::THEORY_REWRITE)
    {
      SET_AND_NOTIFY(proof,
                     proofGranularityMode,
                     options::ProofGranularityMode::THEORY_REWRITE,
                     "enabling proofs");
    }
    // unsat cores are available due to proofs being enabled, as long as
    // SAT proofs are available
    if (opts.smt.unsatCoresMode != options::UnsatCoresMode::SAT_PROOF
        && opts.smt.proofMode != options::ProofMode::PP_ONLY)
    {
      SET_AND_NOTIFY(smt, produceUnsatCores, true, "enabling proofs");
      if (options().prop.satSolver == options::SatSolverMode::MINISAT)
      {
        // if full proofs are available in minisat, use them for unsat cores
        SET_AND_NOTIFY(smt,
                       unsatCoresMode,
                       options::UnsatCoresMode::SAT_PROOF,
                       "enabling proofs, minisat");
      }
      else if (options().prop.satSolver == options::SatSolverMode::CADICAL)
      {
        // unsat cores available by assumptions by default if proofs are enabled
        // with CaDiCaL.
        SET_AND_NOTIFY(smt,
                       unsatCoresMode,
                       options::UnsatCoresMode::ASSUMPTIONS,
                       "enabling proofs, non-minisat");
      }
    }
    // note that this test assumes that granularity modes are ordered and
    // THEORY_REWRITE is gonna be, in the enum, after the lower granularity
    // levels
    if (opts.proof.proofFormatMode == options::ProofFormatMode::ALETHE)
    {
      if (opts.proof.proofGranularityMode
          < options::ProofGranularityMode::THEORY_REWRITE)
      {
        SET_AND_NOTIFY_VAL_SYM(
            proof,
            proofGranularityMode,
            options::ProofGranularityMode::THEORY_REWRITE,
            "Alethe requires granularity at least theory-rewrite");
      }
    }
  }
  if (!opts.smt.produceProofs)
  {
    if (opts.smt.proofMode != options::ProofMode::OFF)
    {
      // if (expert) user set proof mode to something other than off, enable
      // proofs
      SET_AND_NOTIFY(smt, produceProofs, true, "proof mode");
    }
    // if proofs weren't enabled by user, and we are producing difficulty
    if (opts.smt.produceDifficulty)
    {
      SET_AND_NOTIFY(smt, produceProofs, true, "produce difficulty");
      // ensure at least preprocessing proofs are enabled
      if (opts.smt.proofMode == options::ProofMode::OFF)
      {
        SET_AND_NOTIFY_VAL_SYM(
            smt, proofMode, options::ProofMode::PP_ONLY, "produce difficulty");
      }
    }
    // if proofs weren't enabled by user, and we are producing unsat cores
    if (opts.smt.produceUnsatCores)
    {
      SET_AND_NOTIFY(smt, produceProofs, true, "unsat cores");
      if (opts.smt.unsatCoresMode == options::UnsatCoresMode::SAT_PROOF)
      {
        // if requested to be based on proofs, we produce (preprocessing +) SAT
        // proofs
        SET_AND_NOTIFY_VAL_SYM(
            smt, proofMode, options::ProofMode::SAT, "unsat cores SAT proof");
      }
      else if (opts.smt.proofMode == options::ProofMode::OFF)
      {
        // otherwise, we always produce preprocessing proofs
        SET_AND_NOTIFY_VAL_SYM(
            smt, proofMode, options::ProofMode::PP_ONLY, "unsat cores");
      }
    }
  }
  if (opts.smt.produceProofs)
  {
    // determine the prop proof mode, based on which SAT solver we are using
    if (!opts.proof.propProofModeWasSetByUser)
    {
      if (opts.prop.satSolver == options::SatSolverMode::CADICAL)
      {
        // use SAT_EXTERNAL_PROVE for cadical by default
        SET_AND_NOTIFY(proof,
                       propProofMode,
                       options::PropProofMode::SAT_EXTERNAL_PROVE,
                       "cadical");
      }
    }
  }

  // if unsat cores are disabled, then unsat cores mode should be OFF. Similarly
  // for proof mode.
  Assert(opts.smt.produceUnsatCores
         == (opts.smt.unsatCoresMode != options::UnsatCoresMode::OFF));
  Assert(opts.smt.produceProofs
         == (opts.smt.proofMode != options::ProofMode::OFF));

  // if we require disabling options due to proofs, disable them now
  if (opts.smt.produceProofs)
  {
    std::stringstream reasonNoProofs;
    if (incompatibleWithProofs(opts, reasonNoProofs))
    {
      std::stringstream ss;
      ss << reasonNoProofs.str() << " not supported with proofs or unsat cores";
      throw OptionException(ss.str());
    }
  }
  if (d_isInternalSubsolver)
  {
    // these options must be disabled on internal subsolvers, as they are
    // used by the user to rephrase the input.
    SET_AND_NOTIFY_VAL_SYM(quantifiers,
                           sygusInference,
                           options::SygusInferenceMode::OFF,
                           "internal subsolver");
    // deep restart does not work with internal subsolvers?
    SET_AND_NOTIFY_VAL_SYM(smt,
                           deepRestartMode,
                           options::DeepRestartMode::NONE,
                           "internal subsolver");
  }
}

void SetDefaults::finalizeLogic(LogicInfo& logic, Options& opts) const
{
  if (opts.quantifiers.sygusInstWasSetByUser)
  {
    if (opts.quantifiers.sygusInst && isSygus(opts))
    {
      throw OptionException(std::string(
          "SyGuS instantiation quantifiers module cannot be enabled "
          "for SyGuS inputs."));
    }
  }
  else if (!isSygus(opts) && logic.isQuantified()
           && (logic.isPure(THEORY_FP)
               || (logic.isPure(THEORY_ARITH) && !logic.isLinear()
                   && logic.areIntegersUsed()))
           && !opts.base.incrementalSolving)
  {
    SET_AND_NOTIFY(quantifiers, sygusInst, true, "logic");
  }

  if (opts.bv.bitblastMode == options::BitblastMode::EAGER)
  {
    if (opts.smt.produceModels
        && (logic.isTheoryEnabled(THEORY_ARRAYS)
            || logic.isTheoryEnabled(THEORY_UF)))
    {
      if (opts.bv.bitblastModeWasSetByUser
          || opts.smt.produceModelsWasSetByUser)
      {
        std::stringstream ss;
        ss << "Eager bit-blasting currently does not support model generation ";
        ss << "for the combination of bit-vectors with arrays or uinterpreted ";
        ss << "functions. Try --" << options::bv::longName::bitblastMode << "="
           << options::BitblastMode::LAZY << ".";
        throw OptionException(ss.str());
      }
      SET_AND_NOTIFY(
          bv, bitblastMode, options::BitblastMode::LAZY, "model generation");
    }
    else if (!opts.base.incrementalSolving)
    {
      // if not incremental, we rely on ackermann to eliminate other theories.
      SET_AND_NOTIFY(smt, ackermann, true, "bit-blast eager");
    }
    else if (logic.isQuantified() || !logic.isPure(THEORY_BV))
    {
      // requested bitblast=eager in incremental mode, must be QF_BV only.
      throw OptionException(
          std::string("Eager bit-blasting is only support in incremental mode "
                      "if the logic is quantifier-free bit-vectors"));
    }
  }

  if (opts.smt.solveIntAsBV > 0)
  {
    // Int to BV currently always eliminates arithmetic completely (or otherwise
    // fails). Thus, it is safe to eliminate arithmetic. Also, bit-vectors
    // are required.
    logic = logic.getUnlockedCopy();
    logic.enableTheory(THEORY_BV);
    logic.disableTheory(THEORY_ARITH);
    logic.lock();
  }

  if (opts.smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    if (opts.bv.boolToBitvector != options::BoolToBVMode::OFF)
    {
      std::stringstream ss;
      ss << "solving bitvectors as integers is incompatible with --"
         << options::bv::longName::boolToBitvector << ".";
      throw OptionException(ss.str());
    }
    if (logic.isTheoryEnabled(THEORY_BV))
    {
      logic = logic.getUnlockedCopy();
      logic.enableIntegers();
      logic.arithNonLinear();
      logic.lock();
    }
  }

  // set options about ackermannization
  if (opts.smt.ackermann && opts.smt.produceModels
      && (logic.isTheoryEnabled(THEORY_ARRAYS)
          || logic.isTheoryEnabled(THEORY_UF)))
  {
    if (opts.smt.produceModelsWasSetByUser)
    {
      throw OptionException(std::string(
          "Ackermannization currently does not support model generation."));
    }
    SET_AND_NOTIFY(smt, ackermann, false, "model generation");
    // we are not relying on ackermann to eliminate theories in this case
    Assert(opts.bv.bitblastMode != options::BitblastMode::EAGER);
  }

  if (opts.smt.ackermann)
  {
    if (logic.isTheoryEnabled(THEORY_UF))
    {
      logic = logic.getUnlockedCopy();
      logic.disableTheory(THEORY_UF);
      logic.lock();
    }
  }

  // Set default options associated with strings-exp, which is enabled by
  // default if the logic includes strings. Note that enabling stringExp
  // enables quantifiers in the logic, and enables the bounded integer
  // quantifiers module for processing *only* bounded quantifiers generated by
  // the strings theory. It should not have an impact otherwise.
  if (logic.isTheoryEnabled(THEORY_STRINGS)
      && !options().strings.stringExpWasSetByUser)
  {
    SET_AND_NOTIFY(strings, stringExp, true, "logic including strings");
  }
  // If strings-exp is enabled, we require quantifiers. We also enable them
  // if we are using eager string preprocessing or aggressive regular expression
  // elimination, which may introduce quantified formulas at preprocess time.
  if (opts.strings.stringExp || !opts.strings.stringLazyPreproc
      || opts.strings.regExpElim == options::RegExpElimMode::AGG)
  {
    // We require quantifiers since extended functions reduce using them.
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
      Trace("smt") << "turning on quantifier logic, for strings-exp"
                   << std::endl;
    }
    // Note we allow E-matching by default to support combinations of sequences
    // and quantifiers. We also do not enable fmfBound here, which would
    // enable bounded integer instantiation for *all* quantifiers. Instead,
    // the bounded integers module will always process internally generated
    // quantifiers (those marked with InternalQuantAttribute).
  }

  if (opts.arrays.arraysExp)
  {
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
    }
  }

  // We now know whether the input uses sygus. Update the logic to incorporate
  // the theories we need internally for handling sygus problems.
  if (usesSygus(opts))
  {
    logic = logic.getUnlockedCopy();
    logic.enableSygus();
    logic.lock();
  }

  // widen the logic
  widenLogic(logic, opts);

  // check if we have any options that are not supported with quantified logics
  if (logic.isQuantified())
  {
    std::stringstream reasonNoQuant;
    if (incompatibleWithQuantifiers(opts, reasonNoQuant))
    {
      std::stringstream ss;
      ss << reasonNoQuant.str() << " not supported in quantified logics.";
      throw OptionException(ss.str());
    }
  }
  // check if we have separation logic heap types
  if (d_env.hasSepHeap())
  {
    std::stringstream reasonNoSepLogic;
    if (incompatibleWithSeparationLogic(opts, reasonNoSepLogic))
    {
      std::stringstream ss;
      ss << reasonNoSepLogic.str()
         << " not supported when using separation logic.";
      throw OptionException(ss.str());
    }
  }
}

void SetDefaults::setDefaultsPost(const LogicInfo& logic, Options& opts) const
{
  SET_AND_NOTIFY(smt, produceAssertions, true, "always enabled");

  if (opts.smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    /**
     * Operations on 1 bits are better handled as Boolean operations
     * than as integer operations.
     * Therefore, we enable bv-to-bool, which runs before
     * the translation to integers.
     */
    SET_AND_NOTIFY(bv, bitvectorToBool, true, "solve-bv-as-int");
  }

  // Disable options incompatible with incremental solving, or output an error
  // if enabled explicitly.
  if (opts.base.incrementalSolving)
  {
    std::stringstream reasonNoInc;
    std::stringstream suggestNoInc;
    if (incompatibleWithIncremental(logic, opts, reasonNoInc, suggestNoInc))
    {
      std::stringstream ss;
      ss << reasonNoInc.str() << " not supported with incremental solving. "
         << suggestNoInc.str();
      throw OptionException(ss.str());
    }
  }

  // Disable options incompatible with unsat cores or output an error if enabled
  // explicitly
  if (opts.smt.produceUnsatCores)
  {
    // check if the options are not compatible with unsat cores
    std::stringstream reasonNoUc;
    if (incompatibleWithUnsatCores(opts, reasonNoUc))
    {
      std::stringstream ss;
      ss << reasonNoUc.str() << " not supported with unsat cores";
      throw OptionException(ss.str());
    }
  }
  else
  {
    // Turn on unconstrained simplification for QF_AUFBV
    if (!opts.smt.unconstrainedSimpWasSetByUser
        && !opts.base.incrementalSolving)
    {
      // It is also currently incompatible with arithmetic, force the option
      // off.
      bool uncSimp = !opts.base.incrementalSolving && !logic.isQuantified()
                     && !opts.smt.produceModels && !opts.smt.produceAssignments
                     && !opts.smt.checkModels
                     && logic.isTheoryEnabled(THEORY_ARRAYS)
                     && logic.isTheoryEnabled(THEORY_BV)
                     && !logic.isTheoryEnabled(THEORY_ARITH);
      SET_AND_NOTIFY_VAL_SYM(
          smt, unconstrainedSimp, uncSimp, "logic and options");
    }

    // by default, nonclausal simplification is off for QF_SAT
    if (!opts.smt.simplificationModeWasSetByUser)
    {
      bool qf_sat = logic.isPure(THEORY_BOOL) && !logic.isQuantified();
      // simplification=none works better for SMT LIB benchmarks with
      // quantifiers, not others
      if (qf_sat)
      {
        SET_AND_NOTIFY_VAL_SYM(smt,
                               simplificationMode,
                               options::SimplificationMode::NONE,
                               "logic");
      }
      else
      {
        SET_AND_NOTIFY_VAL_SYM(smt,
                               simplificationMode,
                               options::SimplificationMode::BATCH,
                               "logic");
      }
    }
  }

  if (opts.quantifiers.cegqiBv && logic.isQuantified())
  {
    if (opts.bv.boolToBitvector != options::BoolToBVMode::OFF)
    {
      if (opts.bv.boolToBitvectorWasSetByUser)
      {
        throw OptionException(
            "bool-to-bv != off not supported with CEGQI BV for quantified "
            "logics");
      }
      SET_AND_NOTIFY_VAL_SYM(
          bv, boolToBitvector, options::BoolToBVMode::OFF, "cegqiBv");
    }
  }

  // cases where we need produce models
  if (opts.smt.produceAssignments || usesSygus(opts))
  {
    SET_AND_NOTIFY(smt, produceModels, true, "produce assignments or sygus");
  }

  // --ite-simp is an experimental option designed for QF_LIA/nec. This
  // technique is experimental. This benchmark set also requires removing ITEs
  // during preprocessing, before repeating simplification. Hence, we enable
  // this by default.
  if (opts.smt.doITESimp)
  {
    SET_AND_NOTIFY_IF_NOT_USER(smt, earlyIteRemoval, true, "doITESimp");
  }

  // Set the options for the theoryOf
  if (!opts.theory.theoryOfModeWasSetByUser)
  {
    if (logic.isSharingEnabled() && !logic.isTheoryEnabled(THEORY_BV)
        && !logic.isTheoryEnabled(THEORY_STRINGS)
        && !logic.isTheoryEnabled(THEORY_SETS)
        && !logic.isTheoryEnabled(THEORY_BAGS)
        && !(logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
             && !logic.isQuantified()))
    {
      SET_AND_NOTIFY_VAL_SYM(theory,
                             theoryOfMode,
                             options::TheoryOfMode::THEORY_OF_TERM_BASED,
                             "logic");
    }
  }

  // by default, symmetry breaker is on only for non-incremental QF_UF
  if (!opts.uf.ufSymmetryBreakerWasSetByUser)
  {
    // Only applies to non-incremental QF_UF.
    bool qf_uf_noinc = logic.isPure(THEORY_UF) && !logic.isQuantified()
                       && !opts.base.incrementalSolving;
    // We disable this technique when using unsat core production, since it
    // uses a non-standard implementation that sends (unsound) lemmas during
    // presolve.
    // We also disable it by default if safe unsat cores are enabled, or if
    // the proof mode is FULL_STRICT.
    bool val = qf_uf_noinc && !safeUnsatCores(opts)
               && opts.smt.proofMode != options::ProofMode::FULL_STRICT;
    SET_AND_NOTIFY_VAL_SYM(uf, ufSymmetryBreaker, val, "logic and options");
  }

  // If in arrays, set the UF handler to arrays
  if (logic.isTheoryEnabled(THEORY_ARRAYS) && !logic.isHigherOrder()
      && !opts.quantifiers.finiteModelFind
      && (!logic.isQuantified()
          || (logic.isQuantified() && !logic.isTheoryEnabled(THEORY_UF))))
  {
    d_env.setUninterpretedSortOwner(THEORY_ARRAYS);
  }
  else
  {
    d_env.setUninterpretedSortOwner(THEORY_UF);
  }

  if (!opts.smt.simplifyWithCareEnabledWasSetByUser)
  {
    bool qf_aufbv =
        !logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF) && logic.isTheoryEnabled(THEORY_BV);
    SET_AND_NOTIFY_VAL_SYM(smt, simplifyWithCareEnabled, qf_aufbv, "logic");
  }
  // Turn off array eager index splitting for QF_AUFLIA
  if (!opts.arrays.arraysEagerIndexSplittingWasSetByUser)
  {
    if (!logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF)
        && logic.isTheoryEnabled(THEORY_ARITH))
    {
      SET_AND_NOTIFY(arrays, arraysEagerIndexSplitting, false, "logic");
    }
  }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if (!opts.smt.repeatSimpWasSetByUser)
  {
    bool repeatSimp = !logic.isQuantified()
                      && (logic.isTheoryEnabled(THEORY_ARRAYS)
                          && logic.isTheoryEnabled(THEORY_UF)
                          && logic.isTheoryEnabled(THEORY_BV))
                      && !safeUnsatCores(opts);
    SET_AND_NOTIFY_VAL_SYM(smt, repeatSimp, repeatSimp, "logic");
  }

  /* Disable bit-level propagation by default for the BITBLAST solver. */
  if (opts.bv.bvSolver == options::BVSolver::BITBLAST)
  {
    SET_AND_NOTIFY(bv, bitvectorPropagate, false, "bitblast solver");
  }

  if (opts.bv.boolToBitvector == options::BoolToBVMode::ALL
      && !logic.isTheoryEnabled(THEORY_BV))
  {
    if (opts.bv.boolToBitvectorWasSetByUser)
    {
      throw OptionException(
          "bool-to-bv=all not supported for non-bitvector logics.");
    }
    SET_AND_NOTIFY_VAL_SYM(
        bv, boolToBitvector, options::BoolToBVMode::OFF, "non-BV logic");
  }

  // Turn on arith rewrite equalities only for pure arithmetic
  if (!opts.arith.arithRewriteEqWasSetByUser)
  {
    bool arithRewriteEq =
        logic.isPure(THEORY_ARITH) && logic.isLinear() && !logic.isQuantified();
    SET_AND_NOTIFY_VAL_SYM(arith, arithRewriteEq, arithRewriteEq, "logic");
  }
  if (!opts.arith.arithHeuristicPivotsWasSetByUser)
  {
    int16_t heuristicPivots = 5;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      if (logic.isDifferenceLogic())
      {
        heuristicPivots = -1;
      }
      else if (!logic.areIntegersUsed())
      {
        heuristicPivots = 0;
      }
    }
    SET_AND_NOTIFY_VAL_SYM(
        arith, arithHeuristicPivots, heuristicPivots, "logic");
  }
  if (!opts.arith.arithPivotThresholdWasSetByUser)
  {
    uint16_t pivotThreshold = 2;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      if (logic.isDifferenceLogic())
      {
        pivotThreshold = 16;
      }
    }
    SET_AND_NOTIFY_VAL_SYM(arith, arithPivotThreshold, pivotThreshold, "logic");
  }
  if (!opts.arith.arithStandardCheckVarOrderPivotsWasSetByUser)
  {
    int16_t varOrderPivots = -1;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      varOrderPivots = 200;
    }
    SET_AND_NOTIFY_VAL_SYM(
        arith, arithStandardCheckVarOrderPivots, varOrderPivots, "logic");
  }
  if (logic.isPure(THEORY_ARITH) && !logic.areRealsUsed())
  {
    SET_AND_NOTIFY(
        arith, nlExtTangentPlanesInterleave, true, "pure integer logic");
  }
  if (!opts.arith.nlRlvAssertBoundsWasSetByUser)
  {
    bool val = !logic.isQuantified();
    // use bound inference to determine when bounds are irrelevant only when
    // the logic is quantifier-free
    SET_AND_NOTIFY_VAL_SYM(
        arith, nlRlvAssertBounds, val, "non-quantified logic");
  }

  // set the default decision mode
  setDefaultDecisionMode(logic, opts);

  // set up of central equality engine
  if (opts.theory.eeMode == options::EqEngineMode::CENTRAL)
  {
    // use the arithmetic equality solver by default
    SET_AND_NOTIFY_IF_NOT_USER(
        arith, arithEqSolver, true, "central equality engine");
  }

  if (logic.isHigherOrder())
  {
    SET_AND_NOTIFY(theory, assignFunctionValues, true, "higher-order logic");
  }

  // set all defaults in the quantifiers theory, which includes sygus
  setDefaultsQuantifiers(logic, opts);

  // shared selectors are generally not good to combine with standard
  // quantifier techniques e.g. E-matching
  if (logic.isQuantified() && !usesSygus(opts))
  {
    SET_AND_NOTIFY_IF_NOT_USER(
        datatypes, dtSharedSelectors, false, "quantified logic without SyGuS");
  }

  if (opts.prop.minisatSimpMode == options::MinisatSimpMode::ALL)
  {
    // cannot use minisat variable elimination for logics where a theory solver
    // introduces new literals into the search, or for parametric theories
    // which may introduce Boolean term variables. This includes quantifiers
    // (quantifier instantiation), and the lemma schemas used in non-linear
    // and sets. We also can't use it if models are enabled.
    if (logic.isTheoryEnabled(THEORY_SETS) || logic.isTheoryEnabled(THEORY_BAGS)
        || logic.isTheoryEnabled(THEORY_ARRAYS)
        || logic.isTheoryEnabled(THEORY_STRINGS)
        || logic.isTheoryEnabled(THEORY_DATATYPES) || logic.isQuantified()
        || opts.smt.produceModels || opts.smt.produceAssignments
        || opts.smt.checkModels
        || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
    {
      SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(prop,
                                         minisatSimpMode,
                                         options::MinisatSimpMode::CLAUSE_ELIM,
                                         "non-basic logic");
    }
  }

  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
      && opts.arith.nlRlvMode != options::NlRlvMode::NONE)
  {
    SET_AND_NOTIFY(theory, relevanceFilter, true, "nl relevance mode");
  }

  // For now, these array theory optimizations do not support model-building
  if (opts.smt.produceModels || opts.smt.produceAssignments
      || opts.smt.checkModels)
  {
    SET_AND_NOTIFY(arrays, arraysOptimizeLinear, false, "models");
  }

  if (opts.strings.stringFMF)
  {
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(strings,
                                       stringProcessLoopMode,
                                       options::ProcessLoopMode::SIMPLE,
                                       "strings-fmf");
  }

  // !!! All options that require disabling models go here
  std::stringstream reasonNoModel;
  if (incompatibleWithModels(opts, reasonNoModel))
  {
    std::string sOptNoModel = reasonNoModel.str();
    if (opts.smt.produceModels)
    {
      if (opts.smt.produceModelsWasSetByUser)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel << " with model generation.";
        throw OptionException(ss.str());
      }
      SET_AND_NOTIFY(smt, produceModels, false, sOptNoModel);
    }
    if (opts.smt.produceAssignments)
    {
      if (opts.smt.produceAssignmentsWasSetByUser)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (produce-assignments).";
        throw OptionException(ss.str());
      }
      SET_AND_NOTIFY(smt, produceAssignments, false, sOptNoModel);
    }
    if (opts.smt.checkModels)
    {
      if (opts.smt.checkModelsWasSetByUser)
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (check-models).";
        throw OptionException(ss.str());
      }
      SET_AND_NOTIFY(smt, checkModels, false, sOptNoModel);
    }
  }

  if (opts.bv.bitblastMode == options::BitblastMode::EAGER
      && !logic.isPure(THEORY_BV) && logic.getLogicString() != "QF_UFBV")
  {
    throw OptionException(
        "Eager bit-blasting does not currently support theory combination with "
        "any theory other than UF. ");
  }

#ifdef CVC5_USE_POLY
  if (logic == LogicInfo("QF_UFNRA"))
  {
    if (!opts.arith.nlCov && !opts.arith.nlCovWasSetByUser)
    {
      SET_AND_NOTIFY(arith, nlCov, true, "QF_UFNRA");
      SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
          arith, nlExt, options::NlExtMode::LIGHT, "QF_UFNRA");
    }
  }
  else if (logic.isQuantified() && logic.isTheoryEnabled(theory::THEORY_ARITH)
           && logic.areRealsUsed() && !logic.areIntegersUsed()
           && !logic.areTranscendentalsUsed())
  {
    if (!opts.arith.nlCov && !opts.arith.nlCovWasSetByUser)
    {
      SET_AND_NOTIFY(arith, nlCov, true, "logic with reals");
      SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
          arith, nlExt, options::NlExtMode::LIGHT, "logic with reals");
    }
  }
#else
  if (opts.arith.nlCov)
  {
    if (opts.arith.nlCovWasSetByUser)
    {
      std::stringstream ss;
      ss << "Cannot use --" << options::arith::longName::nlCov
         << " without configuring with --poly.";
      throw OptionException(ss.str());
    }
    else
    {
      SET_AND_NOTIFY(arith, nlCov, false, "no support for libpoly");
      SET_AND_NOTIFY_VAL_SYM(
          arith, nlExt, options::NlExtMode::FULL, "no support for libpoly");
    }
  }
#endif
  if (logic.isTheoryEnabled(theory::THEORY_ARITH) && logic.areTranscendentalsUsed())
  {
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
        arith, nlExt, options::NlExtMode::FULL, "logic with transcendentals");
  }
}

bool SetDefaults::isSygus(const Options& opts) const
{
  if (opts.quantifiers.sygus)
  {
    return true;
  }
  if (!d_isInternalSubsolver)
  {
    if (opts.smt.produceAbducts || opts.smt.produceInterpolants
        || opts.quantifiers.sygusInference != options::SygusInferenceMode::OFF)
    {
      // since we are trying to recast as sygus, we assume the input is sygus
      return true;
    }
  }
  return false;
}

bool SetDefaults::usesSygus(const Options& opts) const
{
  if (isSygus(opts))
  {
    return true;
  }
  if (!d_isInternalSubsolver && opts.quantifiers.sygusInst)
  {
    // sygus instantiation uses sygus, but it is not a sygus problem
    return true;
  }
  return false;
}

bool SetDefaults::usesInputConversion(const Options& opts,
                                      std::ostream& reason) const
{
  if (opts.smt.solveBVAsInt != options::SolveBVAsIntMode::OFF)
  {
    reason << "solveBVAsInt";
    return true;
  }
  if (opts.smt.solveIntAsBV > 0)
  {
    reason << "solveIntAsBV";
    return true;
  }
  if (opts.smt.solveRealAsInt)
  {
    reason << "solveRealAsInt";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithProofs(Options& opts,
                                         std::ostream& reason) const
{
  if (opts.parser.freshBinders)
  {
    // When fresh-binders is true, we do not support proof output.
    reason << "fresh-binders";
    return true;
  }
  if (opts.quantifiers.globalNegate)
  {
    // When global negate answers "unsat", it is not due to showing a set of
    // formulas is unsat. Thus, proofs do not apply.
    reason << "global-negate";
    return true;
  }
  bool isFullPf = (opts.smt.proofMode == options::ProofMode::FULL
                   || opts.smt.proofMode == options::ProofMode::FULL_STRICT);
  if (isSygus(opts))
  {
    // we don't support proofs with SyGuS. One issue is that SyGuS evaluation
    // functions are incompatible with our equality proofs. Moreover, enabling
    // proofs for sygus (sub)solvers is irrelevant, since they are not given
    // check-sat queries. Note however that we allow proofs in non-full modes
    // (e.g. unsat cores).
    if (isFullPf)
    {
      reason << "sygus";
      return true;
    }
  }
  // options that are automatically set to support proofs
  if (opts.bv.bvAssertInput)
  {
    SET_AND_NOTIFY_VAL_SYM(bv, bvAssertInput, false, "proofs");
  }
  // If proofs are required and the user did not specify a specific BV solver,
  // we make sure to use the proof producing BITBLAST_INTERNAL solver.
  if (isFullPf)
  {
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
        bv, bvSolver, options::BVSolver::BITBLAST_INTERNAL, "proofs");
  }
  SET_AND_NOTIFY_IF_NOT_USER(arith, nlCovVarElim, false, "proofs");
  if (opts.smt.deepRestartMode != options::DeepRestartMode::NONE)
  {
    reason << "deep restarts";
    return true;
  }
  // specific to SAT solver
  if (opts.prop.satSolver == options::SatSolverMode::CADICAL)
  {
    if (opts.proof.propProofMode == options::PropProofMode::PROOF)
    {
      reason << "(resolution) proofs not supported in cadical";
      return true;
    }
  }
  else if (opts.prop.satSolver == options::SatSolverMode::MINISAT)
  {
    if (opts.proof.propProofMode == options::PropProofMode::SKETCH)
    {
      reason << "(DRAT) proof sketch not supported in minisat";
      return true;
    }
  }
  if (options().theory.lemmaInprocess != options::LemmaInprocessMode::NONE)
  {
    // lemma inprocessing introduces depencencies from learned unit literals
    // that are not tracked.
    reason << "lemma inprocessing";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithModels(const Options& opts,
                                         std::ostream& reason) const
{
  if (opts.smt.unconstrainedSimpWasSetByUser && opts.smt.unconstrainedSimp)
  {
    reason << "unconstrained-simp";
    return true;
  }
  else if (opts.smt.sortInference)
  {
    reason << "sort-inference";
    return true;
  }
  else if (opts.prop.minisatSimpMode == options::MinisatSimpMode::ALL)
  {
    reason << "minisat-simplification";
    return true;
  }
  else if (opts.quantifiers.globalNegate)
  {
    reason << "global-negate";
    return true;
  }
  else if (opts.arrays.arraysWeakEquivalence)
  {
    reason << "arrays-weak-equiv";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithIncremental(const LogicInfo& logic,
                                              Options& opts,
                                              std::ostream& reason,
                                              std::ostream& suggest) const
{
  if (d_env.hasSepHeap())
  {
    reason << "separation logic";
    return true;
  }
  if (opts.smt.ackermann)
  {
    reason << "ackermann";
    return true;
  }
  if (opts.smt.unconstrainedSimp)
  {
    if (opts.smt.unconstrainedSimpWasSetByUser)
    {
      reason << "unconstrained simplification";
      return true;
    }
    SET_AND_NOTIFY(smt, unconstrainedSimp, false, "incremental solving");
  }
  if (opts.bv.bitblastMode == options::BitblastMode::EAGER
      && !logic.isPure(THEORY_BV))
  {
    reason << "eager bit-blasting in non-QF_BV logic";
    suggest << "Try --" << options::bv::longName::bitblastMode << "="
            << options::BitblastMode::LAZY << ".";
    return true;
  }
  if (opts.quantifiers.sygusInference != options::SygusInferenceMode::OFF)
  {
    if (opts.quantifiers.sygusInferenceWasSetByUser)
    {
      reason << "sygus inference";
      return true;
    }
    SET_AND_NOTIFY_VAL_SYM(quantifiers,
                           sygusInference,
                           options::SygusInferenceMode::OFF,
                           "incremental solving");
  }
  if (opts.quantifiers.sygusInst)
  {
    if (opts.quantifiers.sygusInstWasSetByUser)
    {
      reason << "sygus inst";
      return true;
    }
    SET_AND_NOTIFY(quantifiers, sygusInst, false, "incremental solving");
  }
  if (opts.smt.solveIntAsBV > 0)
  {
    reason << "solveIntAsBV";
    return true;
  }
  if (opts.smt.deepRestartMode != options::DeepRestartMode::NONE)
  {
    reason << "deep restarts";
    return true;
  }
  if (opts.parallel.computePartitions > 1)
  {
    reason << "compute partitions";
    return true;
  }

  // disable modes not supported by incremental
  SET_AND_NOTIFY(smt, sortInference, false, "incremental solving");
  SET_AND_NOTIFY(uf, ufssFairnessMonotone, false, "incremental solving");
  SET_AND_NOTIFY(quantifiers, globalNegate, false, "incremental solving");
  SET_AND_NOTIFY(quantifiers, cegqiNestedQE, false, "incremental solving");
  SET_AND_NOTIFY(arith, arithMLTrick, false, "incremental solving");
  return false;
}

bool SetDefaults::incompatibleWithUnsatCores(Options& opts,
                                             std::ostream& reason) const
{
  // All techniques that are incompatible with unsat cores are listed here.
  // A preprocessing pass is incompatible with unsat cores if
  // (A) its reasoning is not local, i.e. it may replace an assertion A by A'
  // where A does not imply A', or if it adds new assertions B that are not
  // tautologies, AND
  // (B) it does not track proofs.
  if (opts.smt.deepRestartMode != options::DeepRestartMode::NONE)
  {
    if (opts.smt.deepRestartModeWasSetByUser)
    {
      reason << "deep restarts";
      return true;
    }
    SET_AND_NOTIFY_VAL_SYM(
        smt, deepRestartMode, options::DeepRestartMode::NONE, "unsat cores");
  }
  if (opts.smt.learnedRewrite)
  {
    if (opts.smt.learnedRewriteWasSetByUser)
    {
      reason << "learned rewrites";
      return true;
    }
    SET_AND_NOTIFY(smt, learnedRewrite, false, "unsat cores");
  }
  // most static learning techniques are local, although arithmetic static
  // learning is not.
  if (opts.arith.arithStaticLearning)
  {
    if (opts.arith.arithStaticLearningWasSetByUser)
    {
      reason << "arith static learning";
      return true;
    }
    SET_AND_NOTIFY(arith, arithStaticLearning, false, "unsat cores");
  }

  if (opts.arith.pbRewrites)
  {
    if (opts.arith.pbRewritesWasSetByUser)
    {
      reason << "pseudoboolean rewrites";
      return true;
    }
    SET_AND_NOTIFY(arith, pbRewrites, false, "unsat cores");
  }

  if (opts.quantifiers.globalNegate)
  {
    if (opts.quantifiers.globalNegateWasSetByUser)
    {
      reason << "global-negate";
      return true;
    }
    SET_AND_NOTIFY(quantifiers, globalNegate, false, "unsat cores");
  }

  if (opts.smt.doITESimp)
  {
    reason << "ITE simp";
    return true;
  }
  return false;
}

bool SetDefaults::safeUnsatCores(const Options& opts) const
{
  // whether we want to force safe unsat cores, i.e., if we are in the default
  // ASSUMPTIONS mode, since other ones are experimental
  return opts.smt.unsatCoresMode == options::UnsatCoresMode::ASSUMPTIONS;
}

bool SetDefaults::incompatibleWithSygus(const Options& opts,
                                        std::ostream& reason) const
{
  // sygus should not be combined with preprocessing passes that convert the
  // input
  if (usesInputConversion(opts, reason))
  {
    return true;
  }
  if (opts.smt.deepRestartMode != options::DeepRestartMode::NONE)
  {
    reason << "deep restarts";
    return true;
  }
  if (opts.quantifiers.globalNegate)
  {
    reason << "global negate";
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithQuantifiers(const Options& opts,
                                              std::ostream& reason) const
{
  if (opts.smt.ackermann)
  {
    reason << "ackermann";
    return true;
  }
  if (opts.arith.nlRlvMode != options::NlRlvMode::NONE)
  {
    // Theory relevance is incompatible with CEGQI and SyQI, since there is no
    // appropriate policy for the relevance of counterexample lemmas (when their
    // guard is entailed to be false, the entire lemma is relevant, not just the
    // guard). Hence, we throw an option exception if quantifiers are enabled.
    reason << "--" << options::arith::longName::nlRlvMode;
    return true;
  }
  return false;
}

bool SetDefaults::incompatibleWithSeparationLogic(Options& opts,
                                                  std::ostream& reason) const
{
  // Spatial formulas in separation logic have a semantics that depends on
  // their position in the AST (e.g. their nesting beneath separation
  // conjunctions). Thus, we cannot apply BCP as a substitution for spatial
  // predicates to the input formula. We disable this option altogether to
  // ensure this is the case
  SET_AND_NOTIFY(smt, simplificationBoolConstProp, false, "separation logic");
  return false;
}

void SetDefaults::widenLogic(LogicInfo& logic, const Options& opts) const
{
  bool needsUf = false;
  // strings require LIA, UF; widen the logic
  if (logic.isTheoryEnabled(THEORY_STRINGS))
  {
    LogicInfo log(logic.getUnlockedCopy());
    // Strings requires arith for length constraints, and also UF
    needsUf = true;
    if (!logic.isTheoryEnabled(THEORY_ARITH) || logic.isDifferenceLogic())
    {
      verbose(1)
          << "Enabling linear integer arithmetic because strings are enabled"
          << std::endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    else if (!logic.areIntegersUsed())
    {
      verbose(1) << "Enabling integer arithmetic because strings are enabled"
                 << std::endl;
      log.enableIntegers();
    }
    logic = log;
    logic.lock();
  }
  if (opts.quantifiers.globalNegate)
  {
    LogicInfo log(logic.getUnlockedCopy());
    log.enableQuantifiers();
    logic = log;
    logic.lock();
  }
  if (opts.quantifiers.preSkolemQuantNested
      && opts.quantifiers.preSkolemQuantNestedWasSetByUser)
  {
    // if pre-skolem nested is explictly set, then we require UF. If it is
    // not explicitly set, it is disabled below if UF is not present.
    verbose(1) << "Enabling UF because preSkolemQuantNested requires it."
               << std::endl;
    needsUf = true;
  }
  if (needsUf
      // Arrays, datatypes and sets permit Boolean terms and thus require UF
      || logic.isTheoryEnabled(THEORY_ARRAYS)
      || logic.isTheoryEnabled(THEORY_DATATYPES)
      || logic.isTheoryEnabled(THEORY_SETS)
      || logic.isTheoryEnabled(THEORY_BAGS)
      // Non-linear arithmetic requires UF to deal with division/mod because
      // their expansion introduces UFs for the division/mod-by-zero case.
      // If we are eliminating non-linear arithmetic via solve-int-as-bv,
      // then this is not required, since non-linear arithmetic will be
      // eliminated altogether (or otherwise fail at preprocessing).
      || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
          && opts.smt.solveIntAsBV == 0)
      // If arithmetic and bv are enabled, it is possible to use bv2nat and
      // int2bv, which require the UF theory.
      || (logic.isTheoryEnabled(THEORY_ARITH)
          && logic.isTheoryEnabled(THEORY_BV))
      // FP requires UF since there are multiple operators that are partially
      // defined (see http://smt-lib.org/papers/BTRW15.pdf for more
      // details).
      || logic.isTheoryEnabled(THEORY_FP))
  {
    if (!logic.isTheoryEnabled(THEORY_UF))
    {
      LogicInfo log(logic.getUnlockedCopy());
      if (!needsUf)
      {
        verbose(1) << "Enabling UF because " << logic << " requires it."
                   << std::endl;
      }
      log.enableTheory(THEORY_UF);
      logic = log;
      logic.lock();
    }
  }
  if (opts.arith.arithMLTrick)
  {
    if (!logic.areIntegersUsed())
    {
      // enable integers
      LogicInfo log(logic.getUnlockedCopy());
      verbose(1) << "Enabling integers because arithMLTrick requires it."
                 << std::endl;
      log.enableIntegers();
      logic = log;
      logic.lock();
    }
  }
}

void SetDefaults::setDefaultsQuantifiers(const LogicInfo& logic,
                                         Options& opts) const
{
  if (opts.quantifiers.fullSaturateQuant)
  {
    SET_AND_NOTIFY(quantifiers, enumInst, true, "full-saturate-quant");
  }
  if (opts.arrays.arraysExp)
  {
    // Allows to answer sat more often by default.
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, fmfBound, true, "arrays-exp");
  }
  if (logic.hasCardinalityConstraints())
  {
    // must have finite model finding on
    SET_AND_NOTIFY(quantifiers,
                   finiteModelFind,
                   true,
                   "logic with cardinality constraints");
  }
  if (opts.quantifiers.instMaxLevel != -1)
  {
    SET_AND_NOTIFY(quantifiers, cegqi, false, "instMaxLevel");
  }
  // enable MBQI if --mbqi-fast-sygus is provided
  if (opts.quantifiers.mbqiFastSygus)
  {
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, mbqi, true, "mbqiFastSygus");
  }
  if (opts.quantifiers.mbqi)
  {
    // MBQI is an alternative to CEGQI/SyQI
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, cegqi, false, "mbqi");
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, sygusInst, false, "mbqi");
  }

  if (opts.quantifiers.fmfBoundLazy)
  {
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, fmfBound, true, "fmfBoundLazy");
  }
  // now have determined whether fmfBound is on/off
  // apply fmfBound options
  if (opts.quantifiers.fmfBound)
  {
    // if bounded integers are set, use no MBQI by default
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
        quantifiers, fmfMbqiMode, options::FmfMbqiMode::NONE, "fmfBound");
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
        quantifiers, prenexQuant, options::PrenexQuantMode::NONE, "fmfBound");
  }
  if (logic.isHigherOrder())
  {
    // if higher-order, then current variants of model-based instantiation
    // cannot be used
    SET_AND_NOTIFY_VAL_SYM(quantifiers,
                           fmfMbqiMode,
                           options::FmfMbqiMode::NONE,
                           "higher-order logic");
    // by default, use store axioms only if --ho-elim is set
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       hoElimStoreAx,
                                       opts.quantifiers.hoElim,
                                       "higher-order logic");
    // Cannot use macros, since lambda lifting and macro elimination are inverse
    // operations.
    SET_AND_NOTIFY(quantifiers, macrosQuant, false, "higher-order logic");
  }
  if (opts.quantifiers.fmfFunWellDefinedRelevant)
  {
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, fmfFunWellDefined, true, "fmfFunWellDefinedRelevant");
  }
  if (opts.quantifiers.fmfFunWellDefined)
  {
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, finiteModelFind, true, "fmfFunWellDefined");
  }

  // now, have determined whether finite model find is on/off
  // apply finite model finding options
  if (opts.quantifiers.finiteModelFind)
  {
    // apply conservative quantifiers splitting
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       quantDynamicSplit,
                                       options::QuantDSplitMode::DEFAULT,
                                       "finiteModelFind");
    // do not use E-matching by default. For E-matching + FMF, the user should
    // specify --finite-model-find --e-matching.
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, eMatching, false, "finiteModelFind");
    // instantiate only on last call
    if (opts.quantifiers.eMatching)
    {
      SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                         instWhenMode,
                                         options::InstWhenMode::LAST_CALL,
                                         "finiteModelFind");
    }
  }

  // apply sygus options
  // if we are attempting to rewrite everything to SyGuS, use sygus()
  if (isSygus(opts))
  {
    std::stringstream reasonNoSygus;
    if (incompatibleWithSygus(opts, reasonNoSygus))
    {
      std::stringstream ss;
      ss << reasonNoSygus.str() << " not supported in sygus.";
      throw OptionException(ss.str());
    }
    // now, set defaults based on sygus
    setDefaultsSygus(opts);
  }
  // counterexample-guided instantiation for non-sygus
  // enable if any possible quantifiers with arithmetic, datatypes or bitvectors
  if ((logic.isQuantified()
       && (logic.isTheoryEnabled(THEORY_ARITH)
           || logic.isTheoryEnabled(THEORY_DATATYPES)
           || logic.isTheoryEnabled(THEORY_BV)
           || logic.isTheoryEnabled(THEORY_FP)))
      || opts.quantifiers.cegqiAll)
  {
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, cegqi, true, "logic");
    // check whether we should apply full cbqi
    if (logic.isPure(THEORY_BV))
    {
      SET_AND_NOTIFY_IF_NOT_USER(
          quantifiers, cegqiFullEffort, true, "pure BV logic");
    }
  }
  if (opts.quantifiers.cegqi)
  {
    if (logic.isPure(THEORY_ARITH) || logic.isPure(THEORY_BV))
    {
      SET_AND_NOTIFY_IF_NOT_USER(
          quantifiers, conflictBasedInst, false, "cegqi pure logic");
      SET_AND_NOTIFY_IF_NOT_USER(
          quantifiers, instNoEntail, false, "cegqi pure logic");
      // only instantiation should happen at last call when model is avaiable
      SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                         instWhenMode,
                                         options::InstWhenMode::LAST_CALL,
                                         "cegqi pure logic");
    }
    else
    {
      // only supported in pure arithmetic or pure BV
      SET_AND_NOTIFY(quantifiers, cegqiNestedQE, false, "cegqi non-pure logic");
    }
    if (opts.quantifiers.globalNegate)
    {
      SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                         prenexQuant,
                                         options::PrenexQuantMode::NONE,
                                         "globalNegate");
    }
  }
  // implied options...
  if (opts.quantifiers.cbqiModeWasSetByUser || opts.quantifiers.cbqiTConstraint)
  {
    SET_AND_NOTIFY(quantifiers, conflictBasedInst, true, "cbqi option");
  }
  if (opts.quantifiers.cegqiNestedQE)
  {
    SET_AND_NOTIFY(quantifiers, prenexQuantUser, true, "cegqiNestedQE");
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       preSkolemQuant,
                                       options::PreSkolemQuantMode::ON,
                                       "cegqiNestedQE");
  }
  // for induction techniques
  if (opts.quantifiers.quantInduction)
  {
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, dtStcInduction, true, "quantInduction");
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, intWfInduction, true, "quantInduction");
  }
  if (opts.quantifiers.dtStcInduction)
  {
    // try to remove ITEs from quantified formulas
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, iteDtTesterSplitQuant, true, "dtStcInduction");
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       iteLiftQuant,
                                       options::IteLiftQuantMode::ALL,
                                       "dtStcInduction");
  }
  if (opts.quantifiers.intWfInduction)
  {
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, purifyTriggers, true, "intWfInduction");
  }
  if (opts.quantifiers.conjectureGenPerRoundWasSetByUser)
  {
    bool conjNZero = (opts.quantifiers.conjectureGenPerRound > 0);
    SET_AND_NOTIFY_VAL_SYM(
        quantifiers, conjectureGen, conjNZero, "conjectureGenPerRound");
  }
  // can't pre-skolemize nested quantifiers without UF theory
  if (!logic.isTheoryEnabled(THEORY_UF)
      && opts.quantifiers.preSkolemQuant != options::PreSkolemQuantMode::OFF)
  {
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, preSkolemQuantNested, false, "preSkolemQuant");
  }
  if (!logic.isTheoryEnabled(THEORY_DATATYPES))
  {
    SET_AND_NOTIFY_VAL_SYM(quantifiers,
                           quantDynamicSplit,
                           options::QuantDSplitMode::NONE,
                           "non-datatypes logic");
  }
  if (opts.quantifiers.globalNegate)
  {
    SET_AND_NOTIFY_VAL_SYM(
        smt, deepRestartMode, options::DeepRestartMode::NONE, "globalNegate");
  }
}

void SetDefaults::setDefaultsSygus(Options& opts) const
{
  SET_AND_NOTIFY(quantifiers, sygus, true, "enabling sygus");
  // must use Ferrante/Rackoff for real arithmetic
  SET_AND_NOTIFY(quantifiers, cegqiMidpoint, true, "sygus");
  // must disable cegqi-bv since it may introduce witness terms, which
  // cannot appear in synthesis solutions
  SET_AND_NOTIFY_IF_NOT_USER(quantifiers, cegqiBv, false, "sygus");
  if (opts.quantifiers.sygusRepairConst)
  {
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, cegqi, true, "sygusRepairConst");
  }
  if (opts.quantifiers.sygusInference != options::SygusInferenceMode::OFF)
  {
    // optimization: apply preskolemization, makes it succeed more often
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       preSkolemQuant,
                                       options::PreSkolemQuantMode::ON,
                                       "sygusInference");
    SET_AND_NOTIFY_IF_NOT_USER(
        quantifiers, preSkolemQuantNested, true, "sygusInference");
  }
  // counterexample-guided instantiation for sygus
  SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                     cegqiSingleInvMode,
                                     options::CegqiSingleInvMode::USE,
                                     "sygus");
  SET_AND_NOTIFY_IF_NOT_USER(quantifiers, conflictBasedInst, false, "sygus");
  SET_AND_NOTIFY_IF_NOT_USER(quantifiers, instNoEntail, false, "sygus");
  // should use full effort cbqi for single invocation and repair const
  SET_AND_NOTIFY_IF_NOT_USER(quantifiers, cegqiFullEffort, true, "sygus");
  // Whether we must use "basic" sygus algorithms. A non-basic sygus algorithm
  // is one that is specialized for returning a single solution. Non-basic
  // sygus algorithms currently include the PBE solver, UNIF+PI, static
  // template inference for invariant synthesis, and single invocation
  // techniques.
  bool reqBasicSygus = false;
  if (opts.smt.produceAbducts)
  {
    // if doing abduction, we should filter strong solutions
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       sygusFilterSolMode,
                                       options::SygusFilterSolMode::STRONG,
                                       "produceAbducts");
    // we must use basic sygus algorithms, since e.g. we require checking
    // a sygus side condition for consistency with axioms.
    reqBasicSygus = true;
  }
  if (opts.quantifiers.sygusStream || opts.base.incrementalSolving)
  {
    // Streaming and incremental mode are incompatible with techniques that
    // focus the search towards finding a single solution.
    reqBasicSygus = true;
  }
  // Now, disable options for non-basic sygus algorithms, if necessary.
  if (reqBasicSygus)
  {
    SET_AND_NOTIFY_IF_NOT_USER(quantifiers, sygusUnifPbe, false, "basic sygus");
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       sygusUnifPi,
                                       options::SygusUnifPiMode::NONE,
                                       "basic sygus");
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       sygusInvTemplMode,
                                       options::SygusInvTemplMode::NONE,
                                       "basic sygus");
    SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(quantifiers,
                                       cegqiSingleInvMode,
                                       options::CegqiSingleInvMode::NONE,
                                       "basic sygus");
  }
  // do not miniscope
  SET_AND_NOTIFY_IF_NOT_USER_VAL_SYM(
      quantifiers, miniscopeQuant, options::MiniscopeQuantMode::OFF, "sygus");
  // do not do macros
  SET_AND_NOTIFY_IF_NOT_USER(quantifiers, macrosQuant, false, "sygus");
}
void SetDefaults::setDefaultDecisionMode(const LogicInfo& logic,
                                         Options& opts) const
{
  // Set decision mode based on logic (if not set by user)
  if (opts.decision.decisionModeWasSetByUser)
  {
    return;
  }
  options::DecisionMode decMode =
      // anything that uses sygus uses internal
      usesSygus(opts) ? options::DecisionMode::INTERNAL :
                      // ALL or its supersets
          logic.hasEverything()
          ? options::DecisionMode::JUSTIFICATION
          : (  // QF_BV
              (!logic.isQuantified() && logic.isPure(THEORY_BV)) ||
                      // QF_AUFBV or QF_ABV or QF_UFBV
                      (!logic.isQuantified()
                       && (logic.isTheoryEnabled(THEORY_ARRAYS)
                           || logic.isTheoryEnabled(THEORY_UF))
                       && logic.isTheoryEnabled(THEORY_BV))
                      ||
                      // QF_AUFLIA (and may be ends up enabling
                      // QF_AUFLRA?)
                      (!logic.isQuantified()
                       && logic.isTheoryEnabled(THEORY_ARRAYS)
                       && logic.isTheoryEnabled(THEORY_UF)
                       && logic.isTheoryEnabled(THEORY_ARITH))
                      ||
                      // QF_LRA
                      (!logic.isQuantified() && logic.isPure(THEORY_ARITH)
                       && logic.isLinear() && !logic.isDifferenceLogic()
                       && !logic.areIntegersUsed())
                      ||
                      // Quantifiers
                      logic.isQuantified() ||
                      // Strings
                      logic.isTheoryEnabled(THEORY_STRINGS)
                  ? options::DecisionMode::JUSTIFICATION
                  : options::DecisionMode::INTERNAL);

  bool stoponly =
      // ALL or its supersets
      logic.hasEverything() || logic.isTheoryEnabled(THEORY_STRINGS)
          ? false
          : (  // QF_AUFLIA
              (!logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
               && logic.isTheoryEnabled(THEORY_UF)
               && logic.isTheoryEnabled(THEORY_ARITH))
                      ||
                      // QF_LRA
                      (!logic.isQuantified() && logic.isPure(THEORY_ARITH)
                       && logic.isLinear() && !logic.isDifferenceLogic()
                       && !logic.areIntegersUsed())
                  ? true
                  : false);

  if (stoponly)
  {
    if (decMode == options::DecisionMode::JUSTIFICATION)
    {
      decMode = options::DecisionMode::STOPONLY;
    }
    else
    {
      Assert(decMode == options::DecisionMode::INTERNAL);
    }
  }
  SET_AND_NOTIFY_VAL_SYM(decision, decisionMode, decMode, "logic");
}

void SetDefaults::notifyModifyOption(const std::string& x,
                                     const std::string& val,
                                     const std::string& reason) const
{
  verbose(1) << "SetDefaults: setting " << x << " to " << val;
  if (!reason.empty())
  {
    verbose(1) << " due to " << reason;
  }
  verbose(1) << std::endl;
  // don't print -o options-auto for internal subsolvers
  if (!d_isInternalSubsolver)
  {
    if (isOutputOn(OutputTag::OPTIONS_AUTO))
    {
      output(OutputTag::OPTIONS_AUTO) << "(options-auto";
      output(OutputTag::OPTIONS_AUTO) << " " << x;
      output(OutputTag::OPTIONS_AUTO) << " " << val;
      if (!reason.empty())
      {
        output(OutputTag::OPTIONS_AUTO) << " :reason \"" << reason << "\"";
      }
      output(OutputTag::OPTIONS_AUTO) << ")" << std::endl;
    }
  }
}

void SetDefaults::disableChecking(Options& opts)
{
  opts.write_smt().checkUnsatCores = false;
  opts.write_smt().produceProofs = false;
  opts.write_smt().checkProofs = false;
  opts.write_smt().debugCheckModels = false;
  opts.write_smt().checkModels = false;
  opts.write_proof().checkProofSteps = false;
}

}  // namespace smt
}  // namespace cvc5::internal
