/*********************                                                        */
/*! \file set_defaults.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of setting default options.
 **/

#include "smt/set_defaults.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/open_ostream.h"
#include "options/option_exception.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/prop_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/set_language.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "theory/theory.h"

using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

void setDefaults(SmtEngine& smte, LogicInfo& logic)
{
  // implied options
  if (options::debugCheckModels())
  {
    Notice() << "SmtEngine: setting checkModel" << std::endl;
    options::checkModels.set(true);
  }
  if (options::checkModels() || options::dumpModels())
  {
    Notice() << "SmtEngine: setting produceModels" << std::endl;
    options::produceModels.set(true);
  }
  if (options::checkModels())
  {
    Notice() << "SmtEngine: setting produceAssignments" << std::endl;
    options::produceAssignments.set(true);
  }
  if (options::dumpUnsatCoresFull())
  {
    Notice() << "SmtEngine: setting dumpUnsatCores" << std::endl;
    options::dumpUnsatCores.set(true);
  }
  if (options::checkUnsatCores() || options::dumpUnsatCores()
      || options::unsatAssumptions())
  {
    Notice() << "SmtEngine: setting unsatCores" << std::endl;
    options::unsatCores.set(true);
  }
  if (options::checkProofs() || options::dumpProofs())
  {
    Notice() << "SmtEngine: setting proof" << std::endl;
    options::proof.set(true);
  }
  if (options::bitvectorAigSimplifications.wasSetByUser())
  {
    Notice() << "SmtEngine: setting bitvectorAig" << std::endl;
    options::bitvectorAig.set(true);
  }
  if (options::bitvectorEqualitySlicer.wasSetByUser())
  {
    Notice() << "SmtEngine: setting bitvectorEqualitySolver" << std::endl;
    options::bitvectorEqualitySolver.set(true);
  }
  if (options::bitvectorAlgebraicBudget.wasSetByUser())
  {
    Notice() << "SmtEngine: setting bitvectorAlgebraicSolver" << std::endl;
    options::bitvectorAlgebraicSolver.set(true);
  }

  // Language-based defaults
  if (!options::bitvectorDivByZeroConst.wasSetByUser())
  {
    // Bitvector-divide-by-zero changed semantics in SMT LIB 2.6, thus we
    // set this option if the input format is SMT LIB 2.6. We also set this
    // option if we are sygus, since we assume SMT LIB 2.6 semantics for sygus.
    options::bitvectorDivByZeroConst.set(
        language::isInputLang_smt2_6(options::inputLanguage())
        || language::isInputLangSygus(options::inputLanguage()));
  }
  bool is_sygus = language::isInputLangSygus(options::inputLanguage());

  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    if (options::produceModels()
        && (logic.isTheoryEnabled(THEORY_ARRAYS)
            || logic.isTheoryEnabled(THEORY_UF)))
    {
      if (options::bitblastMode.wasSetByUser()
          || options::produceModels.wasSetByUser())
      {
        throw OptionException(std::string(
            "Eager bit-blasting currently does not support model generation "
            "for the combination of bit-vectors with arrays or uinterpreted "
            "functions. Try --bitblast=lazy"));
      }
      Notice() << "SmtEngine: setting bit-blast mode to lazy to support model"
               << "generation" << std::endl;
      smte.setOption("bitblastMode", SExpr("lazy"));
    }
    else if (!options::incrementalSolving())
    {
      options::ackermann.set(true);
    }

    if (options::incrementalSolving() && !logic.isPure(THEORY_BV))
    {
      throw OptionException(
          "Incremental eager bit-blasting is currently "
          "only supported for QF_BV. Try --bitblast=lazy.");
    }
  }

  if (options::solveIntAsBV() > 0)
  {
    // not compatible with incremental
    if (options::incrementalSolving())
    {
      throw OptionException(
          "solving integers as bitvectors is currently not supported "
          "when solving incrementally.");
    }
    // Int to BV currently always eliminates arithmetic completely (or otherwise
    // fails). Thus, it is safe to eliminate arithmetic. Also, bit-vectors
    // are required.
    logic = logic.getUnlockedCopy();
    logic.enableTheory(THEORY_BV);
    logic.disableTheory(THEORY_ARITH);
    logic.lock();
  }

  if (options::solveBVAsInt() > 0)
  {
    // not compatible with incremental
    if (options::incrementalSolving())
    {
      throw OptionException(
          "solving bitvectors as integers is currently not supported "
          "when solving incrementally.");
    }
    else if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      throw OptionException(
          "solving bitvectors as integers is incompatible with --bool-to-bv.");
    }
    if (options::solveBVAsInt() > 8)
    {
      /**
       * The granularity sets the size of the ITE in each element
       * of the sum that is generated for bitwise operators.
       * The size of the ITE is 2^{2*granularity}.
       * Since we don't want to introduce ITEs with unbounded size,
       * we bound the granularity.
       */
      throw OptionException("solve-bv-as-int accepts values from 0 to 8.");
    }
    if (logic.isTheoryEnabled(THEORY_BV))
    {
      logic = logic.getUnlockedCopy();
      logic.enableTheory(THEORY_ARITH);
      logic.arithNonLinear();
      logic.lock();
    }
  }

  // set options about ackermannization
  if (options::ackermann() && options::produceModels()
      && (logic.isTheoryEnabled(THEORY_ARRAYS)
          || logic.isTheoryEnabled(THEORY_UF)))
  {
    if (options::produceModels.wasSetByUser())
    {
      throw OptionException(std::string(
          "Ackermannization currently does not support model generation."));
    }
    Notice() << "SmtEngine: turn off ackermannization to support model"
             << "generation" << std::endl;
    options::ackermann.set(false);
  }

  if (options::ackermann())
  {
    if (options::incrementalSolving())
    {
      throw OptionException(
          "Incremental Ackermannization is currently not supported.");
    }

    if (logic.isQuantified())
    {
      throw LogicException("Cannot use Ackermannization on quantified formula");
    }

    if (logic.isTheoryEnabled(THEORY_UF))
    {
      logic = logic.getUnlockedCopy();
      logic.disableTheory(THEORY_UF);
      logic.lock();
    }
    if (logic.isTheoryEnabled(THEORY_ARRAYS))
    {
      logic = logic.getUnlockedCopy();
      logic.disableTheory(THEORY_ARRAYS);
      logic.lock();
    }
  }

  // Set default options associated with strings-exp. We also set these options
  // if we are using eager string preprocessing, which may introduce quantified
  // formulas at preprocess time.
  if (options::stringExp() || !options::stringLazyPreproc())
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
    // We require bounded quantifier handling.
    if (!options::fmfBound.wasSetByUser())
    {
      options::fmfBound.set(true);
      Trace("smt") << "turning on fmf-bound-int, for strings-exp" << std::endl;
    }
    // Turn off E-matching, since some bounded quantifiers introduced by strings
    // (e.g. for replaceall) admit matching loops.
    if (!options::eMatching.wasSetByUser())
    {
      options::eMatching.set(false);
      Trace("smt") << "turning off E-matching, for strings-exp" << std::endl;
    }
    // Do not eliminate extended arithmetic symbols from quantified formulas,
    // since some strategies, e.g. --re-elim-agg, introduce them.
    if (!options::elimExtArithQuant.wasSetByUser())
    {
      options::elimExtArithQuant.set(false);
      Trace("smt") << "turning off elim-ext-arith-quant, for strings-exp"
                   << std::endl;
    }
  }
  // !!!!!!!!!!!!!!!! temporary, to support CI check for old proof system
  if (options::proof())
  {
    options::proofNew.set(false);
  }

  if (options::arraysExp())
  {
    if (!logic.isQuantified())
    {
      logic = logic.getUnlockedCopy();
      logic.enableQuantifiers();
      logic.lock();
    }
    // Allows to answer sat more often by default.
    if (!options::fmfBound.wasSetByUser())
    {
      options::fmfBound.set(true);
      Trace("smt") << "turning on fmf-bound, for arrays-exp" << std::endl;
    }
  }

  // sygus inference may require datatypes
  if (!smte.isInternalSubsolver())
  {
    if (options::produceAbducts() || options::sygusInference()
        || options::sygusRewSynthInput() || options::sygusInst())
    {
      // since we are trying to recast as sygus, we assume the input is sygus
      is_sygus = true;
    }
  }

  // We now know whether the input is sygus. Update the logic to incorporate
  // the theories we need internally for handling sygus problems.
  if (is_sygus)
  {
    logic = logic.getUnlockedCopy();
    logic.enableSygus();
    logic.lock();
  }

  // sygus core connective requires unsat cores
  if (options::sygusCoreConnective())
  {
    options::unsatCores.set(true);
  }

  if ((options::checkModels() || options::checkSynthSol()
       || options::produceAbducts()
       || options::modelCoresMode() != options::ModelCoresMode::NONE
       || options::blockModelsMode() != options::BlockModelsMode::NONE)
      && !options::produceAssertions())
  {
    Notice() << "SmtEngine: turning on produce-assertions to support "
             << "option requiring assertions." << std::endl;
    smte.setOption("produce-assertions", SExpr("true"));
  }

  // Disable options incompatible with incremental solving, unsat cores, and
  // proofs or output an error if enabled explicitly. It is also currently
  // incompatible with arithmetic, force the option off.
  if (options::incrementalSolving() || options::unsatCores()
      || options::proof())
  {
    if (options::unconstrainedSimp())
    {
      if (options::unconstrainedSimp.wasSetByUser())
      {
        throw OptionException(
            "unconstrained simplification not supported with unsat "
            "cores/proofs/incremental solving");
      }
      Notice() << "SmtEngine: turning off unconstrained simplification to "
                  "support unsat cores/proofs/incremental solving"
               << std::endl;
      options::unconstrainedSimp.set(false);
    }
  }
  else
  {
    // Turn on unconstrained simplification for QF_AUFBV
    if (!options::unconstrainedSimp.wasSetByUser())
    {
      bool uncSimp = !logic.isQuantified() && !options::produceModels()
                     && !options::produceAssignments()
                     && !options::checkModels()
                     && logic.isTheoryEnabled(THEORY_ARRAYS)
                     && logic.isTheoryEnabled(THEORY_BV)
                     && !logic.isTheoryEnabled(THEORY_ARITH);
      Trace("smt") << "setting unconstrained simplification to " << uncSimp
                   << std::endl;
      options::unconstrainedSimp.set(uncSimp);
    }
  }

  if (options::incrementalSolving() || options::proof())
  {
    if (options::sygusInference())
    {
      if (options::sygusInference.wasSetByUser())
      {
        throw OptionException(
            "sygus inference not supported with proofs/incremental solving");
      }
      Notice() << "SmtEngine: turning off sygus inference to support "
                  "proofs/incremental solving"
               << std::endl;
      options::sygusInference.set(false);
    }
  }


  if (options::solveBVAsInt() > 0)
  {
    /**
     * Operations on 1 bits are better handled as Boolean operations
     * than as integer operations.
     * Therefore, we enable bv-to-bool, which runs before
     * the translation to integers.
     */
    options::bitvectorToBool.set(true);
  }

  // Disable options incompatible with unsat cores and proofs or output an
  // error if enabled explicitly
  if (options::unsatCores() || options::proof())
  {
    if (options::simplificationMode() != options::SimplificationMode::NONE)
    {
      if (options::simplificationMode.wasSetByUser())
      {
        throw OptionException(
            "simplification not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off simplification to support unsat "
                  "cores/proofs"
               << std::endl;
      options::simplificationMode.set(options::SimplificationMode::NONE);
    }

    if (options::pbRewrites())
    {
      if (options::pbRewrites.wasSetByUser())
      {
        throw OptionException(
            "pseudoboolean rewrites not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off pseudoboolean rewrites to support "
                  "unsat cores/proofs"
               << std::endl;
      smte.setOption("pb-rewrites", false);
    }

    if (options::sortInference())
    {
      if (options::sortInference.wasSetByUser())
      {
        throw OptionException(
            "sort inference not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off sort inference to support unsat "
                  "cores/proofs"
               << std::endl;
      options::sortInference.set(false);
    }

    if (options::preSkolemQuant())
    {
      if (options::preSkolemQuant.wasSetByUser())
      {
        throw OptionException(
            "pre-skolemization not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off pre-skolemization to support unsat "
                  "cores/proofs"
               << std::endl;
      options::preSkolemQuant.set(false);
    }


    if (options::bitvectorToBool())
    {
      if (options::bitvectorToBool.wasSetByUser())
      {
        throw OptionException(
            "bv-to-bool not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off bitvector-to-bool to support unsat "
                  "cores/proofs"
               << std::endl;
      options::bitvectorToBool.set(false);
    }

    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      if (options::boolToBitvector.wasSetByUser())
      {
        throw OptionException(
            "bool-to-bv != off not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off bool-to-bv to support unsat "
                  "cores/proofs"
               << std::endl;
      smte.setOption("boolToBitvector", SExpr("off"));
    }

    if (options::bvIntroducePow2())
    {
      if (options::bvIntroducePow2.wasSetByUser())
      {
        throw OptionException(
            "bv-intro-pow2 not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off bv-intro-pow2 to support "
                  "unsat-cores/proofs"
               << std::endl;
      smte.setOption("bv-intro-pow2", false);
    }

    if (options::repeatSimp())
    {
      if (options::repeatSimp.wasSetByUser())
      {
        throw OptionException(
            "repeat-simp not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off repeat-simp to support unsat "
                  "cores/proofs"
               << std::endl;
      smte.setOption("repeat-simp", false);
    }

    if (options::globalNegate())
    {
      if (options::globalNegate.wasSetByUser())
      {
        throw OptionException(
            "global-negate not supported with unsat cores/proofs");
      }
      Notice() << "SmtEngine: turning off global-negate to support unsat "
                  "cores/proofs"
               << std::endl;
      smte.setOption("global-negate", false);
    }

    if (options::bitvectorAig())
    {
      throw OptionException(
          "bitblast-aig not supported with unsat cores/proofs");
    }
  }
  else
  {
    // by default, nonclausal simplification is off for QF_SAT
    if (!options::simplificationMode.wasSetByUser())
    {
      bool qf_sat = logic.isPure(THEORY_BOOL) && !logic.isQuantified();
      Trace("smt") << "setting simplification mode to <"
                   << logic.getLogicString() << "> " << (!qf_sat) << std::endl;
      // simplification=none works better for SMT LIB benchmarks with
      // quantifiers, not others options::simplificationMode.set(qf_sat ||
      // quantifiers ? options::SimplificationMode::NONE :
      // options::SimplificationMode::BATCH);
      options::simplificationMode.set(qf_sat
                                          ? options::SimplificationMode::NONE
                                          : options::SimplificationMode::BATCH);
    }
  }

  if (options::cegqiBv() && logic.isQuantified())
  {
    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      if (options::boolToBitvector.wasSetByUser())
      {
        throw OptionException(
            "bool-to-bv != off not supported with CBQI BV for quantified "
            "logics");
      }
      Notice() << "SmtEngine: turning off bool-to-bitvector to support CBQI BV"
               << std::endl;
      smte.setOption("boolToBitvector", SExpr("off"));
    }
  }

  // cases where we need produce models
  if (!options::produceModels()
      && (options::produceAssignments() || options::sygusRewSynthCheck()
          || is_sygus))
  {
    Notice() << "SmtEngine: turning on produce-models" << std::endl;
    smte.setOption("produce-models", SExpr("true"));
  }

  /////////////////////////////////////////////////////////////////////////////
  // Theory widening
  //
  // Some theories imply the use of other theories to handle certain operators,
  // e.g. UF to handle partial functions.
  /////////////////////////////////////////////////////////////////////////////
  bool needsUf = false;
  // strings require LIA, UF; widen the logic
  if (logic.isTheoryEnabled(THEORY_STRINGS))
  {
    LogicInfo log(logic.getUnlockedCopy());
    // Strings requires arith for length constraints, and also UF
    needsUf = true;
    if (!logic.isTheoryEnabled(THEORY_ARITH) || logic.isDifferenceLogic()
        || !logic.areIntegersUsed())
    {
      Notice()
          << "Enabling linear integer arithmetic because strings are enabled"
          << std::endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    logic = log;
    logic.lock();
  }
  if (needsUf
      // Arrays, datatypes and sets permit Boolean terms and thus require UF
      || logic.isTheoryEnabled(THEORY_ARRAYS)
      || logic.isTheoryEnabled(THEORY_DATATYPES)
      || logic.isTheoryEnabled(THEORY_SETS)
      // Non-linear arithmetic requires UF to deal with division/mod because
      // their expansion introduces UFs for the division/mod-by-zero case.
      // If we are eliminating non-linear arithmetic via solve-int-as-bv,
      // then this is not required, since non-linear arithmetic will be
      // eliminated altogether (or otherwise fail at preprocessing).
      || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
          && options::solveIntAsBV() == 0)
      // If division/mod-by-zero is not treated as a constant value in BV, we
      // need UF.
      || (logic.isTheoryEnabled(THEORY_BV)
          && !options::bitvectorDivByZeroConst())
      // FP requires UF since there are multiple operators that are partially
      // defined (see http://smtlib.cs.uiowa.edu/papers/BTRW15.pdf for more
      // details).
      || logic.isTheoryEnabled(THEORY_FP))
  {
    if (!logic.isTheoryEnabled(THEORY_UF))
    {
      LogicInfo log(logic.getUnlockedCopy());
      Notice() << "Enabling UF because " << logic << " requires it."
               << std::endl;
      log.enableTheory(THEORY_UF);
      logic = log;
      logic.lock();
    }
  }
  /////////////////////////////////////////////////////////////////////////////

  // Set the options for the theoryOf
  if (!options::theoryOfMode.wasSetByUser())
  {
    if (logic.isSharingEnabled() && !logic.isTheoryEnabled(THEORY_BV)
        && !logic.isTheoryEnabled(THEORY_STRINGS)
        && !logic.isTheoryEnabled(THEORY_SETS))
    {
      Trace("smt") << "setting theoryof-mode to term-based" << std::endl;
      options::theoryOfMode.set(options::TheoryOfMode::THEORY_OF_TERM_BASED);
    }
  }

  // by default, symmetry breaker is on only for non-incremental QF_UF
  if (!options::ufSymmetryBreaker.wasSetByUser())
  {
    bool qf_uf_noinc = logic.isPure(THEORY_UF) && !logic.isQuantified()
                       && !options::incrementalSolving() && !options::proof()
                       && !options::unsatCores();
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf_noinc
                 << std::endl;
    options::ufSymmetryBreaker.set(qf_uf_noinc);
  }

  // If in arrays, set the UF handler to arrays
  if (logic.isTheoryEnabled(THEORY_ARRAYS)
      && (!logic.isQuantified()
          || (logic.isQuantified() && !logic.isTheoryEnabled(THEORY_UF))))
  {
    Theory::setUninterpretedSortOwner(THEORY_ARRAYS);
  }
  else
  {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }

  if (!options::simplifyWithCareEnabled.wasSetByUser())
  {
    bool qf_aufbv =
        !logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF) && logic.isTheoryEnabled(THEORY_BV);

    bool withCare = qf_aufbv;
    Trace("smt") << "setting ite simplify with care to " << withCare
                 << std::endl;
    options::simplifyWithCareEnabled.set(withCare);
  }
  // Turn off array eager index splitting for QF_AUFLIA
  if (!options::arraysEagerIndexSplitting.wasSetByUser())
  {
    if (not logic.isQuantified() && logic.isTheoryEnabled(THEORY_ARRAYS)
        && logic.isTheoryEnabled(THEORY_UF)
        && logic.isTheoryEnabled(THEORY_ARITH))
    {
      Trace("smt") << "setting array eager index splitting to false"
                   << std::endl;
      options::arraysEagerIndexSplitting.set(false);
    }
  }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if (!options::repeatSimp.wasSetByUser())
  {
    bool repeatSimp = !logic.isQuantified()
                      && (logic.isTheoryEnabled(THEORY_ARRAYS)
                          && logic.isTheoryEnabled(THEORY_UF)
                          && logic.isTheoryEnabled(THEORY_BV))
                      && !options::unsatCores();
    Trace("smt") << "setting repeat simplification to " << repeatSimp
                 << std::endl;
    options::repeatSimp.set(repeatSimp);
  }

  if (options::boolToBitvector() == options::BoolToBVMode::ALL
      && !logic.isTheoryEnabled(THEORY_BV))
  {
    if (options::boolToBitvector.wasSetByUser())
    {
      throw OptionException(
          "bool-to-bv=all not supported for non-bitvector logics.");
    }
    Notice() << "SmtEngine: turning off bool-to-bv for non-bv logic: "
             << logic.getLogicString() << std::endl;
    smte.setOption("boolToBitvector", SExpr("off"));
  }

  if (!options::bvEagerExplanations.wasSetByUser()
      && logic.isTheoryEnabled(THEORY_ARRAYS)
      && logic.isTheoryEnabled(THEORY_BV))
  {
    Trace("smt") << "enabling eager bit-vector explanations " << std::endl;
    options::bvEagerExplanations.set(true);
  }

  // Turn on arith rewrite equalities only for pure arithmetic
  if (!options::arithRewriteEq.wasSetByUser())
  {
    bool arithRewriteEq =
        logic.isPure(THEORY_ARITH) && logic.isLinear() && !logic.isQuantified();
    Trace("smt") << "setting arith rewrite equalities " << arithRewriteEq
                 << std::endl;
    options::arithRewriteEq.set(arithRewriteEq);
  }
  if (!options::arithHeuristicPivots.wasSetByUser())
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
    Trace("smt") << "setting arithHeuristicPivots  " << heuristicPivots
                 << std::endl;
    options::arithHeuristicPivots.set(heuristicPivots);
  }
  if (!options::arithPivotThreshold.wasSetByUser())
  {
    uint16_t pivotThreshold = 2;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      if (logic.isDifferenceLogic())
      {
        pivotThreshold = 16;
      }
    }
    Trace("smt") << "setting arith arithPivotThreshold  " << pivotThreshold
                 << std::endl;
    options::arithPivotThreshold.set(pivotThreshold);
  }
  if (!options::arithStandardCheckVarOrderPivots.wasSetByUser())
  {
    int16_t varOrderPivots = -1;
    if (logic.isPure(THEORY_ARITH) && !logic.isQuantified())
    {
      varOrderPivots = 200;
    }
    Trace("smt") << "setting arithStandardCheckVarOrderPivots  "
                 << varOrderPivots << std::endl;
    options::arithStandardCheckVarOrderPivots.set(varOrderPivots);
  }
  if (logic.isPure(THEORY_ARITH) && !logic.areRealsUsed())
  {
    if (!options::nlExtTangentPlanesInterleave.wasSetByUser())
    {
      Trace("smt") << "setting nlExtTangentPlanesInterleave to true"
                   << std::endl;
      options::nlExtTangentPlanesInterleave.set(true);
    }
  }

  // Set decision mode based on logic (if not set by user)
  if (!options::decisionMode.wasSetByUser())
  {
    options::DecisionMode decMode =
        // sygus uses internal
        is_sygus ? options::DecisionMode::INTERNAL :
                 // ALL
            logic.hasEverything()
                ? options::DecisionMode::JUSTIFICATION
                : (  // QF_BV
                      (not logic.isQuantified() && logic.isPure(THEORY_BV)) ||
                              // QF_AUFBV or QF_ABV or QF_UFBV
                              (not logic.isQuantified()
                               && (logic.isTheoryEnabled(THEORY_ARRAYS)
                                   || logic.isTheoryEnabled(THEORY_UF))
                               && logic.isTheoryEnabled(THEORY_BV))
                              ||
                              // QF_AUFLIA (and may be ends up enabling
                              // QF_AUFLRA?)
                              (not logic.isQuantified()
                               && logic.isTheoryEnabled(THEORY_ARRAYS)
                               && logic.isTheoryEnabled(THEORY_UF)
                               && logic.isTheoryEnabled(THEORY_ARITH))
                              ||
                              // QF_LRA
                              (not logic.isQuantified()
                               && logic.isPure(THEORY_ARITH) && logic.isLinear()
                               && !logic.isDifferenceLogic()
                               && !logic.areIntegersUsed())
                              ||
                              // Quantifiers
                              logic.isQuantified() ||
                              // Strings
                              logic.isTheoryEnabled(THEORY_STRINGS)
                          ? options::DecisionMode::JUSTIFICATION
                          : options::DecisionMode::INTERNAL);

    bool stoponly =
        // ALL
        logic.hasEverything() || logic.isTheoryEnabled(THEORY_STRINGS)
            ? false
            : (  // QF_AUFLIA
                  (not logic.isQuantified()
                   && logic.isTheoryEnabled(THEORY_ARRAYS)
                   && logic.isTheoryEnabled(THEORY_UF)
                   && logic.isTheoryEnabled(THEORY_ARITH))
                          ||
                          // QF_LRA
                          (not logic.isQuantified()
                           && logic.isPure(THEORY_ARITH) && logic.isLinear()
                           && !logic.isDifferenceLogic()
                           && !logic.areIntegersUsed())
                      ? true
                      : false);

    Trace("smt") << "setting decision mode to " << decMode << std::endl;
    options::decisionMode.set(decMode);
    options::decisionStopOnly.set(stoponly);
  }
  if (options::incrementalSolving())
  {
    // disable modes not supported by incremental
    options::sortInference.set(false);
    options::ufssFairnessMonotone.set(false);
    options::quantEpr.set(false);
    options::globalNegate.set(false);
    options::bvAbstraction.set(false);
    options::arithMLTrick.set(false);
  }
  if (logic.hasCardinalityConstraints())
  {
    // must have finite model finding on
    options::finiteModelFind.set(true);
  }

  // if it contains a theory with non-termination, do not strictly enforce that
  // quantifiers and theory combination must be interleaved
  if (logic.isTheoryEnabled(THEORY_STRINGS)
      || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
  {
    if (!options::instWhenStrictInterleave.wasSetByUser())
    {
      options::instWhenStrictInterleave.set(false);
    }
  }

  if (options::instMaxLevel() != -1)
  {
    Notice() << "SmtEngine: turning off cbqi to support instMaxLevel"
             << std::endl;
    options::cegqi.set(false);
  }
  // Do we need to track instantiations?
  // Needed for sygus due to single invocation techniques.
  if (options::cegqiNestedQE()
      || (options::proof() && !options::trackInstLemmas.wasSetByUser())
      || is_sygus)
  {
    options::trackInstLemmas.set(true);
  }

  if ((options::fmfBoundLazy.wasSetByUser() && options::fmfBoundLazy())
      || (options::fmfBoundInt.wasSetByUser() && options::fmfBoundInt()))
  {
    options::fmfBound.set(true);
  }
  // now have determined whether fmfBoundInt is on/off
  // apply fmfBoundInt options
  if (options::fmfBound())
  {
    if (!options::mbqiMode.wasSetByUser()
        || (options::mbqiMode() != options::MbqiMode::NONE
            && options::mbqiMode() != options::MbqiMode::FMC))
    {
      // if bounded integers are set, use no MBQI by default
      options::mbqiMode.set(options::MbqiMode::NONE);
    }
    if (!options::prenexQuant.wasSetByUser())
    {
      options::prenexQuant.set(options::PrenexQuantMode::NONE);
    }
  }
  if (options::ufHo())
  {
    // if higher-order, disable proof production
    if (options::proofNew())
    {
      if (options::proofNew.wasSetByUser())
      {
        Warning() << "SmtEngine: turning off proof production (not yet "
                     "supported with --uf-ho)\n";
      }
      options::proofNew.set(false);
    }
    // if higher-order, then current variants of model-based instantiation
    // cannot be used
    if (options::mbqiMode() != options::MbqiMode::NONE)
    {
      options::mbqiMode.set(options::MbqiMode::NONE);
    }
    if (!options::hoElimStoreAx.wasSetByUser())
    {
      // by default, use store axioms only if --ho-elim is set
      options::hoElimStoreAx.set(options::hoElim());
    }
    if (!options::assignFunctionValues())
    {
      // must assign function values
      options::assignFunctionValues.set(true);
    }
    // Cannot use macros, since lambda lifting and macro elimination are inverse
    // operations.
    if (options::macrosQuant())
    {
      options::macrosQuant.set(false);
    }
  }
  if (options::fmfFunWellDefinedRelevant())
  {
    if (!options::fmfFunWellDefined.wasSetByUser())
    {
      options::fmfFunWellDefined.set(true);
    }
  }
  if (options::fmfFunWellDefined())
  {
    if (!options::finiteModelFind.wasSetByUser())
    {
      options::finiteModelFind.set(true);
    }
  }
  // EPR
  if (options::quantEpr())
  {
    if (!options::preSkolemQuant.wasSetByUser())
    {
      options::preSkolemQuant.set(true);
    }
  }

  // now, have determined whether finite model find is on/off
  // apply finite model finding options
  if (options::finiteModelFind())
  {
    // apply conservative quantifiers splitting
    if (!options::quantDynamicSplit.wasSetByUser())
    {
      options::quantDynamicSplit.set(options::QuantDSplitMode::DEFAULT);
    }
    // do not eliminate extended arithmetic symbols from quantified formulas
    if (!options::elimExtArithQuant.wasSetByUser())
    {
      options::elimExtArithQuant.set(false);
    }
    if (!options::eMatching.wasSetByUser())
    {
      options::eMatching.set(options::fmfInstEngine());
    }
    if (!options::instWhenMode.wasSetByUser())
    {
      // instantiate only on last call
      if (options::eMatching())
      {
        options::instWhenMode.set(options::InstWhenMode::LAST_CALL);
      }
    }
  }

  // apply sygus options
  // if we are attempting to rewrite everything to SyGuS, use sygus()
  if (is_sygus)
  {
    if (!options::sygus())
    {
      Trace("smt") << "turning on sygus" << std::endl;
    }
    options::sygus.set(true);
    // must use Ferrante/Rackoff for real arithmetic
    if (!options::cegqiMidpoint.wasSetByUser())
    {
      options::cegqiMidpoint.set(true);
    }
    if (options::sygusRepairConst())
    {
      if (!options::cegqi.wasSetByUser())
      {
        options::cegqi.set(true);
      }
    }
    if (options::sygusInference())
    {
      // optimization: apply preskolemization, makes it succeed more often
      if (!options::preSkolemQuant.wasSetByUser())
      {
        options::preSkolemQuant.set(true);
      }
      if (!options::preSkolemQuantNested.wasSetByUser())
      {
        options::preSkolemQuantNested.set(true);
      }
    }
    // counterexample-guided instantiation for sygus
    if (!options::cegqiSingleInvMode.wasSetByUser())
    {
      options::cegqiSingleInvMode.set(options::CegqiSingleInvMode::USE);
    }
    if (!options::quantConflictFind.wasSetByUser())
    {
      options::quantConflictFind.set(false);
    }
    if (!options::instNoEntail.wasSetByUser())
    {
      options::instNoEntail.set(false);
    }
    if (!options::cegqiFullEffort.wasSetByUser())
    {
      // should use full effort cbqi for single invocation and repair const
      options::cegqiFullEffort.set(true);
    }
    if (options::sygusRew())
    {
      options::sygusRewSynth.set(true);
      options::sygusRewVerify.set(true);
    }
    if (options::sygusRewSynthInput())
    {
      // If we are using synthesis rewrite rules from input, we use
      // sygusRewSynth after preprocessing. See passes/synth_rew_rules.h for
      // details on this technique.
      options::sygusRewSynth.set(true);
      // we should not use the extended rewriter, since we are interested
      // in rewrites that are not in the main rewriter
      if (!options::sygusExtRew.wasSetByUser())
      {
        options::sygusExtRew.set(false);
      }
    }
    // Whether we must use "basic" sygus algorithms. A non-basic sygus algorithm
    // is one that is specialized for returning a single solution. Non-basic
    // sygus algorithms currently include the PBE solver, UNIF+PI, static
    // template inference for invariant synthesis, and single invocation
    // techniques.
    bool reqBasicSygus = false;
    if (options::produceAbducts())
    {
      // if doing abduction, we should filter strong solutions
      if (!options::sygusFilterSolMode.wasSetByUser())
      {
        options::sygusFilterSolMode.set(options::SygusFilterSolMode::STRONG);
      }
      // we must use basic sygus algorithms, since e.g. we require checking
      // a sygus side condition for consistency with axioms.
      reqBasicSygus = true;
    }
    if (options::sygusRewSynth() || options::sygusRewVerify()
        || options::sygusQueryGen())
    {
      // rewrite rule synthesis implies that sygus stream must be true
      options::sygusStream.set(true);
    }
    if (options::sygusStream() || options::incrementalSolving())
    {
      // Streaming and incremental mode are incompatible with techniques that
      // focus the search towards finding a single solution.
      reqBasicSygus = true;
    }
    // Now, disable options for non-basic sygus algorithms, if necessary.
    if (reqBasicSygus)
    {
      if (!options::sygusUnifPbe.wasSetByUser())
      {
        options::sygusUnifPbe.set(false);
      }
      if (options::sygusUnifPi.wasSetByUser())
      {
        options::sygusUnifPi.set(options::SygusUnifPiMode::NONE);
      }
      if (!options::sygusInvTemplMode.wasSetByUser())
      {
        options::sygusInvTemplMode.set(options::SygusInvTemplMode::NONE);
      }
      if (!options::cegqiSingleInvMode.wasSetByUser())
      {
        options::cegqiSingleInvMode.set(options::CegqiSingleInvMode::NONE);
      }
    }
    // do not allow partial functions
    if (!options::bitvectorDivByZeroConst())
    {
      if (options::bitvectorDivByZeroConst.wasSetByUser())
      {
        throw OptionException(
            "--no-bv-div-zero-const is not supported with SyGuS");
      }
      Notice()
          << "SmtEngine: setting bv-div-zero-const to true to support SyGuS"
          << std::endl;
      options::bitvectorDivByZeroConst.set(true);
    }
    if (!options::dtRewriteErrorSel.wasSetByUser())
    {
      options::dtRewriteErrorSel.set(true);
    }
    // do not miniscope
    if (!options::miniscopeQuant.wasSetByUser())
    {
      options::miniscopeQuant.set(false);
    }
    if (!options::miniscopeQuantFreeVar.wasSetByUser())
    {
      options::miniscopeQuantFreeVar.set(false);
    }
    if (!options::quantSplit.wasSetByUser())
    {
      options::quantSplit.set(false);
    }
    // do not do macros
    if (!options::macrosQuant.wasSetByUser())
    {
      options::macrosQuant.set(false);
    }
    if (!options::cegqiPreRegInst.wasSetByUser())
    {
      options::cegqiPreRegInst.set(true);
    }
    // not compatible with proofs
    if (options::proofNew())
    {
      if (options::proofNew.wasSetByUser())
      {
        Notice() << "SmtEngine: setting proof-new to false to support SyGuS"
                 << std::endl;
      }
      options::proofNew.set(false);
    }
  }
  // counterexample-guided instantiation for non-sygus
  // enable if any possible quantifiers with arithmetic, datatypes or bitvectors
  if ((logic.isQuantified()
       && (logic.isTheoryEnabled(THEORY_ARITH)
           || logic.isTheoryEnabled(THEORY_DATATYPES)
           || logic.isTheoryEnabled(THEORY_BV)
           || logic.isTheoryEnabled(THEORY_FP)))
      || options::cegqiAll())
  {
    if (!options::cegqi.wasSetByUser())
    {
      options::cegqi.set(true);
    }
    // check whether we should apply full cbqi
    if (logic.isPure(THEORY_BV))
    {
      if (!options::cegqiFullEffort.wasSetByUser())
      {
        options::cegqiFullEffort.set(true);
      }
    }
  }
  if (options::cegqi())
  {
    if (options::incrementalSolving())
    {
      // cannot do nested quantifier elimination in incremental mode
      options::cegqiNestedQE.set(false);
      options::cegqiPreRegInst.set(false);
    }
    if (logic.isPure(THEORY_ARITH) || logic.isPure(THEORY_BV))
    {
      if (!options::quantConflictFind.wasSetByUser())
      {
        options::quantConflictFind.set(false);
      }
      if (!options::instNoEntail.wasSetByUser())
      {
        options::instNoEntail.set(false);
      }
      if (!options::instWhenMode.wasSetByUser() && options::cegqiModel())
      {
        // only instantiation should happen at last call when model is avaiable
        options::instWhenMode.set(options::InstWhenMode::LAST_CALL);
      }
    }
    else
    {
      // only supported in pure arithmetic or pure BV
      options::cegqiNestedQE.set(false);
    }
    // prenexing
    if (options::cegqiNestedQE())
    {
      // only complete with prenex = normal
      options::prenexQuant.set(options::PrenexQuantMode::NORMAL);
    }
    else if (options::globalNegate())
    {
      if (!options::prenexQuant.wasSetByUser())
      {
        options::prenexQuant.set(options::PrenexQuantMode::NONE);
      }
    }
  }
  // implied options...
  if (options::strictTriggers())
  {
    if (!options::userPatternsQuant.wasSetByUser())
    {
      options::userPatternsQuant.set(options::UserPatMode::TRUST);
    }
  }
  if (options::qcfMode.wasSetByUser() || options::qcfTConstraint())
  {
    options::quantConflictFind.set(true);
  }
  if (options::cegqiNestedQE())
  {
    options::prenexQuantUser.set(true);
    if (!options::preSkolemQuant.wasSetByUser())
    {
      options::preSkolemQuant.set(true);
    }
  }
  // for induction techniques
  if (options::quantInduction())
  {
    if (!options::dtStcInduction.wasSetByUser())
    {
      options::dtStcInduction.set(true);
    }
    if (!options::intWfInduction.wasSetByUser())
    {
      options::intWfInduction.set(true);
    }
  }
  if (options::dtStcInduction())
  {
    // try to remove ITEs from quantified formulas
    if (!options::iteDtTesterSplitQuant.wasSetByUser())
    {
      options::iteDtTesterSplitQuant.set(true);
    }
    if (!options::iteLiftQuant.wasSetByUser())
    {
      options::iteLiftQuant.set(options::IteLiftQuantMode::ALL);
    }
  }
  if (options::intWfInduction())
  {
    if (!options::purifyTriggers.wasSetByUser())
    {
      options::purifyTriggers.set(true);
    }
  }
  if (options::conjectureNoFilter())
  {
    if (!options::conjectureFilterActiveTerms.wasSetByUser())
    {
      options::conjectureFilterActiveTerms.set(false);
    }
    if (!options::conjectureFilterCanonical.wasSetByUser())
    {
      options::conjectureFilterCanonical.set(false);
    }
    if (!options::conjectureFilterModel.wasSetByUser())
    {
      options::conjectureFilterModel.set(false);
    }
  }
  if (options::conjectureGenPerRound.wasSetByUser())
  {
    if (options::conjectureGenPerRound() > 0)
    {
      options::conjectureGen.set(true);
    }
    else
    {
      options::conjectureGen.set(false);
    }
  }
  // can't pre-skolemize nested quantifiers without UF theory
  if (!logic.isTheoryEnabled(THEORY_UF) && options::preSkolemQuant())
  {
    if (!options::preSkolemQuantNested.wasSetByUser())
    {
      options::preSkolemQuantNested.set(false);
    }
  }
  if (!logic.isTheoryEnabled(THEORY_DATATYPES))
  {
    options::quantDynamicSplit.set(options::QuantDSplitMode::NONE);
  }

  // until bugs 371,431 are fixed
  if (!options::minisatUseElim.wasSetByUser())
  {
    // cannot use minisat elimination for logics where a theory solver
    // introduces new literals into the search. This includes quantifiers
    // (quantifier instantiation), and the lemma schemas used in non-linear
    // and sets. We also can't use it if models are enabled.
    if (logic.isTheoryEnabled(THEORY_SETS) || logic.isQuantified()
        || options::produceModels() || options::produceAssignments()
        || options::checkModels()
        || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
    {
      options::minisatUseElim.set(false);
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (options::produceModels() || options::produceAssignments()
      || options::checkModels())
  {
    options::arraysOptimizeLinear.set(false);
    options::arraysLazyRIntro1.set(false);
  }

  if (options::proof())
  {
    if (options::incrementalSolving())
    {
      if (options::incrementalSolving.wasSetByUser())
      {
        throw OptionException("--incremental is not supported with proofs");
      }
      Warning()
          << "SmtEngine: turning off incremental solving mode (not yet "
             "supported with --proof, try --tear-down-incremental instead)"
          << std::endl;
      smte.setOption("incremental", SExpr("false"));
    }
    if (logic > LogicInfo("QF_AUFBVLRA"))
    {
      throw OptionException(
          "Proofs are only supported for sub-logics of QF_AUFBVLIA.");
    }
    if (options::bitvectorAlgebraicSolver())
    {
      if (options::bitvectorAlgebraicSolver.wasSetByUser())
      {
        throw OptionException(
            "--bv-algebraic-solver is not supported with proofs");
      }
      Notice() << "SmtEngine: turning off bv algebraic solver to support proofs"
               << std::endl;
      options::bitvectorAlgebraicSolver.set(false);
    }
    if (options::bitvectorEqualitySolver())
    {
      if (options::bitvectorEqualitySolver.wasSetByUser())
      {
        throw OptionException("--bv-eq-solver is not supported with proofs");
      }
      Notice() << "SmtEngine: turning off bv eq solver to support proofs"
               << std::endl;
      options::bitvectorEqualitySolver.set(false);
    }
    if (options::bitvectorInequalitySolver())
    {
      if (options::bitvectorInequalitySolver.wasSetByUser())
      {
        throw OptionException(
            "--bv-inequality-solver is not supported with proofs");
      }
      Notice() << "SmtEngine: turning off bv ineq solver to support proofs"
               << std::endl;
      options::bitvectorInequalitySolver.set(false);
    }
  }

  if (!options::bitvectorEqualitySolver())
  {
    if (options::bvLazyRewriteExtf())
    {
      if (options::bvLazyRewriteExtf.wasSetByUser())
      {
        throw OptionException(
            "--bv-lazy-rewrite-extf requires --bv-eq-solver to be set");
      }
    }
    Trace("smt")
        << "disabling bvLazyRewriteExtf since equality solver is disabled"
        << std::endl;
    options::bvLazyRewriteExtf.set(false);
  }

  if (!options::sygusExprMinerCheckUseExport())
  {
    if (options::sygusExprMinerCheckTimeout.wasSetByUser())
    {
      throw OptionException(
          "--sygus-expr-miner-check-timeout=N requires "
          "--sygus-expr-miner-check-use-export");
    }
    if (options::sygusRewSynthInput() || options::produceAbducts())
    {
      std::stringstream ss;
      ss << (options::sygusRewSynthInput() ? "--sygus-rr-synth-input"
                                           : "--produce-abducts");
      ss << "requires --sygus-expr-miner-check-use-export";
      throw OptionException(ss.str());
    }
  }

  if (options::stringFMF() && !options::stringProcessLoopMode.wasSetByUser())
  {
    Trace("smt") << "settting stringProcessLoopMode to 'simple' since "
                    "--strings-fmf enabled"
                 << std::endl;
    options::stringProcessLoopMode.set(options::ProcessLoopMode::SIMPLE);
  }

  // !!! All options that require disabling models go here
  bool disableModels = false;
  std::string sOptNoModel;
  if (options::unconstrainedSimp.wasSetByUser() && options::unconstrainedSimp())
  {
    disableModels = true;
    sOptNoModel = "unconstrained-simp";
  }
  else if (options::sortInference())
  {
    disableModels = true;
    sOptNoModel = "sort-inference";
  }
  else if (options::minisatUseElim())
  {
    disableModels = true;
    sOptNoModel = "minisat-elimination";
  }
  else if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
           && !options::nlExt())
  {
    disableModels = true;
    sOptNoModel = "nonlinear arithmetic without nl-ext";
  }
  else if (options::globalNegate())
  {
    disableModels = true;
    sOptNoModel = "global-negate";
  }
  if (disableModels)
  {
    if (options::produceModels())
    {
      if (options::produceModels.wasSetByUser())
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel << " with model generation.";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-models to support "
               << sOptNoModel << std::endl;
      smte.setOption("produce-models", SExpr("false"));
    }
    if (options::produceAssignments())
    {
      if (options::produceAssignments.wasSetByUser())
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (produce-assignments).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off produce-assignments to support "
               << sOptNoModel << std::endl;
      smte.setOption("produce-assignments", SExpr("false"));
    }
    if (options::checkModels())
    {
      if (options::checkModels.wasSetByUser())
      {
        std::stringstream ss;
        ss << "Cannot use " << sOptNoModel
           << " with model generation (check-models).";
        throw OptionException(ss.str());
      }
      Notice() << "SmtEngine: turning off check-models to support "
               << sOptNoModel << std::endl;
      smte.setOption("check-models", SExpr("false"));
    }
  }

  if (options::bitblastMode() == options::BitblastMode::EAGER
      && !logic.isPure(THEORY_BV) && logic.getLogicString() != "QF_UFBV"
      && logic.getLogicString() != "QF_ABV")
  {
    throw OptionException(
        "Eager bit-blasting does not currently support theory combination. "
        "Note that in a QF_BV problem UF symbols can be introduced for "
        "division. "
        "Try --bv-div-zero-const to interpret division by zero as a constant.");
  }
  // !!!!!!!!!!!!!!!! temporary, until proof-new is functional
  if (options::proofNew())
  {
    throw OptionException("--proof-new is not yet supported.");
  }
}

}  // namespace smt
}  // namespace CVC4
