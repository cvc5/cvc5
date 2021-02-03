/*********************                                                        */
/*! \file set_defaults.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

void setDefaults(LogicInfo& logic, bool isInternalSubsolver)
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
  if (options::checkUnsatCores() || options::checkUnsatCoresNew()
      || options::dumpUnsatCores() || options::unsatAssumptions())
  {
    Notice() << "SmtEngine: setting unsatCores" << std::endl;
    options::unsatCores.set(true);
  }
  if (options::checkUnsatCoresNew())
  {
    options::proofNew.set(true);
  }
  if (options::bitvectorAigSimplifications.wasSetByUser())
  {
    Notice() << "SmtEngine: setting bitvectorAig" << std::endl;
    options::bitvectorAig.set(true);
  }
  if (options::bitvectorAlgebraicBudget.wasSetByUser())
  {
    Notice() << "SmtEngine: setting bitvectorAlgebraicSolver" << std::endl;
    options::bitvectorAlgebraicSolver.set(true);
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
      options::bitblastMode.set(options::BitblastMode::LAZY);
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

    // Force lazy solver since we don't handle EAGER_ATOMS in the
    // BVSolver::BITBLAST solver.
    options::bvSolver.set(options::BVSolver::LAZY);
  }

  /* Only BVSolver::LAZY natively supports int2bv and nat2bv, for other solvers
   * we need to eagerly eliminate the operators. */
  if (options::bvSolver() == options::BVSolver::SIMPLE
      || options::bvSolver() == options::BVSolver::BITBLAST)
  {
    options::bvLazyReduceExtf.set(false);
    options::bvLazyRewriteExtf.set(false);
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

  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      throw OptionException(
          "solving bitvectors as integers is incompatible with --bool-to-bv.");
    }
    if (options::BVAndIntegerGranularity() > 8)
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

  // --ite-simp is an experimental option designed for QF_LIA/nec. This
  // technique is experimental. This benchmark set also requires removing ITEs
  // during preprocessing, before repeating simplification. Hence, we enable
  // this by default.
  if (options::doITESimp())
  {
    if (!options::earlyIteRemoval.wasSetByUser())
    {
      options::earlyIteRemoval.set(true);
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
    // Note we allow E-matching by default to support combinations of sequences
    // and quantifiers.
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
  if (!isInternalSubsolver)
  {
    if (options::produceAbducts()
        || options::produceInterpols() != options::ProduceInterpols::NONE
        || options::sygusInference() || options::sygusRewSynthInput()
        || options::sygusInst())
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
       || options::produceInterpols() != options::ProduceInterpols::NONE
       || options::modelCoresMode() != options::ModelCoresMode::NONE
       || options::blockModelsMode() != options::BlockModelsMode::NONE)
      && !options::produceAssertions())
  {
    Notice() << "SmtEngine: turning on produce-assertions to support "
             << "option requiring assertions." << std::endl;
    options::produceAssertions.set(true);
  }

  // Disable options incompatible with incremental solving, unsat cores or
  // output an error if enabled explicitly. It is also currently incompatible
  // with arithmetic, force the option off.
  if (options::incrementalSolving() || options::unsatCores())
  {
    if (options::unconstrainedSimp())
    {
      if (options::unconstrainedSimp.wasSetByUser())
      {
        throw OptionException(
            "unconstrained simplification not supported with unsat "
            "cores/incremental solving");
      }
      Notice() << "SmtEngine: turning off unconstrained simplification to "
                  "support unsat cores/incremental solving"
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

  if (options::incrementalSolving())
  {
    if (options::sygusInference())
    {
      if (options::sygusInference.wasSetByUser())
      {
        throw OptionException(
            "sygus inference not supported with incremental solving");
      }
      Notice() << "SmtEngine: turning off sygus inference to support "
                  "incremental solving"
               << std::endl;
      options::sygusInference.set(false);
    }
  }

  if (options::solveBVAsInt() != options::SolveBVAsIntMode::OFF)
  {
    /**
     * Operations on 1 bits are better handled as Boolean operations
     * than as integer operations.
     * Therefore, we enable bv-to-bool, which runs before
     * the translation to integers.
     */
    options::bitvectorToBool.set(true);
  }

  // Disable options incompatible with unsat cores or output an error if enabled
  // explicitly
  if (options::unsatCores())
  {
    if (options::simplificationMode() != options::SimplificationMode::NONE)
    {
      if (options::simplificationMode.wasSetByUser())
      {
        throw OptionException("simplification not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off simplification to support unsat "
                  "cores"
               << std::endl;
      options::simplificationMode.set(options::SimplificationMode::NONE);
    }

    if (options::pbRewrites())
    {
      if (options::pbRewrites.wasSetByUser())
      {
        throw OptionException(
            "pseudoboolean rewrites not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off pseudoboolean rewrites to support "
                  "unsat cores"
               << std::endl;
      options::pbRewrites.set(false);
    }

    if (options::sortInference())
    {
      if (options::sortInference.wasSetByUser())
      {
        throw OptionException("sort inference not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off sort inference to support unsat "
                  "cores"
               << std::endl;
      options::sortInference.set(false);
    }

    if (options::preSkolemQuant())
    {
      if (options::preSkolemQuant.wasSetByUser())
      {
        throw OptionException(
            "pre-skolemization not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off pre-skolemization to support unsat "
                  "cores"
               << std::endl;
      options::preSkolemQuant.set(false);
    }


    if (options::bitvectorToBool())
    {
      if (options::bitvectorToBool.wasSetByUser())
      {
        throw OptionException("bv-to-bool not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bitvector-to-bool to support unsat "
                  "cores"
               << std::endl;
      options::bitvectorToBool.set(false);
    }

    if (options::boolToBitvector() != options::BoolToBVMode::OFF)
    {
      if (options::boolToBitvector.wasSetByUser())
      {
        throw OptionException(
            "bool-to-bv != off not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bool-to-bv to support unsat "
                  "cores"
               << std::endl;
      options::boolToBitvector.set(options::BoolToBVMode::OFF);
    }

    if (options::bvIntroducePow2())
    {
      if (options::bvIntroducePow2.wasSetByUser())
      {
        throw OptionException("bv-intro-pow2 not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bv-intro-pow2 to support "
                  "unsat-cores"
               << std::endl;
      options::bvIntroducePow2.set(false);
    }

    if (options::repeatSimp())
    {
      if (options::repeatSimp.wasSetByUser())
      {
        throw OptionException("repeat-simp not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off repeat-simp to support unsat "
                  "cores"
               << std::endl;
      options::repeatSimp.set(false);
    }

    if (options::globalNegate())
    {
      if (options::globalNegate.wasSetByUser())
      {
        throw OptionException("global-negate not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off global-negate to support unsat "
                  "cores"
               << std::endl;
      options::globalNegate.set(false);
    }

    if (options::bitvectorAig())
    {
      throw OptionException("bitblast-aig not supported with unsat cores");
    }

    if (options::doITESimp())
    {
      throw OptionException("ITE simp not supported with unsat cores");
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
      options::boolToBitvector.set(options::BoolToBVMode::OFF);
    }
  }

  // cases where we need produce models
  if (!options::produceModels()
      && (options::produceAssignments() || options::sygusRewSynthCheck()
          || is_sygus))
  {
    Notice() << "SmtEngine: turning on produce-models" << std::endl;
    options::produceModels.set(true);
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
    if (!logic.isTheoryEnabled(THEORY_ARITH) || logic.isDifferenceLogic())
    {
      Notice()
          << "Enabling linear integer arithmetic because strings are enabled"
          << std::endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    else if (!logic.areIntegersUsed())
    {
      Notice() << "Enabling integer arithmetic because strings are enabled"
               << std::endl;
      log.enableIntegers();
    }
    logic = log;
    logic.lock();
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
          && options::solveIntAsBV() == 0)
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
        && !logic.isTheoryEnabled(THEORY_SETS)
        && !logic.isTheoryEnabled(THEORY_BAGS)
        && !(logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
             && !logic.isQuantified()))
    {
      Trace("smt") << "setting theoryof-mode to term-based" << std::endl;
      options::theoryOfMode.set(options::TheoryOfMode::THEORY_OF_TERM_BASED);
    }
  }

  // by default, symmetry breaker is on only for non-incremental QF_UF
  if (!options::ufSymmetryBreaker.wasSetByUser())
  {
    bool qf_uf_noinc = logic.isPure(THEORY_UF) && !logic.isQuantified()
                       && !options::incrementalSolving()
                       && !options::unsatCores();
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf_noinc
                 << std::endl;
    options::ufSymmetryBreaker.set(qf_uf_noinc);
  }

  // If in arrays, set the UF handler to arrays
  if (logic.isTheoryEnabled(THEORY_ARRAYS) && !options::ufHo()
      && !options::finiteModelFind()
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
    options::boolToBitvector.set(options::BoolToBVMode::OFF);
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
    options::globalNegate.set(false);
    options::bvAbstraction.set(false);
    options::arithMLTrick.set(false);
  }
  if (logic.hasCardinalityConstraints())
  {
    // must have finite model finding on
    options::finiteModelFind.set(true);
  }

  if (options::instMaxLevel() != -1)
  {
    Notice() << "SmtEngine: turning off cbqi to support instMaxLevel"
             << std::endl;
    options::cegqi.set(false);
  }
  // Do we need to track instantiations?
  if (options::unsatCores() && !options::trackInstLemmas.wasSetByUser())
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

  // now, have determined whether finite model find is on/off
  // apply finite model finding options
  if (options::finiteModelFind())
  {
    // apply conservative quantifiers splitting
    if (!options::quantDynamicSplit.wasSetByUser())
    {
      options::quantDynamicSplit.set(options::QuantDSplitMode::DEFAULT);
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
    // must disable cegqi-bv since it may introduce witness terms, which
    // cannot appear in synthesis solutions
    if (!options::cegqiBv.wasSetByUser())
    {
      options::cegqiBv.set(false);
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
    // use tangent planes by default, since we want to put effort into
    // the verification step for sygus queries with non-linear arithmetic
    if (!options::nlExtTangentPlanes.wasSetByUser())
    {
      options::nlExtTangentPlanes.set(true);
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
    if (options::globalNegate())
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
    if (logic.isTheoryEnabled(THEORY_SETS)
        || logic.isTheoryEnabled(THEORY_BAGS)
        || logic.isQuantified()
        || options::produceModels() || options::produceAssignments()
        || options::checkModels()
        || (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()))
    {
      options::minisatUseElim.set(false);
    }
  }

  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear()
      && options::nlRlvMode() != options::NlRlvMode::NONE)
  {
    if (!options::relevanceFilter())
    {
      if (options::relevanceFilter.wasSetByUser())
      {
        Warning() << "SmtEngine: turning on relevance filtering to support "
                     "--nl-ext-rlv="
                  << options::nlRlvMode() << std::endl;
      }
      // must use relevance filtering techniques
      options::relevanceFilter.set(true);
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (options::produceModels() || options::produceAssignments()
      || options::checkModels())
  {
    options::arraysOptimizeLinear.set(false);
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
      options::produceModels.set(false);
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
      options::produceAssignments.set(false);
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
      options::checkModels.set(false);
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

  if (logic == LogicInfo("QF_UFNRA"))
  {
#ifdef CVC4_USE_POLY
    if (!options::nlCad() && !options::nlCad.wasSetByUser())
    {
      options::nlCad.set(true);
      if (!options::nlExt.wasSetByUser())
      {
        options::nlExt.set(false);
      }
      if (!options::nlRlvMode.wasSetByUser())
      {
        options::nlRlvMode.set(options::NlRlvMode::INTERLEAVE);
      }
    }
#endif
  }
#ifndef CVC4_USE_POLY
  if (options::nlCad())
  {
    if (options::nlCad.wasSetByUser())
    {
      std::stringstream ss;
      ss << "Cannot use " << options::nlCad.getName() << " without configuring with --poly.";
      throw OptionException(ss.str());
    }
    else
    {
      Notice() << "Cannot use --" << options::nlCad.getName()
               << " without configuring with --poly." << std::endl;
      options::nlCad.set(false);
      options::nlExt.set(true);
    }
  }
#endif
}

}  // namespace smt
}  // namespace CVC4
