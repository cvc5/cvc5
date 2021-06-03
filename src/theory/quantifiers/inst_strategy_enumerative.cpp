/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, MikolasJanota, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of an enumerative instantiation strategy.
 */

#include "theory/quantifiers/inst_strategy_enumerative.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_tuple_enumerator.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

InstStrategyEnum::InstStrategyEnum(QuantifiersState& qs,
                                   QuantifiersInferenceManager& qim,
                                   QuantifiersRegistry& qr,
                                   TermRegistry& tr,
                                   RelevantDomain* rd)
    : QuantifiersModule(qs, qim, qr, tr), d_rd(rd), d_fullSaturateLimit(-1)
{
}
void InstStrategyEnum::presolve()
{
  d_fullSaturateLimit = options::fullSaturateLimit();
}
bool InstStrategyEnum::needsCheck(Theory::Effort e)
{
  if (d_fullSaturateLimit == 0)
  {
    return false;
  }
  if (options::fullSaturateInterleave())
  {
    // if interleaved, we run at the same time as E-matching
    if (d_qstate.getInstWhenNeedsCheck(e))
    {
      return true;
    }
  }
  if (options::fullSaturateQuant())
  {
    if (e >= Theory::EFFORT_LAST_CALL)
    {
      return true;
    }
  }
  return false;
}

void InstStrategyEnum::reset_round(Theory::Effort e) {}
void InstStrategyEnum::check(Theory::Effort e, QEffort quant_e)
{
  bool doCheck = false;
  bool fullEffort = false;
  if (d_fullSaturateLimit != 0)
  {
    if (options::fullSaturateInterleave())
    {
      // we only add when interleaved with other strategies
      doCheck = quant_e == QEFFORT_STANDARD && d_qim.hasPendingLemma();
    }
    if (options::fullSaturateQuant() && !doCheck)
    {
      if (!d_qstate.getValuation().needCheck())
      {
        doCheck = quant_e == QEFFORT_LAST_CALL;
        fullEffort = true;
      }
    }
  }
  if (!doCheck)
  {
    return;
  }
  Assert(!d_qstate.isInConflict());
  double clSet = 0;
  if (Trace.isOn("fs-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("fs-engine") << "---Full Saturation Round, effort = " << e << "---"
                       << std::endl;
  }
  unsigned rstart = options::fullSaturateQuantRd() ? 0 : 1;
  unsigned rend = fullEffort ? 1 : rstart;
  unsigned addedLemmas = 0;
  // First try in relevant domain of all quantified formulas, if no
  // instantiations exist, try arbitrary ground terms.
  // Notice that this stratification of effort levels makes it so that some
  // quantified formulas may not be instantiated (if they have no instances
  // at effort level r=0 but another quantified formula does). We prefer
  // this stratification since effort level r=1 may be highly expensive in the
  // case where we have a quantified formula with many entailed instances.
  FirstOrderModel* fm = d_treg.getModel();
  unsigned nquant = fm->getNumAssertedQuantifiers();
  std::map<Node, bool> alreadyProc;
  for (unsigned r = rstart; r <= rend; r++)
  {
    if (d_rd || r > 0)
    {
      if (r == 0)
      {
        Trace("inst-alg") << "-> Relevant domain instantiate..." << std::endl;
        Trace("inst-alg-debug") << "Compute relevant domain..." << std::endl;
        d_rd->compute();
        Trace("inst-alg-debug") << "...finished" << std::endl;
      }
      else
      {
        Trace("inst-alg") << "-> Ground term instantiate..." << std::endl;
      }
      for (unsigned i = 0; i < nquant; i++)
      {
        Node q = fm->getAssertedQuantifier(i, true);
        bool doProcess = d_qreg.hasOwnership(q, this)
                         && fm->isQuantifierActive(q)
                         && alreadyProc.find(q) == alreadyProc.end();
        if (doProcess)
        {
          if (process(q, fullEffort, r == 0))
          {
            // don't need to mark this if we are not stratifying
            if (!options::fullSaturateStratify())
            {
              alreadyProc[q] = true;
            }
            // added lemma
            addedLemmas++;
          }
          if (d_qstate.isInConflict())
          {
            break;
          }
        }
      }
      if (d_qstate.isInConflict()
          || (addedLemmas > 0 && options::fullSaturateStratify()))
      {
        // we break if we are in conflict, or if we added any lemma at this
        // effort level and we stratify effort levels.
        break;
      }
    }
  }
  if (Trace.isOn("fs-engine"))
  {
    Trace("fs-engine") << "Added lemmas = " << addedLemmas << std::endl;
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("fs-engine") << "Finished full saturation engine, time = "
                       << (clSet2 - clSet) << std::endl;
  }
  if (d_fullSaturateLimit > 0)
  {
    d_fullSaturateLimit--;
  }
}

bool InstStrategyEnum::process(Node quantifier, bool fullEffort, bool isRd)
{
  // ignore if constant true (rare case of non-standard quantifier whose body
  // is rewritten to true)
  if (quantifier[1].isConst() && quantifier[1].getConst<bool>())
  {
    return false;
  }

  TermTupleEnumeratorEnv ttec;
  ttec.d_fullEffort = fullEffort;
  ttec.d_increaseSum = options::fullSaturateSum();
  // make the enumerator, which is either relevant domain or term database
  // based on the flag isRd.
  std::unique_ptr<TermTupleEnumeratorInterface> enumerator(
      isRd ? mkTermTupleEnumeratorRd(quantifier, &ttec, d_rd)
           : mkTermTupleEnumerator(
                 quantifier, &ttec, d_qstate, d_treg.getTermDatabase()));
  std::vector<Node> terms;
  std::vector<bool> failMask;
  Instantiate* ie = d_qim.getInstantiate();
  for (enumerator->init(); enumerator->hasNext();)
  {
    if (d_qstate.isInConflict())
    {
      // could be conflicting for an internal reason
      return false;
    }
    enumerator->next(terms);
    // try instantiation
    failMask.clear();
    /* if (ie->addInstantiation(quantifier, terms)) */
    if (ie->addInstantiationExpFail(
            quantifier, terms, failMask, InferenceId::QUANTIFIERS_INST_ENUM))
    {
      Trace("inst-alg-rd") << "Success!" << std::endl;
      return true;
    }
    else
    {
      enumerator->failureReason(failMask);
    }
  }
  return false;
  // TODO : term enumerator instantiation?
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
