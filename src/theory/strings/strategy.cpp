/*********************                                                        */
/*! \file strategy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the strategy of the theory of strings.
 **/

#include "theory/strings/strategy."

#include "theory/strings/theory_strings.h"

namespace CVC4 {
namespace theory {
namespace strings {

std::ostream& operator<<(std::ostream& out, InferStep s)
{
  switch (s)
  {
    case BREAK: out << "break"; break;
    case CHECK_INIT: out << "check_init"; break;
    case CHECK_CONST_EQC: out << "check_const_eqc"; break;
    case CHECK_EXTF_EVAL: out << "check_extf_eval"; break;
    case CHECK_CYCLES: out << "check_cycles"; break;
    case CHECK_FLAT_FORMS: out << "check_flat_forms"; break;
    case CHECK_NORMAL_FORMS_EQ: out << "check_normal_forms_eq"; break;
    case CHECK_NORMAL_FORMS_DEQ: out << "check_normal_forms_deq"; break;
    case CHECK_CODES: out << "check_codes"; break;
    case CHECK_LENGTH_EQC: out << "check_length_eqc"; break;
    case CHECK_EXTF_REDUCTION: out << "check_extf_reduction"; break;
    case CHECK_MEMBERSHIP: out << "check_membership"; break;
    case CHECK_CARDINALITY: out << "check_cardinality"; break;
    default: out << "?"; break;
  }
  return out;
}

Strategy::Strategy(TheoryStrings& parent)
    : d_parent(parent),
      d_strategy_init(false)
{
  
}

Strategy::~Strategy() {

}

bool Strategy::hasStrategyEffort(Effort e) const
{
  return d_strat_steps.find(e) != d_strat_steps.end();
}

void Strategy::addStrategyStep(InferStep s, int effort, bool addBreak)
{
  // must run check init first
  Assert((s == CHECK_INIT) == d_infer_steps.empty());
  // must use check cycles when using flat forms
  Assert(s != CHECK_FLAT_FORMS
         || std::find(d_infer_steps.begin(), d_infer_steps.end(), CHECK_CYCLES)
                != d_infer_steps.end());
  d_infer_steps.push_back(s);
  d_infer_step_effort.push_back(effort);
  if (addBreak)
  {
    d_infer_steps.push_back(BREAK);
    d_infer_step_effort.push_back(0);
  }
}

void Strategy::initializeStrategy()
{
  // initialize the strategy if not already done so
  if (!d_strategy_init)
  {
    std::map<Effort, unsigned> step_begin;
    std::map<Effort, unsigned> step_end;
    d_strategy_init = true;
    // beginning indices
    step_begin[EFFORT_FULL] = 0;
    if (options::stringEager())
    {
      step_begin[EFFORT_STANDARD] = 0;
    }
    // add the inference steps
    addStrategyStep(CHECK_INIT);
    addStrategyStep(CHECK_CONST_EQC);
    addStrategyStep(CHECK_EXTF_EVAL, 0);
    addStrategyStep(CHECK_CYCLES);
    if (options::stringFlatForms())
    {
      addStrategyStep(CHECK_FLAT_FORMS);
    }
    addStrategyStep(CHECK_EXTF_REDUCTION, 1);
    if (options::stringEager())
    {
      // do only the above inferences at standard effort, if applicable
      step_end[EFFORT_STANDARD] = d_infer_steps.size() - 1;
    }
    if (!options::stringEagerLen())
    {
      addStrategyStep(CHECK_REGISTER_TERMS_PRE_NF);
    }
    addStrategyStep(CHECK_NORMAL_FORMS_EQ);
    addStrategyStep(CHECK_EXTF_EVAL, 1);
    if (!options::stringEagerLen() && options::stringLenNorm())
    {
      addStrategyStep(CHECK_LENGTH_EQC, 0, false);
      addStrategyStep(CHECK_REGISTER_TERMS_NF);
    }
    addStrategyStep(CHECK_NORMAL_FORMS_DEQ);
    addStrategyStep(CHECK_CODES);
    if (options::stringEagerLen() && options::stringLenNorm())
    {
      addStrategyStep(CHECK_LENGTH_EQC);
    }
    if (options::stringExp() && !options::stringGuessModel())
    {
      addStrategyStep(CHECK_EXTF_REDUCTION, 2);
    }
    addStrategyStep(CHECK_MEMBERSHIP);
    addStrategyStep(CHECK_CARDINALITY);
    step_end[EFFORT_FULL] = d_infer_steps.size() - 1;
    if (options::stringExp() && options::stringGuessModel())
    {
      step_begin[EFFORT_LAST_CALL] = d_infer_steps.size();
      // these two steps are run in parallel
      addStrategyStep(CHECK_EXTF_REDUCTION, 2, false);
      addStrategyStep(CHECK_EXTF_EVAL, 3);
      step_end[EFFORT_LAST_CALL] = d_infer_steps.size() - 1;
    }
    // set the beginning/ending ranges
    for (const std::pair<const Effort, unsigned>& it_begin : step_begin)
    {
      Effort e = it_begin.first;
      std::map<Effort, unsigned>::iterator it_end = step_end.find(e);
      Assert(it_end != step_end.end());
      d_strat_steps[e] =
          std::pair<unsigned, unsigned>(it_begin.second, it_end->second);
    }
  }
}

void Strategy::runStrategy(unsigned sbegin, unsigned send)
{
  Trace("strings-process") << "----check, next round---" << std::endl;
  for (unsigned i = sbegin; i <= send; i++)
  {
    InferStep curr = d_infer_steps[i];
    if (curr == BREAK)
    {
      if (d_im.hasProcessed())
      {
        break;
      }
    }
    else
    {
      d_parent.runInferStep(curr, d_infer_step_effort[i]);
      if (d_state.isInConflict())
      {
        break;
      }
    }
  }
  Trace("strings-process") << "----finished round---" << std::endl;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
