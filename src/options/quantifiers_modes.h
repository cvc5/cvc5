/*********************                                                        */
/*! \file quantifiers_modes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BASE__QUANTIFIERS_MODES_H
#define __CVC4__BASE__QUANTIFIERS_MODES_H

#include <iostream>

namespace CVC4 {
namespace theory {
namespace quantifiers {

enum InstWhenMode {
  /** Apply instantiation round before full effort (possibly at standard effort) */
  INST_WHEN_PRE_FULL,
  /** Apply instantiation round at full effort or above  */
  INST_WHEN_FULL,
  /** Apply instantiation round at full effort, after all other theories finish, or above  */
  INST_WHEN_FULL_DELAY,
  /** Apply instantiation round at full effort half the time, and last call always */
  INST_WHEN_FULL_LAST_CALL,
  /** Apply instantiation round at full effort after all other theories finish half the time, and last call always */
  INST_WHEN_FULL_DELAY_LAST_CALL,
  /** Apply instantiation round at last call only */
  INST_WHEN_LAST_CALL,
};

enum LiteralMatchMode {
  /** Do not consider polarity of patterns */
  LITERAL_MATCH_NONE,
  /** Conservatively consider polarity of patterns */
  LITERAL_MATCH_USE,
  /** Aggressively consider polarity of Boolean predicates */
  LITERAL_MATCH_AGG_PREDICATE,
  /** Aggressively consider polarity of all terms */
  LITERAL_MATCH_AGG,
};

enum MbqiMode {
  /** mbqi from CADE 24 paper */
  MBQI_GEN_EVAL,
  /** no mbqi */
  MBQI_NONE,
  /** default, mbqi from Section 5.4.2 of AJR thesis */
  MBQI_FMC,
  /** mbqi with integer intervals */
  MBQI_FMC_INTERVAL,
  /** abstract mbqi algorithm */
  MBQI_ABS,
  /** mbqi trust (produce no instantiations) */
  MBQI_TRUST,
};

enum QcfWhenMode {
  /** default, apply at full effort */
  QCF_WHEN_MODE_DEFAULT,
  /** apply at last call */
  QCF_WHEN_MODE_LAST_CALL,
  /** apply at standard effort */
  QCF_WHEN_MODE_STD,
  /** apply based on heuristics */
  QCF_WHEN_MODE_STD_H,
};

enum QcfMode {
  /** default, use qcf for conflicts only */
  QCF_CONFLICT_ONLY,
  /** use qcf for conflicts and propagations */
  QCF_PROP_EQ,
  /** use qcf for conflicts, propagations and heuristic instantiations */
  QCF_PARTIAL,
};

enum UserPatMode {
  /** use but do not trust */
  USER_PAT_MODE_USE,
  /** default, if patterns are supplied for a quantifier, use only those */
  USER_PAT_MODE_TRUST,
  /** resort to user patterns only when necessary */
  USER_PAT_MODE_RESORT,
  /** ignore user patterns */
  USER_PAT_MODE_IGNORE,
  /** interleave use/resort for user patterns */
  USER_PAT_MODE_INTERLEAVE,
};

enum TriggerSelMode {
  /** only consider minimal terms for triggers */
  TRIGGER_SEL_MIN,
  /** only consider maximal terms for triggers */
  TRIGGER_SEL_MAX,
  /** consider minimal terms for single triggers, maximal for non-single */
  TRIGGER_SEL_MIN_SINGLE_MAX,
  /** consider minimal terms for single triggers, all for non-single */
  TRIGGER_SEL_MIN_SINGLE_ALL,
  /** consider all terms for triggers */
  TRIGGER_SEL_ALL,
};

enum TriggerActiveSelMode {
  /** always use all triggers */
  TRIGGER_ACTIVE_SEL_ALL,
  /** only use triggers with minimal # of ground terms */
  TRIGGER_ACTIVE_SEL_MIN,
  /** only use triggers with maximal # of ground terms */
  TRIGGER_ACTIVE_SEL_MAX,
};

enum CVC4_PUBLIC PrenexQuantMode {
  /** do not prenex */
  PRENEX_QUANT_NONE,
  /** prenex same sign quantifiers */
  PRENEX_QUANT_SIMPLE,
  /** aggressive prenex, disjunctive prenex normal form */
  PRENEX_QUANT_DISJ_NORMAL,
  /** prenex normal form */
  PRENEX_QUANT_NORMAL,
};

enum CegqiFairMode {
  /** enforce fairness by UF corresponding to datatypes size */
  CEGQI_FAIR_UF_DT_SIZE,
  /** enforce fairness by datatypes size */
  CEGQI_FAIR_DT_SIZE,
  /** enforce fairness by datatypes height bound */
  CEGQI_FAIR_DT_HEIGHT_PRED,
  /** enforce fairness by datatypes size bound */
  CEGQI_FAIR_DT_SIZE_PRED,
  /** do not use fair strategy for CEGQI */
  CEGQI_FAIR_NONE,
};

enum TermDbMode {
  /** consider all terms in master equality engine */
  TERM_DB_ALL,
  /** consider only relevant terms */
  TERM_DB_RELEVANT,
};

enum IteLiftQuantMode {
  /** do not lift ITEs in quantified formulas */
  ITE_LIFT_QUANT_MODE_NONE,
  /** only lift ITEs in quantified formulas if reduces the term size */
  ITE_LIFT_QUANT_MODE_SIMPLE,
  /** lift ITEs  */
  ITE_LIFT_QUANT_MODE_ALL,
};

enum CegqiSingleInvMode {
  /** do not use single invocation techniques */
  CEGQI_SI_MODE_NONE,
  /** use single invocation techniques */
  CEGQI_SI_MODE_USE,
  /** always use single invocation techniques, abort if solution reconstruction will fail */
  CEGQI_SI_MODE_ALL_ABORT,
  /** always use single invocation techniques */
  CEGQI_SI_MODE_ALL,
};

enum SygusInvTemplMode {
  /** synthesize I( x ) */
  SYGUS_INV_TEMPL_MODE_NONE,
  /** synthesize ( pre( x ) V I( x ) ) */
  SYGUS_INV_TEMPL_MODE_PRE,
  /** synthesize ( post( x ) ^ I( x ) ) */
  SYGUS_INV_TEMPL_MODE_POST,
};

enum MacrosQuantMode {
  /** infer all definitions */
  MACROS_QUANT_MODE_ALL,
  /** infer ground definitions */
  MACROS_QUANT_MODE_GROUND,
  /** infer ground uf definitions */
  MACROS_QUANT_MODE_GROUND_UF,
};

enum QuantDSplitMode {
  /** never do quantifiers splitting */
  QUANT_DSPLIT_MODE_NONE,
  /** default */
  QUANT_DSPLIT_MODE_DEFAULT,
  /** do quantifiers splitting aggressively */
  QUANT_DSPLIT_MODE_AGG,
};

enum QuantRepMode {
  /** let equality engine choose representatives */
  QUANT_REP_MODE_EE,
  /** default, choose representatives that appear first */
  QUANT_REP_MODE_FIRST,
  /** choose representatives that have minimal depth */
  QUANT_REP_MODE_DEPTH,
};

enum FmfBoundMinMode {
  /** do not minimize bounds */
  FMF_BOUND_MIN_NONE,
  /** default, minimize integer ranges */
  FMF_BOUND_MIN_INT_RANGE,
  /** minimize set cardinality ranges */
  FMF_BOUND_MIN_SET_CARD,
  /** minimize all bounds */
  FMF_BOUND_MIN_ALL,
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::quantifiers::InstWhenMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__BASE__QUANTIFIERS_MODES_H */
