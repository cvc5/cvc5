/*********************                                                        */
/*! \file modes.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__MODES_H
#define __CVC4__THEORY__QUANTIFIERS__MODES_H

#include <iostream>

namespace CVC4 {
namespace theory {
namespace quantifiers {

typedef enum {
  /** Apply instantiation round before full effort (possibly at standard effort) */
  INST_WHEN_PRE_FULL,
  /** Apply instantiation round at full effort or above  */
  INST_WHEN_FULL,
  /** Apply instantiation round at full effort, after all other theories finish, or above  */
  INST_WHEN_FULL_DELAY,
  /** Apply instantiation round at full effort half the time, and last call always */
  INST_WHEN_FULL_LAST_CALL,
  /** Apply instantiation round at last call only */
  INST_WHEN_LAST_CALL,
} InstWhenMode;

typedef enum {
  /** Do not consider polarity of patterns */
  LITERAL_MATCH_NONE,
  /** Consider polarity of boolean predicates only */
  LITERAL_MATCH_PREDICATE,
  /** Consider polarity of boolean predicates, as well as equalities */
  LITERAL_MATCH_EQUALITY,
} LiteralMatchMode;

typedef enum {
  /** default, use all methods for axioms */
  AXIOM_INST_MODE_DEFAULT,
  /** only use heuristic methods for axioms, return unknown in the case no instantiations are produced */
  AXIOM_INST_MODE_TRUST,
  /** only use heuristic methods for axioms, resort to all methods when no instantiations are produced */
  AXIOM_INST_MODE_PRIORITY,
} AxiomInstMode;

typedef enum {
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
} MbqiMode;

typedef enum {
  /** default, apply at full effort */
  QCF_WHEN_MODE_DEFAULT,
  /** apply at last call */
  QCF_WHEN_MODE_LAST_CALL,
  /** apply at standard effort */
  QCF_WHEN_MODE_STD,
  /** apply based on heuristics */
  QCF_WHEN_MODE_STD_H,
} QcfWhenMode;

typedef enum {
  /** default, use qcf for conflicts only */
  QCF_CONFLICT_ONLY,
  /** use qcf for conflicts and propagations */
  QCF_PROP_EQ,
  /** use qcf for conflicts, propagations and heuristic instantiations */
  QCF_PARTIAL,
  /** use qcf for model checking */
  QCF_MC,
} QcfMode;

typedef enum {
  /** use but do not trust */
  USER_PAT_MODE_USE,
  /** default, if patterns are supplied for a quantifier, use only those */
  USER_PAT_MODE_TRUST,
  /** resort to user patterns only when necessary */
  USER_PAT_MODE_RESORT,
  /** ignore user patterns */
  USER_PAT_MODE_IGNORE,
} UserPatMode;

typedef enum {
  /** default for trigger selection */
  TRIGGER_SEL_DEFAULT,
  /** only consider minimal terms for triggers */
  TRIGGER_SEL_MIN,
  /** only consider maximal terms for triggers */
  TRIGGER_SEL_MAX,
} TriggerSelMode;

typedef enum CVC4_PUBLIC {
  /** default : prenex quantifiers without user patterns */
  PRENEX_NO_USER_PAT,
  /** prenex all */
  PRENEX_ALL,
  /** prenex none */
  PRENEX_NONE,
} PrenexQuantMode;

typedef enum {
  /** enforce fairness by UF corresponding to datatypes size */
  CEGQI_FAIR_UF_DT_SIZE,
  /** enforce fairness by datatypes size */
  CEGQI_FAIR_DT_SIZE,
  /** enforce fairness by datatypes height bound */
  CEGQI_FAIR_DT_HEIGHT_PRED,
  /** do not use fair strategy for CEGQI */
  CEGQI_FAIR_NONE,
} CegqiFairMode;

typedef enum {
  /** consider all terms in master equality engine */
  TERM_DB_ALL,
  /** consider only relevant terms */
  TERM_DB_RELEVANT,
} TermDbMode;


}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::quantifiers::InstWhenMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODES_H */
