/*********************                                                        */
/*! \file modes.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

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
  /** default, mbqi from CADE 24 paper */
  MBQI_DEFAULT,
  /** no mbqi */
  MBQI_NONE,
  /** implementation that mimics inst-gen */
  MBQI_INST_GEN,
  /** mbqi from Section 5.4.2 of AJR thesis */
  MBQI_FMC,
  /** mbqi with integer intervals */
  MBQI_FMC_INTERVAL,
  /** mbqi with interval abstraction of uninterpreted sorts */
  MBQI_INTERVAL,
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
  /** use qcf for model checking */
  QCF_MC,
} QcfMode;

typedef enum {
  /** default, use but do not trust */
  USER_PAT_MODE_DEFAULT,
  /** if patterns are supplied for a quantifier, use only those */
  USER_PAT_MODE_TRUST,
  /** ignore user patterns */
  USER_PAT_MODE_IGNORE,
} UserPatMode;

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::quantifiers::InstWhenMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODES_H */
