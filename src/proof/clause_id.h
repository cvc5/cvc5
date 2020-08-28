/*********************                                                        */
/*! \file clause_id.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definition of ClauseId
 **
 ** A ClauseId is a shared identifier between the proofs module and the sat
 ** solver for a clause.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__CLAUSE_ID_H
#define CVC4__PROOF__CLAUSE_ID_H

namespace CVC4 {

/**
 * A ClauseId is a shared identifier between the proofs module and the sat
 * solver for a clause.
 */
typedef unsigned ClauseId;

/** Reserved clauseId values used in the resolution proof. The represent,
 * respectively, the empty clause, that adding the clause to the SAT solver was
 * a no-op, and that an error occurred when trying to add. */
const ClauseId ClauseIdEmpty(-1);
const ClauseId ClauseIdUndef(-2);
const ClauseId ClauseIdError(-3);

}/* CVC4 namespace */

#endif /* CVC4__PROOF__CLAUSE_ID_H */
