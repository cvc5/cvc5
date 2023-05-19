/******************************************************************************
 * Top contributors (to current version):
 *   Paul Meng, Liana Hadarean, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of ClauseId.
 *
 * A ClauseId is a shared identifier between the proofs module and the sat
 * solver for a clause.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__CLAUSE_ID_H
#define CVC5__PROOF__CLAUSE_ID_H

namespace cvc5::internal {

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

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__CLAUSE_ID_H */
