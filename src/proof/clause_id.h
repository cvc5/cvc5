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

const ClauseId ClauseIdEmpty(-1);
const ClauseId ClauseIdUndef(-2);
const ClauseId ClauseIdError(-3);
const ClauseId ClauseIdInput(-4);
const ClauseId ClauseIdLemma(-5);

}/* CVC4 namespace */

#endif /* CVC4__PROOF__CLAUSE_ID_H */
