/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An exception signaling that a Theory should immediately
 * stop performing processing.
 *
 * An exception signaling that a Theory should immediately stop
 * performing processing and relinquish control to its caller (e.g.,
 * in a parallel environment).  A Theory might be interrupted if it
 * calls into its cvc5::internal::theory::OutputChannel, and it should only
 * catch this exception to perform emergency repair of any invariants
 * it must re-establish.  Further, if this exception is caught by a
 * Theory, the Theory should rethrow the same exception (via "throw;"
 * in the exception block) rather than return, as the Interrupted
 * instance might contain additional information needed for the
 * proper management of cvc5 components.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__INTERRUPTED_H
#define CVC5__THEORY__INTERRUPTED_H

#include "base/exception.h"

namespace cvc5::internal {
namespace theory {

class Interrupted : public cvc5::internal::Exception
{
}; /* class Interrupted */

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__INTERRUPTED_H */
