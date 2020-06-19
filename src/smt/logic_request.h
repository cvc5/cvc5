/*********************                                                        */
/*! \file logic_request.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An object to request logic widening in the running SmtEngine
 **
 ** An object to request logic widening in the running SmtEngine.  This
 ** class exists as a proxy between theory code and the SmtEngine, allowing
 ** a theory to enable another theory in the SmtEngine after initialization
 ** (thus the usual, public setLogic() cannot be used).  This is mainly to
 ** support features like uninterpreted divide-by-zero (to support the
 ** partial function DIVISION), where during theory expansion, the theory
 ** of uninterpreted functions needs to be added to the logic to support
 ** partial functions.
 **/

#include "cvc4_private.h"

#ifndef CVC4__LOGIC_REQUEST_H
#define CVC4__LOGIC_REQUEST_H

#include "expr/kind.h"

namespace CVC4 {

class SmtEngine;

class LogicRequest {
  /** The SmtEngine at play. */
  SmtEngine& d_smt;

public:
  LogicRequest(SmtEngine& smt) : d_smt(smt) { }

  /** Widen the logic to include the given theory. */
  void widenLogic(theory::TheoryId id);

  /** Enable Integers. */
  void enableIntegers();

};/* class LogicRequest */

}/* CVC4 namespace */

#endif /* CVC4__LOGIC_REQUEST_H */
