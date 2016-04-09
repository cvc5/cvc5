/*********************                                                        */
/*! \file theory_fp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_H
#define __CVC4__THEORY__FP__THEORY_FP_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace fp {

class TheoryFp : public Theory {
public:

  /** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
  TheoryFp(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo);

  Node expandDefinition(LogicRequest &, Node node);

  void check(Effort);

  std::string identify() const {
    return "THEORY_FP";
  }

};/* class TheoryFp */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
