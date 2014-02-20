/*********************                                                        */
/*! \file theory_rewriterules.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewrite Engine classes
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H

#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "theory/valuation.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "context/context_mm.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {

class TheoryRewriteRules : public Theory {
private:

  KEEP_STATISTIC(TimerStat, d_theoryTime, "theory::rewriterules::theoryTime");
 public:
  /** Constructs a new instance of TheoryRewriteRules
      w.r.t. the provided context.*/
  TheoryRewriteRules(context::Context* c,
                     context::UserContext* u,
                     OutputChannel& out,
                     Valuation valuation,
                     const LogicInfo& logicInfo);

  /** Usual function for theories */
  void check(Theory::Effort e);
  Node explain(TNode n);
  void collectModelInfo( TheoryModel* m, bool fullModel );
  void notifyEq(TNode lhs, TNode rhs);
  std::string identify() const {
    return "THEORY_REWRITERULES";
  }

};/* class TheoryRewriteRules */

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H */
