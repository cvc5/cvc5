/*********************                                                        */
/*! \file theory_quantifiers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of quantifiers.
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H
#define __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H

#include "context/cdhashmap.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/valuation.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TheoryQuantifiers : public Theory {
 public:
  TheoryQuantifiers(context::Context* c, context::UserContext* u,
                    OutputChannel& out, Valuation valuation,
                    const LogicInfo& logicInfo);
  ~TheoryQuantifiers();

  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;
  void addSharedTerm(TNode t) override;
  void notifyEq(TNode lhs, TNode rhs);
  void preRegisterTerm(TNode n) override;
  void presolve() override;
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;
  void check(Effort e) override;
  Node getNextDecisionRequest(unsigned& priority) override;
  Node getValue(TNode n);
  bool collectModelInfo(TheoryModel* m) override;
  void shutdown() override {}
  std::string identify() const override
  {
    return std::string("TheoryQuantifiers");
  }
  void setUserAttribute(const std::string& attr,
                        Node n,
                        std::vector<Node> node_values,
                        std::string str_value) override;
  bool ppDontRewriteSubterm(TNode atom) override
  {
    return atom.getKind() == kind::FORALL || atom.getKind() == kind::EXISTS;
  }

 private:
  void assertUniversal( Node n );
  void assertExistential( Node n );
  void computeCareGraph() override;

  using BoolMap = context::CDHashMap<Node, bool, NodeHashFunction>;

  /** number of instantiations */
  int d_numInstantiations;
  int d_baseDecLevel;

};/* class TheoryQuantifiers */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H */
