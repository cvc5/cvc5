/*********************                                                        */
/*! \file theory_quantifiers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of quantifiers.
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H
#define CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H

#include "context/cdhashmap.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
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

  TheoryRewriter* getTheoryRewriter() override { return &d_rewriter; }

  /** finish initialization */
  void finishInit() override;
  void preRegisterTerm(TNode n) override;
  void presolve() override;
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;
  void check(Effort e) override;
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

 private:
  /** The theory rewriter for this theory. */
  QuantifiersRewriter d_rewriter;
};/* class TheoryQuantifiers */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H */
