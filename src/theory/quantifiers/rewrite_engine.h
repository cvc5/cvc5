/*********************                                                        */
/*! \file rewrite_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "cvc4_private.h"

#ifndef CVC4__REWRITE_ENGINE_H
#define CVC4__REWRITE_ENGINE_H

#include <map>
#include <vector>

#include "expr/attribute.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {

/**
 * An attribute for marking a priority value for rewrite rules.
 */
struct RrPriorityAttributeId
{
};
typedef expr::Attribute<RrPriorityAttributeId, uint64_t> RrPriorityAttribute;

namespace quantifiers {

class RewriteEngine : public QuantifiersModule
{
  std::vector< Node > d_rr_quant;
  std::vector< Node > d_priority_order;
  std::map< Node, Node > d_rr;
  /** explicitly provided patterns */
  std::map< Node, std::vector< inst::Trigger* > > d_rr_triggers;
  /** get the quantifer info object */
  std::map< Node, Node > d_qinfo_n;
  std::map< Node, QuantInfo > d_qinfo;
  double getPriority( Node f );
  bool d_needsSort;
  std::map< Node, std::map< Node, Node > > d_inst_const_node;
  Node getInstConstNode( Node n, Node q );

 private:
  int checkRewriteRule( Node f, Theory::Effort e );

 public:
  RewriteEngine(context::Context* c,
                QuantifiersEngine* qe,
                QuantConflictFind* qcf);

  bool needsCheck(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  void registerQuantifier(Node f) override;
  void assertNode(Node n) override;
  bool checkCompleteFor(Node q) override;
  /** Identify this module */
  std::string identify() const override { return "RewriteEngine"; }

 private:
  /**
   * A pointer to the quantifiers conflict find module of the quantifiers
   * engine. This is the module that computes instantiations for rewrite rule
   * quantifiers.
   */
  QuantConflictFind* d_qcf;
};

}
}
}

#endif
