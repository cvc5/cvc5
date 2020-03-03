/*********************                                                        */
/*! \file sygus_inst.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SyGuS instantiator class.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_INST_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_INST_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class SygusInst : public QuantifiersModule
{
 public:
  SygusInst(QuantifiersEngine* qe);
  ~SygusInst() = default;

  bool needsCheck(Theory::Effort e) override;

  QEffort needsModel(Theory::Effort e) override;

  void reset_round(Theory::Effort e) override;

  void check(Theory::Effort e, QEffort quant_e) override;

  bool checkCompleteFor(Node q) override;

  void preRegisterQuantifier(Node q) override;

  std::string identify() const override { return "SygusInst"; }

 private:
  Node getCeLiteral(Node n);

  void registerCeLemma(Node q, std::vector<TypeNode>& dtypes);

  std::unordered_map<Node, Node, NodeHashFunction> d_inst_constants;
  std::unordered_map<Node, Node, NodeHashFunction> d_var_eval;
  std::unordered_map<Node, Node, NodeHashFunction> d_ce_lits;

  std::unordered_map<Node, std::unique_ptr<DecisionStrategy>, NodeHashFunction>
      d_dstrat;

  std::unordered_set<Node, NodeHashFunction> d_active_quant;
  std::unordered_set<Node, NodeHashFunction> d_inactive_quant;

  context::CDHashSet<Node, NodeHashFunction> d_lemma_cache;
  context::CDHashSet<Node, NodeHashFunction> d_ce_lemma_cache;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
