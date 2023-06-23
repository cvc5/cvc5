/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers registry.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REGISTRY_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REGISTRY_H

#include "expr/node.h"
#include "theory/quantifiers/quant_bound_inference.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_preprocess.h"

namespace cvc5::internal {
namespace theory {

class QuantifiersModule;

namespace quantifiers {

class Instantiate;

/**
 * The quantifiers registry, which manages basic information about which
 * quantifiers modules have ownership of quantified formulas, and manages
 * the allocation of instantiation constants per quantified formula.
 */
class QuantifiersRegistry : public QuantifiersUtil
{
  friend class Instantiate;

 public:
  QuantifiersRegistry(Env& env);
  ~QuantifiersRegistry() {}
  /**
   * Register quantifier, which allocates the instantiation constants for q.
   */
  void registerQuantifier(Node q) override;
  /** reset */
  bool reset(Theory::Effort e) override;
  /** identify */
  std::string identify() const override;
  //----------------------------- ownership
  /** get the owner of quantified formula q */
  QuantifiersModule* getOwner(Node q) const;
  /**
   * Set owner of quantified formula q to module m with given priority. If
   * the quantified formula has previously been assigned an owner with
   * lower priority, that owner is overwritten.
   */
  void setOwner(Node q, QuantifiersModule* m, int32_t priority = 0);
  /**
   * Return true if module q has no owner registered or if its registered owner is m.
   */
  bool hasOwnership(Node q, QuantifiersModule* m) const;
  //----------------------------- end ownership
  //----------------------------- instantiation constants
  /** get the i^th instantiation constant of q */
  Node getInstantiationConstant(Node q, size_t i) const;
  /** get number of instantiation constants for q */
  size_t getNumInstantiationConstants(Node q) const;
  /** get the ce body q[e/x] */
  Node getInstConstantBody(Node q);
  /** returns node n with bound vars of q replaced by instantiation constants of
     q node n : is the future pattern node q : is the quantifier containing
     which bind the variable return a pattern where the variable are replaced by
     variable for instantiation.
   */
  Node substituteBoundVariablesToInstConstants(Node n, Node q);
  /** substitute { instantiation constants of q -> bound variables of q } in n
   */
  Node substituteInstConstantsToBoundVariables(Node n, Node q);
  /** substitute { variables of q -> terms } in n */
  Node substituteBoundVariables(Node n, Node q, const std::vector<Node>& terms);
  /** substitute { instantiation constants of q -> terms } in n */
  Node substituteInstConstants(Node n, Node q, const std::vector<Node>& terms);
  //----------------------------- end instantiation constants
  /** Get quantifiers attributes utility class */
  QuantAttributes& getQuantAttributes();
  /** Get quantifiers bound inference utility */
  QuantifiersBoundInference& getQuantifiersBoundInference();
  /** Get the preprocess utility */
  QuantifiersPreprocess& getPreprocess();
  /**
   * Get quantifiers name, which returns a variable corresponding to the name of
   * quantified formula q if q has a name, or otherwise returns q itself.
   */
  Node getNameForQuant(Node q) const;
  /**
   * Get name for quantified formula. Returns true if q has a name or if req
   * is false. Sets name to the result of the above method.
   */
  bool getNameForQuant(Node q, Node& name, bool req = true) const;

 private:
  /**
   * Maps quantified formulas to the module that owns them, if any module has
   * specifically taken ownership of it.
   */
  std::map<Node, QuantifiersModule*> d_owner;
  /**
   * The priority value associated with the ownership of quantified formulas
   * in the domain of the above map, where higher values take higher
   * precendence.
   */
  std::map<Node, int32_t> d_owner_priority;
  /** map from universal quantifiers to the list of variables */
  std::map<Node, std::vector<Node> > d_vars;
  /** map from universal quantifiers to their inst constant body */
  std::map<Node, Node> d_inst_const_body;
  /** instantiation constants to universal quantifiers */
  std::map<Node, Node> d_inst_constants_map;
  /** map from universal quantifiers to the list of instantiation constants */
  std::map<Node, std::vector<Node> > d_inst_constants;
  /** The quantifiers attributes class */
  QuantAttributes d_quantAttr;
  /** The quantifiers bound inference class */
  QuantifiersBoundInference d_quantBoundInf;
  /** The quantifiers preprocessor utility */
  QuantifiersPreprocess d_quantPreproc;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REGISTRY_H */
