/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for inferring templates for invariant problems.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__TEMPLATE_INFER_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__TEMPLATE_INFER_H

#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/transition_inference.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * This class infers templates for an invariant-to-synthesize based on the
 * template mode. It uses the transition inference to choose a template.
 */
class SygusTemplateInfer : protected EnvObj
{
 public:
  SygusTemplateInfer(Env& env);
  ~SygusTemplateInfer() {}
  /**
   * Initialize this class for synthesis conjecture q. If applicable, the
   * templates for functions-to-synthesize for q are accessible by the
   * calls below afterwards.
   */
  void initialize(Node q);
  /**
   * Get template for program prog. This returns a term of the form t[x] where
   * x is the template argument (see below)
   */
  Node getTemplate(Node prog) const;
  /**
   * Get the template argument for program prog. This is a variable which
   * indicates the position of the function/predicate to synthesize.
   */
  Node getTemplateArg(Node prog) const;

 private:
  /** The quantified formula we initialized with */
  Node d_quant;
  /** transition relation pre and post version per function to synthesize  */
  std::map<Node, Node> d_trans_pre;
  std::map<Node, Node> d_trans_post;
  /** the template for each function to synthesize */
  std::map<Node, Node> d_templ;
  /**
   * The template argument for each function to synthesize (occurs in exactly
   * one position of its template)
   */
  std::map<Node, Node> d_templ_arg;
  /** transition inference module */
  TransitionInference d_ti;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
