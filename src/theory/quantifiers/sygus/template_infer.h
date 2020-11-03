/*********************                                                        */
/*! \file tempate_infer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for inferring templates for invariant problems
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__TEMPLATE_INFER_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__TEMPLATE_INFER_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/sygus/transition_inference.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TemplateInfer
{
 public:
  TemplateInfer() {}
  ~TemplateInfer() {}
  // get simplified conjecture
  Node getSimplifiedConjecture() { return d_simp_quant; }
  /** initialize this class for synthesis conjecture q */
  void initialize(Node q);

  Node getTransPre(Node prog) const;
  Node getTransPost(Node prog) const;
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
  /** transition inference module for each function to synthesize */
  std::map<Node, TransitionInference> d_ti;
};

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif
