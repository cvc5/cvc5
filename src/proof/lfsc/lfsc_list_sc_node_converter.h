/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of LFSC node conversion for list variables in side conditions
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_LIST_SC_NODE_CONVERTER_H
#define CVC4__PROOF__LFSC__LFSC_LIST_SC_NODE_CONVERTER_H

#include "expr/node_converter.h"
#include "proof/lfsc/lfsc_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * Convert list variables in side conditions. This class converts nodes
 * representing LFSC side condition programs to a form that prints properly
 * in LFSC. In particular, this node converter gives consideration to
 * input variables that are "list" variables in the rewrite DSL.
 *
 * For example, for DSL rule:
 *   (define-rule bool-and-flatten
 *      ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
 *      (and xs (and b ys) zs) (and xs zs b ys))
 * This is a helper class used to compute the conclusion of this rule. This
 * class is used to turn
 *   (= (and xs (and b ys) zs) (and xs zs b ys))
 * into:
 *   (=
 *      (nary_concat
 *        f_and
 *        xs
 *        (and (and b ys) zs)
 *        true)
 *      (nary_elim
 *        f_and
 *        (nary_concat f_and xs (nary_concat f_and zs (and b ys) true) true)
 *        true)))
 * Where notice that the list variables xs, ys, zs are treated as lists to
 * concatenate instead of being subterms, according to the semantics of list
 * variables in the rewrite DSL. For exact definitions of nary_elim,
 * nary_concat, see the LFSC signature nary_programs.plf.
 *
 * This runs in two modes.
 * - If isPre is true, then the input is in its original form, and we add
 * applications of nary_elim.
 * - If isPre is false, then the input is in converted form, and we add
 * applications of nary_concat.
 */
class LfscListScNodeConverter : public NodeConverter
{
 public:
  LfscListScNodeConverter(LfscNodeConverter& conv,
                          const std::unordered_set<Node>& listVars,
                          bool isPre = false);
  /** convert to internal */
  Node postConvert(Node n) override;

 private:
  /** Make application for */
  Node mkOperatorFor(const std::string& name,
                     const std::vector<Node>& children,
                     TypeNode retType);
  /** The parent converter, used for getting internal symbols and utilities */
  LfscNodeConverter& d_conv;
  /** Variables we are treating as list variables */
  std::unordered_set<Node> d_listVars;
  /** In pre or post */
  bool d_isPre;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
