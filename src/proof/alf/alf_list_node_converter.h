/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ALF node conversion for list variables in DSL rules
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF__ALF_LIST_NODE_CONVERTER_H
#define CVC4__PROOF__ALF__ALF_LIST_NODE_CONVERTER_H

#include "expr/node_converter.h"
#include "proof/alf/alf_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * This node converter adds applications of "singleton elimination" to
 * accurately reflect the difference in semantics between ALF and RARE.
 *
 * This is used when printing RARE rules in ALF. For example, the RARE rule:
 *
 * (define-rule bool-or-false ((xs Bool :list) (ys Bool :list))
 *    (or xs false ys)
 *    (or xs ys))
 *
 * becomes the ALF rule:
 *
 * (declare-rule bool-or-false ((xs Bool :list) (ys Bool :list))
 *   :args (xs ys)
 *   :conclusion (= (or xs false ys)) ($singleton_elim (or xs ys)))
 * )
 *
 * Where note that $singleton_elim is defined in our ALF signature:
 *
 * (program $singleton_elim
 *   ((T Type) (S Type) (U Type) (f (-> T U S)) (x S) (x1 T) (x2 T :list))
 *   (S) S
 *   (
 *     (($singleton_elim (f x1 x2))
 *        (alf.ite (alf.is_eq x2 (alf.nil f x1 x2)) x1 (f x1 x2)))
 *     (($singleton_elim x)
 *        x)
 *   )
 * )
 *
 * In the above rule, notice that $singleton_elim is applied to (or xs ys).
 * The reason is that (or xs ys) *may* become a singleton list when xs and ys
 * are instantiated. Say xs -> [A] and ys -> []. In RARE, the conclusion is
 *   (= (or A false) A)
 * In ALF, the conclusion is:
 *   (= (or A false) (or A))
 *
 * The above transformation takes into account the difference in semantics.
 * More generally, we apply $singleton_elim to any subterm of the input
 * term that has fewer than 2 children that are not marked with :list.
 */
class AlfListNodeConverter : public NodeConverter
{
 public:
  AlfListNodeConverter(NodeManager* nm, BaseAlfNodeConverter& tproc);
  /** Convert node n based on the conversion described above. */
  Node postConvert(Node n) override;

 private:
  /** The parent converter, used for getting internal symbols and utilities */
  BaseAlfNodeConverter& d_tproc;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
