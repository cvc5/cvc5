/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
 * This is used when printing RARE rules in Eunoia. For example, the RARE rule:
 *
 * (define-rule bool-or-false ((xs Bool :list) (ys Bool :list))
 *    (or xs false ys)
 *    (or xs ys))
 *
 * becomes the Eunoia rule:
 *
 * (declare-rule bool-or-false ((xs Bool :list) (ys Bool :list))
 *   :args (xs ys)
 *   :conclusion (= (or xs false ys)) ($singleton_elim (or xs ys)))
 * )
 *
 * Where note that $singleton_elim is defined in our CPC Eunoia signature:
 *
 * (program $singleton_elim
 *   ((T Type) (S Type) (U Type) (f (-> T U S)) (x S) (x1 T) (x2 T :list))
 *   (S) S
 *   (
 *     (($singleton_elim (f x1 x2))
 *        (eo::ite (eo::is_eq x2 (eo::nil f x1 x2)) x1 (f x1 x2)))
 *     (($singleton_elim x)
 *        x)
 *   )
 * )
 *
 * In the above rule, notice that $singleton_elim is applied to (or xs ys).
 * The reason is that (or xs ys) *may* become a singleton list when xs and ys
 * are instantiated. Say xs -> [A] and ys -> []. In RARE, the conclusion is
 *   (= (or A false) A)
 * In Eunoia, the conclusion is:
 *   (= (or A false) (or A))
 *
 * The above transformation takes into account the difference in semantics.
 * More generally, we apply $singleton_elim to any subterm of the input
 * term that has fewer than 2 children that are not marked with :list.
 *
 * We additionally convert terms that represent empty sets and sequences
 * in their internal cvc5+RARE representation. In particular,
 *   (@set.empty_of_type (@type_of x1)) becomes (set.empty T1).
 *   (@seq.empty_of_type (@type_of x1)) becomes (seq.empty T1).
 * where T1 is the type of x1, which was assigned by the dependent type
 * converter (alf_dependent_type_converter.h). We take this mapping as
 * an input to this class.
 */
class AlfListNodeConverter : public NodeConverter
{
 public:
  /**
   * @param nm The node manager
   * @param tproc The node converter, for converting terms to their final
   * form to be printed
   * @param adtcMap Mapping from variables to symbols whose names are the
   * types of the variables assigned to them. For example, a variable of type
   * ?Set may be mapped to `(Set T1)` where `T1` is a sort name allocated by
   * the dependent type converter (alf_dependent_type_converter.h).
   * @param useSingletonElim Whether we are introducing $singleton_elim to
   * terms.
   */
  AlfListNodeConverter(NodeManager* nm,
                       BaseAlfNodeConverter& tproc,
                       const std::map<Node, Node>& adtcMap,
                       bool useSingletonElim = true);
  /** Convert node n based on the conversion described above. */
  Node preConvert(Node n) override;
  /** Convert node n based on the conversion described above. */
  Node postConvert(Node n) override;

 private:
  /** The parent converter, used for getting internal symbols and utilities */
  BaseAlfNodeConverter& d_tproc;
  /** Are we introducing $singleton_elim? */
  bool d_useSingletonElim;
  /** Mapping symbols to a node whose name is the type associated to that symbol
   */
  const std::map<Node, Node>& d_adtcMap;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
