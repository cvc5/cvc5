/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The SetsToBags preprocessing pass.
 *
 * Converts set terms into bag terms.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__SETS_TO_BAGS_H
#define CVC5__PREPROCESSING__PASSES__SETS_TO_BAGS_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"
#include "options/sets_options.h"
#include "preprocessing/preprocessing_pass.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Converts set terms into bag terms. The set type (Set T) is converted to the
 * bag type (Bag T'), where T' is the conversion of T. Set operators are
 * converted as follows, where x' and A' are the conversions of x and A:
 *
 *   set.empty            ---> bag.empty
 *   (set.singleton x)    ---> (bag x' 1)
 *   (set.insert x A)     ---> (bag.setof (bag.union_max (bag x' 1) A'))
 *   (set.union A B)      ---> (bag.setof (bag.union_max A' B'))
 *   (set.inter A B)      ---> (bag.inter_min A' B')
 *   (set.minus A B)      ---> (bag.difference_subtract A' B')
 *   (set.subset A B)     ---> (bag.subbag A' B')
 *   (set.member x A)     ---> (bag.member x' A')
 *   (set.card A)         ---> (bag.card A')
 *   (set.is_empty A)     ---> (= A' bag.empty)
 *   (set.is_singleton A) ---> (= A' (bag (bag.choose A') 1))
 *   (set.choose A)       ---> (bag.choose A')
 *   (set.map f A)        ---> (bag.map f' A')
 *   (set.filter p A)     ---> (bag.filter p' A')
 *   (set.all p A)        ---> (bag.all p' A')
 *   (set.some p A)       ---> (bag.some p' A')
 *   (set.fold f t A)     ---> (bag.fold f' t' A')
 *   set.universe         ---> U
 *   (set.complement A)   ---> (bag.difference_subtract U A')
 *
 * where U is a fresh bag constant named bag.universe. The SetsToBags pass
 * ensures that every other bag term of the same type is a subbag of U.
 *
 * A set union always takes the bag.setof of a bag union. Otherwise, the
 * conversion depends on the mode:
 * - SETOF: every converted set term t is wrapped as (bag.setof t), which
 *   preserves the semantics of sets.
 * - RELAXED: bag.setof is not added, which relaxes the semantics of sets to
 *   the semantics of bags. The answers are for the resulting bag problem.
 */
class SetsToBagsConverter : protected EnvObj, public NodeConverter
{
 public:
  SetsToBagsConverter(Env& env, options::SetsToBagsMode mode);
  /** Get the universe bags constructed so far, indexed by their bag type */
  const std::map<TypeNode, Node>& getUniverses() const;

 protected:
  /** Throws a logic exception for datatypes whose fields have set types */
  TypeNode preConvertType(TypeNode tn) override;
  /** Converts (Set T) to (Bag T) */
  TypeNode postConvertType(TypeNode tn) override;
  /** Converts orig, whose converted children are terms, to a bag term */
  Node postConvertUntyped(Node orig,
                          const std::vector<Node>& terms,
                          bool termsChanged) override;

 private:
  /** Converts orig, an application of a set operator, to a bag term */
  Node convertSetOperator(Node orig, const std::vector<Node>& terms);
  /** Get the universe bag of type bagType */
  Node getUniverse(TypeNode bagType);
  /** Returns (bag.setof b) in mode SETOF if b is not trivially a set */
  Node mkSetof(Node b);
  /** Returns (bag.setof (bag.union_max a b)) */
  Node mkUnion(Node a, Node b);
  /** Throws a logic exception if extended set operators are not enabled */
  void checkSetsExp() const;
  /** The conversion mode */
  options::SetsToBagsMode d_mode;
  /** Map from bag types to their universe bag */
  std::map<TypeNode, Node> d_universes;
};

/**
 * The preprocessing pass that converts set terms into bag terms using the
 * converter above. If a universe bag U was introduced for bag type (Bag T),
 * each assertion is conjoined with (bag.subbag b U) for each bag term b of
 * type (Bag T) in it that does not occur below a binder.
 *
 * Since the rewriter eliminates set operators, e.g. set.subset, this pass
 * runs before the input is rewritten.
 *
 * Since there is no conversion from the model values of bags to sets, this
 * pass is incompatible with model generation. In mode SETOF, the assertions
 * are marked as model unsound if a universe bag was introduced, since a model
 * of the bags may not correspond to a model of the sets then. In mode RELAXED,
 * the answers are for the bag problem. In both modes, the converted
 * assertions are satisfiable if the original ones are, hence "unsat" answers
 * are preserved for the sets.
 */
class SetsToBags : public PreprocessingPass
{
 public:
  SetsToBags(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /**
   * Add to conj the constraints (bag.subbag b U) for each bag term b in n
   * that does not occur below a binder, where U is the universe bag of the
   * type of b.
   */
  void addUniverseConstraints(Node n, std::vector<Node>& conj) const;
  /** The converter */
  SetsToBagsConverter d_converter;
  /**
   * Whether a model of the converted assertions may not correspond to a model
   * of the original ones, in which case this and all future calls mark the
   * assertions as model unsound.
   */
  bool d_modelUnsound;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__SETS_TO_BAGS_H */
