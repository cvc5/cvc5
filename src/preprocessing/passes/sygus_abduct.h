/*********************                                                        */
/*! \file sygus_abduct.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus abduction preprocessing pass, which transforms an arbitrary
 ** input into an abduction problem.
 **/

#ifndef CVC4__PREPROCESSING__PASSES__SYGUS_ABDUCT_H
#define CVC4__PREPROCESSING__PASSES__SYGUS_ABDUCT_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** SygusAbduct
 *
 * A preprocessing utility that turns a set of quantifier-free assertions into
 * a sygus conjecture that encodes an abduction problem. In detail, if our
 * input formula is F( x ) for free symbols x, then we construct the sygus
 * conjecture:
 *
 * exists A. forall x. ( A( x ) => ~F( x ) )
 *
 * where A( x ) is a predicate over the free symbols of our input. In other
 * words, A( x ) is a sufficient condition for showing ~F( x ).
 *
 * Another way to view this is A( x ) is any condition such that A( x ) ^ F( x )
 * is unsatisfiable.
 *
 * A common use case is to find the weakest such A that meets the above
 * specification. We do this by streaming solutions (sygus-stream) for A
 * while filtering stronger solutions (sygus-filter-sol=strong). These options
 * are enabled by default when this preprocessing class is used (sygus-abduct).
 *
 * If the input F( x ) is partitioned into axioms Fa and negated conjecture Fc
 * Fa( x ) ^ Fc( x ), then the sygus conjecture we construct is:
 *
 * exists A. ( exists y. A( y ) ^ Fa( y ) ) ^ forall x. ( A( x ) => ~F( x ) )
 *
 * In other words, A( y ) must be consistent with our axioms Fa and imply
 * ~F( x ). We encode this conjecture using SygusSideConditionAttribute.
 */
class SygusAbduct : public PreprocessingPass
{
 public:
  SygusAbduct(PreprocessingPassContext* preprocContext);

  /**
   * Returns the sygus conjecture corresponding to the abduction problem for
   * input problem (F above) given by asserts, and axioms (Fa above) given by
   * axioms. Note that axioms is expected to be a subset of asserts.
   *
   * The type abdGType (if non-null) is a sygus datatype type that encodes the
   * grammar that should be used for solutions of the abduction conjecture.
   */
  static Node mkAbductionConjecture(const std::vector<Node>& asserts,
                                    const std::vector<Node>& axioms,
                                    TypeNode abdGType);

 protected:
  /**
   * Replaces the set of assertions by an abduction sygus problem described
   * above.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__SYGUS_ABDUCT_H_ */
