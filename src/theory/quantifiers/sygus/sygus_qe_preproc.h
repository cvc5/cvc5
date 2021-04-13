/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus quantifier elimination preprocessor.
 */

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/**
 * This module does quantifier elimination as a preprocess step
 * for "non-ground single invocation synthesis conjectures":
 *   exists f. forall xy. P[ f(x), x, y ]
 * We run quantifier elimination:
 *   exists y. P[ z, x, y ] ----> Q[ z, x ]
 * Where we replace the original conjecture with:
 *   exists f. forall x. Q[ f(x), x ]
 * For more details, see Example 6 of Reynolds et al. SYNT 2017.
 */
class SygusQePreproc
{
 public:
  SygusQePreproc();
  ~SygusQePreproc() {}
  /**
   * Preprocess. Returns a lemma of the form q = nq where nq is obtained
   * by the quantifier elimination technique outlined above.
   */
  Node preprocess(Node q);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H */
