/*********************                                                        */
/*! \file sygus_qe_preproc.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus quantifier elimination preprocessor
 **/

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H

#include <string>
#include <vector>
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

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
  SygusQePreproc(QuantifiersEngine* qe);
  ~SygusQePreproc() {}
  /**
   * Preprocess. Returns a lemma of the form q = nq where nq is obtained
   * by the quantifier elimination technique outlined above.
   */
  Node preprocess(Node q);

 private:
  /** Pointer to quantifiers engine */
  QuantifiersEngine* d_quantEngine;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H */
