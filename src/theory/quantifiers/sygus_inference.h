/*********************                                                        */
/*! \file sygus_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_inference
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_INFERENCE_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_INFERENCE_H

#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusInference
 *
 * A preprocessing utility that turns a set of (quantified) assertions into a
 * single SyGuS conjecture. If this is possible, we solve for this single Sygus
 * conjecture using a separate copy of the SMT engine. If sygus successfully
 * solves the conjecture, we plug the synthesis solutions back into the original
 * problem, thus obtaining a set of model substitutions under which the
 * assertions should simplify to true.
 */
class SygusInference
{
 public:
  SygusInference();
  ~SygusInference() {}
  /** simplify assertions
   *
   * Either replaces all uninterpreted functions in assertions by their
   * interpretation in the solution found by a separate call to an SMT engine
   * and returns true, or leaves the assertions unmodified and returns false.
   *
   * We fail if either a sygus conjecture that corresponds to assertions cannot
   * be inferred, or the sygus conjecture we infer is infeasible.
   */
  bool simplify(std::vector<Node>& assertions);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_INFERENCE_H */
