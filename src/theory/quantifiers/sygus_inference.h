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
 * A preprocessing utility to turn a set of (quantified) assertions into a 
 * single SyGuS conjecture.
 */
class SygusInference 
{
public:
  SygusInference();
  ~SygusInference(){}
  /** simplify assertions
   *
   * Either replaces assertions with an equivalent SyGus conjecture and returns
   * true (if possible), or otherwise returns false.
   */
  bool simplify(std::vector<Node>& assertions);
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_INFERENCE_H */
