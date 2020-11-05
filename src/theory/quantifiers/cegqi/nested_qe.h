/*********************                                                        */
/*! \file nested_qe.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Methods for counterexample-guided quantifier instantiation
 ** based on nested quantifier elimination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEQGI__NESTED_QE_H
#define CVC4__THEORY__QUANTIFIERS__CEQGI__NESTED_QE_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class NestedQe
{
public:
  NestedQe();
  ~NestedQe(){}
  /**
   * Register quantified formula
   *
   * Return true if q has nested quantified formulas.
   */
  bool registerQuantifiedFormula(Node q);
  /**
   * Get quantifier elimination for q.
   */
  /** Get nested quantification */
  static bool getNestedQuantification(Node q, std::vector<Node>& nqs);
  /** 
   * Does q have nested quantification?
   */
  /** 
   * Do nested quantifier elimination.
   */
  static Node doNestedQe(Node q, bool keepTopLevel=false);
private:
  /** Map from quantified formula q to its nested quantifiers */
  
  /**
   * Run quantifier free formula for quantified formula q with no nested
   * quantification.
   */
  static Node doQe(Node q);
};

}
}
}

#endif
