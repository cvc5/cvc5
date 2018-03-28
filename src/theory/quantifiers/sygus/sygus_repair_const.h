/*********************                                                        */
/*! \file sygus_repair_const.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_repair_const
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
class CegConjecture;

/** SygusRepairConst
 * 
 * This module is used to repair portions of candidate solutions. In particular,
 * given a synthesis conjecture:
 *   exists f. forall x. P( f, x )
 * and a candidate solution f = \x. t[x,c] where c are constants, this function
 * checks whether there exists a term of the form \x. t[x,c'] for some constants
 * c' such that:
 *   forall x. P( (\x. t[x,c']), x ) 
 * holds, where notice that the above formula after beta-reduction may be one
 * in pure first-order logic in a decidable theory (say linear arithmetic).
 * To check this, we invoke a separate instance of the SmtEngine within
 * repairSolution(...) below.
 */
class SygusRepairConst 
{
public:
  SygusRepairConst(QuantifiersEngine * qe, CegConjecture* p);
  ~SygusRepairConst(){}
  /** repair solution 
   * 
   * If this function returns non-null sol', then sol' is obtained by replacing
   * constants in sol with other constants, and sol' is a solution for the
   * parent synthesis conjecture associated with this class.
   */
  Node repairSolution( Node sol );
private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** the synthesis conjecture that this class is associated with */
  CegConjecture* d_parent;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H */
