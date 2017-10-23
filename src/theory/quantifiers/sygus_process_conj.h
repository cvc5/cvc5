/*********************                                                        */
/*! \file sygus_process_conj.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Techniqures for static preprocessing and analysis of
 ** sygus conjectures.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_PPROCESS_CONJ_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_PROCESSS_CONJ_H

#include "expr/node.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** ceg conjecture process
*
* This class implements static techniques for preprocessing and analysis of
* sygus conjectures.
*/
class CegConjectureProcess {
public:
  CegConjectureProcess( QuantifiersEngine * qe );
  ~CegConjectureProcess();
  /** get original version of conjecture */
  Node getConjecture() { return d_quant; }
  /** process the conjecture q */
  void process( Node q );
  /** print out debug information about this conjecture */
  void debugPrint( const char * c );
private:
  /** reference to quantifier engine */
  QuantifiersEngine * d_qe;
  /** quantified formula asserted */
  Node d_quant;
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
