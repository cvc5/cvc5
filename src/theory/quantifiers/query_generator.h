/*********************                                                        */
/*! \file query_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief query_generator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS___H
#define __CVC4__THEORY__QUANTIFIERS___H

#include <map>

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** QueryGenerator
 * 
 */
class QueryGenerator 
{
public:
  QueryGenerator( QuantifiersEngine * qe );
  ~QueryGenerator(){}
private:
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS___H */
