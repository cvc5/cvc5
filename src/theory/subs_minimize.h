/*********************                                                        */
/*! \file subs_minimize.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief subs_minimize
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SUBSTITUTION_MINIMIZE_H
#define __CVC4__THEORY__SUBSTITUTION_MINIMIZE_H

#include <map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {

/** SubstitutionMinimize
 * 
 */
class SubstitutionMinimize 
{
public:
  SubstitutionMinimize();
  ~SubstitutionMinimize(){}

  bool find(Node n, Node target, const std::vector< Node >& vars, const std::vector< Node >& subs,
            std::vector< Node >& reqVars );
};

} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__SUBSTITUTION_MINIMIZE_H */
