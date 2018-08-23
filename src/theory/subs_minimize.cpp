/*********************                                                        */
/*! \file subs_minimize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of subs_minimize
 **/

#include "theory/subs_minimize.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
  
SubstitutionMinimize::SubstitutionMinimize() {

}

bool SubstitutionMinimize::find(Node n, Node target, const std::vector< Node >& vars, const std::vector< Node >& subs,
                                std::vector< Node >& reqVars )
{
  return false;
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
