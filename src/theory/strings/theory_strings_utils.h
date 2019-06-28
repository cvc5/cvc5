/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Util functions for theory strings.
 **
 ** Util functions for theory strings.
 **/

#include "cvc4_private.h"

#pragma once

#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node_manager.h"

namespace CVC4 {
namespace theory {
namespace strings {
namespace utils {

/** 
 * Make the conjunction of nodes in a. Removes duplicate conjuncts, returns
 * true if a is empty, and a single literal if a has size 1.
 */
Node mkAnd(std::vector<Node>& a);

}
}
}
}
