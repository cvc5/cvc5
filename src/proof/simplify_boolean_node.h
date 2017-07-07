/*********************                                                        */
/*! \file simplify_boolean_node.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simplifying a boolean node, needed for constructing LFSC proofs.
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SIMPLIFY_BOOLEAN_NODE_H
#define __CVC4__SIMPLIFY_BOOLEAN_NODE_H

namespace CVC4 {

Node simplifyBooleanNode(const Node &n);

}/* CVC4 namespace */

#endif /* __CVC4__SIMPLIFY_BOOLEAN_NODE_H */
