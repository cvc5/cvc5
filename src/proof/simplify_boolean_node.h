/*********************                                                        */
/*! \file simplify_boolean_node.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simplifying a boolean node, needed for constructing LFSC proofs.
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__SIMPLIFY_BOOLEAN_NODE_H
#define CVC4__SIMPLIFY_BOOLEAN_NODE_H

namespace CVC4 {

Node simplifyBooleanNode(const Node &n);

}/* CVC4 namespace */

#endif /* CVC4__SIMPLIFY_BOOLEAN_NODE_H */
