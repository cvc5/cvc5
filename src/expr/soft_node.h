/*********************                                                        */
/** soft_node.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Encapsulation of a pointer to node information that is explicitly
 ** NOT reference-counted.  These "smart pointers" do NOT keep live
 ** the NodeValue object to which they refer.
 **/

#ifndef __CVC4__SOFT_NODE_H
#define __CVC4__SOFT_NODE_H

#include "expr/node.h"

namespace CVC4 {
namespace expr {

/**
 * For now, treat SoftNodes as regular Nodes.  We'll address this
 * later.
 */
typedef CVC4::Node SoftNode;
typedef CVC4::Node TNode;

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SOFT_NODE_H */
