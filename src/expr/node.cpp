/*********************                                                        */
/** node.cpp
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
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "expr/node.h"
#include "util/output.h"

#include <iostream>

using namespace std;

namespace CVC4 {
namespace expr {

const int NodeSetDepth::s_iosIndex = std::ios_base::xalloc();

}/* CVC4::expr namespace */
}/* CVC4 namespace */
