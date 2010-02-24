/*********************                                                        */
/** theory.cpp
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
 ** Base for theory interface.
 **/

#include "theory/theory.h"

namespace CVC4 {
namespace theory {

bool Theory::done() {
  return d_nextAssertion >= d_assertions.size(); 
}


Node Theory::get() {
  Node n = d_assertions[d_nextAssertion];
  d_nextAssertion = d_nextAssertion + 1;
  return n;
}

void Theory::assertFact(const Node& n){
  d_assertions.push_back(n);
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
