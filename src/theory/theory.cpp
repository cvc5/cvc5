/*********************                                                        */
/*! \file theory.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base for theory interface.
 **
 ** Base for theory interface.
 **/

#include "theory/theory.h"
#include "util/Assert.h"

#include <vector>

using namespace std;

namespace CVC4 {
namespace theory {

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::MIN_EFFORT:
    os << "MIN_EFFORT"; break;
  case Theory::QUICK_CHECK:
    os << "QUICK_CHECK"; break;
  case Theory::STANDARD:
    os << "STANDARD"; break;
  case Theory::FULL_EFFORT:
    os << "FULL_EFFORT"; break;
  default:
      Unreachable();
  }
  return os;
}/* ostream& operator<<(ostream&, Theory::Effort) */

}/* CVC4::theory namespace */
}/* CVC4 namespace */
