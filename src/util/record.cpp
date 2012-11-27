/*********************                                                        */
/*! \file record.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A class representing a record definition
 **
 ** A class representing a record definition.
 **/

#include "util/record.h"

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& os, const Record& r) {
  os << "[# ";
  bool first = true;
  for(Record::iterator i = r.begin(); i != r.end(); ++i) {
    if(!first) {
      os << ", ";
    }
    os << (*i).first << ":" << (*i).second;
    first = false;
  }
  os << " #]";

  return os;
}

}/* CVC4 namespace */
