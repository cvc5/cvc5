/*********************                                                        */
/*! \file idl_assertion_db.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/idl/idl_assertion_db.h"

using namespace CVC4;
using namespace theory;
using namespace idl;

IDLAssertionDB::IDLAssertionDB(context::Context* c)
: d_assertions(c)
, d_variableLists(c)
{}

void IDLAssertionDB::add(const IDLAssertion& assertion, TNode var) {
  // Is there a list for the variable already?
  unsigned previous = -1;
  var_to_unsigned_map::iterator find = d_variableLists.find(var);
  if (find != d_variableLists.end()) {
    previous = (*find).second;
  }
  // Add to the DB
  d_variableLists[var] = d_assertions.size();
  d_assertions.push_back(IDLAssertionListElement(assertion, previous));
}

IDLAssertionDB::iterator::iterator(IDLAssertionDB& db, TNode var)
: d_db(db)
, d_current(-1)
{
  var_to_unsigned_map::const_iterator find = d_db.d_variableLists.find(var);
  if (find != d_db.d_variableLists.end()) {
    d_current = (*find).second;
  }
}

void IDLAssertionDB::iterator::next() {
  if (d_current != (unsigned)(-1)) {
    d_current = d_db.d_assertions[d_current].d_previous;
  }
}

IDLAssertion IDLAssertionDB::iterator::get() const {
  return d_db.d_assertions[d_current].d_assertion;
}
