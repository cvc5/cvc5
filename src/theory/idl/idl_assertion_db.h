/*********************                                                        */
/*! \file idl_assertion_db.h
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

#pragma once

#include "theory/idl/idl_assertion.h"
#include "context/cdlist.h"

namespace CVC4 {
namespace theory {
namespace idl {

/**
 * Context-dependent database assertions, organized by variable. Each variable
 * can be associated a list of IDL assertions. The list of assertions can
 * be iterated over using the provided iterator class.
 */
class IDLAssertionDB {

  /** Elements of the assertion lists */
  struct IDLAssertionListElement {
    /** The assertion itself */
    IDLAssertion d_assertion;
    /** The index of the previous element (-1 for null) */
    unsigned d_previous;

    IDLAssertionListElement(const IDLAssertion& assertion, unsigned previous)
    : d_assertion(assertion), d_previous(previous)
    {}
  };

  /** All assertions in a context dependent stack */
  context::CDList<IDLAssertionListElement> d_assertions;

  typedef context::CDHashMap<TNode, unsigned, TNodeHashFunction> var_to_unsigned_map;

  /** Map from variables to the first element of their list */
  var_to_unsigned_map d_variableLists;

public:

  /** Create a new assertion database */
  IDLAssertionDB(context::Context* c);

  /** Add a new assertion, attach to the list of the given variable */
  void add(const IDLAssertion& assertion, TNode var);

  /** Iteration over the constraints of a variable */
  class iterator {
    /** The database */
    const IDLAssertionDB& d_db;
    /** Index of the current constraint */
    unsigned d_current;
  public:
    /** Construct the iterator for the variable */
    iterator(IDLAssertionDB& db, TNode var);
    /** Is this iterator done */
    bool done() const { return d_current == (unsigned)(-1); }
    /** Next element */
    void next();
    /** Get the assertion */
    IDLAssertion get() const;
  };
};

}
}
}




