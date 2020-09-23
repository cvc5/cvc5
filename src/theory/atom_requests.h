/*********************                                                        */
/*! \file atom_requests.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "theory/theory.h"
#include "context/cdlist.h"
#include "context/cdhashset.h"
#include "context/cdhashmap.h"

namespace CVC4 {

class AtomRequests {

public:

  /** Which atom and where to send it */
  struct Request {
    /** Atom */
    Node d_atom;
    /** Where to send it */
    theory::TheoryId d_toTheory;

    Request(TNode a, theory::TheoryId tt) : d_atom(a), d_toTheory(tt) {}
    Request() : d_toTheory(theory::THEORY_LAST) {}

    bool operator == (const Request& other) const {
      return d_atom == other.d_atom && d_toTheory == other.d_toTheory;
    }

    size_t hash() const { return d_atom.getId(); }
  };

  AtomRequests(context::Context* context);

  /** Mark the atom to be sent to a theory, when the trigger atom gets assigned */
  void add(TNode triggerAtom, TNode atomToSend, theory::TheoryId toTheory);

  /** Returns true if the node is a trigger and has a list of atoms to send */
  bool isTrigger(TNode atom) const;

  /** Indices in lists */
  typedef size_t element_index;

  class atom_iterator {
    const AtomRequests& d_requests;
    element_index d_index;
    friend class AtomRequests;
    atom_iterator(const AtomRequests& requests, element_index start)
        : d_requests(requests), d_index(start)
    {
    }

  public:
    /** Is this iterator done  */
    bool done() const;
    /** Go to the next element */
    void next();
    /** Get the actual request */
    const Request& get() const;
  };

  atom_iterator getAtomIterator(TNode trigger) const;

private:

  struct RequestHashFunction {
    size_t operator () (const Request& r) const {
      return r.hash();
    }
  };

  /** Set of all requests so we don't add twice */
  context::CDHashSet<Request, RequestHashFunction> d_allRequests;

  static const element_index null_index = -1;

  struct Element {
    /** Current request */
    Request d_request;
    /** Previous request */
    element_index d_previous;

    Element(const Request& r, element_index p) : d_request(r), d_previous(p) {}
  };

  /** We index the requests in this vector, it's a list */
  context::CDList<Element> d_requests;

  typedef context::CDHashMap<Node, element_index, NodeHashFunction> trigger_to_list_map;

  /** Map from triggers, to the list of elements they trigger */
  trigger_to_list_map d_triggerToRequestMap;

  /** Get the list index of the trigger */
  element_index getList(TNode trigger) const;

};

}




