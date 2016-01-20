/*********************                                                        */
/*! \file managed_listener.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Output utility classes and functions
 **
 ** Output utility classes and functions.
 **/

#include "base/listener.h"

#include <list>

#include "base/cvc4_assert.h"

namespace CVC4 {

Listener::Listener(){}
Listener::~Listener(){}

ListenerCollection::ListenerCollection() : d_listeners() {}
ListenerCollection::~ListenerCollection() { Assert(empty()); }

ListenerCollection::iterator ListenerCollection::addListener(Listener* listener)
{
  return d_listeners.insert(d_listeners.end(), listener);
}

void ListenerCollection::removeListener(iterator position) {
  d_listeners.erase(position);
}

void ListenerCollection::notify() {
  for(iterator i = d_listeners.begin(), iend = d_listeners.end(); i != iend;
      ++i)
  {
    Listener* listener = *i;
    listener->notify();
  }
}

bool ListenerCollection::empty() const { return d_listeners.empty(); }


RegisterListener::RegisterListener(ListenerCollection* collection,
                                   Listener* listener)
    : d_listener(listener)
    , d_position()
    , d_collection(collection)
{
  d_position = d_collection->addListener(d_listener);
}

RegisterListener::~RegisterListener() {
  d_collection->removeListener(d_position);
  delete d_listener;
}

}/* CVC4 namespace */
