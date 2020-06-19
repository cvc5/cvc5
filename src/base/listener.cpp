/*********************                                                        */
/*! \file listener.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Output utility classes and functions
 **
 ** Output utility classes and functions.
 **/

#include "base/listener.h"

#include <list>

#include "base/check.h"

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


ListenerCollection::Registration::Registration(
    ListenerCollection* collection, Listener* listener)
    : d_listener(listener)
    , d_position()
    , d_collection(collection)
{
  d_position = d_collection->addListener(d_listener);
}

ListenerCollection::Registration::~Registration() {
  d_collection->removeListener(d_position);
  delete d_listener;
}

 ListenerCollection::Registration* ListenerCollection::registerListener(
     Listener* listener)
{
  return new Registration(this, listener);
}


ListenerRegistrationList::ListenerRegistrationList()
    : d_registrations()
{}

ListenerRegistrationList::~ListenerRegistrationList() {
  clear();
}

void ListenerRegistrationList::add(
    ListenerCollection::Registration* registration)
{
  d_registrations.push_back(registration);
}

void ListenerRegistrationList::clear(){
  typedef std::list<ListenerCollection::Registration*>::iterator iterator;
  for(iterator i = d_registrations.begin(), iend = d_registrations.end();
      i != iend; ++i)
  {
    ListenerCollection::Registration* current = *i;
    delete current;
  }
  d_registrations.clear();
}


}/* CVC4 namespace */
