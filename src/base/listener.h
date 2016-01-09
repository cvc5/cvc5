/*********************                                                        */
/*! \file listener.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Utility classes for listeners and collections of listeners.
 **
 ** Utilities for the development of a Listener interface class. This class
 ** provides a single notification that must be overwritten. This file also
 ** provides a utility class for a collection of listeners and an RAII style
 ** RegisterListener class for managing the relationship between Listeners
 ** and the manager.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LISTENER_H
#define __CVC4__LISTENER_H

#include <list>

namespace CVC4 {

/**
 * Listener interface class.
 *
 * The interface provides a notify() function.
 */
class CVC4_PUBLIC Listener {
public:
  Listener();
  virtual ~Listener();

  /** Note that notify may throw arbitrary exceptions. */
  virtual void notify() = 0;
};

/**
 * ListenerCollection is a list of Listener instances.
 * One can add and remove Listeners.
 *
 * ListenerCollection does not own the memory of the Listeners.
 * As a sanity check, it asserted that all of its listeners
 * have been removed.
 */
class CVC4_PUBLIC ListenerCollection {
public:
  typedef std::list<Listener*> ListenerList;
  typedef ListenerList::iterator iterator;

  ListenerCollection();

  ~ListenerCollection();

  iterator addListener(Listener* listener);

  void removeListener(iterator position);

  void notify();

  bool empty() const;

private:
  ListenerList d_listeners;
};

/**
 * RegisterListener is an RAII utility function for using Listener
 * with ListenerCollection.
 *
 * On construction, the RegisterListener takes a ListenerCollection, collection,
 * and a Listener*, listener. It takes over the memory for listener. It then
 * add listener to collection. On destruction it removes listener and calls
 * delete on listener.
 *
 * Because of this usage, a RegisterListener must be destroyed before
 * collection.
 */
class CVC4_PUBLIC RegisterListener {
public:
  RegisterListener(ListenerCollection* collection, Listener* listener);
  ~RegisterListener();

private:
  Listener* d_listener;
  ListenerCollection::iterator d_position;
  ListenerCollection* d_collection;
};


}/* CVC4 namespace */

#endif /* __CVC4__LISTENER_H */
