/*********************                                                        */
/*! \file listener.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility classes for listeners and collections of listeners.
 **
 ** Utilities for the development of a Listener interface class. This class
 ** provides a single notification that must be overwritten. This file also
 ** provides a utility class for a collection of listeners and an RAII style
 ** Registration class for managing the relationship between Listeners
 ** and the collection.
 **/

#include "cvc4_public.h"

#ifndef CVC4__LISTENER_H
#define CVC4__LISTENER_H

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

  /** Creates an empty listener collection. */
  ListenerCollection();

  /**
   * Destroys an iterator collection.
   * If assertions are on, this throws an AssertionException if the collection
   * is not empty().
   */
  ~ListenerCollection();

  /**
   * This adds a listener to the current collection and returns
   * an iterator to the listener in the collection.
   * The user of the collection must call removeListener() using
   * this iterator.
   * The collection does not take over the memory for the listener.
   */
  iterator addListener(Listener* listener);

  /**
   * Remove an listener using the iterator distributed when adding the
   * listener.
   */
  void removeListener(iterator position);

  /** Calls notify() on all listeners in the collection. */
  void notify();

  /** Returns true if the collection contains no listeners. */
  bool empty() const;

  /**
   * Registration is an RAII utility function for using Listener
   * with ListenerCollection.
   *
   * On construction, the Registration takes a ListenerCollection,
   * collection,
   * and a Listener*, listener. It takes over the memory for listener. It then
   * adds listener to collection. On destruction it removes listener and calls
   * delete on listener.
   *
   * Because of this usage, a Registration must be destroyed before the
   * ListenerCollection it is attached to.
   */
  class CVC4_PUBLIC Registration {
  public:
    Registration(ListenerCollection* collection, Listener* listener);
    ~Registration();

  private:
    Listener* d_listener;
    ListenerCollection::iterator d_position;
    ListenerCollection* d_collection;
  };/* class CVC4::ListenerCollection::Registration */


  /**
   * Returns a new Registration given a Listener that is attached to this
   * ListenerCollection. Management of the memory is handed to the user of
   * this function. To remove the listener, call the destructor for the
   * Registration.
   */
  Registration* registerListener(Listener* listener);

private:

  /**
   * Disabling the copy-constructor.
   * The user of the class must be know to remove listeners on the collection.
   * Allowing copies will only cause confusion.
   */
  ListenerCollection(const ListenerCollection& copy) = delete;

  /**
   * Disabling the assignment operator.
   * The user of the class must be know to remove listeners on the collection.
   * Allowing copies will only cause confusion.
   */
  ListenerCollection& operator=(const ListenerCollection& copy) = delete;

  /** A list of the listeners in the collection.*/
  ListenerList d_listeners;
};/* class CVC4::ListenerCollection */

/**
 * A list of ListenerCollection::Registration* pointers.
 *
 * This list assumes it has control over all of the memory of the registrations.
 */
class ListenerRegistrationList {
 public:
  ListenerRegistrationList();
  ~ListenerRegistrationList();

  void add(ListenerCollection::Registration* registration);
  void clear();

 private:
  /** Disallow copying.*/
  ListenerRegistrationList(const ListenerRegistrationList&) = delete;
  /** Disallow assignment.*/
  ListenerRegistrationList operator=(const ListenerRegistrationList&) = delete;
  std::list<ListenerCollection::Registration*> d_registrations;
};/* class CVC4::ListenerRegistrationList */

}/* CVC4 namespace */

#endif /* CVC4__LISTENER_H */
