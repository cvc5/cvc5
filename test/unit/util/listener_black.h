/*********************                                                        */
/*! \file listener_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4 output classes.
 **
 ** Black box testing of CVC4 output classes.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "base/listener.h"

using namespace CVC4;
using namespace std;

class ListenerBlack : public CxxTest::TestSuite {

  std::multiset<std::string> d_events;

  class EventListener : public Listener {
   public:
    EventListener(std::multiset<std::string>& events, std::string name)
        : d_events(events), d_name(name) {}
    ~EventListener(){}

    virtual void notify() { d_events.insert(d_name); }

   private:
    std::multiset<std::string>& d_events;
    std::string d_name;
  };

public:

  static std::multiset<std::string> mkMultiset(std::string arr[], int len){
    return std::multiset<std::string>(arr, arr + len);
  }

  void setUp() {
    d_events.clear();
  }

  void tearDown() {
    d_events.clear();
  }

  void testEmptyCollection() {
    // Makes an new collection and tests that it is empty.
    ListenerCollection* collection = new ListenerCollection;
    TS_ASSERT(collection->empty());
    TS_ASSERT_THROWS_NOTHING( delete collection );
  }

  void testSingletonCollection() {
    ListenerCollection collection;
    std::string expected[1] = {"a"};
    {
      ListenerCollection::Registration a(&collection, new EventListener(d_events, "a"));
      collection.notify();
      TS_ASSERT(not collection.empty());
    }
    TS_ASSERT(collection.empty());
    TS_ASSERT_EQUALS(d_events, mkMultiset(expected, 1));
  }

  void testSingleRegisterTearDown() {
    // Tests that collection succeeds at destruction after
    // registering a single event.
    ListenerCollection* collection = new ListenerCollection;
    {
      ListenerCollection::Registration a(collection, new EventListener(d_events, "a"));
      TS_ASSERT(not collection->empty());
      // The destructor for a now runs.
    }
    TS_ASSERT(collection->empty());
    TS_ASSERT_THROWS_NOTHING( delete collection );
  }

  void testMultipleCollection() {
    ListenerCollection* collection = new ListenerCollection;
    {
      ListenerCollection::Registration c(collection, new EventListener(d_events, "c"));
      collection->notify();
      // d_events == {"c"}
      ListenerCollection::Registration b(collection, new EventListener(d_events, "b"));
      ListenerCollection::Registration a(collection, new EventListener(d_events, "a"));
      collection->notify();
      // d_events == {"a", "b", "c", "c"}
      TS_ASSERT(not collection->empty());
    }
    TS_ASSERT(collection->empty());
    std::string expected[4] = {"a", "b", "c", "c"};
    TS_ASSERT_EQUALS(d_events, mkMultiset(expected, 4));
    TS_ASSERT_THROWS_NOTHING( delete collection );
  }

  void testRegisterMiddleTearDown() {
    // Tests that collection succeeds at destruction after
    // registering several events.
    ListenerCollection* collection = new ListenerCollection;
    {
      ListenerCollection::Registration a(collection, new EventListener(d_events, "a"));
      ListenerCollection::Registration* b =
          new ListenerCollection::Registration(collection, new EventListener(d_events, "b"));
      ListenerCollection::Registration c(collection, new EventListener(d_events, "c"));

      collection->notify();
      delete b;
      collection->notify();
      // The destructor for a and c now run.
      TS_ASSERT(not collection->empty());
    }
    TS_ASSERT(collection->empty());
    TS_ASSERT_THROWS_NOTHING( delete collection );
  }



  void testRegisterMultiple() {
    // This tests adds and notify multiple times.
    ListenerCollection collection;

    std::vector<ListenerCollection::Registration*> listeners;
    for(int i = 0; i < 4 ; ++i){
      stringstream ss; ss << i;
      Listener* listener = new EventListener(d_events, ss.str());
      listeners.push_back(new ListenerCollection::Registration(&collection, listener));
      collection.notify();
    }

    TS_ASSERT(not collection.empty());
    for(unsigned i=0; i < listeners.size(); ++i){
      ListenerCollection::Registration* at_i = listeners[i];
      delete at_i;
    }
    listeners.clear();
    TS_ASSERT(collection.empty());

    std::string expected[10] =
        {"0", "0", "0", "0", "1", "1", "1", "2", "2", "3"};
    TS_ASSERT_EQUALS(d_events, mkMultiset(expected, 10));

    // No more events occur.
    collection.notify();
    TS_ASSERT_EQUALS(d_events, mkMultiset(expected, 10));
  }

};
