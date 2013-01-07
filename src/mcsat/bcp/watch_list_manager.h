#pragma once

#include <vector>

#include "mcsat/clause/literal.h"
#include "mcsat/clause/literal_table.h"
#include "mcsat/clause/clause_ref.h"

#include "mcsat/variable/variable_db.h"
#include "mcsat/clause/clause_db.h"

namespace CVC4 {
namespace mcsat {


class WatchListManager {

public:

  struct Watcher {
    CRef cref;
    Literal blocker;

    Watcher(CRef cref, Literal blocker)
    : cref(cref), blocker(blocker) {}

    Watcher() {}
  };
  
  typedef std::vector<Watcher> clause_list;
  typedef literal_table<clause_list> watch_lists;

private:

  /** Watchlist indexed by literals */
  watch_lists d_watchLists;

  /** Whether the list needs cleanup */
  literal_table<bool> d_needsCleanup;
  
public:

  void add(Literal lit, CRef cRef, Literal blocker) {
    Debug("mcsat::bcp::watch") << "WatchListManager::add(" << lit << ", " << cRef << ")" << std::endl;
    d_watchLists[lit].push_back(Watcher(cRef, blocker));
  }
  
  class remove_iterator {
    
    friend class WatchListManager;
    
    /** The watch-lists from the manager */
    watch_lists& d_watchLists;     
    
    /** Index of the watch list */
    size_t d_literal;

    /** Element beyond the last to keep */
    size_t d_end_of_keep;
    /** Current element */
    size_t d_current;
 
    remove_iterator(watch_lists& lists, size_t index)
    : d_watchLists(lists)
    , d_literal(index)
    , d_end_of_keep(0)
    , d_current(0)
    {}

  public:
    
    /** Is there a next element */
    bool done() const {
      return d_current == d_watchLists[d_literal].size();
    }
    /** Continue to the next element and keep this one */
    void next_and_keep() {
      d_watchLists[d_literal][d_end_of_keep ++] = d_watchLists[d_literal][d_current ++];
    }
    /** Continue to the next element and remove this one */
    void next_and_remove() { 
      ++ d_current;
    }
    /** Get the current element */
    const Watcher& operator * () const {
      return d_watchLists[d_literal][d_current];
    }

    Watcher& operator * () {
      return d_watchLists[d_literal][d_current];
    }

    /** Removes removed elements from the list */
    ~remove_iterator() {
      while (!done()) {
	next_and_keep();
      }
      Assert(d_watchLists[d_literal].size() >= d_end_of_keep);
      d_watchLists[d_literal].resize(d_end_of_keep);
    }
  };

  /** Returns the iterator that can remove elements */
  remove_iterator begin(Literal l) {
    Debug("mcsat::bcp::watch") << "WatchListManager::begin(" << l << "): in list: " << d_watchLists[l].size() << std::endl;
    return remove_iterator(d_watchLists, l.index());
  }

  void gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc);

};

}
}
