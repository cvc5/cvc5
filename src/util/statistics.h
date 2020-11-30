/*********************                                                        */
/*! \file statistics.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Mathias Preiner
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

#include "cvc4_public.h"

#ifndef CVC4__STATISTICS_H
#define CVC4__STATISTICS_H

#include <iterator>
#include <ostream>
#include <set>
#include <string>
#include <utility>

#include "util/sexpr.h"

namespace CVC4 {

class Stat;

class CVC4_PUBLIC StatisticsBase {
protected:

  static std::string s_regDelim;

  /** A helper class for comparing two statistics */
  struct StatCmp {
    bool operator()(const Stat* s1, const Stat* s2) const;
  };/* struct StatisticsRegistry::StatCmp */

  /** A type for a set of statistics */
  typedef std::set< Stat*, StatCmp > StatSet;

  std::string d_prefix;

  /** The set of statistics in this object */
  StatSet d_stats;

  StatisticsBase();
  StatisticsBase(const StatisticsBase& stats);
  StatisticsBase& operator=(const StatisticsBase& stats);

public:

  virtual ~StatisticsBase() { }

  class CVC4_PUBLIC iterator : public std::iterator< std::input_iterator_tag, std::pair<std::string, SExpr> > {
    StatSet::iterator d_it;

    iterator(StatSet::iterator it) : d_it(it) { }

    friend class StatisticsBase;

  public:
    iterator() : d_it() { }
    iterator(const iterator& it) : d_it(it.d_it) { }
    value_type operator*() const;
    iterator& operator++() { ++d_it; return *this; }
    iterator operator++(int) { iterator old = *this; ++d_it; return old; }
    bool operator==(const iterator& i) const { return d_it == i.d_it; }
    bool operator!=(const iterator& i) const { return d_it != i.d_it; }
  };/* class StatisticsBase::iterator */

  /** An iterator type over a set of statistics. */
  typedef iterator const_iterator;

  /** Set the output prefix for this set of statistics. */
  virtual void setPrefix(const std::string& prefix);

  /** Flush all statistics to the given output stream. */
  void flushInformation(std::ostream& out) const;

  /**
   * Flush all statistics to the given file descriptor. Safe to use in a signal
   * handler.
   */
  void safeFlushInformation(int fd) const;

  /** Get the value of a named statistic. */
  SExpr getStatistic(std::string name) const;

  /**
   * Get an iterator to the beginning of the range of the set of
   * statistics.
   */
  const_iterator begin() const;

  /**
   * Get an iterator to the end of the range of the set of statistics.
   */
  const_iterator end() const;

};/* class StatisticsBase */

class CVC4_PUBLIC Statistics : public StatisticsBase {
  void clear();
  void copyFrom(const StatisticsBase&);

public:

  /**
   * Override the copy constructor to do a "deep" copy of statistics
   * values.
   */
  Statistics(const StatisticsBase& stats);
  Statistics(const Statistics& stats);

  ~Statistics();

  /**
   * Override the assignment operator to do a "deep" copy of statistics
   * values.
   */
  Statistics& operator=(const StatisticsBase& stats);
  Statistics& operator=(const Statistics& stats);

};/* class Statistics */

}/* CVC4 namespace */

#endif /* CVC4__STATISTICS_H */
