/*********************                                                        */
/*! \file statistics_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics utility classes
 **
 ** Statistics utility classes, including classes for holding (and referring
 ** to) statistics, the statistics registry, and some other associated
 ** classes.
 **
 ** This file is somewhat unique in that it is a "cvc4_private_library.h"
 ** header. Because of this, most classes need to be marked as CVC4_PUBLIC.
 ** This is because CVC4_PUBLIC is connected to the visibility of the linkage
 ** in the object files for the class. It does not dictate what headers are
 ** installed.
 ** Because the StatisticsRegistry and associated classes are built into
 ** libutil, which is used by libcvc4, and then later used by the libmain
 ** without referring to libutil as well. Thus the without marking these as
 ** CVC4_PUBLIC the symbols would be external in libutil, internal in libcvc4,
 ** and not be visible to libmain and linking would fail.
 ** You can debug this using "nm" on the .so and .o files in the builds/
 ** directory. See
 ** http://eli.thegreenplace.net/2013/07/09/library-order-in-static-linking
 ** for a longer discussion on symbol visibility.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__STATISTICS_REGISTRY_H
#define CVC4__STATISTICS_REGISTRY_H

#include <stdint.h>

#include <ctime>
#include <iomanip>
#include <map>
#include <sstream>
#include <vector>

#include "base/exception.h"
#include "lib/clock_gettime.h"
#include "util/safe_print.h"
#include "util/statistics.h"

namespace CVC4 {

/**
 * Prints a timespec.
 *
 * This is used in the implementation of TimerStat. This needs to be available
 * before Stat due to ordering constraints in clang for TimerStat.
 */
std::ostream& operator<<(std::ostream& os, const timespec& t) CVC4_PUBLIC;

#ifdef CVC4_STATISTICS_ON
#  define CVC4_USE_STATISTICS true
#else
#  define CVC4_USE_STATISTICS false
#endif


/**
 * The base class for all statistics.
 *
 * This base class keeps the name of the statistic and declares the (pure)
 * virtual function flushInformation().  Derived classes must implement
 * this function and pass their name to the base class constructor.
 *
 * This class also (statically) maintains the delimiter used to separate
 * the name and the value when statistics are output.
 */
class Stat {
protected:
  /** The name of this statistic */
  std::string d_name;

public:

  /** Nullary constructor, does nothing */
  Stat() { }

  /**
   * Construct a statistic with the given name.  Debug builds of CVC4
   * will throw an assertion exception if the given name contains the
   * statistic delimiter string.
   */
  Stat(const std::string& name) : d_name(name)
  {
    if(CVC4_USE_STATISTICS) {
      CheckArgument(d_name.find(", ") == std::string::npos, name,
                    "Statistics names cannot include a comma (',')");
    }
  }

  /** Destruct a statistic.  This base-class version does nothing. */
  virtual ~Stat() {}

  /**
   * Flush the value of this statistic to an output stream.  Should
   * finish the output with an end-of-line character.
   */
  virtual void flushInformation(std::ostream& out) const = 0;

  /**
   * Flush the value of this statistic to a file descriptor. Should finish the
   * output with an end-of-line character. Should be safe to use in a signal
   * handler.
   */
  virtual void safeFlushInformation(int fd) const = 0;

  /**
   * Flush the name,value pair of this statistic to an output stream.
   * Uses the statistic delimiter string between name and value.
   *
   * May be redefined by a child class
   */
  virtual void flushStat(std::ostream& out) const {
    if(CVC4_USE_STATISTICS) {
      out << d_name << ", ";
      flushInformation(out);
    }
  }

  /**
   * Flush the name,value pair of this statistic to a file descriptor. Uses the
   * statistic delimiter string between name and value.
   *
   * May be redefined by a child class
   */
  virtual void safeFlushStat(int fd) const {
    if (CVC4_USE_STATISTICS) {
      safe_print(fd, d_name);
      safe_print(fd, ", ");
      safeFlushInformation(fd);
    }
  }

  /** Get the name of this statistic. */
  const std::string& getName() const {
    return d_name;
  }

  /** Get the value of this statistic as a string. */
  virtual SExpr getValue() const {
    std::stringstream ss;
    flushInformation(ss);
    return SExpr(ss.str());
  }

};/* class Stat */

// A generic way of making a SExpr from templated stats code.
// for example, the uint64_t version ensures that we create
// Integer-SExprs for ReadOnlyDataStats (like those inside
// Minisat) without having to specialize the entire
// ReadOnlyDataStat class template.
template <class T>
inline SExpr mkSExpr(const T& x) {
  std::stringstream ss;
  ss << x;
  return SExpr(ss.str());
}

template <>
inline SExpr mkSExpr(const uint64_t& x) {
  return SExpr(Integer(x));
}

template <>
inline SExpr mkSExpr(const int64_t& x) {
  return SExpr(Integer(x));
}

template <>
inline SExpr mkSExpr(const int& x) {
  return SExpr(Integer(x));
}

template <>
inline SExpr mkSExpr(const Integer& x) {
  return SExpr(x);
}

template <>
inline SExpr mkSExpr(const double& x) {
  // roundabout way to get a Rational from a double
  std::stringstream ss;
  ss << std::fixed << std::setprecision(8) << x;
  return SExpr(Rational::fromDecimal(ss.str()));
}

template <>
inline SExpr mkSExpr(const Rational& x) {
  return SExpr(x);
}

/**
 * A class to represent a "read-only" data statistic of type T.  Adds to
 * the Stat base class the pure virtual function getData(), which returns
 * type T, and flushInformation(), which outputs the statistic value to an
 * output stream (using the same existing stream insertion operator).
 *
 * Template class T must have stream insertion operation defined:
 * std::ostream& operator<<(std::ostream&, const T&)
 */
template <class T>
class ReadOnlyDataStat : public Stat {
public:
  /** The "payload" type of this data statistic (that is, T). */
  typedef T payload_t;

  /** Construct a read-only data statistic with the given name. */
  ReadOnlyDataStat(const std::string& name) :
    Stat(name) {
  }

  /** Get the value of the statistic. */
  virtual T getData() const = 0;

  /** Get a reference to the data value of the statistic. */
  virtual const T& getDataRef() const = 0;

  /** Flush the value of the statistic to the given output stream. */
  void flushInformation(std::ostream& out) const override
  {
    if(CVC4_USE_STATISTICS) {
      out << getData();
    }
  }

  void safeFlushInformation(int fd) const override
  {
    if (CVC4_USE_STATISTICS) {
      safe_print<T>(fd, getDataRef());
    }
  }

  SExpr getValue() const override { return mkSExpr(getData()); }

};/* class ReadOnlyDataStat<T> */


/**
 * A data statistic class.  This class extends a read-only data statistic
 * with assignment (the statistic can be set as well as read).  This class
 * adds to the read-only case a pure virtual function setData(), thus
 * providing the basic interface for a data statistic: getData() to get the
 * statistic value, and setData() to set it.
 *
 * As with the read-only data statistic class, template class T must have
 * stream insertion operation defined:
 * std::ostream& operator<<(std::ostream&, const T&)
 */
template <class T>
class DataStat : public ReadOnlyDataStat<T> {
public:

  /** Construct a data statistic with the given name. */
  DataStat(const std::string& name) :
    ReadOnlyDataStat<T>(name) {
  }

  /** Set the data statistic. */
  virtual void setData(const T&) = 0;

};/* class DataStat<T> */


/**
 * A data statistic that references a data cell of type T,
 * implementing getData() by referencing that memory cell, and
 * setData() by reassigning the statistic to point to the new
 * data cell.  The referenced data cell is kept as a const
 * reference, meaning the referenced data is never actually
 * modified by this class (it must be externally modified for
 * a reference statistic to make sense).  A common use for
 * this type of statistic is to output a statistic that is kept
 * outside the statistics package (for example, one that's kept
 * by a theory implementation for internal heuristic purposes,
 * which is important to keep even if statistics are turned off).
 *
 * Template class T must have an assignment operator=().
 */
template <class T>
class ReferenceStat : public DataStat<T> {
private:
  /** The referenced data cell */
  const T* d_data;

public:
  /**
   * Construct a reference stat with the given name and a reference
   * to NULL.
   */
  ReferenceStat(const std::string& name) :
    DataStat<T>(name),
    d_data(NULL) {
  }

  /**
   * Construct a reference stat with the given name and a reference to
   * the given data.
   */
  ReferenceStat(const std::string& name, const T& data) :
    DataStat<T>(name),
    d_data(NULL) {
    setData(data);
  }

  /** Set this reference statistic to refer to the given data cell. */
  void setData(const T& t) override
  {
    if(CVC4_USE_STATISTICS) {
      d_data = &t;
    }
  }

  /** Get the value of the referenced data cell. */
  T getData() const override { return *d_data; }

  /** Get a reference to the value of the referenced data cell. */
  const T& getDataRef() const override { return *d_data; }

};/* class ReferenceStat<T> */

/**
 * A data statistic that keeps a T and sets it with setData().
 *
 * Template class T must have an operator=() and a copy constructor.
 */
template <class T>
class BackedStat : public DataStat<T> {
protected:
  /** The internally-kept statistic value */
  T d_data;

public:

  /** Construct a backed statistic with the given name and initial value. */
  BackedStat(const std::string& name, const T& init) :
    DataStat<T>(name),
    d_data(init) {
  }

  /** Set the underlying data value to the given value. */
  void setData(const T& t) override
  {
    if(CVC4_USE_STATISTICS) {
      d_data = t;
    }
  }

  /** Identical to setData(). */
  BackedStat<T>& operator=(const T& t) {
    if(CVC4_USE_STATISTICS) {
      d_data = t;
    }
    return *this;
  }

  /** Get the underlying data value. */
  T getData() const override { return d_data; }

  /** Get a reference to the underlying data value. */
  const T& getDataRef() const override { return d_data; }

};/* class BackedStat<T> */

/**
 * A wrapper Stat for another Stat.
 *
 * This type of Stat is useful in cases where a module (like the
 * CongruenceClosure module) might keep its own statistics, but might
 * be instantiated in many contexts by many clients.  This makes such
 * a statistic inappopriate to register with the StatisticsRegistry
 * directly, as all would be output with the same name (and may be
 * unregistered too quickly anyway).  A WrappedStat allows the calling
 * client (say, TheoryUF) to wrap the Stat from the client module,
 * giving it a globally unique name.
 */
template <class Stat>
class WrappedStat : public ReadOnlyDataStat<typename Stat::payload_t> {
  typedef typename Stat::payload_t T;

  const ReadOnlyDataStat<T>& d_stat;

  /** Private copy constructor undefined (no copy permitted). */
  WrappedStat(const WrappedStat&) = delete;
  /** Private assignment operator undefined (no copy permitted). */
  WrappedStat<T>& operator=(const WrappedStat&) = delete;

public:

  /**
   * Construct a wrapped statistic with the given name that wraps the
   * given statistic.
   */
  WrappedStat(const std::string& name, const ReadOnlyDataStat<T>& stat) :
    ReadOnlyDataStat<T>(name),
    d_stat(stat) {
  }

  /** Get the data of the underlying (wrapped) statistic. */
  T getData() const override { return d_stat.getData(); }

  /** Get a reference to the data of the underlying (wrapped) statistic. */
  const T& getDataRef() const override { return d_stat.getDataRef(); }

  void safeFlushInformation(int fd) const override
  {
    // ReadOnlyDataStat uses getDataRef() to get the information to print,
    // which might not be appropriate for all wrapped statistics. Delegate the
    // printing to the wrapped statistic instead.
    d_stat.safeFlushInformation(fd);
  }

  SExpr getValue() const override { return d_stat.getValue(); }

};/* class WrappedStat<T> */

/**
 * A backed integer-valued (64-bit signed) statistic.
 * This doesn't functionally differ from its base class BackedStat<int64_t>,
 * except for adding convenience functions for dealing with integers.
 */
class IntStat : public BackedStat<int64_t> {
public:

  /**
   * Construct an integer-valued statistic with the given name and
   * initial value.
   */
  IntStat(const std::string& name, int64_t init) :
    BackedStat<int64_t>(name, init) {
  }

  /** Increment the underlying integer statistic. */
  IntStat& operator++() {
    if(CVC4_USE_STATISTICS) {
      ++d_data;
    }
    return *this;
  }

  /** Increment the underlying integer statistic by the given amount. */
  IntStat& operator+=(int64_t val) {
    if(CVC4_USE_STATISTICS) {
      d_data += val;
    }
    return *this;
  }

  /** Keep the maximum of the current statistic value and the given one. */
  void maxAssign(int64_t val) {
    if(CVC4_USE_STATISTICS) {
      if(d_data < val) {
        d_data = val;
      }
    }
  }

  /** Keep the minimum of the current statistic value and the given one. */
  void minAssign(int64_t val) {
    if(CVC4_USE_STATISTICS) {
      if(d_data > val) {
        d_data = val;
      }
    }
  }

  SExpr getValue() const override { return SExpr(Integer(d_data)); }

};/* class IntStat */

template <class T>
class SizeStat : public Stat {
private:
  const T& d_sized;
public:
  SizeStat(const std::string&name, const T& sized) :
    Stat(name), d_sized(sized) {}
  ~SizeStat() {}

  void flushInformation(std::ostream& out) const override
  {
    out << d_sized.size();
  }

  void safeFlushInformation(int fd) const override
  {
    safe_print<uint64_t>(fd, d_sized.size());
  }

  SExpr getValue() const override { return SExpr(Integer(d_sized.size())); }

};/* class SizeStat */

/**
 * The value for an AverageStat is the running average of (e1, e_2, ..., e_n),
 *   (e1 + e_2 + ... + e_n)/n,
 * where e_i is an entry added by an addEntry(e_i) call.
 * The value is initially always 0.
 * (This is to avoid making parsers confused.)
 *
 * A call to setData() will change the running average but not reset the
 * running count, so should generally be avoided.  Call addEntry() to add
 * an entry to the average calculation.
 */
class AverageStat : public BackedStat<double> {
private:
  /**
   * The number of accumulations of the running average that we
   * have seen so far.
   */
  uint32_t d_count;
  double d_sum;

public:
  /** Construct an average statistic with the given name. */
  AverageStat(const std::string& name) :
    BackedStat<double>(name, 0.0), d_count(0), d_sum(0.0) {
  }

  /** Add an entry to the running-average calculation. */
  void addEntry(double e) {
    if(CVC4_USE_STATISTICS) {
      ++d_count;
      d_sum += e;
      setData(d_sum / d_count);
    }
  }

  SExpr getValue() const override
  {
    std::stringstream ss;
    ss << std::fixed << std::setprecision(8) << d_data;
    return SExpr(Rational::fromDecimal(ss.str()));
  }

};/* class AverageStat */

/** A statistic that contains a SExpr. */
class SExprStat : public Stat {
private:
  SExpr d_data;

public:

  /**
   * Construct a SExpr-valued statistic with the given name and
   * initial value.
   */
  SExprStat(const std::string& name, const SExpr& init) :
    Stat(name), d_data(init){}

  void flushInformation(std::ostream& out) const override
  {
    out << d_data;
  }

  void safeFlushInformation(int fd) const override
  {
    // SExprStat is only used in statistics.cpp in copyFrom, which we cannot
    // do in a signal handler anyway.
    safe_print(fd, "<unsupported>");
  }

  SExpr getValue() const override { return d_data; }

};/* class SExprStat */

template <class T>
class HistogramStat : public Stat {
private:
  typedef std::map<T, unsigned int> Histogram;
  Histogram d_hist;
public:

  /** Construct a histogram of a stream of entries. */
  HistogramStat(const std::string& name) : Stat(name) {}
  ~HistogramStat() {}

  void flushInformation(std::ostream& out) const override
  {
    if(CVC4_USE_STATISTICS) {
      typename Histogram::const_iterator i = d_hist.begin();
      typename Histogram::const_iterator end =  d_hist.end();
      out << "[";
      while(i != end){
        const T& key = (*i).first;
        unsigned int count = (*i).second;
        out << "("<<key<<" : "<<count<< ")";
        ++i;
        if(i != end){
          out << ", ";
        }
      }
      out << "]";
    }
  }

  void safeFlushInformation(int fd) const override
  {
    if (CVC4_USE_STATISTICS) {
      typename Histogram::const_iterator i = d_hist.begin();
      typename Histogram::const_iterator end = d_hist.end();
      safe_print(fd, "[");
      while (i != end) {
        const T& key = (*i).first;
        unsigned int count = (*i).second;
        safe_print(fd, "(");
        safe_print<T>(fd, key);
        safe_print(fd, " : ");
        safe_print<uint64_t>(fd, count);
        safe_print(fd, ")");
        ++i;
        if (i != end) {
          safe_print(fd, ", ");
        }
      }
      safe_print(fd, "]");
    }
  }

  HistogramStat& operator<<(const T& val){
    if(CVC4_USE_STATISTICS) {
      if(d_hist.find(val) == d_hist.end()){
        d_hist.insert(std::make_pair(val,0));
      }
      d_hist[val]++;
    }
    return (*this);
  }

};/* class HistogramStat */

/****************************************************************************/
/* Statistics Registry                                                      */
/****************************************************************************/

/**
 * The main statistics registry.  This registry maintains the list of
 * currently active statistics and is able to "flush" them all.
 */
class CVC4_PUBLIC StatisticsRegistry : public StatisticsBase, public Stat {
private:

  /** Private copy constructor undefined (no copy permitted). */
  StatisticsRegistry(const StatisticsRegistry&) = delete;

public:

  /** Construct an nameless statistics registry */
  StatisticsRegistry() {}

  /** Construct a statistics registry */
  StatisticsRegistry(const std::string& name);

  /**
   * Set the name of this statistic registry, used as prefix during
   * output.  (This version overrides StatisticsBase::setPrefix().)
   */
  void setPrefix(const std::string& name) override { d_prefix = d_name = name; }

  /** Overridden to avoid the name being printed */
  void flushStat(std::ostream& out) const override;

  void flushInformation(std::ostream& out) const override;

  void safeFlushInformation(int fd) const override;

  SExpr getValue() const override
  {
    std::vector<SExpr> v;
    for(StatSet::iterator i = d_stats.begin(); i != d_stats.end(); ++i) {
      std::vector<SExpr> w;
      w.push_back(SExpr((*i)->getName()));
      w.push_back((*i)->getValue());
      v.push_back(SExpr(w));
    }
    return SExpr(v);
  }

  /** Register a new statistic */
  void registerStat(Stat* s);

  /** Unregister a new statistic */
  void unregisterStat(Stat* s);

};/* class StatisticsRegistry */

class CodeTimer;

/**
 * A timer statistic.  The timer can be started and stopped
 * arbitrarily, like a stopwatch; the value of the statistic at the
 * end is the accumulated time over all (start,stop) pairs.
 */
class CVC4_PUBLIC TimerStat : public BackedStat<timespec> {

  // strange: timespec isn't placed in 'std' namespace ?!
  /** The last start time of this timer */
  timespec d_start;

  /** Whether this timer is currently running */
  bool d_running;

public:

  typedef CVC4::CodeTimer CodeTimer;

  /**
   * Construct a timer statistic with the given name.  Newly-constructed
   * timers have a 0.0 value and are not running.
   */
  TimerStat(const std::string& name)
      : BackedStat<timespec>(name, {0, 0}), d_start{0, 0}, d_running(false) {}

  /** Start the timer. */
  void start();

  /**
   * Stop the timer and update the statistic value with the
   * accumulated time.
   */
  void stop();

  /** If the timer is currently running */
  bool running() const;

  timespec getData() const override;

  void safeFlushInformation(int fd) const override
  {
    // Overwrite the implementation in the superclass because we cannot use
    // getDataRef(): it might return stale data if the timer is currently
    // running.
    ::timespec data = getData();
    safe_print<timespec>(fd, data);
  }

  SExpr getValue() const override;

};/* class TimerStat */

/**
 * Utility class to make it easier to call stop() at the end of a
 * code block.  When constructed, it starts the timer.  When
 * destructed, it stops the timer.
 */
class CodeTimer {
  TimerStat& d_timer;
  bool d_reentrant;

  /** Private copy constructor undefined (no copy permitted). */
  CodeTimer(const CodeTimer& timer) = delete;
  /** Private assignment operator undefined (no copy permitted). */
  CodeTimer& operator=(const CodeTimer& timer) = delete;

public:
  CodeTimer(TimerStat& timer, bool allow_reentrant = false) : d_timer(timer), d_reentrant(false) {
    if(!allow_reentrant || !(d_reentrant = d_timer.running())) {
      d_timer.start();
    }
  }
  ~CodeTimer() {
    if(!d_reentrant) {
      d_timer.stop();
    }
  }
};/* class CodeTimer */

/**
 * Resource-acquisition-is-initialization idiom for statistics
 * registry.  Useful for stack-based statistics (like in the driver).
 * This RAII class only does registration and unregistration.
 */
class CVC4_PUBLIC RegisterStatistic {
public:
  RegisterStatistic(StatisticsRegistry* reg, Stat* stat);
  ~RegisterStatistic();

private:
  StatisticsRegistry* d_reg;
  Stat* d_stat;

};/* class RegisterStatistic */

#undef CVC4_USE_STATISTICS

}/* CVC4 namespace */

#endif /* CVC4__STATISTICS_REGISTRY_H */
