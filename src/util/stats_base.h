/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base statistic classes.
 */

#include "cvc4_private_library.h"

#ifndef CVC5__UTIL__STATS_BASE_H
#define CVC5__UTIL__STATS_BASE_H

#include <iomanip>
#include <sstream>
#include <string>

#include "cvc4_export.h"
#include "util/safe_print.h"
#include "util/sexpr.h"
#include "util/stats_utils.h"

#ifdef CVC5_STATISTICS_ON
#define CVC5_USE_STATISTICS true
#else
#define CVC5_USE_STATISTICS false
#endif

namespace cvc5 {

/**
 * The base class for all statistics.
 *
 * This base class keeps the name of the statistic and declares the (pure)
 * virtual functions flushInformation() and safeFlushInformation().
 * Derived classes must implement these function and pass their name to
 * the base class constructor.
 */
class CVC4_EXPORT Stat
{
 public:
  /**
   * Construct a statistic with the given name.  Debug builds of CVC4
   * will throw an assertion exception if the given name contains the
   * statistic delimiter string.
   */
  Stat(const std::string& name);

  /** Destruct a statistic.  This base-class version does nothing. */
  virtual ~Stat() = default;

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

  /** Get the name of this statistic. */
  const std::string& getName() const { return d_name; }

  /** Get the value of this statistic as a string. */
  virtual SExpr getValue() const
  {
    std::stringstream ss;
    flushInformation(ss);
    return SExpr(ss.str());
  }

 protected:
  /** The name of this statistic */
  std::string d_name;
}; /* class Stat */

/**
 * A data statistic that keeps a T and sets it with setData().
 *
 * Template class T must have an operator=() and a copy constructor.
 */
template <class T>
class BackedStat : public Stat
{
 public:
  /** Construct a backed statistic with the given name and initial value. */
  BackedStat(const std::string& name, const T& init) : Stat(name), d_data(init)
  {
  }

  /** Set the underlying data value to the given value. */
  void set(const T& t)
  {
    if (CVC5_USE_STATISTICS)
    {
      d_data = t;
    }
  }

  const T& get() const { return d_data; }

  /** Flush the value of the statistic to the given output stream. */
  virtual void flushInformation(std::ostream& out) const override
  {
    out << d_data;
  }

  virtual void safeFlushInformation(int fd) const override
  {
    safe_print<T>(fd, d_data);
  }

 protected:
  /** The internally-kept statistic value */
  T d_data;
}; /* class BackedStat<T> */

/**
 * A data statistic that references a data cell of type T,
 * implementing get() by referencing that memory cell, and
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
class ReferenceStat : public Stat
{
 public:
  /**
   * Construct a reference stat with the given name and a reference
   * to nullptr.
   */
  ReferenceStat(const std::string& name) : Stat(name) {}

  /**
   * Construct a reference stat with the given name and a reference to
   * the given data.
   */
  ReferenceStat(const std::string& name, const T& data) : Stat(name)
  {
    set(data);
  }

  /** Set this reference statistic to refer to the given data cell. */
  void set(const T& t)
  {
    if (CVC5_USE_STATISTICS)
    {
      d_data = &t;
    }
  }
  const T& get() const { return *d_data; }

  /** Flush the value of the statistic to the given output stream. */
  virtual void flushInformation(std::ostream& out) const override
  {
    out << *d_data;
  }

  virtual void safeFlushInformation(int fd) const override
  {
    safe_print<T>(fd, *d_data);
  }

 private:
  /** The referenced data cell */
  const T* d_data = nullptr;
}; /* class ReferenceStat<T> */

/**
 * A backed integer-valued (64-bit signed) statistic.
 * This doesn't functionally differ from its base class BackedStat<int64_t>,
 * except for adding convenience functions for dealing with integers.
 */
class IntStat : public BackedStat<int64_t>
{
 public:
  /**
   * Construct an integer-valued statistic with the given name and
   * initial value.
   */
  IntStat(const std::string& name, int64_t init);

  /** Increment the underlying integer statistic. */
  IntStat& operator++();
  /** Increment the underlying integer statistic. */
  IntStat& operator++(int);

  /** Increment the underlying integer statistic by the given amount. */
  IntStat& operator+=(int64_t val);

  /** Keep the maximum of the current statistic value and the given one. */
  void maxAssign(int64_t val);

  /** Keep the minimum of the current statistic value and the given one. */
  void minAssign(int64_t val);

  SExpr getValue() const override { return SExpr(Integer(d_data)); }

}; /* class IntStat */

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
class AverageStat : public BackedStat<double>
{
 public:
  /** Construct an average statistic with the given name. */
  AverageStat(const std::string& name);

  /** Add an entry to the running-average calculation. */
  AverageStat& operator<<(double e);

  SExpr getValue() const override;

 private:
  /**
   * The number of accumulations of the running average that we
   * have seen so far.
   */
  uint32_t d_count = 0;
  double d_sum = 0;
}; /* class AverageStat */

template <class T>
class SizeStat : public Stat
{
 public:
  SizeStat(const std::string& name, const T& sized) : Stat(name), d_sized(sized)
  {
  }
  ~SizeStat() {}

  /** Flush the value of the statistic to the given output stream. */
  void flushInformation(std::ostream& out) const override
  {
    out << d_sized.size();
  }

  void safeFlushInformation(int fd) const override
  {
    safe_print(fd, d_sized.size());
  }

 private:
  const T& d_sized;
}; /* class SizeStat */

}  // namespace cvc5

#endif
