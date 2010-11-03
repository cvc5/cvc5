/*********************                                                        */
/*! \file stats.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__STATS_H
#define __CVC4__STATS_H

#include <string>
#include <ostream>
#include <sstream>
#include <iomanip>
#include <set>
#include <ctime>

#include "util/Assert.h"
#include "lib/clock_gettime.h"

namespace CVC4 {


#ifdef CVC4_STATISTICS_ON
#  define __CVC4_USE_STATISTICS true
#else
#  define __CVC4_USE_STATISTICS false
#endif

class CVC4_PUBLIC Stat;

class CVC4_PUBLIC StatisticsRegistry {
private:
  struct StatCmp {
    inline bool operator()(const Stat* s1, const Stat* s2) const;
  };/* class StatisticsRegistry::StatCmp */

  typedef std::set< Stat*, StatCmp > StatSet;
  static StatSet d_registeredStats;

public:

  typedef StatSet::const_iterator const_iterator;

  static void flushStatistics(std::ostream& out);

  static inline void registerStat(Stat* s) throw(AssertionException);
  static inline void unregisterStat(Stat* s) throw(AssertionException);

  static inline const_iterator begin() {
    return d_registeredStats.begin();
  }
  static inline const_iterator end() {
    return d_registeredStats.end();
  }
};/* class StatisticsRegistry */


class CVC4_PUBLIC Stat {
private:
  std::string d_name;

  static std::string s_delim;

public:

  Stat(const std::string& s) throw(CVC4::AssertionException) :
    d_name(s) {
    if(__CVC4_USE_STATISTICS) {
      AlwaysAssert(d_name.find(s_delim) == std::string::npos);
    }
  }
  virtual ~Stat() {}

  virtual void flushInformation(std::ostream& out) const = 0;

  void flushStat(std::ostream& out) const {
    if(__CVC4_USE_STATISTICS) {
      out << d_name << s_delim;
      flushInformation(out);
    }
  }

  const std::string& getName() const {
    return d_name;
  }

  virtual std::string getValue() const = 0;
};/* class Stat */

inline bool StatisticsRegistry::StatCmp::operator()(const Stat* s1,
                                                    const Stat* s2) const {
  return s1->getName() < s2->getName();
}

inline void StatisticsRegistry::registerStat(Stat* s)
  throw(AssertionException) {
  if(__CVC4_USE_STATISTICS) {
    AlwaysAssert(d_registeredStats.find(s) == d_registeredStats.end());
    d_registeredStats.insert(s);
  }
}/* StatisticsRegistry::registerStat */


inline void StatisticsRegistry::unregisterStat(Stat* s)
  throw(AssertionException) {
  if(__CVC4_USE_STATISTICS) {
    AlwaysAssert(d_registeredStats.find(s) != d_registeredStats.end());
    d_registeredStats.erase(s);
  }
}/* StatisticsRegistry::unregisterStat */



/**
 * class T must have stream insertion operation defined.
 * std::ostream& operator<<(std::ostream&, const T&);
 */
template <class T>
class DataStat : public Stat {
public:
  DataStat(const std::string& s) :
    Stat(s) {
  }

  virtual const T& getData() const = 0;
  virtual void setData(const T&) = 0;

  void flushInformation(std::ostream& out) const {
    if(__CVC4_USE_STATISTICS) {
      out << getData();
    }
  }

  std::string getValue() const {
    std::stringstream ss;
    ss << getData();
    return ss.str();
  }
};/* class DataStat */


/** T must have an assignment operator=(). */
template <class T>
class ReferenceStat : public DataStat<T> {
private:
  const T* d_data;

public:
  ReferenceStat(const std::string& s) :
    DataStat<T>(s),
    d_data(NULL) {
  }

  ReferenceStat(const std::string& s, const T& data) :
    DataStat<T>(s),
    d_data(NULL) {
    setData(data);
  }

  void setData(const T& t) {
    if(__CVC4_USE_STATISTICS) {
      d_data = &t;
    }
  }

  const T& getData() const {
    if(__CVC4_USE_STATISTICS) {
      return *d_data;
    } else {
      Unreachable();
    }
  }
};/* class ReferenceStat */


/** T must have an operator=() and a copy constructor. */
template <class T>
class BackedStat : public DataStat<T> {
protected:
  T d_data;

public:

  BackedStat(const std::string& s, const T& init) :
    DataStat<T>(s),
    d_data(init) {
  }

  void setData(const T& t) {
    if(__CVC4_USE_STATISTICS) {
      d_data = t;
    }
  }

  BackedStat<T>& operator=(const T& t) {
    if(__CVC4_USE_STATISTICS) {
      d_data = t;
    }
    return *this;
  }

  const T& getData() const {
    if(__CVC4_USE_STATISTICS) {
      return d_data;
    } else {
      Unreachable();
    }
  }
};/* class BackedStat */


class IntStat : public BackedStat<int64_t> {
public:

  IntStat(const std::string& s, int64_t init) :
    BackedStat<int64_t>(s, init) {
  }

  IntStat& operator++() {
    if(__CVC4_USE_STATISTICS) {
      ++d_data;
    }
    return *this;
  }

  IntStat& operator+=(int64_t val) {
    if(__CVC4_USE_STATISTICS) {
      d_data+= val;
    }
    return *this;
  }

  void maxAssign(int64_t val) {
    if(__CVC4_USE_STATISTICS) {
      if(d_data < val) {
        d_data = val;
      }
    }
  }

  void minAssign(int64_t val) {
    if(__CVC4_USE_STATISTICS) {
      if(d_data > val) {
        d_data = val;
      }
    }
  }
};/* class IntStat */


/**
 * The value for an AverageStat is the running average of (e1, e_2, ..., e_n),
 *   (e1 + e_2 + ... + e_n)/n,
 * where e_i is an entry added by an addEntry(e_i) call.
 * The value is initially always 0.
 * (This is to avoid making parsers confused.)
 */
class AverageStat : public BackedStat<double> {
private:
  uint32_t n;

public:
  AverageStat(const std::string& s) :
    BackedStat<double>(s, 0.0 ), n(0) {
  }

  void addEntry(double e){
    double oldSum = n*getData();
    ++n;
    double newSum = oldSum + e;
    setData(newSum / n);
  }

};/* class AverageStat */


// some utility functions for ::timespec
inline ::timespec& operator+=(::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  const long nsec_per_sec = 1000000000L; // one thousand million
  a.tv_sec += b.tv_sec;
  long nsec = a.tv_nsec + b.tv_nsec;
  while(nsec < 0) {
    nsec += nsec_per_sec;
    ++a.tv_sec;
  }
  while(nsec >= nsec_per_sec) {
    nsec -= nsec_per_sec;
    --a.tv_sec;
  }
  a.tv_nsec = nsec;
  return a;
}
inline ::timespec& operator-=(::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  const long nsec_per_sec = 1000000000L; // one thousand million
  a.tv_sec -= b.tv_sec;
  long nsec = a.tv_nsec - b.tv_nsec;
  while(nsec < 0) {
    nsec += nsec_per_sec;
    ++a.tv_sec;
  }
  while(nsec >= nsec_per_sec) {
    nsec -= nsec_per_sec;
    --a.tv_sec;
  }
  a.tv_nsec = nsec;
  return a;
}
inline ::timespec operator+(const ::timespec& a, const ::timespec& b) {
  ::timespec result = a;
  return result += b;
}
inline ::timespec operator-(const ::timespec& a, const ::timespec& b) {
  ::timespec result = a;
  return result -= b;
}
inline bool operator==(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec == b.tv_sec && a.tv_nsec == b.tv_nsec;
}
inline bool operator!=(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a == b);
}
inline bool operator<(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec < b.tv_sec ||
    (a.tv_sec == b.tv_sec && a.tv_nsec < b.tv_nsec);
}
inline bool operator>(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec > b.tv_sec ||
    (a.tv_sec == b.tv_sec && a.tv_nsec > b.tv_nsec);
}
inline bool operator<=(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a > b);
}
inline bool operator>=(const ::timespec& a, const ::timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a < b);
}
inline std::ostream& operator<<(std::ostream& os, const ::timespec& t) {
  // assumes t.tv_nsec is in range
  return os << t.tv_sec << "."
            << std::setfill('0') << std::setw(8) << std::right << t.tv_nsec;
}


class TimerStat : public BackedStat< ::timespec > {
  // strange: timespec isn't placed in 'std' namespace ?!
  ::timespec d_start;
  bool d_running;

public:

  TimerStat(const std::string& s) :
    BackedStat< ::timespec >(s, ::timespec()),
    d_running(false) {
  }

  void start() {
    if(__CVC4_USE_STATISTICS) {
      AlwaysAssert(!d_running);
      clock_gettime(CLOCK_MONOTONIC, &d_start);
      d_running = true;
    }
  }

  void stop() {
    if(__CVC4_USE_STATISTICS) {
      AlwaysAssert(d_running);
      ::timespec end;
      clock_gettime(CLOCK_MONOTONIC, &end);
      d_data += end - d_start;
      d_running = false;
    }
  }
};/* class TimerStat */


#undef __CVC4_USE_STATISTICS

}/* CVC4 namespace */

#endif /* __CVC4__STATS_H */
