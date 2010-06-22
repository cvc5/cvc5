/*********************                                                        */
/*! \file stats.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** rief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__STATS_H
#define __CVC4__STATS_H

#include <string>
#include <ostream>
#include <set>
#include "util/Assert.h"

namespace CVC4 {


#ifdef CVC4_STATISTICS_ON
#define USE_STATISTICS true
#else
#define USE_STATISTICS false
#endif

class CVC4_PUBLIC Stat;

class CVC4_PUBLIC StatisticsRegistry {
private:
  struct StatCmp;

  typedef std::set< Stat*, StatCmp > StatSet;
  static StatSet d_registeredStats;

public:
  static void flushStatistics(std::ostream& out);

  static inline void registerStat(Stat* s) throw (AssertionException);
}; /* class StatisticsRegistry */


class CVC4_PUBLIC Stat {
private:
  std::string d_name;

  static std::string s_delim;

public:

  Stat(const std::string& s) throw (CVC4::AssertionException) : d_name(s)
  {
    if(USE_STATISTICS){
      AlwaysAssert(d_name.find(s_delim) == std::string::npos);
    }
  }
  virtual ~Stat() {}

  virtual void flushInformation(std::ostream& out) const = 0;

  void flushStat(std::ostream& out) const{
    if(USE_STATISTICS){
      out << d_name << s_delim;
      flushInformation(out);
    }
  }

  const std::string& getName() const {
    return d_name;
  }
};

struct StatisticsRegistry::StatCmp {
  bool operator()(const Stat* s1, const Stat* s2) const
  {
    return (s1->getName()) < (s2->getName());
  }
};

inline void StatisticsRegistry::registerStat(Stat* s) throw (AssertionException){
  if(USE_STATISTICS){
    AlwaysAssert(d_registeredStats.find(s) == d_registeredStats.end());
    d_registeredStats.insert(s);
  }
}



/**
 *  class T must have stream insertion operation defined.
 * std::ostream& operator<<(std::ostream&, const T&);
 */
template<class T>
class DataStat : public Stat{
public:
  DataStat(const std::string& s) : Stat(s) {}

  virtual const T& getData() const = 0;
  virtual void setData(const T&) = 0;

  void flushInformation(std::ostream& out) const{
    if(USE_STATISTICS){
      out << getData();
    }
  }
};

/** T must have an assignment operator=(). */
template <class T>
class ReferenceStat: public DataStat<T>{
private:
  const T* d_data;

public:
  ReferenceStat(const std::string& s):
    DataStat<T>(s), d_data(NULL)
  {}

  ReferenceStat(const std::string& s, const T& data):
    DataStat<T>(s),d_data(NULL)
  {
    setData(data);
  }

  void setData(const T& t){
    if(USE_STATISTICS){
      d_data = &t;
    }
  }
  const T& getData() const{
    if(USE_STATISTICS){
      return *d_data;
    }else{
      Unreachable();
    }
  }
};

/** T must have an operator=() and a copy constructor. */
template <class T>
class BackedStat: public DataStat<T>{
protected:
  T d_data;

public:

  BackedStat(const std::string& s, const T& init): DataStat<T>(s), d_data(init)
  {}

  void setData(const T& t) {
    if(USE_STATISTICS){
      d_data = t;
    }
  }

  BackedStat<T>& operator=(const T& t){
    if(USE_STATISTICS){
      d_data = t;
    }
    return *this;
  }

  const T& getData() const{
    if(USE_STATISTICS){
      return d_data;
    }else{
      Unreachable();
    }
  }
};

class IntStat : public BackedStat<int64_t>{
public:

  IntStat(const std::string& s, int64_t init): BackedStat<int64_t>(s, init)
  {}

  IntStat& operator++(){
    if(USE_STATISTICS){
      ++d_data;
    }
    return *this;
  }

  IntStat& operator+=(int64_t val){
    if(USE_STATISTICS){
      d_data+= val;
    }
    return *this;
  }

  void maxAssign(int64_t val){
    if(USE_STATISTICS){
      if(d_data < val){
        d_data = val;
      }
    }
  }

  void minAssign(int64_t val){
    if(USE_STATISTICS){
      if(d_data > val){
        d_data = val;
      }
    }
  }
};

#undef USE_STATISTICS

}/* CVC4 namespace */

#endif /* __CVC4__STATS_H */
