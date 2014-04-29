/*********************                                                        */
/*! \file regexp.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__REGEXP_H
#define __CVC4__REGEXP_H

#include <iostream>
#include <iomanip>
#include <string>
#include <set>
#include <sstream>
#include "util/exception.h"
//#include "util/integer.h"
#include "util/hash.h"

namespace CVC4 {

class CVC4_PUBLIC String {
public:
  static unsigned int convertCharToUnsignedInt( char c ) {
    int i = (int)c;
    i = i-65;
    return (unsigned int)(i<0 ? i+256 : i);
  }
  static char convertUnsignedIntToChar( unsigned int i ){
    int ii = i+65;
    return (char)(ii>=256 ? ii-256 : ii);
  }
  static bool isPrintable( unsigned int i ){
    char c = convertUnsignedIntToChar( i );
    return isprint( (int)c );
  }

private:
  std::vector<unsigned int> d_str;

  bool isVecSame(const std::vector<unsigned int> &a, const std::vector<unsigned int> &b) const {
    if(a.size() != b.size()) return false;
    else {
      for(unsigned int i=0; i<a.size(); ++i)
        if(a[i] != b[i]) return false;
      return true;
    }
  }

  //guarded
  char hexToDec(char c) {
    if(isdigit(c)) {
      return c - '0';
    } else if (c >= 'a' && c >= 'f') {
      return c - 'a' + 10;
    } else {
      return c - 'A' + 10;
    }
  }

  void toInternal(const std::string &s);

public:
  String() {}

  String(const std::string &s) {
    toInternal(s);
  }

  String(const char* s) {
    std::string stmp(s);
    toInternal(stmp);
  }

  String(const char c) {
    d_str.push_back( convertCharToUnsignedInt(c) );
  }

  String(const std::vector<unsigned int> &s) : d_str(s) { }

  ~String() {}

  String& operator =(const String& y) {
    if(this != &y) d_str = y.d_str;
    return *this;
  }

  bool operator ==(const String& y) const {
    return isVecSame(d_str, y.d_str);
  }

  bool operator !=(const String& y) const {
    return  ! ( isVecSame(d_str, y.d_str) );
  }

  String concat (const String& other) const {
    std::vector<unsigned int> ret_vec(d_str);
    ret_vec.insert( ret_vec.end(), other.d_str.begin(), other.d_str.end() );
    return String(ret_vec);
  }

  bool operator <(const String& y) const {
    if(d_str.size() != y.d_str.size()) return d_str.size() < y.d_str.size();
    else {
      for(unsigned int i=0; i<d_str.size(); ++i)
        if(d_str[i] != y.d_str[i]) return d_str[i] < y.d_str[i];

      return false;
    }
  }

  bool operator >(const String& y) const {
    if(d_str.size() != y.d_str.size()) return d_str.size() > y.d_str.size();
    else {
      for(unsigned int i=0; i<d_str.size(); ++i)
        if(d_str[i] != y.d_str[i]) return d_str[i] > y.d_str[i];

      return false;
    }
  }

  bool operator <=(const String& y) const {
    if(d_str.size() != y.d_str.size()) return d_str.size() < y.d_str.size();
    else {
      for(unsigned int i=0; i<d_str.size(); ++i)
        if(d_str[i] != y.d_str[i]) return d_str[i] < y.d_str[i];

      return true;
    }
  }

  bool operator >=(const String& y) const {
    if(d_str.size() != y.d_str.size()) return d_str.size() > y.d_str.size();
    else {
      for(unsigned int i=0; i<d_str.size(); ++i)
        if(d_str[i] != y.d_str[i]) return d_str[i] > y.d_str[i];

      return true;
    }
  }

  bool strncmp(const String &y, unsigned int n) const {
    for(unsigned int i=0; i<n; ++i)
      if(d_str[i] != y.d_str[i]) return false;
    return true;
  }

  bool rstrncmp(const String &y, unsigned int n) const {
    for(unsigned int i=0; i<n; ++i)
      if(d_str[d_str.size() - i - 1] != y.d_str[y.d_str.size() - i - 1]) return false;
    return true;
  }

  bool isEmptyString() const {
    return ( d_str.size() == 0 );
  }

  unsigned int operator[] (const unsigned int i) const {
  //Assert( i < d_str.size() && i >= 0);
    return d_str[i];
  }
  /*
   * Convenience functions
   */
  std::string toString() const;

  unsigned size() const {
    return d_str.size();
  }

  char getFirstChar() const {
    return convertUnsignedIntToChar( d_str[0] );
  }

  bool isRepeated() const {
  if(d_str.size() > 1) {
    unsigned int f = d_str[0];
    for(unsigned i=1; i<d_str.size(); ++i) {
      if(f != d_str[i]) return false;
    }
  }
  return true;
  }

  bool tailcmp(const String &y, int &c) const {
    int id_x = d_str.size() - 1;
    int id_y = y.d_str.size() - 1;
    while(id_x>=0 && id_y>=0) {
      if(d_str[id_x] != y.d_str[id_y]) {
        c = id_x;
        return false;
      }
      --id_x; --id_y;
    }
    c = id_x == -1 ? ( - (id_y+1) ) : (id_x + 1);
    return true;
  }

  std::size_t find(const String &y, const int start = 0) const {
    if(d_str.size() < y.d_str.size() + (std::size_t) start) return std::string::npos;
    if(y.d_str.size() == 0) return (std::size_t) start;
    if(d_str.size() == 0) return std::string::npos;
    std::size_t ret = std::string::npos;
    for(int i = start; i <= (int) d_str.size() - (int) y.d_str.size(); i++) {
      if(d_str[i] == y.d_str[0]) {
        std::size_t j=0;
        for(; j<y.d_str.size(); j++) {
          if(d_str[i+j] != y.d_str[j]) break;
        }
        if(j == y.d_str.size()) {
          ret = (std::size_t) i;
          break;
        }
      }
    }
    return ret;
  }

  String replace(const String &s, const String &t) const {
    std::size_t ret = find(s);
    if( ret != std::string::npos ) {
      std::vector<unsigned int> vec;
      vec.insert(vec.begin(), d_str.begin(), d_str.begin() + ret);
      vec.insert(vec.end(), t.d_str.begin(), t.d_str.end());
      vec.insert(vec.end(), d_str.begin() + ret + s.d_str.size(), d_str.end());
      return String(vec);
    } else {
      return *this;
    }
  }

  String substr(unsigned i) const {
    std::vector<unsigned int> ret_vec;
    std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
    ret_vec.insert(ret_vec.end(), itr, d_str.end());
    return String(ret_vec);
  }
  String substr(unsigned i, unsigned j) const {
    std::vector<unsigned int> ret_vec;
    std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
    ret_vec.insert( ret_vec.end(), itr, itr + j );
    return String(ret_vec);
  }

  String prefix(unsigned i) const {
    return substr(0, i);
  }
  String suffix(unsigned i) const {
    return substr(d_str.size() - i, i);
  }
  bool overlap(String &y) const;

  bool isNumber() const {
   if(d_str.size() == 0) return false;
   for(unsigned int i=0; i<d_str.size(); ++i) {
     char c = convertUnsignedIntToChar( d_str[i] );
     if(c<'0' || c>'9') {
       return false;
     }
   }
   return true;
  }
  int toNumber() const {
   if(isNumber()) {
     int ret=0;
     for(unsigned int i=0; i<d_str.size(); ++i) {
       char c = convertUnsignedIntToChar( d_str[i] );
       ret = ret * 10 + (int)c - (int)'0';
     }
     return ret;
   } else {
     return -1;
   }
  }
  void getCharSet(std::set<unsigned int> &cset) const;
};/* class String */

namespace strings {

struct CVC4_PUBLIC StringHashFunction {
  size_t operator()(const ::CVC4::String& s) const {
    return __gnu_cxx::hash<const char*>()(s.toString().c_str());
  }
};/* struct StringHashFunction */

}/* CVC4::strings namespace */

std::ostream& operator <<(std::ostream& os, const String& s) CVC4_PUBLIC;

class CVC4_PUBLIC RegExp {
protected:
  int d_type;
public:
  RegExp() : d_type(1) {}

  RegExp(const int t) : d_type(t) {}

  ~RegExp() {}

  bool operator ==(const RegExp& y) const {
    return d_type == y.d_type ;
  }

  bool operator !=(const RegExp& y) const {
    return d_type != y.d_type ;
  }

  bool operator <(const RegExp& y) const {
    return d_type < y.d_type;
  }

  bool operator >(const RegExp& y) const {
    return d_type > y.d_type ;
  }

  bool operator <=(const RegExp& y) const {
    return d_type <= y.d_type;
  }

  bool operator >=(const RegExp& y) const {
    return d_type >= y.d_type ;
  }

  int getType() const { return d_type; }
};/* class RegExp */

/**
 * Hash function for the RegExp constants.
 */
struct CVC4_PUBLIC RegExpHashFunction {
  inline size_t operator()(const RegExp& s) const {
    return (size_t)s.getType();
  }
};/* struct RegExpHashFunction */

std::ostream& operator <<(std::ostream& os, const RegExp& s) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__REGEXP_H */
