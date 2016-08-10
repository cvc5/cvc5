/*********************                                                        */
/*! \file regexp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__REGEXP_H
#define __CVC4__REGEXP_H

#include <vector>
#include <string>
#include <set>
#include <sstream>
#include <cassert>

#include "base/exception.h"
#include "util/hash.h"

namespace CVC4 {

class CVC4_PUBLIC String {
public:
  static unsigned convertCharToUnsignedInt( unsigned char c ) {
    unsigned i = c;
    i = i + 191;
    return (i>=256 ? i-256 : i);
  }
  static unsigned char convertUnsignedIntToChar( unsigned i ){
    unsigned ii = i+65;
    return (unsigned char)(ii>=256 ? ii-256 : ii);
  }
  static bool isPrintable( unsigned i ){
    unsigned char c = convertUnsignedIntToChar( i );
    return (c>=' ' && c<='~');//isprint( (int)c );
  }

private:
  std::vector<unsigned> d_str;

  bool isVecSame(const std::vector<unsigned> &a, const std::vector<unsigned> &b) const {
    if(a.size() != b.size()) return false;
    else {
      return std::equal(a.begin(), a.end(), b.begin());
      //for(unsigned int i=0; i<a.size(); ++i)
        //if(a[i] != b[i]) return false;
      //return true;
    }
  }

  //guarded
  unsigned char hexToDec(unsigned char c) {
    if(c>='0' && c<='9') {
      return c - '0';
    } else if (c >= 'a' && c <= 'f') {
      return c - 'a' + 10;
    } else {
      assert(c >= 'A' && c <= 'F');
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

  String(const unsigned char c) {
    d_str.push_back( convertCharToUnsignedInt(c) );
  }

  String(const std::vector<unsigned> &s) : d_str(s) { }

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
        if(d_str[i] != y.d_str[i]) return convertUnsignedIntToChar(d_str[i]) < convertUnsignedIntToChar(y.d_str[i]);

      return false;
    }
  }

  bool operator >(const String& y) const {
    if(d_str.size() != y.d_str.size()) return d_str.size() > y.d_str.size();
    else {
      for(unsigned int i=0; i<d_str.size(); ++i)
        if(d_str[i] != y.d_str[i]) return convertUnsignedIntToChar(d_str[i]) > convertUnsignedIntToChar(y.d_str[i]);

      return false;
    }
  }

  bool operator <=(const String& y) const {
    if(d_str.size() != y.d_str.size()) return d_str.size() < y.d_str.size();
    else {
      for(unsigned int i=0; i<d_str.size(); ++i)
        if(d_str[i] != y.d_str[i]) return convertUnsignedIntToChar(d_str[i]) < convertUnsignedIntToChar(y.d_str[i]);

      return true;
    }
  }

  bool operator >=(const String& y) const {
    if(d_str.size() != y.d_str.size()) return d_str.size() > y.d_str.size();
    else {
      for(unsigned int i=0; i<d_str.size(); ++i)
        if(d_str[i] != y.d_str[i]) return convertUnsignedIntToChar(d_str[i]) > convertUnsignedIntToChar(y.d_str[i]);

      return true;
    }
  }

  bool strncmp(const String &y, const std::size_t np) const {
    std::size_t n = np;
    std::size_t b = (d_str.size() >= y.d_str.size()) ? d_str.size() : y.d_str.size();
    std::size_t s = (d_str.size() <= y.d_str.size()) ? d_str.size() : y.d_str.size();
    if(n > s) {
      if(b == s) {
        n = s;
      } else {
        return false;
      }
    }
    for(std::size_t i=0; i<n; ++i)
      if(d_str[i] != y.d_str[i]) return false;
    return true;
  }

  bool rstrncmp(const String &y, const std::size_t np) const {
    std::size_t n = np;
    std::size_t b = (d_str.size() >= y.d_str.size()) ? d_str.size() : y.d_str.size();
    std::size_t s = (d_str.size() <= y.d_str.size()) ? d_str.size() : y.d_str.size();
    if(n > s) {
      if(b == s) {
        n = s;
      } else {
        return false;
      }
    }
    for(std::size_t i=0; i<n; ++i)
      if(d_str[d_str.size() - i - 1] != y.d_str[y.d_str.size() - i - 1]) return false;
    return true;
  }

  bool isEmptyString() const {
    return ( d_str.size() == 0 );
  }

  /*char operator[] (const std::size_t i) const {
    assert( i < d_str.size() );
    return convertUnsignedIntToChar(d_str[i]);
  }*/
  /*
   * Convenience functions
   */
  std::string toString() const;

  std::size_t size() const {
    return d_str.size();
  }

  unsigned char getFirstChar() const {
    return convertUnsignedIntToChar( d_str[0] );
  }

  unsigned char getLastChar() const {
    assert(d_str.size() != 0);
    return convertUnsignedIntToChar( d_str[d_str.size() - 1] );
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

  std::size_t find(const String &y, const std::size_t start = 0) const {
    if(d_str.size() < y.d_str.size() + start) return std::string::npos;
    if(y.d_str.size() == 0) return start;
    if(d_str.size() == 0) return std::string::npos;
    std::vector<unsigned>::const_iterator itr = std::search(d_str.begin() + start, d_str.end(), y.d_str.begin(), y.d_str.end());
    if(itr != d_str.end()) {
      return itr - d_str.begin();
    }else{
      return std::string::npos;
    }
  }
  
  std::size_t rfind( String &y, const std::size_t start = 0) {
    std::reverse( d_str.begin(), d_str.end() );
    std::reverse( y.d_str.begin(), y.d_str.end() );
    std::size_t f = find( y, start );
    std::reverse( d_str.begin(), d_str.end() );
    std::reverse( y.d_str.begin(), y.d_str.end() );
    if( f==std::string::npos ){
      return std::string::npos;
    }else{
      return f;
    }
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

  String substr(std::size_t i) const {
    assert(i <= d_str.size());
    std::vector<unsigned int> ret_vec;
    std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
    ret_vec.insert(ret_vec.end(), itr, d_str.end());
    return String(ret_vec);
  }
  String substr(std::size_t i, std::size_t j) const {
    assert(i+j <= d_str.size());
    std::vector<unsigned int> ret_vec;
    std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
    ret_vec.insert( ret_vec.end(), itr, itr + j );
    return String(ret_vec);
  }

  String prefix(std::size_t i) const {
    return substr(0, i);
  }
  String suffix(std::size_t i) const {
    return substr(d_str.size() - i, i);
  }
  // if y=y1...yn and overlap returns m, then this is x1...y1...ym
  std::size_t overlap(String &y) const;
  // if y=y1...yn and overlap returns m, then this is y(n+1-m)...yn...xk
  std::size_t roverlap(String &y) const;

  bool isNumber() const {
   if(d_str.size() == 0) return false;
   for(unsigned int i=0; i<d_str.size(); ++i) {
     unsigned char c = convertUnsignedIntToChar( d_str[i] );
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
       unsigned char c = convertUnsignedIntToChar( d_str[i] );
       ret = ret * 10 + (int)c - (int)'0';
     }
     return ret;
   } else {
     return -1;
   }
  }

  void getCharSet(std::set<unsigned char> &cset) const;

  std::vector<unsigned> getVec() const {
    return d_str;
  }
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
