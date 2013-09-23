/*********************                                                        */
/*! \file regexp.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
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
#include <string>
//#include "util/exception.h"
//#include "util/integer.h"
#include "util/hash.h"

namespace CVC4 {

class CVC4_PUBLIC Char {

private:
  unsigned int d_char;

public:
  Char() {}

  Char(const unsigned int c)
      : d_char(c) {}

  ~Char() {}

  Char& operator =(const Char& y) {
    if(this != &y) d_char = y.d_char;
    return *this;
  }

  bool operator ==(const Char& y) const {
    return d_char == y.d_char ;
  }

  bool operator !=(const Char& y) const {
    return d_char != y.d_char ;
  }

  bool operator <(const Char& y) const {
    return d_char < y.d_char;
  }

  bool operator >(const Char& y) const {
    return d_char > y.d_char ;
  }

  bool operator <=(const Char& y) const {
    return d_char <= y.d_char;
  }

  bool operator >=(const Char& y) const {
    return d_char >= y.d_char ;
  }

  /*
   * Convenience functions
   */
  std::string toString() const {
    std::string str = "1";
    str[0] = (char) d_char;
    return str;
  }

  unsigned size() const {
    return 1;
  }

  const char* c_str() const {
    return toString().c_str();
  }
};/* class Char */

namespace strings {

struct CharHashFunction {
  size_t operator()(const ::CVC4::Char& c) const {
    return __gnu_cxx::hash<const char*>()(c.toString().c_str());
  }
};/* struct CharHashFunction */

}

inline std::ostream& operator <<(std::ostream& os, const Char& c) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const Char& c) {
  return os << "\"" << c.toString() << "\"";
}

class CVC4_PUBLIC String {

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

public:
  String() {}

  String(const std::string &s) {
    for(unsigned int i=0; i<s.size(); ++i) {
        d_str.push_back( convertCharToUnsignedInt(s[i]) );
    }
  }

  String(const char* s) {
    for(unsigned int i=0,len=strlen(s); i<len; ++i) {
        d_str.push_back( convertCharToUnsignedInt(s[i]) );
    }
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

  /*
   * Convenience functions
   */
  std::string toString() const {
    std::string str;
    for(unsigned int i=0; i<d_str.size(); ++i) {
      str += convertUnsignedIntToChar( d_str[i] );
	  //TODO isPrintable: ( "\\" + (convertUnsignedIntToChar( d_str[i] ) );
    }
    return str;
  }

  unsigned size() const {
    return d_str.size();
  }

  String substr(unsigned i) const {
    std::vector<unsigned int> ret_vec;
    std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
    //for(unsigned k=0; k<i; k++) ++itr;
    ret_vec.insert(ret_vec.end(), itr, d_str.end());
      return String(ret_vec);
  }
  String substr(unsigned i, unsigned j) const {
    std::vector<unsigned int> ret_vec;
    std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
    //for(unsigned k=0; k<i; k++) ++itr;
    //std::vector<unsigned int>::const_iterator itr2 = itr;
    //for(unsigned k=0; k<j; k++) ++itr2;
    ret_vec.insert( ret_vec.end(), itr, itr + j );
      return String(ret_vec);
  }

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

};/* class String */

namespace strings {

struct StringHashFunction {
  size_t operator()(const ::CVC4::String& s) const {
    return __gnu_cxx::hash<const char*>()(s.toString().c_str());
  }
};/* struct StringHashFunction */

}

inline std::ostream& operator <<(std::ostream& os, const String& s) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const String& s) {
  return os << "\"" << s.toString() << "\"";
}

class CVC4_PUBLIC RegExp {

private:
  std::string d_str;

public:
  RegExp() {}

  RegExp(const std::string s)
      : d_str(s) {}

  ~RegExp() {}

  RegExp& operator =(const RegExp& y) {
    if(this != &y) d_str = y.d_str;
    return *this;
  }

  bool operator ==(const RegExp& y) const {
    return d_str == y.d_str ;
  }

  bool operator !=(const RegExp& y) const {
    return d_str != y.d_str ;
  }

  String concat (const RegExp& other) const {
    return String(d_str + other.d_str);
  }

  bool operator <(const RegExp& y) const {
    return d_str < y.d_str;
  }

  bool operator >(const RegExp& y) const {
    return d_str > y.d_str ;
  }

  bool operator <=(const RegExp& y) const {
    return d_str <= y.d_str;
  }

  bool operator >=(const RegExp& y) const {
    return d_str >= y.d_str ;
  }

  /*
   * Convenience functions
   */

  size_t hash() const {
    unsigned int h = 1;

    for (size_t i = 0; i < d_str.length(); ++i) {
        h = (h << 5)  + d_str[i];
    }

    return h;
  }

  std::string toString() const {
    return d_str;
  }

  unsigned size() const {
    return d_str.size();
  }
};/* class String */

/**
 * Hash function for the RegExp constants.
 */
struct CVC4_PUBLIC RegExpHashFunction {
  inline size_t operator()(const RegExp& s) const {
    return s.hash();
  }
};/* struct RegExpHashFunction */

inline std::ostream& operator <<(std::ostream& os, const RegExp& s) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const RegExp& s) {
  return os << s.toString();
}
}/* CVC4 namespace */

#endif /* __CVC4__STRING_H */
