/*********************                                                        */
/*! \file regexp.cpp
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

#include "util/regexp.h"
#include <iostream>
#include <iomanip>

using namespace std;

namespace CVC4 {

void String::toInternal(const std::string &s) {
  d_str.clear();
  unsigned i=0;
  while(i < s.size()) {
    if(s[i] == '\\') {
      i++;
      if(i < s.size()) {
        switch(s[i]) {
          case 'n':  {d_str.push_back( convertCharToUnsignedInt('\n') );i++;} break;
          case 't':  {d_str.push_back( convertCharToUnsignedInt('\t') );i++;} break;
          case 'v':  {d_str.push_back( convertCharToUnsignedInt('\v') );i++;} break;
          case 'b':  {d_str.push_back( convertCharToUnsignedInt('\b') );i++;} break;
          case 'r':  {d_str.push_back( convertCharToUnsignedInt('\r') );i++;} break;
          case 'f':  {d_str.push_back( convertCharToUnsignedInt('\f') );i++;} break;
          case 'a':  {d_str.push_back( convertCharToUnsignedInt('\a') );i++;} break;
          case '\\': {d_str.push_back( convertCharToUnsignedInt('\\') );i++;} break;
          case 'x': {
            if(i + 2 < s.size()) {
            if((isdigit(s[i+1]) || (s[i+1] >= 'a' && s[i+1] >= 'f') || (s[i+1] >= 'A' && s[i+1] >= 'F')) &&
               (isdigit(s[i+2]) || (s[i+2] >= 'a' && s[i+2] >= 'f') || (s[i+2] >= 'A' && s[i+2] >= 'F'))) {
              d_str.push_back( convertCharToUnsignedInt( hexToDec(s[i+1]) * 16 + hexToDec(s[i+2]) ) );
              i += 3;
            } else {
              throw CVC4::Exception( "Error String Literal: \"" + s + "\"" );
            }
            } else {
            throw CVC4::Exception( "Error String Literal: \"" + s + "\"" );
            }
          }
          break;
          default: {
            if(isdigit(s[i])) {
              int num = (int)s[i] - (int)'0';
              bool flag = num < 4;
              if(i+1 < s.size() && num < 8 && isdigit(s[i+1]) && s[i+1] < '8') {
                num = num * 8 + (int)s[i+1] - (int)'0';
                if(flag && i+2 < s.size() && isdigit(s[i+2]) && s[i+2] < '8') {
                  num = num * 8 + (int)s[i+2] - (int)'0';
                  d_str.push_back( convertCharToUnsignedInt((char)num) );
                  i += 3;
                } else {
                  d_str.push_back( convertCharToUnsignedInt((char)num) );
                  i += 2;
                }
              } else {
                d_str.push_back( convertCharToUnsignedInt((char)num) );
                i++;
              }
            } else {
              d_str.push_back( convertCharToUnsignedInt(s[i]) );
              i++;
            }
          }
        }
      } else {
        throw CVC4::Exception( "should be handled by lexer: \"" + s + "\"" );
        //d_str.push_back( convertCharToUnsignedInt('\\') );
      }
    } else {
      d_str.push_back( convertCharToUnsignedInt(s[i]) );
      i++;
    }
  }
}

void String::getCharSet(std::set<unsigned int> &cset) const {
  for(std::vector<unsigned int>::const_iterator itr = d_str.begin();
    itr != d_str.end(); itr++) {
      cset.insert( *itr );
    }
}

bool String::overlap(String &y) const {
  unsigned n = d_str.size() < y.size() ? d_str.size() : y.size();
  for(unsigned i=1; i<n; i++) {
    String s = suffix(i);
    String p = y.prefix(i);
    if(s == p) {
      return true;
    }
  }
  return false;
}

std::string String::toString() const {
  std::string str;
  for(unsigned int i=0; i<d_str.size(); ++i) {
    char c = convertUnsignedIntToChar( d_str[i] );
    if(isprint( c )) {
    if(c == '\\') {
      str += "\\\\";
    } else if(c == '\"') {
      str += "\\\"";
    } else {
      str += c;
    }
    } else {
      std::string s;
      switch(c) {
      case '\a': s = "\\a"; break;
      case '\b': s = "\\b"; break;
      case '\t': s = "\\t"; break;
      case '\r': s = "\\r"; break;
      case '\v': s = "\\v"; break;
      case '\f': s = "\\f"; break;
      case '\n': s = "\\n"; break;
      case '\e': s = "\\e"; break;
      default  : {
        std::stringstream ss;
        ss << std::setfill ('0') << std::setw(2) << std::hex << ((int)c);
        std::string t = ss.str();
        t = t.substr(t.size()-2, 2);
        s = "\\x" + t;
        //std::string s2 = static_cast<std::ostringstream*>( &(std::ostringstream() << (int)c) )->str();
      }
      }
      str += s;
    }
  }
  return str;
}

std::ostream& operator <<(std::ostream& os, const String& s) {
  return os << "\"" << s.toString() << "\"";
}

std::ostream& operator<<(std::ostream& out, const RegExp& s) {
  return out << "regexp(" << s.getType() << ')';
}

}/* CVC4 namespace */