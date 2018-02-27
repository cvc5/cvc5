/*********************                                                        */
/*! \file regexp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tianyi Liang, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/regexp.h"

#include <algorithm>
#include <climits>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "base/cvc4_assert.h"
#include "base/exception.h"

using namespace std;

namespace CVC4 {

static_assert(UCHAR_MAX == 255, "Unsigned char is assumed to have 256 values.");

int String::cmp(const String &y) const {
  if (size() != y.size()) {
    return size() < y.size() ? -1 : 1;
  }
  for (unsigned int i = 0; i < size(); ++i) {
    if (d_str[i] != y.d_str[i]) {
      return getUnsignedCharAt(i) < y.getUnsignedCharAt(i) ? -1 : 1;
    }
  }
  return 0;
}

String String::concat(const String &other) const {
  std::vector<unsigned int> ret_vec(d_str);
  ret_vec.insert(ret_vec.end(), other.d_str.begin(), other.d_str.end());
  return String(ret_vec);
}

bool String::strncmp(const String &y, const std::size_t np) const {
  std::size_t n = np;
  std::size_t b = (size() >= y.size()) ? size() : y.size();
  std::size_t s = (size() <= y.size()) ? size() : y.size();
  if (n > s) {
    if (b == s) {
      n = s;
    } else {
      return false;
    }
  }
  for (std::size_t i = 0; i < n; ++i) {
    if (d_str[i] != y.d_str[i]) return false;
  }
  return true;
}

bool String::rstrncmp(const String &y, const std::size_t np) const {
  std::size_t n = np;
  std::size_t b = (size() >= y.size()) ? size() : y.size();
  std::size_t s = (size() <= y.size()) ? size() : y.size();
  if (n > s) {
    if (b == s) {
      n = s;
    } else {
      return false;
    }
  }
  for (std::size_t i = 0; i < n; ++i) {
    if (d_str[size() - i - 1] != y.d_str[y.size() - i - 1]) return false;
  }
  return true;
}

std::vector<unsigned> String::toInternal(const std::string &s,
                                         bool useEscSequences) {
  std::vector<unsigned> str;
  unsigned i = 0;
  while (i < s.size()) {
    if (s[i] == '\\' && useEscSequences) {
      i++;
      if (i < s.size()) {
        switch (s[i]) {
          case 'n': {
            str.push_back(convertCharToUnsignedInt('\n'));
            i++;
          } break;
          case 't': {
            str.push_back(convertCharToUnsignedInt('\t'));
            i++;
          } break;
          case 'v': {
            str.push_back(convertCharToUnsignedInt('\v'));
            i++;
          } break;
          case 'b': {
            str.push_back(convertCharToUnsignedInt('\b'));
            i++;
          } break;
          case 'r': {
            str.push_back(convertCharToUnsignedInt('\r'));
            i++;
          } break;
          case 'f': {
            str.push_back(convertCharToUnsignedInt('\f'));
            i++;
          } break;
          case 'a': {
            str.push_back(convertCharToUnsignedInt('\a'));
            i++;
          } break;
          case '\\': {
            str.push_back(convertCharToUnsignedInt('\\'));
            i++;
          } break;
          case 'x': {
            if (i + 2 < s.size()) {
              if (isxdigit(s[i + 1]) && isxdigit(s[i + 2])) {
                str.push_back(convertCharToUnsignedInt(hexToDec(s[i + 1]) * 16 +
                                                       hexToDec(s[i + 2])));
                i += 3;
              } else {
                throw CVC4::Exception("Illegal String Literal: \"" + s + "\"");
              }
            } else {
              throw CVC4::Exception("Illegal String Literal: \"" + s +
                                    "\", must have two digits after \\x");
            }
          } break;
          default: {
            if (isdigit(s[i])) {
              // octal escape sequences  TODO : revisit (issue #1251).
              int num = (int)s[i] - (int)'0';
              bool flag = num < 4;
              if (i + 1 < s.size() && num < 8 && isdigit(s[i + 1]) &&
                  s[i + 1] < '8') {
                num = num * 8 + (int)s[i + 1] - (int)'0';
                if (flag && i + 2 < s.size() && isdigit(s[i + 2]) &&
                    s[i + 2] < '8') {
                  num = num * 8 + (int)s[i + 2] - (int)'0';
                  str.push_back(convertCharToUnsignedInt((unsigned char)num));
                  i += 3;
                } else {
                  str.push_back(convertCharToUnsignedInt((unsigned char)num));
                  i += 2;
                }
              } else {
                str.push_back(convertCharToUnsignedInt((unsigned char)num));
                i++;
              }
            } else if ((unsigned)s[i] > 127) {
              throw CVC4::Exception("Illegal String Literal: \"" + s +
                                    "\", must use escaped sequence");
            } else {
              str.push_back(convertCharToUnsignedInt(s[i]));
              i++;
            }
          }
        }
      } else {
        throw CVC4::Exception("should be handled by lexer: \"" + s + "\"");
        // str.push_back( convertCharToUnsignedInt('\\') );
      }
    } else if ((unsigned)s[i] > 127 && useEscSequences) {
      throw CVC4::Exception("Illegal String Literal: \"" + s +
                            "\", must use escaped sequence");
    } else {
      str.push_back(convertCharToUnsignedInt(s[i]));
      i++;
    }
  }
  return str;
}

unsigned char String::getUnsignedCharAt(size_t pos) const {
  Assert(pos < size());
  return convertUnsignedIntToChar(d_str[pos]);
}

std::size_t String::overlap(const String &y) const {
  std::size_t i = size() < y.size() ? size() : y.size();
  for (; i > 0; i--) {
    String s = suffix(i);
    String p = y.prefix(i);
    if (s == p) {
      return i;
    }
  }
  return i;
}

std::size_t String::roverlap(const String &y) const {
  std::size_t i = size() < y.size() ? size() : y.size();
  for (; i > 0; i--) {
    String s = prefix(i);
    String p = y.suffix(i);
    if (s == p) {
      return i;
    }
  }
  return i;
}

std::string String::toString(bool useEscSequences) const {
  std::string str;
  for (unsigned int i = 0; i < size(); ++i) {
    unsigned char c = convertUnsignedIntToChar(d_str[i]);
    if (!useEscSequences) {
      str += c;
    } else if (isprint(c)) {
      if (c == '\\') {
        str += "\\\\";
      }
      // else if(c == '\"') {
      //  str += "\\\"";
      //}
      else {
        str += c;
      }
    } else {
      std::string s;
      switch (c) {
        case '\a':
          s = "\\a";
          break;
        case '\b':
          s = "\\b";
          break;
        case '\t':
          s = "\\t";
          break;
        case '\r':
          s = "\\r";
          break;
        case '\v':
          s = "\\v";
          break;
        case '\f':
          s = "\\f";
          break;
        case '\n':
          s = "\\n";
          break;
        case '\e':
          s = "\\e";
          break;
        default: {
          std::stringstream ss;
          ss << std::setfill('0') << std::setw(2) << std::hex << ((int)c);
          std::string t = ss.str();
          t = t.substr(t.size() - 2, 2);
          s = "\\x" + t;
          // std::string s2 = static_cast<std::ostringstream*>(
          // &(std::ostringstream() << (int)c) )->str();
        }
      }
      str += s;
    }
  }
  return str;
}

bool String::isRepeated() const {
  if (size() > 1) {
    unsigned int f = d_str[0];
    for (unsigned i = 1; i < size(); ++i) {
      if (f != d_str[i]) return false;
    }
  }
  return true;
}

bool String::tailcmp(const String &y, int &c) const {
  int id_x = size() - 1;
  int id_y = y.size() - 1;
  while (id_x >= 0 && id_y >= 0) {
    if (d_str[id_x] != y.d_str[id_y]) {
      c = id_x;
      return false;
    }
    --id_x;
    --id_y;
  }
  c = id_x == -1 ? (-(id_y + 1)) : (id_x + 1);
  return true;
}

std::size_t String::find(const String &y, const std::size_t start) const {
  if (size() < y.size() + start) return std::string::npos;
  if (y.empty()) return start;
  if (empty()) return std::string::npos;

  std::vector<unsigned>::const_iterator itr = std::search(
      d_str.begin() + start, d_str.end(), y.d_str.begin(), y.d_str.end());
  if (itr != d_str.end()) {
    return itr - d_str.begin();
  }
  return std::string::npos;
}

std::size_t String::rfind(const String &y, const std::size_t start) const {
  if (size() < y.size() + start) return std::string::npos;
  if (y.empty()) return start;
  if (empty()) return std::string::npos;

  std::vector<unsigned>::const_reverse_iterator itr = std::search(
      d_str.rbegin() + start, d_str.rend(), y.d_str.rbegin(), y.d_str.rend());
  if (itr != d_str.rend()) {
    return itr - d_str.rbegin();
  }
  return std::string::npos;
}

String String::replace(const String &s, const String &t) const {
  std::size_t ret = find(s);
  if (ret != std::string::npos) {
    std::vector<unsigned int> vec;
    vec.insert(vec.begin(), d_str.begin(), d_str.begin() + ret);
    vec.insert(vec.end(), t.d_str.begin(), t.d_str.end());
    vec.insert(vec.end(), d_str.begin() + ret + s.size(), d_str.end());
    return String(vec);
  } else {
    return *this;
  }
}

String String::substr(std::size_t i) const {
  Assert(i <= size());
  std::vector<unsigned int> ret_vec;
  std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
  ret_vec.insert(ret_vec.end(), itr, d_str.end());
  return String(ret_vec);
}

String String::substr(std::size_t i, std::size_t j) const {
  Assert(i + j <= size());
  std::vector<unsigned int> ret_vec;
  std::vector<unsigned int>::const_iterator itr = d_str.begin() + i;
  ret_vec.insert(ret_vec.end(), itr, itr + j);
  return String(ret_vec);
}

bool String::isNumber() const {
  if (d_str.empty()) {
    return false;
  }
  for (unsigned character : d_str) {
    if (!isDigit(character))
    {
      return false;
    }
  }
  return true;
}

bool String::isDigit(unsigned character)
{
  unsigned char c = convertUnsignedIntToChar(character);
  return c >= '0' && c <= '9';
}

size_t String::maxSize()
{
  return std::numeric_limits<size_t>::max();
}

int String::toNumber() const {
  if (isNumber()) {
    int ret = 0;
    for (unsigned int i = 0; i < size(); ++i) {
      unsigned char c = convertUnsignedIntToChar(d_str[i]);
      ret = ret * 10 + (int)c - (int)'0';
    }
    return ret;
  } else {
    return -1;
  }
}

unsigned char String::hexToDec(unsigned char c) {
  if (c >= '0' && c <= '9') {
    return c - '0';
  } else if (c >= 'a' && c <= 'f') {
    return c - 'a' + 10;
  } else {
    Assert(c >= 'A' && c <= 'F');
    return c - 'A' + 10;
  }
}

std::ostream &operator<<(std::ostream &os, const String &s) {
  return os << "\"" << s.toString(true) << "\"";
}

std::ostream &operator<<(std::ostream &out, const RegExp &s) {
  return out << "regexp(" << s.getType() << ')';
}

}  // namespace CVC4
