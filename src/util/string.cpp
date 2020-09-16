/*********************                                                        */
/*! \file string.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the string data type.
 **/

#include "util/string.h"

#include <algorithm>
#include <climits>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "base/check.h"
#include "base/exception.h"

using namespace std;

namespace CVC4 {

static_assert(UCHAR_MAX == 255, "Unsigned char is assumed to have 256 values.");

String::String(const std::vector<unsigned> &s) : d_str(s)
{
#ifdef CVC4_ASSERTIONS
  for (unsigned u : d_str)
  {
    Assert(u < num_codes());
  }
#endif
}

int String::cmp(const String &y) const {
  if (size() != y.size()) {
    return size() < y.size() ? -1 : 1;
  }
  for (unsigned int i = 0; i < size(); ++i) {
    if (d_str[i] != y.d_str[i]) {
      unsigned cp = d_str[i];
      unsigned cpy = y.d_str[i];
      return cp < cpy ? -1 : 1;
    }
  }
  return 0;
}

String String::concat(const String &other) const {
  std::vector<unsigned int> ret_vec(d_str);
  ret_vec.insert(ret_vec.end(), other.d_str.begin(), other.d_str.end());
  return String(ret_vec);
}

bool String::strncmp(const String& y, std::size_t n) const
{
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

bool String::rstrncmp(const String& y, std::size_t n) const
{
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

void String::addCharToInternal(unsigned char ch, std::vector<unsigned>& str)
{
  // if not a printable character
  if (ch > 127 || ch < 32)
  {
    std::stringstream serr;
    serr << "Illegal string character: \"" << ch
         << "\", must use escape sequence";
    throw CVC4::Exception(serr.str());
  }
  else
  {
    str.push_back(static_cast<unsigned>(ch));
  }
}

std::vector<unsigned> String::toInternal(const std::string& s,
                                         bool useEscSequences)
{
  std::vector<unsigned> str;
  unsigned i = 0;
  while (i < s.size())
  {
    // get the current character
    char si = s[i];
    if (si != '\\' || !useEscSequences)
    {
      addCharToInternal(si, str);
      ++i;
      continue;
    }
    // the vector of characters, in case we fail to read an escape sequence
    std::vector<unsigned> nonEscCache;
    // process the '\'
    addCharToInternal(si, nonEscCache);
    ++i;
    // are we an escape sequence?
    bool isEscapeSequence = true;
    // the string corresponding to the hexadecimal code point
    std::stringstream hexString;
    // is the slash followed by a 'u'? Could be last character.
    if (i >= s.size() || s[i] != 'u')
    {
      isEscapeSequence = false;
    }
    else
    {
      // process the 'u'
      addCharToInternal(s[i], nonEscCache);
      ++i;
      bool isStart = true;
      bool isEnd = false;
      bool hasBrace = false;
      while (i < s.size())
      {
        // add the next character
        si = s[i];
        if (isStart)
        {
          isStart = false;
          // possibly read '{'
          if (si == '{')
          {
            hasBrace = true;
            addCharToInternal(si, nonEscCache);
            ++i;
            continue;
          }
        }
        else if (si == '}')
        {
          // can only end if we had an open brace and read at least one digit
          isEscapeSequence = hasBrace && !hexString.str().empty();
          isEnd = true;
          addCharToInternal(si, nonEscCache);
          ++i;
          break;
        }
        // must be a hex digit at this point
        if (!isHexDigit(static_cast<unsigned>(si)))
        {
          isEscapeSequence = false;
          break;
        }
        hexString << si;
        addCharToInternal(si, nonEscCache);
        ++i;
        if (!hasBrace && hexString.str().size() == 4)
        {
          // will be finished reading \ u d_3 d_2 d_1 d_0 with no parens
          isEnd = true;
          break;
        }
        else if (hasBrace && hexString.str().size() > 5)
        {
          // too many digits enclosed in brace, not an escape sequence
          isEscapeSequence = false;
          break;
        }
      }
      if (!isEnd)
      {
        // if we were interrupted before ending, then this is not a valid
        // escape sequence
        isEscapeSequence = false;
      }
    }
    if (isEscapeSequence)
    {
      Assert(!hexString.str().empty() && hexString.str().size() <= 5);
      // Otherwise, we add the escaped character.
      // This is guaranteed not to overflow due to the length of hstr.
      uint32_t val;
      hexString >> std::hex >> val;
      if (val > num_codes())
      {
        // Failed due to being out of range. This can happen for strings of
        // the form \ u { d_4 d_3 d_2 d_1 d_0 } where d_4 is a hexadecimal not
        // in the range [0-2].
        isEscapeSequence = false;
      }
      else
      {
        str.push_back(val);
      }
    }
    // if we did not successfully parse an escape sequence, we add back all
    // characters that we cached
    if (!isEscapeSequence)
    {
      str.insert(str.end(), nonEscCache.begin(), nonEscCache.end());
    }
  }
#ifdef CVC4_ASSERTIONS
  for (unsigned u : str)
  {
    Assert(u < num_codes());
  }
#endif
  return str;
}

unsigned String::front() const
{
  Assert(!d_str.empty());
  return d_str.front();
}

unsigned String::back() const
{
  Assert(!d_str.empty());
  return d_str.back();
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
  std::stringstream str;
  for (unsigned int i = 0; i < size(); ++i) {
    // we always print forward slash as a code point so that it cannot
    // be interpreted as specifying part of a code point, e.g. the string
    // '\' + 'u' + '0' of length three.
    if (isPrintable(d_str[i]) && d_str[i] != '\\' && !useEscSequences)
    {
      str << static_cast<char>(d_str[i]);
    }
    else
    {
      std::stringstream ss;
      ss << std::hex << d_str[i];
      str << "\\u{" << ss.str() << "}";
    }
  }
  return str.str();
}

bool String::isLeq(const String &y) const
{
  for (unsigned i = 0; i < size(); ++i)
  {
    if (i >= y.size())
    {
      return false;
    }
    unsigned ci = d_str[i];
    unsigned cyi = y.d_str[i];
    if (ci > cyi)
    {
      return false;
    }
    if (ci < cyi)
    {
      return true;
    }
  }
  return true;
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

bool String::hasPrefix(const String& y) const
{
  size_t s = size();
  size_t ys = y.size();
  if (ys > s)
  {
    return false;
  }
  for (size_t i = 0; i < ys; i++)
  {
    if (d_str[i] != y.d_str[i])
    {
      return false;
    }
  }
  return true;
}

bool String::hasSuffix(const String& y) const
{
  size_t s = size();
  size_t ys = y.size();
  if (ys > s)
  {
    return false;
  }
  size_t idiff = s - ys;
  for (size_t i = 0; i < ys; i++)
  {
    if (d_str[i + idiff] != y.d_str[i])
    {
      return false;
    }
  }
  return true;
}

String String::update(std::size_t i, const String& t) const
{
  if (i < size())
  {
    std::vector<unsigned> vec(d_str.begin(), d_str.begin() + i);
    size_t remNum = size() - i;
    size_t tnum = t.d_str.size();
    if (tnum >= remNum)
    {
      vec.insert(vec.end(), t.d_str.begin(), t.d_str.begin() + remNum);
    }
    else
    {
      vec.insert(vec.end(), t.d_str.begin(), t.d_str.end());
      vec.insert(vec.end(), d_str.begin() + i + tnum, d_str.end());
    }
    return String(vec);
  }
  return *this;
}

String String::replace(const String &s, const String &t) const {
  std::size_t ret = find(s);
  if (ret != std::string::npos) {
    std::vector<unsigned> vec;
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
  std::vector<unsigned> ret_vec;
  std::vector<unsigned>::const_iterator itr = d_str.begin() + i;
  ret_vec.insert(ret_vec.end(), itr, d_str.end());
  return String(ret_vec);
}

String String::substr(std::size_t i, std::size_t j) const {
  Assert(i + j <= size());
  std::vector<unsigned> ret_vec;
  std::vector<unsigned>::const_iterator itr = d_str.begin() + i;
  ret_vec.insert(ret_vec.end(), itr, itr + j);
  return String(ret_vec);
}

bool String::noOverlapWith(const String& y) const
{
  return y.find(*this) == std::string::npos
         && this->find(y) == std::string::npos && this->overlap(y) == 0
         && y.overlap(*this) == 0;
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
  // '0' to '9'
  return 48 <= character && character <= 57;
}

bool String::isHexDigit(unsigned character)
{
  // '0' to '9' or 'A' to 'F' or 'a' to 'f'
  return isDigit(character) || (65 <= character && character <= 70)
         || (97 <= character && character <= 102);
}

bool String::isPrintable(unsigned character)
{
  // Unicode 0x00020 (' ') to 0x0007E ('~')
  return 32 <= character && character <= 126;
}

size_t String::maxSize() { return std::numeric_limits<uint32_t>::max(); }

Rational String::toNumber() const
{
  // when smt2 standard for strings is set, this may change, based on the
  // semantics of str.from.int for leading zeros
  return Rational(toString());
}

std::ostream &operator<<(std::ostream &os, const String &s) {
  return os << "\"" << s.toString(true) << "\"";
}

}  // namespace CVC4
