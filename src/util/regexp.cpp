/*********************                                                        */
/*! \file regexp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of data structures for regular expression operators.
 **/

#include "util/regexp.h"

#include <ostream>

namespace CVC4 {

RegExpRepeat::RegExpRepeat(uint32_t repeatAmount) : d_repeatAmount(repeatAmount)
{
}

bool RegExpRepeat::operator==(const RegExpRepeat& r) const
{
  return d_repeatAmount == r.d_repeatAmount;
}

RegExpLoop::RegExpLoop(uint32_t l, uint32_t h)
    : d_loopMinOcc(l), d_loopMaxOcc(h)
{
}

bool RegExpLoop::operator==(const RegExpLoop& r) const
{
  return d_loopMinOcc == r.d_loopMinOcc && d_loopMaxOcc == r.d_loopMaxOcc;
}

size_t RegExpRepeatHashFunction::operator()(const RegExpRepeat& r) const
{
  return r.d_repeatAmount;
}

size_t RegExpLoopHashFunction::operator()(const RegExpLoop& r) const
{
  return r.d_loopMinOcc + r.d_loopMaxOcc;
}

std::ostream& operator<<(std::ostream& os, const RegExpRepeat& r)
{
  return os << r.d_repeatAmount;
}

std::ostream& operator<<(std::ostream& os, const RegExpLoop& r)
{
  return os << "[" << r.d_loopMinOcc << ".." << r.d_loopMaxOcc << "]";
}

}  // namespace CVC4
