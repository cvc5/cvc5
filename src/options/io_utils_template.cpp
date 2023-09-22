/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IO manipulation classes.
 */

#include <iomanip>
#include <iostream>

#include "options/io_utils.h"

namespace cvc5::internal::options::ioutils {
namespace {

// There is no good way to figure out whether the value behind iword() was
// explicitly set. The default value is zero; we shift by some random constant
// such that zero is never a valid value, and we can still use both negative
// and positive values.
static constexpr long value_offset = 1024;

template <typename T>
void setData(std::ios_base& ios, int iosIndex, T value)
{
  ios.iword(iosIndex) = static_cast<long>(value) + value_offset;
}
template <typename T>
T getData(std::ios_base& ios, int iosIndex, T defaultValue)
{
  long& l = ios.iword(iosIndex);
  if (l == 0)
  {
    return defaultValue;
  }
  return static_cast<T>(l - value_offset);
}

}  // namespace

// clang-format off
${ioimpls}$
// clang-format on

Scope::Scope(std::ios_base& ios)
    : d_ios(ios),
// clang-format off
${ioscope_memberinit}$
// clang-format on
{
}

Scope::~Scope()
{
// clang-format off
${ioscope_restore}$
// clang-format on
}

}  // namespace cvc5::internal::options::ioutils
