/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IO manipulation classes.
 */

#include "options/io_utils.h"

#include <iomanip>
#include <iostream>

namespace cvc5::internal::options::ioutils {
namespace {

template <typename T>
void setData(std::ios_base& ios, int iosIndex, T value)
{
  constexpr long offset = 1024;
  ios.iword(iosIndex) = static_cast<long>(value) + offset;
}
template <typename T>
T getData(std::ios_base& ios, int iosIndex, T defaultValue)
{
  // There is no good way to figure out whether the value was explicitly set.
  // The default value is zero; we shift by some random constant such that
  // zero is never a valid value, and we can still use both negative and
  // positive values.
  constexpr long offset = 1024;
  long& l = ios.iword(iosIndex);
  if (l == 0)
  {
    l = static_cast<long>(defaultValue) + offset;
  }
  return static_cast<T>(l - offset);
}

}  // namespace

const static int s_iosDagThresh = std::ios_base::xalloc();
const static int s_iosNodeDepth = std::ios_base::xalloc();
const static int s_iosOutputLang = std::ios_base::xalloc();

static thread_local int64_t s_dagThreshDefault = 1;
static thread_local int64_t s_nodeDepthDefault = -1;
static thread_local Language s_outputLangDefault = Language::LANG_AUTO;

void setDefaultDagThresh(int64_t value) { s_dagThreshDefault = value; }
void setDefaultNodeDepth(int64_t value) { s_nodeDepthDefault = value; }
void setDefaultOutputLang(Language value) { s_outputLangDefault = value; }

void applyDagThresh(std::ios_base& ios, int64_t dagThresh)
{
  setData(ios, s_iosDagThresh, dagThresh);
}
void applyNodeDepth(std::ios_base& ios, int64_t nodeDepth)
{
  setData(ios, s_iosNodeDepth, nodeDepth);
}
void applyOutputLang(std::ios_base& ios, Language outputLang)
{
  setData(ios, s_iosOutputLang, outputLang);
}

void apply(std::ios_base& ios,
           int64_t dagThresh,
           int64_t nodeDepth,
           Language outputLang)
{
  applyDagThresh(ios, dagThresh);
  applyNodeDepth(ios, nodeDepth);
  applyOutputLang(ios, outputLang);
}

int64_t getDagThresh(std::ios_base& ios)
{
  return getData(ios, s_iosDagThresh, s_dagThreshDefault);
}
int64_t getNodeDepth(std::ios_base& ios)
{
  return getData(ios, s_iosNodeDepth, s_nodeDepthDefault);
}
Language getOutputLang(std::ios_base& ios)
{
  return getData(ios, s_iosOutputLang, s_outputLangDefault);
}

Scope::Scope(std::ios_base& ios)
    : d_ios(ios),
      d_dagThresh(getDagThresh(ios)),
      d_nodeDepth(getNodeDepth(ios)),
      d_outputLang(getOutputLang(ios))
{
}
Scope::~Scope() { apply(d_ios, d_dagThresh, d_nodeDepth, d_outputLang); }

}  // namespace cvc5::internal::options::ioutils
