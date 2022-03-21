/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Encapsulation of the result of a query.
 */
#include "util/result.h"

#include <algorithm>
#include <cctype>
#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "options/io_utils.h"

using namespace std;

namespace cvc5 {

SynthResult::SynthResult()
    : d_status(NONE), d_unknownExplanation(Result::UNKNOWN_REASON)
{
}

SynthResult::SynthResult(const std::vector<Node>& sol)
    : d_status(SUCCESS), d_unknownExplanation(UNKNOWN_REASON), d_solution(sol)
{
}

SynthResult::SynthResult(Status s,
               Result::UnknownExplanation unknownExplanation)
    : d_status(s),
      d_unknownExplanation(unknownExplanation)
{
  PrettyCheckArgument(s == UNKNOWN,
                      "improper use of unknown-result constructor");
}
Status SynthResult::getStatus() const { return d_status; }

Result::UnknownExplanation SynthResult::getUnknownExplanation() const { return d_unknownExplanation; }

const std::vector<Node>& SynthResult::getSolution() const { return d_solution; }

ostream& operator<<(ostream& out, SynthResult::Status s)
{
  switch (s) {
    case SynthResult::NONE: out << "NONE"; break;
    case SynthResult::SUCCESS:
      out << "SUCCESS";
      break;
    case SynthResult::FAIL:
      out << "FAIL";
      break;
    case SynthResult::UNKNOWN: out << "UNKNOWN"; break;
    default: Unhandled() << s;
  }
  return out;
}

ostream& operator<<(ostream& out, enum SynthResult::UnknownExplanation e)
{
  switch (e)
  {
    case SynthResult::REQUIRES_FULL_CHECK: out << "REQUIRES_FULL_CHECK"; break;
    case SynthResult::INCOMPLETE: out << "INCOMPLETE"; break;
    case SynthResult::TIMEOUT: out << "TIMEOUT"; break;
    case SynthResult::RESOURCEOUT: out << "RESOURCEOUT"; break;
    case SynthResult::MEMOUT: out << "MEMOUT"; break;
    case SynthResult::INTERRUPTED: out << "INTERRUPTED"; break;
    case SynthResult::NO_STATUS: out << "NO_STATUS"; break;
    case SynthResult::UNSUPPORTED: out << "UNSUPPORTED"; break;
    case SynthResult::OTHER: out << "OTHER"; break;
    case SynthResult::UNKNOWN_REASON: out << "UNKNOWN_REASON"; break;
    default: Unhandled() << e;
  }
  return out;
}

ostream& operator<<(ostream& out, const SynthResult& r) {
  Language language = options::ioutils::getOutputLang(out);
  switch (language) {
    case Language::LANG_SYGUS_V2: r.toStreamSmt2(out); break;
    case Language::LANG_TPTP: r.toStreamTptp(out); break;
    default:
      if (language::isLangSmt2(language))
      {
        r.toStreamSmt2(out);
      }
      else
      {
        r.toStreamDefault(out);
      }
  };
  return out;
}

}  // namespace cvc5
