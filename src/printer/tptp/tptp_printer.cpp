/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The pretty-printer interface for the TPTP output language.
 */
#include "printer/tptp/tptp_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/node_manager.h"    // for VarNameAttr
#include "options/language.h"     // for LANG_AST
#include "options/smt_options.h"  // for unsat cores
#include "proof/unsat_core.h"

using namespace std;

namespace cvc5::internal {
namespace printer {
namespace tptp {

void TptpPrinter::toStream(std::ostream& out, TNode n) const
{
  options::ioutils::Scope scope(out);
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  n.toStream(out);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, Kind k) const
{
  options::ioutils::Scope scope(out);
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  out << k;
}

void TptpPrinter::toStream(std::ostream& out, const smt::Model& m) const
{
  std::string statusName(m.isKnownSat() ? "FiniteModel"
                                        : "CandidateFiniteModel");
  out << "% SZS output start " << statusName << " for " << m.getInputName()
      << endl;
  {
    options::ioutils::Scope scope(out);
    options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
    getPrinter(out)->toStream(out, m);
  }
  out << "% SZS output end " << statusName << " for " << m.getInputName()
      << endl;
}

void TptpPrinter::toStreamCmdSuccess(std::ostream& out) const
{
  getPrinter(Language::LANG_SMTLIB_V2_6)->toStreamCmdSuccess(out);
}

void TptpPrinter::toStreamCmdInterrupted(std::ostream& out) const
{
  getPrinter(Language::LANG_SMTLIB_V2_6)->toStreamCmdInterrupted(out);
}

void TptpPrinter::toStreamCmdUnsupported(std::ostream& out) const
{
  getPrinter(Language::LANG_SMTLIB_V2_6)->toStreamCmdUnsupported(out);
}

void TptpPrinter::toStreamCmdFailure(std::ostream& out,
                                     const std::string& message) const
{
  getPrinter(Language::LANG_SMTLIB_V2_6)->toStreamCmdFailure(out, message);
}

void TptpPrinter::toStreamCmdRecoverableFailure(
    std::ostream& out, const std::string& message) const
{
  getPrinter(Language::LANG_SMTLIB_V2_6)
      ->toStreamCmdRecoverableFailure(out, message);
}

void TptpPrinter::toStreamModelSort(std::ostream& out,
                                    TypeNode tn,
                                    const std::vector<Node>& elements) const
{
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

void TptpPrinter::toStreamModelTerm(std::ostream& out,
                                    const Node& n,
                                    const Node& value) const
{
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

void TptpPrinter::toStream(std::ostream& out, const UnsatCore& core) const
{
  out << "% SZS output start UnsatCore " << std::endl;
  if (core.useNames())
  {
    // use the names
    const std::vector<std::string>& cnames = core.getCoreNames();
    for (const std::string& cn : cnames)
    {
      out << cn << std::endl;
    }
  }
  else
  {
    // otherwise, use the formulas
    for (UnsatCore::const_iterator i = core.begin(); i != core.end(); ++i)
    {
      out << *i << endl;
    }
  }
  out << "% SZS output end UnsatCore " << std::endl;
}

}  // namespace tptp
}  // namespace printer
}  // namespace cvc5::internal
