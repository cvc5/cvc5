/*********************                                                        */
/*! \file tptp_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the TPTP output language
 **
 ** The pretty-printer interface for the TPTP output language.
 **/
#include "printer/tptp/tptp_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/expr.h"            // for ExprSetDepth etc..
#include "expr/node_manager.h"    // for VarNameAttr
#include "options/language.h"     // for LANG_AST
#include "options/smt_options.h"  // for unsat cores
#include "proof/unsat_core.h"
#include "smt/command.h"
#include "smt/node_command.h"
#include "smt/smt_engine.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace tptp {

void TptpPrinter::toStream(std::ostream& out,
                           TNode n,
                           int toDepth,
                           size_t dag) const
{
  n.toStream(out, toDepth, dag, language::output::LANG_SMTLIB_V2_5);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const CommandStatus* s) const
{
  s->toStream(out, language::output::LANG_SMTLIB_V2_5);
}/* TptpPrinter::toStream() */

void TptpPrinter::toStream(std::ostream& out, const smt::Model& m) const
{
  std::string statusName(m.isKnownSat() ? "FiniteModel"
                                        : "CandidateFiniteModel");
  out << "% SZS output start " << statusName << " for " << m.getInputName()
      << endl;
  this->Printer::toStreamUsing(language::output::LANG_SMTLIB_V2_5, out, m);
  out << "% SZS output end " << statusName << " for " << m.getInputName()
      << endl;
}

void TptpPrinter::toStreamModelSort(std::ostream& out,
                                    const smt::Model& m,
                                    TypeNode tn) const
{
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

void TptpPrinter::toStreamModelTerm(std::ostream& out,
                                    const smt::Model& m,
                                    Node n) const
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

}/* CVC4::printer::tptp namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */
