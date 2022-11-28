/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 tokens.
 */

#include "parser/flex/smt2_parser.h"

#include "base/output.h"

namespace cvc5 {
namespace parser {

Smt2Parser::Smt2Parser(Solver* solver, SymbolManager* sm, bool strictMode, bool isSygus)
    : FlexParser(solver, sm),
      d_isSygus(isSygus),
      d_slex(),
      d_state(this, solver, sm, strictMode, isSygus),
      d_termParser(d_slex),
      d_cmdParser(d_slex, d_termParser)
{
  d_lex = &d_slex;
}
Command* Smt2Parser::nextCommand() { return d_cmdParser.nextCommand(); }

Term Smt2Parser::nextExpression() { return d_termParser.nextExpression(); }

}  // namespace parser
}  // namespace cvc5
