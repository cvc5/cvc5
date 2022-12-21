/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Francois Bobot, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of TPTP parser.
 */

#include "parser/tptp/tptp_antlr.h"

namespace cvc5 {
namespace parser {

Tptp::Tptp(cvc5::Solver* solver, SymbolManager* sm, bool strictMode)
    : Parser(), d_state(this, solver, sm, strictMode)
{
}

Tptp::~Tptp() {}
ParserState* Tptp::getState() { return &d_state; }
TptpState* Tptp::getTptpState() { return &d_state; }

}  // namespace parser
}  // namespace cvc5
