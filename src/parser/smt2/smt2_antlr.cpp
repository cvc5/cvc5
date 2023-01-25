/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 constants.
 */
#include "parser/smt2/smt2_antlr.h"

namespace cvc5 {
namespace parser {

Smt2::Smt2(cvc5::Solver* solver,
           SymbolManager* sm,
           bool strictMode,
           bool isSygus)
    : Parser(), d_state(this, solver, sm, strictMode, isSygus)
{
}

ParserState* Smt2::getState() { return &d_state; }

Smt2::~Smt2() {}

Smt2State* Smt2::getSmt2State() { return &d_state; }

}  // namespace parser
}  // namespace cvc5
