/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
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

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__SMT2_H
#define CVC5__PARSER__SMT2_H

#include "api/cpp/cvc5.h"
#include "parser/parser.h"
#include "parser/smt2/smt2_state.h"

namespace cvc5 {
namespace parser {

/*
 * This class is deprecated and used only for the ANTLR parser.
 */
class Smt2 : public Parser
{
  friend class ParserBuilder;
 protected:
  Smt2(Solver* solver,
       SymbolManager* sm,
       bool strictMode = false,
       bool parseOnly = false,
       bool isSygus = false);
  /** get state */
  ParserState* getState() override;

 public:
  ~Smt2();
  /** Get the state */
  Smt2State* getSmt2State();

 private:
  /** The state object */
  Smt2State d_state;
}; /* class Smt2 */

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
