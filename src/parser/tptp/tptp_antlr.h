/******************************************************************************
 * Top contributors (to current version):
 *   Francois Bobot, Andrew Reynolds, Mathias Preiner
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

#include "cvc5parser_private.h"
#include "parser/antlr_input.h"

#ifndef CVC5__PARSER__TPTP_ANTLR_H
#define CVC5__PARSER__TPTP_ANTLR_H

#include <cvc5/cvc5.h>

#include "parser/parse_op.h"
#include "parser/parser_antlr.h"
#include "parser/tptp/tptp.h"
#include "util/hash.h"

namespace cvc5 {
namespace parser {

/*
 * This class is deprecated and used only for the ANTLR parser.
 */
class Tptp : public Parser
{
  friend class ParserBuilder;

 protected:
  Tptp(cvc5::Solver* solver, SymbolManager* sm, bool strictMode = false);

  /** get state */
  ParserState* getState() override;

 public:
  ~Tptp();
  /** Get state */
  TptpState* getTptpState();

 private:
  /** The state */
  TptpState d_state;
}; /* class Tptp */

namespace tptp {
/**
 * Just exists to provide the uintptr_t constructor that ANTLR
 * requires.
 */
struct myExpr : public cvc5::Term
{
  myExpr() : cvc5::Term() {}
  myExpr(void*) : cvc5::Term() {}
  myExpr(const cvc5::Term& e) : cvc5::Term(e) {}
  myExpr(const myExpr& e) : cvc5::Term(e) {}
}; /* struct myExpr*/

enum NonAssoc
{
  NA_IFF,
  NA_IMPLIES,
  NA_REVIMPLIES,
  NA_REVIFF,
  NA_REVOR,
  NA_REVAND,
};

}  // namespace tptp

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__TPTP_INPUT_H */
