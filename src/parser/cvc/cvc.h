/*********************                                                        */
/*! \file cvc.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The parser class for the CVC language.
 **
 ** The parser class for the CVC language.
 **/

#include "cvc4parser_private.h"

#ifndef CVC4__PARSER__CVC_H
#define CVC4__PARSER__CVC_H

#include "api/cvc4cpp.h"
#include "parser/parser.h"
#include "smt/command.h"

namespace CVC4 {

namespace parser {

class Cvc : public Parser
{
  friend class ParserBuilder;

 public:
  void forceLogic(const std::string& logic) override;

 protected:
  Cvc(api::Solver* solver,
      Input* input,
      bool strictMode = false,
      bool parseOnly = false)
      : Parser(solver, input, strictMode, parseOnly)
  {
  }
};

}  // namespace parser
}  // namespace CVC4

#endif /* CVC4__PARSER__CVC_H */
