/*
 * smt_parser.h
 *
 *  Created on: Mar 5, 2010
 *      Author: chris
 */

#ifndef SMT_PARSER_H_
#define SMT_PARSER_H_

#include "parser/antlr_input.h"
#include "parser/smt/generated/SmtLexer.h"
#include "parser/smt/generated/SmtParser.h"

// extern void SmtParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class SmtInput : public AntlrInput {
public:
  SmtInput(ExprManager* exprManager, const std::string& filename, bool useMmap);
  SmtInput(ExprManager* exprManager, const std::string& input, const std::string& name);
  ~SmtInput();

protected:
  Command* doParseCommand() throw(ParserException);
  Expr doParseExpr() throw(ParserException);
  pANTLR3_LEXER getLexer();
  pANTLR3_LEXER createLexer(pANTLR3_INPUT_STREAM input);
  pANTLR3_PARSER createParser(pANTLR3_COMMON_TOKEN_STREAM tokenStream);

private:
  void init();
  pSmtLexer d_pSmtLexer;
  pSmtParser d_pSmtParser;
}; // class SmtInput
} // namespace parser

} // namespace CVC4

#endif /* SMT_PARSER_H_ */
