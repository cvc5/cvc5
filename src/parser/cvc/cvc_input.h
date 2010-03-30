/*
 * cvc_parser.h
 *
 *  Created on: Mar 5, 2010
 *      Author: chris
 */

#ifndef CVC_PARSER_H_
#define CVC_PARSER_H_

#include "parser/antlr_input.h"
#include "parser/cvc/generated/CvcLexer.h"
#include "parser/cvc/generated/CvcParser.h"

// extern void CvcParserSetAntlrParser(CVC4::parser::AntlrParser* newAntlrParser);

namespace CVC4 {

class Command;
class Expr;
class ExprManager;

namespace parser {

class CvcInput : public AntlrInput {
public:
  CvcInput(ExprManager* exprManager, const std::string& filename, bool useMmap);
  CvcInput(ExprManager* exprManager, const std::string& input, const std::string& name);
  ~CvcInput();

protected:
  Command* doParseCommand() throw(ParserException);
  Expr doParseExpr() throw(ParserException);
  pANTLR3_LEXER getLexer();
  pANTLR3_LEXER createLexer(pANTLR3_INPUT_STREAM input);
  pANTLR3_PARSER createParser(pANTLR3_COMMON_TOKEN_STREAM tokenStream);

private:
  void init();
  pCvcLexer d_pCvcLexer;
  pCvcParser d_pCvcParser;
}; // class CvcInput

} // namespace parser

} // namespace CVC4

#endif /* CVC_PARSER_H_ */
