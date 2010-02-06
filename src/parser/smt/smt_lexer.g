/* *******************                                                        */
/*  smt_lexer.g
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Lexer for SMT-LIB input language.
 **/

options {
  language = "Cpp";            // C++ output for antlr
  namespaceStd  = "std";       // Cosmetic option to get rid of long defines in generated code
  namespaceAntlr = "antlr";    // Cosmetic option to get rid of long defines in generated code
  namespace = "CVC4::parser";  // Wrap everything in the smtparser namespace
}

/**
 * AntlrSmtLexer class is a stream tokenizer (lexer) for the SMT-LIB benchmark
 * language.
 */
class AntlrSmtLexer extends Lexer;

options {
  exportVocab = SmtVocabulary;  // Name of the shared token vocabulary
  testLiterals = false;         // Do not check for literals by default
  defaultErrorHandler = false;  // Skip the default error handling, just break with exceptions
  k = 2;
}

tokens {
  // Base SMT-LIB tokens
  DISTINCT      = "distinct";
  ITE           = "ite";
  IF_THEN_ELSE  = "if_then_else";
  TRUE          = "true";
  FALSE         = "false";
  NOT           = "not";
  IMPLIES       = "implies";
  AND           = "and";
  OR            = "or";
  XOR           = "xor";
  IFF           = "iff";
  EXISTS        = "exists";
  FORALL        = "forall";
  LET           = "let";
  FLET          = "flet";
  THEORY        = "theory";
  LOGIC         = "logic";
  SAT           = "sat";
  UNSAT         = "unsat";
  UNKNOWN       = "unknown";
  BENCHMARK     = "benchmark";
  // The SMT attribute tokens
  LOGIC_ATTR       = ":logic";
  ASSUMPTION_ATTR  = ":assumption";
  FORMULA_ATTR     = ":formula";
  STATUS_ATTR      = ":status";
  EXTRASORTS_ATTR  = ":extrasorts";
  EXTRAFUNS_ATTR   = ":extrafuns";
  EXTRAPREDS_ATTR  = ":extrapreds";
  C_NOTES       = ":notes";
  // arithmetic symbols
  EQUAL         = "=";
  LESS_THAN     = "<";
  GREATER_THAN  = ">";
  AMPERSAND     = "&";
  AT            = "@";
  POUND         = "#";
  PLUS          = "+";
  MINUS         = "-";
  STAR          = "*";
  DIV           = "/";
  PERCENT       = "%";
  PIPE          = "|";
  TILDE         = "~";
}

/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
protected
ALPHA options { paraphrase = "a letter"; }
  :  'a'..'z'
  |  'A'..'Z'
  ;

/**
 * Matches the digits (0-9)
 */
protected
DIGIT options { paraphrase = "a digit"; }
  :   '0'..'9'
  ;

/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER options { paraphrase = "an identifier"; testLiterals = true; }
  :  ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*
  ;

/**
 * Matches an identifier starting with a colon. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a colon.
 */
C_IDENTIFIER options { paraphrase = "an identifier starting with a colon"; testLiterals = true; }
  :  ':' ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*
  ;

/**
 * Matches the value of user-defined annotations or attributes. The only constraint imposed on a user-defined value is that it start with
 * an open brace and end with closed brace.
 */
USER_VALUE
  :   '{'
      ( '\n' { newline(); }
      | ~('{' | '}' | '\n')
        )*
    '}'
  ;

/**
 * Matches the question mark symbol ('?').
 */
QUESTION_MARK options { paraphrase = "a question mark '?'"; }
  :  '?'
  ;

/**
 * Matches the dollar sign ('$').
 */
DOLLAR_SIGN options { paraphrase = "a dollar sign '$'"; }
  :  '$'
  ;

/**
 * Matches the left bracket ('(').
 */
LPAREN options { paraphrase = "a left parenthesis '('"; }
  :   '(';

/**
 * Matches the right bracket ('(').
 */
RPAREN options { paraphrase = "a right parenthesis ')'"; }
  :   ')';

/**
 * Matches and skips whitespace in the input.
 */
WHITESPACE options { paraphrase = "whitespace"; }
  :  (' ' | '\t' | '\f')              { $setType(antlr::Token::SKIP); }
  ;

/**
 * Matches and skips the newline symbols in the input.
 */
NEWLINE options { paraphrase = "a newline"; }
  :   ('\r' '\n' | '\r' | '\n')       { $setType(antlr::Token::SKIP); newline(); }
  ;

/**
 * Matches a numeral from the input (non-empty sequence of digits).
 */
NUMERAL options { paraphrase = "a numeral"; }
  :  (DIGIT)+
  ;

/**
 * Matches an allowed escaped character.
 */
protected ESCAPE
  : '\\' ('"' | '\\' | 'n' | 't' | 'r')
  ;

/**
 * Matches a double quoted string literal. Escaping is supported, and escape
 * character '\' has to be escaped.
 */
STRING_LITERAL options { paraphrase = "a string literal"; }
  :  '"' (ESCAPE | ~('"'|'\\'))* '"'
  ;

/**
 * Matches the comments and ignores them
 */
COMMENT options { paraphrase = "comment"; }
  : ';' (~('\n' | '\r'))*                    { $setType(antlr::Token::SKIP); }
  ;

/* Arithmetic symbol tokens */
EQUAL :   "=";
LESS_THAN : "<";
GREATER_THAN : ">";
AMPERSAND :  "&";
AT :  "@";
POUND :  "#";
PLUS :  "+";
MINUS :  "-";
STAR :  "*";
DIV :  "/";
PERCENT :  "%";
PIPE :  "|";
TILDE : "~";
