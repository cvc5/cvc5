/* *******************                                                        */
/*! \file Smt2.g
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Parser for SMT-LIB v2 input language.
 **
 ** Parser for SMT-LIB v2 input language.
 **/

grammar Smt2;

options {
  // C output for antlr
  language = 'C';

  // Skip the default error handling, just break with exceptions
  // defaultErrorHandler = false;

  // Only lookahead of <= k requested (disable for LL* parsing)
  // Note that CVC4's BoundedTokenBuffer requires a fixed k !
  // If you change this k, change it also in smt2_input.cpp !
  k = 2;
}/* options */

@header {
/**
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/
}/* @header */

@lexer::includes {

/** This suppresses warnings about the redefinition of token symbols between
  * different parsers. The redefinitions should be harmless as long as no
  * client: (a) #include's the lexer headers for two grammars AND (b) uses the
  * token symbol definitions.
  */
#pragma GCC system_header

/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#define ANTLR3_INLINE_INPUT_ASCII

#include "parser/antlr_tracing.h"

}/* @lexer::includes */

@lexer::postinclude {
#include <stdint.h>

#include "parser/smt2/smt2.h"
#include "parser/antlr_input.h"

using namespace CVC4;
using namespace CVC4::parser;

#undef PARSER_STATE
#define PARSER_STATE ((Smt2*)LEXER->super)
}/* @lexer::postinclude */

@parser::includes {
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/antlr_tracing.h"

namespace CVC4 {
  class Expr;

  namespace parser {
    namespace smt2 {
      /**
       * Just exists to provide the uintptr_t constructor that ANTLR
       * requires.
       */
      struct myExpr : public CVC4::Expr {
        myExpr() : CVC4::Expr() {}
        myExpr(void*) : CVC4::Expr() {}
        myExpr(const Expr& e) : CVC4::Expr(e) {}
        myExpr(const myExpr& e) : CVC4::Expr(e) {}
      };/* struct myExpr */
    }/* CVC4::parser::smt2 namespace */
  }/* CVC4::parser namespace */
}/* CVC4 namespace */

}/* @parser::includes */

@parser::postinclude {

#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/smt2/smt2.h"
#include "util/integer.h"
#include "util/output.h"
#include "util/rational.h"
#include <vector>

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Smt2*)PARSER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

}/* parser::postinclude */

/**
 * Parses an expression.
 * @return the parsed expression, or the Null Expr if we've reached the end of the input
 */
parseExpr returns [CVC4::parser::smt2::myExpr expr]
  : term[expr]
  | EOF
  ;

/**
 * Parses a command
 * @return the parsed command, or NULL if we've reached the end of the input
 */
parseCommand returns [CVC4::Command* cmd = NULL]
  : LPAREN_TOK c = command RPAREN_TOK { $cmd = c; }
  | EOF { $cmd = 0; }
  ;

/**
 * Parse the internal portion of the command, ignoring the surrounding parentheses.
 */
command returns [CVC4::Command* cmd = NULL]
@declarations {
  std::string name;
  std::vector<std::string> names;
  Expr expr;
  Type t;
  std::vector<Expr> terms;
  std::vector<Type> sorts;
  std::vector<std::pair<std::string, Type> > sortedVarNames;
  SExpr sexpr;
}
  : /* set the logic */
    SET_LOGIC_TOK SYMBOL
    { name = AntlrInput::tokenText($SYMBOL);
      Debug("parser") << "set logic: '" << name << "'" << std::endl;
      if( PARSER_STATE->strictModeEnabled() && PARSER_STATE->logicIsSet() ) {
        PARSER_STATE->parseError("Only one set-logic is allowed.");
      }
      PARSER_STATE->setLogic(name);
      $cmd = new SetBenchmarkLogicCommand(name); }
  | SET_INFO_TOK KEYWORD symbolicExpr[sexpr]
    { name = AntlrInput::tokenText($KEYWORD);
      PARSER_STATE->setInfo(name,sexpr);
      cmd = new SetInfoCommand(name,sexpr); }
  | /* get-info */
    GET_INFO_TOK KEYWORD
    { cmd = new GetInfoCommand(AntlrInput::tokenText($KEYWORD)); }
  | /* set-option */
    SET_OPTION_TOK KEYWORD symbolicExpr[sexpr]
    { name = AntlrInput::tokenText($KEYWORD);
      PARSER_STATE->setOption(name,sexpr);
      cmd = new SetOptionCommand(name,sexpr); }
  | /* get-option */
    GET_OPTION_TOK KEYWORD
    { cmd = new GetOptionCommand(AntlrInput::tokenText($KEYWORD)); }
  | /* sort declaration */
    DECLARE_SORT_TOK symbol[name,CHECK_UNDECLARED,SYM_SORT] n=INTEGER_LITERAL
    { Debug("parser") << "declare sort: '" << name
                      << "' arity=" << n << std::endl;
      unsigned arity = AntlrInput::tokenToUnsigned(n);
      if(arity == 0) {
        Type type = PARSER_STATE->mkSort(name);
        $cmd = new DeclareTypeCommand(name, 0, type);
      } else {
        Type type = PARSER_STATE->mkSortConstructor(name, arity);
        $cmd = new DeclareTypeCommand(name, arity, type);
      }
    }
  | /* sort definition */
    DEFINE_SORT_TOK symbol[name,CHECK_UNDECLARED,SYM_SORT]
    LPAREN_TOK symbolList[names,CHECK_NONE,SYM_SORT] RPAREN_TOK
    {
      PARSER_STATE->pushScope();
      for(std::vector<std::string>::const_iterator i = names.begin(),
            iend = names.end();
          i != iend;
          ++i) {
        sorts.push_back(PARSER_STATE->mkSort(*i));
      }
    }
    sortSymbol[t,CHECK_DECLARED]
    { PARSER_STATE->popScope();
      // Do NOT call mkSort, since that creates a new sort!
      // This name is not its own distinct sort, it's an alias.
      PARSER_STATE->defineParameterizedType(name, sorts, t);
      $cmd = new DefineTypeCommand(name, sorts, t);
    }
  | /* function declaration */
    DECLARE_FUN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    LPAREN_TOK sortList[sorts] RPAREN_TOK
    sortSymbol[t,CHECK_DECLARED]
    { Debug("parser") << "declare fun: '" << name << "'" << std::endl;
      if( sorts.size() > 0 ) {
        t = EXPR_MANAGER->mkFunctionType(sorts, t);
      }
      PARSER_STATE->mkVar(name, t);
      $cmd = new DeclareFunctionCommand(name, t); }
  | /* function definition */
    DEFINE_FUN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    sortSymbol[t,CHECK_DECLARED]
    { /* add variables to parser state before parsing term */
      Debug("parser") << "define fun: '" << name << "'" << std::endl;
      if( sortedVarNames.size() > 0 ) {
        std::vector<CVC4::Type> sorts;
        sorts.reserve(sortedVarNames.size());
        for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
              sortedVarNames.begin(), iend = sortedVarNames.end();
            i != iend;
            ++i) {
          sorts.push_back((*i).second);
        }
        t = EXPR_MANAGER->mkFunctionType(sorts, t);
      }
      PARSER_STATE->pushScope();
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end();
          i != iend;
          ++i) {
        terms.push_back(PARSER_STATE->mkVar((*i).first, (*i).second));
      }
    }
    term[expr]
    { PARSER_STATE->popScope();
      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      Expr func = PARSER_STATE->mkFunction(name, t);
      $cmd = new DefineFunctionCommand(name, func, terms, expr);
    }
  | /* value query */
    ( GET_VALUE_TOK |
      EVAL_TOK
      { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError("Strict compliance mode doesn't recognize \"eval\".  Maybe you want (get-value...)?");
        }
      } )
    LPAREN_TOK termList[terms,expr] RPAREN_TOK
    { if(terms.size() == 1) {
        $cmd = new GetValueCommand(terms[0]);
      } else {
        CommandSequence* seq = new CommandSequence();
        for(std::vector<Expr>::const_iterator i = terms.begin(),
              iend = terms.end();
            i != iend;
            ++i) {
          seq->addCommand(new GetValueCommand(*i));
        }
        $cmd = seq;
      }
    }
  | /* get-assignment */
    GET_ASSIGNMENT_TOK
    { cmd = new GetAssignmentCommand; }
  | /* assertion */
    ASSERT_TOK term[expr]
    { cmd = new AssertCommand(expr); }
  | /* checksat */
    CHECKSAT_TOK
    { cmd = new CheckSatCommand(MK_CONST(bool(true))); }
  | /* get-assertions */
    GET_ASSERTIONS_TOK
    { cmd = new GetAssertionsCommand; }
  | /* get-proof */
    GET_PROOF_TOK
    { cmd = new GetProofCommand; }
  | /* get-unsat-core */
    GET_UNSAT_CORE_TOK
    { UNSUPPORTED("unsat cores not yet supported"); }
  | /* push */
    PUSH_TOK
    ( k=INTEGER_LITERAL
      { unsigned n = AntlrInput::tokenToUnsigned(k);
        if(n == 0) {
          cmd = new EmptyCommand;
        } else if(n == 1) {
          cmd = new PushCommand;
        } else {
          CommandSequence* seq = new CommandSequence;
          do {
            seq->addCommand(new PushCommand);
          } while(--n > 0);
          cmd = seq;
        }
      }
    | { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError("Strict compliance mode demands an integer to be provided to PUSH.  Maybe you want (push 1)?");
        } else {
          cmd = new PushCommand;
        }
      } )
  | POP_TOK
    ( k=INTEGER_LITERAL
      { unsigned n = AntlrInput::tokenToUnsigned(k);
        if(n == 0) {
          cmd = new EmptyCommand;
        } else if(n == 1) {
          cmd = new PopCommand;
        } else {
          CommandSequence* seq = new CommandSequence;
          do {
            seq->addCommand(new PopCommand);
          } while(--n > 0);
          cmd = seq;
        }
      }
    | { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError("Strict compliance mode demands an integer to be provided to POP.  Maybe you want (pop 1)?");
        } else {
          cmd = new PopCommand;
        }
      } )
  | EXIT_TOK
    { cmd = new QuitCommand; }

    /* CVC4-extended SMT-LIBv2 commands */
  | extendedCommand[cmd]
    { if(PARSER_STATE->strictModeEnabled()) {
        PARSER_STATE->parseError("Extended commands are not permitted while operating in strict compliance mode.");
      }
    }
  ;

extendedCommand[CVC4::Command*& cmd]
@declarations {
  std::vector<CVC4::Datatype> dts;
  Type t;
  Expr e;
  SExpr sexpr;
  std::string name;
  std::vector<std::string> names;
  std::vector<Type> sorts;
}
    /* Z3's extended SMT-LIBv2 set of commands syntax */
  : DECLARE_DATATYPES_TOK
    { /* open a scope to keep the UnresolvedTypes contained */
      PARSER_STATE->pushScope(); }
    LPAREN_TOK ( LPAREN_TOK datatypeDef[dts] RPAREN_TOK )+ RPAREN_TOK
    { PARSER_STATE->popScope();
      cmd = new DatatypeDeclarationCommand(PARSER_STATE->mkMutualDatatypeTypes(dts)); }

  | DECLARE_SORTS_TOK
  | DECLARE_FUNS_TOK
    LPAREN_TOK
    ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE] nonemptySortList[sorts] RPAREN_TOK )+
    RPAREN_TOK
  | DECLARE_PREDS_TOK
    LPAREN_TOK
    ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE] sortList[sorts] RPAREN_TOK )+
    RPAREN_TOK
  | DEFINE_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE] term[e]
  | DEFINE_SORTS_TOK
    LPAREN_TOK
    ( LPAREN_TOK ( symbol[name,CHECK_UNDECLARED,SYM_SORT] LPAREN_TOK symbolList[names,CHECK_NONE,SYM_SORT] RPAREN_TOK |
                   symbol[name,CHECK_UNDECLARED,SYM_SORT] symbol[name,CHECK_NONE,SYM_SORT] ) RPAREN_TOK RPAREN_TOK )+
    RPAREN_TOK
  | DECLARE_CONST_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE] sortSymbol[t,CHECK_DECLARED]

  | SIMPLIFY_TOK term[e]
    { cmd = new SimplifyCommand(e); }
  | ECHO_TOK
    ( simpleSymbolicExpr[sexpr]
      { Message() << sexpr << std::endl; }
    | { Message() << std::endl; } )
    { cmd = new EmptyCommand; }
  ;

simpleSymbolicExpr[CVC4::SExpr& sexpr]
@declarations {
  CVC4::Kind k;
  std::string s;
}
  : INTEGER_LITERAL
    { sexpr = SExpr(AntlrInput::tokenToInteger($INTEGER_LITERAL)); }
  | DECIMAL_LITERAL
    { sexpr = SExpr(AntlrInput::tokenToRational($DECIMAL_LITERAL)); }
  | str[s]
    { sexpr = SExpr(s); }
  | SYMBOL
    { sexpr = SExpr(AntlrInput::tokenText($SYMBOL)); }
  | builtinOp[k]
    { std::stringstream ss;
      ss << Expr::setlanguage(CVC4::language::output::LANG_SMTLIB_V2) << EXPR_MANAGER->mkConst(k);
      sexpr = SExpr(ss.str());
    }
  | KEYWORD
    { sexpr = SExpr(AntlrInput::tokenText($KEYWORD)); }
  ;

symbolicExpr[CVC4::SExpr& sexpr]
@declarations {
  std::vector<SExpr> children;
}
  : simpleSymbolicExpr[sexpr]
  | LPAREN_TOK
    (symbolicExpr[sexpr] { children.push_back(sexpr); } )*
  	RPAREN_TOK
    { sexpr = SExpr(children); }
  ;

/**
 * Matches a term.
 * @return the expression representing the formula
 */
term[CVC4::Expr& expr]
@init {
  Debug("parser") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
  Kind kind;
  Expr op;
  std::string name;
  std::vector<Expr> args;
  SExpr sexpr;
}
  : /* a built-in operator application */
    LPAREN_TOK builtinOp[kind] termList[args,expr] RPAREN_TOK
    {
      if( kind == CVC4::kind::EQUAL &&
          args.size() > 0 &&
          args[0].getType() == EXPR_MANAGER->booleanType() ) {
        /* Use IFF for boolean equalities. */
        kind = CVC4::kind::IFF;
      }

      if( !PARSER_STATE->strictModeEnabled() &&
          (kind == CVC4::kind::AND || kind == CVC4::kind::OR) &&
          args.size() == 1) {
        /* Unary AND/OR can be replaced with the argument.
	       It just so happens expr should already by the only argument. */
        Assert( expr == args[0] );
      } else if( CVC4::kind::isAssociative(kind) &&
                 args.size() > EXPR_MANAGER->maxArity(kind) ) {
    	/* Special treatment for associative operators with lots of children */
        expr = EXPR_MANAGER->mkAssociative(kind,args);
      } else if( kind == CVC4::kind::MINUS && args.size() == 1 ) {
        expr = MK_EXPR(CVC4::kind::UMINUS, args[0]);
      } else {
        PARSER_STATE->checkOperator(kind, args.size());
        expr = MK_EXPR(kind, args);
      }
    }

  | /* A non-built-in function application */
    LPAREN_TOK
    functionName[name,CHECK_DECLARED]
    { PARSER_STATE->checkFunctionLike(name);
      const bool isDefinedFunction =
        PARSER_STATE->isDefinedFunction(name);
      if(isDefinedFunction) {
        expr = PARSER_STATE->getFunction(name);
        kind = CVC4::kind::APPLY;
      } else {
        expr = PARSER_STATE->getVariable(name);
        Type t = expr.getType();
        if( t.isConstructor() ){
          kind = CVC4::kind::APPLY_CONSTRUCTOR;
        }else if( t.isSelector() ){
          kind = CVC4::kind::APPLY_SELECTOR;
        }else if( t.isTester() ){
          kind = CVC4::kind::APPLY_TESTER;
        }else{
          kind = CVC4::kind::APPLY_UF;
        }
      }
      args.push_back(expr);
    }
    termList[args,expr] RPAREN_TOK
    { Debug("parser") << "args has size " << args.size() << std::endl << "expr is " << expr << std::endl;
      for(std::vector<Expr>::iterator i = args.begin(); i != args.end(); ++i)
        Debug("parser") << "++ " << *i << std::endl;
      expr = MK_EXPR(kind, args); }

  | /* An indexed function application */
    LPAREN_TOK indexedFunctionName[op] termList[args,expr] RPAREN_TOK
    { expr = MK_EXPR(op, args); }

  | /* a let binding */
    LPAREN_TOK LET_TOK LPAREN_TOK
    { PARSER_STATE->pushScope(); }
    ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE] term[expr] RPAREN_TOK
      { PARSER_STATE->defineVar(name,expr); } )+
    RPAREN_TOK
    term[expr]
    RPAREN_TOK
    { PARSER_STATE->popScope(); }

    /* a variable */
  | symbol[name,CHECK_DECLARED,SYM_VARIABLE]
    { const bool isDefinedFunction =
        PARSER_STATE->isDefinedFunction(name);
      if(isDefinedFunction) {
        expr = MK_EXPR(CVC4::kind::APPLY,
                       PARSER_STATE->getFunction(name));
      } else {
        expr = PARSER_STATE->getVariable(name);
        Type t = PARSER_STATE->getType(name);
        if(t.isConstructor() && ConstructorType(t).getArity() == 0) {
          // don't require parentheses, immediately turn it into an apply
          expr = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, expr);
        }
      }
    }

    /* attributed expressions */
  | LPAREN_TOK ATTRIBUTE_TOK term[expr] KEYWORD symbolicExpr[sexpr] RPAREN_TOK
    { std::string attr = AntlrInput::tokenText($KEYWORD);
      if(attr == ":named") {
        name = sexpr.getValue();
        // FIXME ensure expr is a closed subterm
        // check that sexpr is a fresh function symbol
        PARSER_STATE->checkDeclaration(name, CHECK_UNDECLARED, SYM_VARIABLE);
        // define it
        Expr func = PARSER_STATE->mkFunction(name, expr.getType());
        // bind name to expr with define-fun
        Command* c =
          new DefineNamedFunctionCommand(name, func, std::vector<Expr>(), expr);
        PARSER_STATE->preemptCommand(c);
      } else {
        std::stringstream ss;
        ss << "Attribute `" << attr << "' not supported";
        PARSER_STATE->parseError(ss.str());
      }
    }

    /* constants */
  | INTEGER_LITERAL
    { expr = MK_CONST( AntlrInput::tokenToInteger($INTEGER_LITERAL) ); }

  | DECIMAL_LITERAL
    { // FIXME: This doesn't work because an SMT rational is not a
      // valid GMP rational string
      expr = MK_CONST( AntlrInput::tokenToRational($DECIMAL_LITERAL) ); }

  | LPAREN_TOK INDEX_TOK bvLit=SYMBOL size=INTEGER_LITERAL RPAREN_TOK
    { if(AntlrInput::tokenText($bvLit).find("bv") == 0) {
        expr = MK_CONST( AntlrInput::tokenToBitvector($bvLit, $size) );
      } else {
        PARSER_STATE->parseError("Unexpected symbol `" + AntlrInput::tokenText($bvLit) + "'");
      }
    }

  | HEX_LITERAL
    { Assert( AntlrInput::tokenText($HEX_LITERAL).find("#x") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
      expr = MK_CONST( BitVector(hexString, 16) ); }

  | BINARY_LITERAL
    { Assert( AntlrInput::tokenText($BINARY_LITERAL).find("#b") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 2);
      expr = MK_CONST( BitVector(binString, 2) ); }

    // NOTE: Theory constants go here
  ;

/**
 * Matches a bit-vector operator (the ones parametrized by numbers)
 */
indexedFunctionName[CVC4::Expr& op]
  : LPAREN_TOK INDEX_TOK
    ( 'extract' n1=INTEGER_LITERAL n2=INTEGER_LITERAL
      { op = MK_CONST(BitVectorExtract(AntlrInput::tokenToUnsigned($n1),
                                       AntlrInput::tokenToUnsigned($n2))); }
    | 'repeat' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorRepeat(AntlrInput::tokenToUnsigned($n))); }
    | 'zero_extend' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorZeroExtend(AntlrInput::tokenToUnsigned($n))); }
    | 'sign_extend' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorSignExtend(AntlrInput::tokenToUnsigned($n))); }
    | 'rotate_left' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorRotateLeft(AntlrInput::tokenToUnsigned($n))); }
    | 'rotate_right' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorRotateRight(AntlrInput::tokenToUnsigned($n))); }
    | badIndexedFunctionName
   )
    RPAREN_TOK
  ;

/**
 * Matches an erroneous indexed function name (and args) for better
 * error reporting.
 */
badIndexedFunctionName
@declarations {
  std::string name;
}
  : symbol[name,CHECK_NONE,SYM_VARIABLE] INTEGER_LITERAL+
      { PARSER_STATE->parseError(std::string("Unknown indexed function `") + name + "'"); }
  ;

/**
 * Matches a sequence of terms and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with terms
 * @param expr an Expr reference for the elements of the sequence
 */
/* NOTE: We pass an Expr in here just to avoid allocating a fresh Expr every
 * time through this rule. */
termList[std::vector<CVC4::Expr>& formulas, CVC4::Expr& expr]
  : ( term[expr] { formulas.push_back(expr); } )+
  ;

/**
 * Matches a string, and strips off the quotes.
 */
str[std::string& s]
  : STRING_LITERAL
    { s = AntlrInput::tokenText($STRING_LITERAL);
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
    }
  ;

/**
* Matches a builtin operator symbol and sets kind to its associated Expr kind.
*/
builtinOp[CVC4::Kind& kind]
@init {
  Debug("parser") << "builtin: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : NOT_TOK      { $kind = CVC4::kind::NOT;     }
  | IMPLIES_TOK  { $kind = CVC4::kind::IMPLIES; }
  | AND_TOK      { $kind = CVC4::kind::AND;     }
  | OR_TOK       { $kind = CVC4::kind::OR;      }
  | XOR_TOK      { $kind = CVC4::kind::XOR;     }
  | EQUAL_TOK    { $kind = CVC4::kind::EQUAL;   }
  | DISTINCT_TOK { $kind = CVC4::kind::DISTINCT; }
  | ITE_TOK      { $kind = CVC4::kind::ITE; }
  | GREATER_THAN_TOK
                 { $kind = CVC4::kind::GT; }
  | GREATER_THAN_EQUAL_TOK
                 { $kind = CVC4::kind::GEQ; }
  | LESS_THAN_EQUAL_TOK
                 { $kind = CVC4::kind::LEQ; }
  | LESS_THAN_TOK
                 { $kind = CVC4::kind::LT; }
  | PLUS_TOK     { $kind = CVC4::kind::PLUS; }
  | MINUS_TOK    { $kind = CVC4::kind::MINUS; }
  | STAR_TOK     { $kind = CVC4::kind::MULT; }
  | DIV_TOK      { $kind = CVC4::kind::DIVISION; }
  | INTS_DIV_TOK      { $kind = CVC4::kind::INTS_DIVISION; }
  | INTS_MOD_TOK      { $kind = CVC4::kind::INTS_MODULUS; }

  | SELECT_TOK   { $kind = CVC4::kind::SELECT; }
  | STORE_TOK    { $kind = CVC4::kind::STORE; }

  | CONCAT_TOK   { $kind = CVC4::kind::BITVECTOR_CONCAT; }
  | BVNOT_TOK   { $kind = CVC4::kind::BITVECTOR_NOT; }
  | BVAND_TOK   { $kind = CVC4::kind::BITVECTOR_AND; }
  | BVOR_TOK   { $kind = CVC4::kind::BITVECTOR_OR; }
  | BVNEG_TOK   { $kind = CVC4::kind::BITVECTOR_NEG; }
  | BVADD_TOK   { $kind = CVC4::kind::BITVECTOR_PLUS; }
  | BVMUL_TOK   { $kind = CVC4::kind::BITVECTOR_MULT; }
  | BVUDIV_TOK   { $kind = CVC4::kind::BITVECTOR_UDIV; }
  | BVUREM_TOK   { $kind = CVC4::kind::BITVECTOR_UREM; }
  | BVSHL_TOK     { $kind = CVC4::kind::BITVECTOR_SHL; }
  | BVLSHR_TOK     { $kind = CVC4::kind::BITVECTOR_LSHR; }
  | BVULT_TOK     { $kind = CVC4::kind::BITVECTOR_ULT; }
  | BVNAND_TOK     { $kind = CVC4::kind::BITVECTOR_NAND; }
  | BVNOR_TOK     { $kind = CVC4::kind::BITVECTOR_NOR; }
  | BVXOR_TOK     { $kind = CVC4::kind::BITVECTOR_XOR; }
  | BVXNOR_TOK     { $kind = CVC4::kind::BITVECTOR_XNOR; }
  | BVCOMP_TOK     { $kind = CVC4::kind::BITVECTOR_COMP; }
  | BVSUB_TOK     { $kind = CVC4::kind::BITVECTOR_SUB; }
  | BVSDIV_TOK     { $kind = CVC4::kind::BITVECTOR_SDIV; }
  | BVSREM_TOK     { $kind = CVC4::kind::BITVECTOR_SREM; }
  | BVSMOD_TOK     { $kind = CVC4::kind::BITVECTOR_SMOD; }
  | BVASHR_TOK     { $kind = CVC4::kind::BITVECTOR_ASHR; }
  | BVULE_TOK     { $kind = CVC4::kind::BITVECTOR_ULE; }
  | BVUGT_TOK     { $kind = CVC4::kind::BITVECTOR_UGT; }
  | BVUGE_TOK     { $kind = CVC4::kind::BITVECTOR_UGE; }
  | BVSLT_TOK     { $kind = CVC4::kind::BITVECTOR_SLT; }
  | BVSLE_TOK     { $kind = CVC4::kind::BITVECTOR_SLE; }
  | BVSGT_TOK     { $kind = CVC4::kind::BITVECTOR_SGT; }
  | BVSGE_TOK     { $kind = CVC4::kind::BITVECTOR_SGE; }

  // NOTE: Theory operators go here
  ;

/**
 * Matches a (possibly undeclared) function symbol (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[std::string& name, CVC4::parser::DeclarationCheck check]
  : symbol[name,check,SYM_VARIABLE]
  ;

/**
 * Matches an previously declared function symbol (returning an Expr)
 */
functionSymbol[CVC4::Expr& fun]
@declarations {
	std::string name;
}
  : functionName[name,CHECK_DECLARED]
    { PARSER_STATE->checkFunctionLike(name);
      fun = PARSER_STATE->getVariable(name); }
  ;

/**
 * Matches a sequence of sort symbols and fills them into the given
 * vector.
 */
sortList[std::vector<CVC4::Type>& sorts]
@declarations {
  Type t;
}
  : ( sortSymbol[t,CHECK_DECLARED] { sorts.push_back(t); } )*
  ;

nonemptySortList[std::vector<CVC4::Type>& sorts]
@declarations {
  Type t;
}
  : ( sortSymbol[t,CHECK_DECLARED] { sorts.push_back(t); } )+
  ;

/**
 * Matches a sequence of (variable,sort) symbol pairs and fills them
 * into the given vector.
 */
sortedVarList[std::vector<std::pair<std::string, CVC4::Type> >& sortedVars]
@declarations {
  std::string name;
  Type t;
}
  : ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE] sortSymbol[t,CHECK_DECLARED] RPAREN_TOK
      { sortedVars.push_back(make_pair(name, t)); }
    )*
  ;

/**
 * Matches the sort symbol, which can be an arbitrary symbol.
 * @param check the check to perform on the name
 */
sortName[std::string& name, CVC4::parser::DeclarationCheck check]
  : symbol[name,check,SYM_SORT]
  ;

sortSymbol[CVC4::Type& t, CVC4::parser::DeclarationCheck check]
@declarations {
  std::string name;
  std::vector<CVC4::Type> args;
  std::vector<uint64_t> numerals;
}
  : sortName[name,CHECK_NONE]
  	{ 
  	  if( check == CHECK_DECLARED || PARSER_STATE->isDeclared(name, SYM_SORT) ){ 
  	    t = PARSER_STATE->getSort(name);                                          
  	  }else{                                                                    
  	    t = PARSER_STATE->mkUnresolvedType(name);                                 
  	  }                                          
  	}
  | LPAREN_TOK INDEX_TOK symbol[name,CHECK_NONE,SYM_SORT] nonemptyNumeralList[numerals] RPAREN_TOK
    {
      if( name == "BitVec" ) {
        if( numerals.size() != 1 ) {
          PARSER_STATE->parseError("Illegal bitvector type.");
        }
        t = EXPR_MANAGER->mkBitVectorType(numerals.front());
      } else {
        Unhandled(name);
      }
    }
  | LPAREN_TOK symbol[name,CHECK_NONE,SYM_SORT] sortList[args] RPAREN_TOK
    {
      if( name == "Array" ) {
        if( args.size() != 2 ) {
          PARSER_STATE->parseError("Illegal array type.");
        }
        t = EXPR_MANAGER->mkArrayType( args[0], args[1] );
      } else {
        t = PARSER_STATE->getSort(name, args);
      }
    }
  ;

/**
 * Matches a list of symbols, with check and type arguments as for the
 * symbol[] rule below.
 */
symbolList[std::vector<std::string>& names,
           CVC4::parser::DeclarationCheck check,
           CVC4::parser::SymbolType type]
@declarations {
  std::string id;
}
  : ( symbol[id,check,type] { names.push_back(id); } )*
  ;

/**
 * Matches an symbol and sets the string reference parameter id.
 * @param id string to hold the symbol
 * @param check what kinds of check to do on the symbol
 * @param type the intended namespace for the symbol
 */
symbol[std::string& id,
       CVC4::parser::DeclarationCheck check,
       CVC4::parser::SymbolType type]
  : SYMBOL
    { id = AntlrInput::tokenText($SYMBOL);
      Debug("parser") << "symbol: " << id
                      << " check? " << check
                      << " type? " << type << std::endl;
      PARSER_STATE->checkDeclaration(id, check, type); }
  ;

/**
 * Matches a nonempty list of numerals.
 * @param numerals the (empty) vector to house the numerals.
 */
nonemptyNumeralList[std::vector<uint64_t>& numerals]
  : ( INTEGER_LITERAL
      { numerals.push_back(AntlrInput::tokenToUnsigned($INTEGER_LITERAL)); }
    )+
  ;

/**
 * Parses a datatype definition
 */
datatypeDef[std::vector<CVC4::Datatype>& datatypes]
@init {
  std::string id, id2;
  Type t;
  std::vector< Type > params;
}
    /* This really needs to be CHECK_NONE, or mutually-recursive
     * datatypes won't work, because this type will already be
     * "defined" as an unresolved type; don't worry, we check
     * below. */
  : symbol[id,CHECK_NONE,SYM_SORT] { PARSER_STATE->pushScope(); }
    ( '[' symbol[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2);
        params.push_back( t );
      }
      ( symbol[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2);
        params.push_back( t ); }
      )* ']'
    )?
    { datatypes.push_back(Datatype(id,params));
      if(!PARSER_STATE->isUnresolvedType(id)) {
        // if not unresolved, must be undeclared
        PARSER_STATE->checkDeclaration(id, CHECK_UNDECLARED, SYM_SORT);
      }
    }
    ( LPAREN_TOK constructorDef[datatypes.back()] RPAREN_TOK )+
    { PARSER_STATE->popScope(); }
  ;

/**
 * Parses a constructor defintion for type
 */
constructorDef[CVC4::Datatype& type]
@init {
  std::string id;
  CVC4::DatatypeConstructor* ctor = NULL;
}
  : symbol[id,CHECK_UNDECLARED,SYM_SORT]
    { // make the tester
      std::string testerId("is_");
      testerId.append(id);
      PARSER_STATE->checkDeclaration(testerId, CHECK_UNDECLARED, SYM_SORT);
      ctor = new CVC4::DatatypeConstructor(id, testerId);
    }
    ( LPAREN_TOK selector[*ctor] RPAREN_TOK )*
    { // make the constructor
      type.addConstructor(*ctor);
      Debug("parser-idt") << "constructor: " << id.c_str() << std::endl;
      delete ctor;
    }
  ;

selector[CVC4::DatatypeConstructor& ctor]
@init {
  std::string id;
  Type t, t2;
}
  : symbol[id,CHECK_UNDECLARED,SYM_SORT] sortSymbol[t,CHECK_NONE]
    { ctor.addArg(id, t);
      Debug("parser-idt") << "selector: " << id.c_str() << std::endl;
    }
  ;

// Base SMT-LIB tokens
ASSERT_TOK : 'assert';
CHECKSAT_TOK : 'check-sat';
DECLARE_FUN_TOK : 'declare-fun';
DECLARE_SORT_TOK : 'declare-sort';
DEFINE_FUN_TOK : 'define-fun';
DEFINE_SORT_TOK : 'define-sort';
GET_VALUE_TOK : 'get-value';
GET_ASSIGNMENT_TOK : 'get-assignment';
GET_ASSERTIONS_TOK : 'get-assertions';
GET_PROOF_TOK : 'get-proof';
GET_UNSAT_CORE_TOK : 'get-unsat-core';
EXIT_TOK : 'exit';
ITE_TOK : 'ite';
LET_TOK : 'let';
ATTRIBUTE_TOK : '!';
LPAREN_TOK : '(';
RPAREN_TOK : ')';
INDEX_TOK : '_';
SET_LOGIC_TOK : 'set-logic';
SET_INFO_TOK : 'set-info';
GET_INFO_TOK : 'get-info';
SET_OPTION_TOK : 'set-option';
GET_OPTION_TOK : 'get-option';
PUSH_TOK : 'push';
POP_TOK : 'pop';

// extended commands
DECLARE_DATATYPES_TOK : 'declare-datatypes';
DECLARE_SORTS_TOK : 'declare-sorts';
DECLARE_FUNS_TOK : 'declare-funs';
DECLARE_PREDS_TOK : 'declare-preds';
DEFINE_TOK : 'define';
DEFINE_SORTS_TOK : 'define-sorts';
DECLARE_CONST_TOK : 'declare-const';
SIMPLIFY_TOK : 'simplify';
EVAL_TOK : 'eval';
ECHO_TOK : 'echo';

// operators (NOTE: theory symbols go here)
AMPERSAND_TOK     : '&';
AND_TOK           : 'and';
AT_TOK            : '@';
DISTINCT_TOK      : 'distinct';
DIV_TOK           : '/';
EQUAL_TOK         : '=';
EXISTS_TOK        : 'exists';
FORALL_TOK        : 'forall';
GREATER_THAN_TOK  : '>';
GREATER_THAN_EQUAL_TOK  : '>=';
IMPLIES_TOK       : '=>';
LESS_THAN_TOK     : '<';
LESS_THAN_EQUAL_TOK     : '<=';
MINUS_TOK         : '-';
NOT_TOK           : 'not';
OR_TOK            : 'or';
// PERCENT_TOK       : '%';
PLUS_TOK          : '+';
POUND_TOK         : '#';
SELECT_TOK        : 'select';
STAR_TOK          : '*';
STORE_TOK         : 'store';
// TILDE_TOK         : '~';
XOR_TOK           : 'xor';

INTS_DIV_TOK : 'div';
INTS_MOD_TOK : 'mod';

CONCAT_TOK : 'concat';
BVNOT_TOK : 'bvnot';
BVAND_TOK : 'bvand';
BVOR_TOK : 'bvor';
BVNEG_TOK : 'bvneg';
BVADD_TOK : 'bvadd';
BVMUL_TOK : 'bvmul';
BVUDIV_TOK : 'bvudiv';
BVUREM_TOK : 'bvurem';
BVSHL_TOK : 'bvshl';
BVLSHR_TOK : 'bvlshr';
BVULT_TOK : 'bvult';
BVNAND_TOK : 'bvnand';
BVNOR_TOK : 'bvnor';
BVXOR_TOK : 'bvxor';
BVXNOR_TOK : 'bvxnor';
BVCOMP_TOK : 'bvcomp';
BVSUB_TOK : 'bvsub';
BVSDIV_TOK : 'bvsdiv';
BVSREM_TOK : 'bvsrem';
BVSMOD_TOK : 'bvsmod';
BVASHR_TOK : 'bvashr';
BVULE_TOK : 'bvule';
BVUGT_TOK : 'bvugt';
BVUGE_TOK : 'bvuge';
BVSLT_TOK : 'bvslt';
BVSLE_TOK : 'bvsle';
BVSGT_TOK : 'bvsgt';
BVSGE_TOK : 'bvsge';

/**
 * Matches a symbol from the input. A symbol is a "simple" symbol or a
 * sequence of printable ASCII characters that starts and ends with | and
 * does not otherwise contain |.
 */
SYMBOL
  : SIMPLE_SYMBOL
  | '|' ~('|')+ '|'
  ;

/**
 * Matches a keyword from the input. A keyword is a simple symbol prefixed
 * with a colon.
 */
KEYWORD
  : ':' SIMPLE_SYMBOL
  ;

/** Matches a "simple" symbol: a non-empty sequence of letters, digits and
 * the characters + - / * = % ? ! . $ ~ & ^ < > @ that does not start with a
 * digit, and is not the special reserved symbol '_'.
 */
fragment SIMPLE_SYMBOL
  : (ALPHA | SYMBOL_CHAR) (ALPHA | DIGIT | SYMBOL_CHAR)+
  | ALPHA
  | SYMBOL_CHAR_NOUNDERSCORE
  ;

/**
 * Matches and skips whitespace in the input.
 */
WHITESPACE
  : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); }
  ;

/**
 * Matches an integer constant from the input (non-empty sequence of
 * digits, with no leading zeroes).
 */
INTEGER_LITERAL
  : NUMERAL
  ;

/**
 * Match an integer constant. In non-strict mode, this is any sequence
 * of digits. In strict mode, non-zero integers can't have leading
 * zeroes.
 */
fragment NUMERAL
@init {
  char *start = (char*) GETCHARINDEX();
}
  : DIGIT+
    { Debug("parser-extra") << "NUMERAL: "
       << (uintptr_t)start << ".." << GETCHARINDEX()
       << " strict? " << (bool)(PARSER_STATE->strictModeEnabled())
       << " ^0? " << (bool)(*start == '0')
       << " len>1? " << (bool)(start < (char*)(GETCHARINDEX() - 1))
       << std::endl; }
    { !PARSER_STATE->strictModeEnabled() ||
      *start != '0' ||
      start == (char*)(GETCHARINDEX() - 1) }?
  ;

/**
 * Matches a decimal constant from the input.
 */
DECIMAL_LITERAL
  : NUMERAL '.' DIGIT+
  ;

/**
 * Matches a hexadecimal constant.
 */
HEX_LITERAL
  : '#x' HEX_DIGIT+
  ;

/**
 * Matches a binary constant.
 */
BINARY_LITERAL
  : '#b' ('0' | '1')+
  ;


/**
 * Matches a double quoted string literal. Escaping is supported, and
 * escape character '\' has to be escaped.
 */
STRING_LITERAL
  : '"' (ESCAPE | ~('"'|'\\'))* '"'
  ;

/**
 * Matches the comments and ignores them
 */
COMMENT
  : ';' (~('\n' | '\r'))* { SKIP(); }
  ;

/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment
ALPHA
  : 'a'..'z'
  | 'A'..'Z'
  ;

/**
 * Matches the digits (0-9)
 */
fragment DIGIT : '0'..'9';

fragment HEX_DIGIT : DIGIT | 'a'..'f' | 'A'..'F';

/**
 * Matches the characters that may appear in a "symbol" (i.e., an identifier)
 */
fragment SYMBOL_CHAR_NOUNDERSCORE
  : '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '~'
  | '&' | '^' | '<' | '>' | '@'
  ;

fragment SYMBOL_CHAR
  : SYMBOL_CHAR_NOUNDERSCORE | '_'
  ;

/**
 * Matches an allowed escaped character.
 */
fragment ESCAPE : '\\' ('"' | '\\' | 'n' | 't' | 'r');
