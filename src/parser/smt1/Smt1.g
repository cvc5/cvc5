/* *******************                                                        */
/*! \file Smt1.g
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Parser for SMT-LIB input language.
 **
 ** Parser for SMT-LIB input language.
 **/

grammar Smt1;

options {
  // C output for antlr
  language = 'C';

  // Skip the default error handling, just break with exceptions
  // defaultErrorHandler = false;

  // Only lookahead of <= k requested (disable for LL* parsing)
  // Note that CVC4's BoundedTokenBuffer requires a fixed k !
  // If you change this k, change it also in smt1_input.cpp !
  k = 2;
}/* options */

@header {
/**
 ** This file is part of CVC4.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/
}/* @header */

@lexer::includes {

// This should come immediately after #include <antlr3.h> in the generated
// files. See the documentation in "parser/antlr_undefines.h" for more details.
#include "parser/antlr_undefines.h"

/** This suppresses warnings about the redefinition of token symbols between
  * different parsers. The redefinitions should be harmless as long as no
  * client: (a) #include's the lexer headers for two grammars AND (b) uses the
  * token symbol definitions.
  */
#pragma GCC system_header

#if defined(CVC4_COMPETITION_MODE) && !defined(CVC4_SMTCOMP_APPLICATION_TRACK)
/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#  define ANTLR3_INLINE_INPUT_ASCII
#  define ANTLR3_INLINE_INPUT_8BIT
#endif /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */

#include "parser/antlr_tracing.h"
}/* @lexer::includes */

@parser::includes {

// This should come immediately after #include <antlr3.h> in the generated
// files. See the documentation in "parser/antlr_undefines.h" for more details.
#include "parser/antlr_undefines.h"

#include <stdint.h>

#include "base/ptr_closer.h"
#include "smt/command.h"
#include "parser/parser.h"
#include "parser/antlr_tracing.h"

namespace CVC4 {
  class Expr;

  namespace parser {
    namespace smt1 {
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

      /**
       * Just exists to provide the uintptr_t constructor that ANTLR
       * requires.
       */
      struct myType : public CVC4::Type {
        myType() : CVC4::Type() {}
        myType(void*) : CVC4::Type() {}
        myType(const Type& t) : CVC4::Type(t) {}
        myType(const myType& t) : CVC4::Type(t) {}
      };/* struct myType */
    }/* CVC4::parser::smt1 namespace */
  }/* CVC4::parser namespace */
}/* CVC4 namespace */

}/* @parser::includes */

@parser::postinclude {

#include <vector>

#include "base/output.h"
#include "base/ptr_closer.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/smt1/smt1.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Smt1*)PARSER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst

}/* @parser::postinclude */


/**
 * Parses an expression.
 * @return the parsed expression
 */
parseExpr returns [CVC4::parser::smt1::myExpr expr]
  : annotatedFormula[expr]
  | EOF
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd_return = NULL]
@declarations {
  CVC4::PtrCloser<CVC4::Command> cmd;
}
@after {
  cmd_return = cmd.release();
}
  : b = benchmark[&cmd]
  | LPAREN_TOK c=IDENTIFIER
    { std::string s = AntlrInput::tokenText($c);
      if(s == "set" || s == "get") {
        PARSER_STATE->parseError(std::string("In SMT-LIBv1 mode, expected keyword `benchmark', but it looks like you're writing SMT-LIBv2.  Use --lang smt for SMT-LIBv2."));
      } else {
        PARSER_STATE->parseError(std::string("expected keyword `benchmark', got `" + s + "'"));
      }
    }
  ;

/**
 * Matches the whole SMT-LIB benchmark.
 * @return the sequence command containing the whole problem
 */
benchmark [CVC4::PtrCloser<CVC4::Command>* cmd]
  : LPAREN_TOK BENCHMARK_TOK IDENTIFIER benchAttributes[cmd] RPAREN_TOK
  | EOF
  ;

/**
 * Matches a sequence of benchmark attributes and returns a pointer to a
 * command sequence.
 * @return the command sequence
 */
benchAttributes [CVC4::PtrCloser<CVC4::Command>* cmd]
@init {
  CVC4::PtrCloser<CVC4::CommandSequence> cmd_seq(new CommandSequence());
  CVC4::PtrCloser<CVC4::Command> attribute;
}
@after {
  cmd->reset(cmd_seq.release());
}
  : (benchAttribute[&attribute]
     { if (attribute) cmd_seq->addCommand(attribute.release()); }
    )+
  ;

/**
 * Matches a benchmark attribute, such as ':logic', ':formula', and returns
 * a corresponding command
 * @return a command corresponding to the attribute
 */
benchAttribute [CVC4::PtrCloser<CVC4::Command>* smt_command]
@declarations {
  std::string name;
  BenchmarkStatus b_status;
  Expr expr;
  CVC4::PtrCloser<CVC4::CommandSequence> command_seq;
  CVC4::PtrCloser<CVC4::Command> declaration_command;
}
  : LOGIC_TOK identifier[name,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->preemptCommand(new SetBenchmarkLogicCommand(name));
      PARSER_STATE->setLogic(name);
      smt_command->reset(new EmptyCommand());
    }
  | ASSUMPTION_TOK annotatedFormula[expr]
    { smt_command->reset(new AssertCommand(expr)); }
  | FORMULA_TOK annotatedFormula[expr]
    { smt_command->reset(new CheckSatCommand(expr)); }
  | STATUS_TOK status[b_status]
    { smt_command->reset(new SetBenchmarkStatusCommand(b_status)); }
  | EXTRAFUNS_TOK LPAREN_TOK
    { command_seq.reset(new CommandSequence()); }
    ( functionDeclaration[&declaration_command]
      { command_seq->addCommand(declaration_command.release()); }
    )+ RPAREN_TOK
      { smt_command->reset(command_seq.release()); }
  | EXTRAPREDS_TOK LPAREN_TOK
    { command_seq.reset(new CommandSequence()); }
    ( predicateDeclaration[&declaration_command]
      { command_seq->addCommand(declaration_command.release()); }
    )+ RPAREN_TOK
      { smt_command->reset(command_seq.release()); }
  | EXTRASORTS_TOK LPAREN_TOK
      { command_seq.reset(new CommandSequence()); }
    ( sortDeclaration[&declaration_command]
      { command_seq->addCommand(declaration_command.release()); }
    )+ RPAREN_TOK
      { smt_command->reset(command_seq.release()); }
  | NOTES_TOK STRING_LITERAL
    { smt_command->reset(
          new CommentCommand(AntlrInput::tokenText($STRING_LITERAL))); }
  | annotation[smt_command]
  ;

/**
 * Matches an annotated formula.
 * @return the expression representing the formula
 */
annotatedFormula[CVC4::Expr& expr]
@init {
  Debug("parser") << "annotated formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
  Kind kind;
  std::string name;
  std::vector<Expr> args; /* = getExprVector(); */
  std::vector<Expr> args2;
  Expr op; /* Operator expression FIXME: move away kill it */
}
  : /* a built-in operator application */
    LPAREN_TOK builtinOp[kind] annotatedFormulas[args,expr]
    { if((kind == CVC4::kind::AND || kind == CVC4::kind::OR) && args.size() == 1) {
        /* Unary AND/OR can be replaced with the argument.
	 * It just so happens expr should already be the only argument. */
        assert( expr == args[0] );
      } else if( CVC4::kind::isAssociative(kind) &&
                 args.size() > EXPR_MANAGER->maxArity(kind) ) {
    	/* Special treatment for associative operators with lots of children */
        expr = EXPR_MANAGER->mkAssociative(kind,args);
      } else if(!PARSER_STATE->strictModeEnabled() &&
                kind == CVC4::kind::MINUS && args.size() == 1) {
        /* Special fix-up for unary minus improperly used in some benchmarks */
        expr = MK_EXPR(CVC4::kind::UMINUS, args[0]);
      } else {
        PARSER_STATE->checkArity(kind, args.size());
        expr = MK_EXPR(kind, args);
      }
    }
    termAnnotation[expr]* RPAREN_TOK

  | /* A quantifier */
    LPAREN_TOK
    ( FORALL_TOK { kind = kind::FORALL; } | EXISTS_TOK { kind = kind::EXISTS; } )
    { PARSER_STATE->pushScope(); }
    ( LPAREN_TOK let_identifier[name,CHECK_NONE] t=sortSymbol RPAREN_TOK
      { args.push_back(PARSER_STATE->mkBoundVar(name, t)); }
    )+
    annotatedFormula[expr]
    { args2.push_back( MK_EXPR( kind::BOUND_VAR_LIST, args ) );
      args2.push_back(expr);
      expr = MK_EXPR(kind, args2);
    }
    termAnnotation[expr]* RPAREN_TOK
    { PARSER_STATE->popScope(); }

  | /* A non-built-in function application */

    // Semantic predicate not necessary if parenthesized subexpressions
    // are disallowed
    // { isFunction(LT(2)->getText()) }?
    LPAREN_TOK
    parameterizedOperator[op]
    annotatedFormulas[args,expr]
    // TODO: check arity
    { expr = MK_EXPR(op,args); }
    termAnnotation[expr]* RPAREN_TOK

  | /* An ite expression */
    LPAREN_TOK ITE_TOK
    annotatedFormula[expr]
    { args.push_back(expr); }
    annotatedFormula[expr]
    { args.push_back(expr); }
    annotatedFormula[expr]
    { args.push_back(expr);
      expr = MK_EXPR(CVC4::kind::ITE, args); }
    termAnnotation[expr]* RPAREN_TOK

  | /* a let/flet binding */
    LPAREN_TOK
    ( LET_TOK LPAREN_TOK let_identifier[name,CHECK_UNDECLARED]
      | FLET_TOK LPAREN_TOK flet_identifier[name,CHECK_UNDECLARED] )
    annotatedFormula[expr] RPAREN_TOK
    { PARSER_STATE->pushScope();
      PARSER_STATE->defineVar(name,expr); }
    annotatedFormula[expr]
    termAnnotation[expr]* RPAREN_TOK
    { PARSER_STATE->popScope(); }

    /* constants */
  | TRUE_TOK          { expr = MK_CONST(bool(true)); }
  | FALSE_TOK         { expr = MK_CONST(bool(false)); }
  | NUMERAL_TOK
    { expr = MK_CONST( AntlrInput::tokenToInteger($NUMERAL_TOK) ); }
  | RATIONAL_TOK
    { // FIXME: This doesn't work because an SMT rational is not a
      // valid GMP rational string
      expr = MK_CONST( AntlrInput::tokenToRational($RATIONAL_TOK) ); }
  | n = BITVECTOR_BV_CONST '[' size = NUMERAL_TOK ']'
    { expr = MK_CONST( AntlrInput::tokenToBitvector($n, $size) ); }
  | n = BITVECTOR1_BV_CONST
    { unsigned int bit = AntlrInput::tokenText($n)[3] - '0';
      expr = MK_CONST( BitVector(1, bit) );
    }
    // NOTE: Theory constants go here
    /* TODO: quantifiers, arithmetic constants */

  | /* a variable */
    ( identifier[name,CHECK_DECLARED,SYM_VARIABLE]
      | let_identifier[name,CHECK_DECLARED]
      | flet_identifier[name,CHECK_DECLARED] )
    { expr = PARSER_STATE->getVariable(name); }
  ;

/**
 * Matches a sequence of annotated formulas and puts them into the
 * formulas vector.
 * @param formulas the vector to fill with formulas
 * @param expr an Expr reference for the elements of the sequence
 */
/* NOTE: We pass an Expr in here just to avoid allocating a fresh Expr every
 * time through this rule. */
annotatedFormulas[std::vector<CVC4::Expr>& formulas, CVC4::Expr& expr]
  : ( annotatedFormula[expr] { formulas.push_back(expr); } )+
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
  | IFF_TOK      { $kind = CVC4::kind::EQUAL;   }
  | EQUAL_TOK    { $kind = CVC4::kind::EQUAL;   }
  | DISTINCT_TOK { $kind = CVC4::kind::DISTINCT; }
  // Arithmetic
  | GREATER_THAN_TOK
                 { $kind = CVC4::kind::GT; }
  | GREATER_THAN_TOK EQUAL_TOK
                 { $kind = CVC4::kind::GEQ; }
  | LESS_THAN_TOK EQUAL_TOK
                 { $kind = CVC4::kind::LEQ; }
  | LESS_THAN_TOK
                 { $kind = CVC4::kind::LT; }
  | PLUS_TOK     { $kind = CVC4::kind::PLUS; }
  | STAR_TOK     { $kind = CVC4::kind::MULT; }
  | TILDE_TOK    { $kind = CVC4::kind::UMINUS; }
  | MINUS_TOK    { $kind = CVC4::kind::MINUS; }
  | DIV_TOK      { $kind = CVC4::kind::DIVISION; }
  // Bit-vectors
  | CONCAT_TOK   { $kind = CVC4::kind::BITVECTOR_CONCAT; }
  | BVAND_TOK    { $kind = CVC4::kind::BITVECTOR_AND;    }
  | BVOR_TOK     { $kind = CVC4::kind::BITVECTOR_OR;     }
  | BVXOR_TOK    { $kind = CVC4::kind::BITVECTOR_XOR;    }
  | BVNOT_TOK    { $kind = CVC4::kind::BITVECTOR_NOT;    }
  | BVNAND_TOK   { $kind = CVC4::kind::BITVECTOR_NAND;   }
  | BVNOR_TOK    { $kind = CVC4::kind::BITVECTOR_NOR;    }
  | BVXNOR_TOK   { $kind = CVC4::kind::BITVECTOR_XNOR;   }
  | BVCOMP_TOK   { $kind = CVC4::kind::BITVECTOR_COMP;   }
  | BVMUL_TOK    { $kind = CVC4::kind::BITVECTOR_MULT;   }
  | BVADD_TOK    { $kind = CVC4::kind::BITVECTOR_PLUS;   }
  | BVSUB_TOK    { $kind = CVC4::kind::BITVECTOR_SUB;    }
  | BVNEG_TOK    { $kind = CVC4::kind::BITVECTOR_NEG;    }
  | BVUDIV_TOK   { $kind = CVC4::kind::BITVECTOR_UDIV;   }
  | BVUREM_TOK   { $kind = CVC4::kind::BITVECTOR_UREM;   }
  | BVSDIV_TOK   { $kind = CVC4::kind::BITVECTOR_SDIV;   }
  | BVSREM_TOK   { $kind = CVC4::kind::BITVECTOR_SREM;   }
  | BVSMOD_TOK   { $kind = CVC4::kind::BITVECTOR_SMOD;   }
  | BVSHL_TOK    { $kind = CVC4::kind::BITVECTOR_SHL;    }
  | BVLSHR_TOK   { $kind = CVC4::kind::BITVECTOR_LSHR;   }
  | BVASHR_TOK   { $kind = CVC4::kind::BITVECTOR_ASHR;   }
  | BVULT_TOK    { $kind = CVC4::kind::BITVECTOR_ULT;    }
  | BVULE_TOK    { $kind = CVC4::kind::BITVECTOR_ULE;    }
  | BVUGT_TOK    { $kind = CVC4::kind::BITVECTOR_UGT;    }
  | BVUGE_TOK    { $kind = CVC4::kind::BITVECTOR_UGE;    }
  | BVSLT_TOK    { $kind = CVC4::kind::BITVECTOR_SLT;    }
  | BVSLE_TOK    { $kind = CVC4::kind::BITVECTOR_SLE;    }
  | BVSGT_TOK    { $kind = CVC4::kind::BITVECTOR_SGT;    }
  | BVSGE_TOK    { $kind = CVC4::kind::BITVECTOR_SGE;    }
  // arrays
  | SELECT_TOK   { $kind = CVC4::kind::SELECT; }
  | STORE_TOK    { $kind = CVC4::kind::STORE; }
  // NOTE: Theory operators go here
  ;

/**
 * Matches an operator.
 */
parameterizedOperator[CVC4::Expr& op]
  : functionSymbol[op]
  | bitVectorOperator[op]
  ;

/**
 * Matches a bit-vector operator (the ones parametrized by numbers)
 */
bitVectorOperator[CVC4::Expr& op]
  : EXTRACT_TOK '[' n1 = NUMERAL_TOK ':' n2 = NUMERAL_TOK ']'
    { op = MK_CONST(BitVectorExtract(AntlrInput::tokenToUnsigned($n1), AntlrInput::tokenToUnsigned($n2))); }
  | REPEAT_TOK '[' n = NUMERAL_TOK ']'
    { op = MK_CONST(BitVectorRepeat(AntlrInput::tokenToUnsigned($n))); }
  | ZERO_EXTEND_TOK '[' n = NUMERAL_TOK ']'
    { op = MK_CONST(BitVectorZeroExtend(AntlrInput::tokenToUnsigned($n))); }
  | SIGN_EXTEND_TOK '[' n = NUMERAL_TOK ']'
    { op = MK_CONST(BitVectorSignExtend(AntlrInput::tokenToUnsigned($n))); }
  | ROTATE_LEFT_TOK '[' n = NUMERAL_TOK ']'
    { op = MK_CONST(BitVectorRotateLeft(AntlrInput::tokenToUnsigned($n))); }
  | ROTATE_RIGHT_TOK '[' n = NUMERAL_TOK ']'
    { op = MK_CONST(BitVectorRotateRight(AntlrInput::tokenToUnsigned($n))); }
  ;

/**
 * Matches a (possibly undeclared) predicate identifier (returning the string).
 * @param check what kind of check to do with the symbol
 */
predicateName[std::string& name, CVC4::parser::DeclarationCheck check]
  :  functionName[name,check]
  ;

/**
 * Matches a (possibly undeclared) function identifier (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[std::string& name, CVC4::parser::DeclarationCheck check]
  :  identifier[name,check,SYM_VARIABLE]
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
 * Matches an attribute name from the input (:attribute_name).
 */
attribute[std::string& s]
  : ATTR_IDENTIFIER
    { s = AntlrInput::tokenText($ATTR_IDENTIFIER); }
  ;

functionDeclaration[CVC4::PtrCloser<CVC4::Command>* smt_command]
@declarations {
  std::string name;
  std::vector<Type> sorts;
}
  : LPAREN_TOK functionName[name,CHECK_UNDECLARED]
      t = sortSymbol // require at least one sort
    { sorts.push_back(t); }
      sortList[sorts] RPAREN_TOK
    { if( sorts.size() == 1 ) {
        assert( t == sorts[0] );
      } else {
        t = EXPR_MANAGER->mkFunctionType(sorts);
      }
      Expr func = PARSER_STATE->mkVar(name, t);
      smt_command->reset(new DeclareFunctionCommand(name, func, t));
    }
  ;

/**
 * Matches the declaration of a predicate and declares it
 */
predicateDeclaration[CVC4::PtrCloser<CVC4::Command>* smt_command]
@declarations {
  std::string name;
  std::vector<Type> p_sorts;
}
  : LPAREN_TOK predicateName[name,CHECK_UNDECLARED] sortList[p_sorts] RPAREN_TOK
    { Type t;
      if( p_sorts.empty() ) {
        t = EXPR_MANAGER->booleanType();
      } else {
        t = EXPR_MANAGER->mkPredicateType(p_sorts);
      }
      Expr func = PARSER_STATE->mkVar(name, t);
      smt_command->reset(new DeclareFunctionCommand(name, func, t));
    }
  ;

sortDeclaration[CVC4::PtrCloser<CVC4::Command>* smt_command]
@declarations {
  std::string name;
}
  : sortName[name,CHECK_UNDECLARED]
    { Debug("parser") << "sort decl: '" << name << "'" << std::endl;
      Type type = PARSER_STATE->mkSort(name);
      smt_command->reset(new DeclareTypeCommand(name, 0, type));
    }
  ;

/**
 * Matches a sequence of sort symbols and fills them into the given vector.
 */
sortList[std::vector<CVC4::Type>& sorts]
  : ( t = sortSymbol { sorts.push_back(t); })*
  ;

/**
 * Matches the sort symbol, which can be an arbitrary identifier.
 * @param check the check to perform on the name
 */
sortName[std::string& name, CVC4::parser::DeclarationCheck check]
  : identifier[name,check,SYM_SORT]
  ;

sortSymbol returns [CVC4::parser::smt1::myType t]
@declarations {
  std::string name;
}
  : sortName[name,CHECK_NONE]
  	{ $t = PARSER_STATE->getSort(name); }
  | BITVECTOR_TOK '[' NUMERAL_TOK ']' {
  	$t = EXPR_MANAGER->mkBitVectorType(AntlrInput::tokenToUnsigned($NUMERAL_TOK));
    }
  /* attaching 'Array' to '[' allows us to parse regular 'Array' correctly in
   * e.g. QF_AX, and also 'Array[m:n]' in e.g. QF_AUFBV */
  | 'Array[' n1=NUMERAL_TOK ':' n2=NUMERAL_TOK ']' {
        $t = EXPR_MANAGER->mkArrayType(EXPR_MANAGER->mkBitVectorType(AntlrInput::tokenToUnsigned(n1)),
                                       EXPR_MANAGER->mkBitVectorType(AntlrInput::tokenToUnsigned(n2)));
    }
  ;

/**
 * Matches the status of the benchmark, one of 'sat', 'unsat' or 'unknown'.
 */
status[ CVC4::BenchmarkStatus& status ]
  : SAT_TOK       { $status = SMT_SATISFIABLE;    }
  | UNSAT_TOK     { $status = SMT_UNSATISFIABLE;  }
  | UNKNOWN_TOK   { $status = SMT_UNKNOWN;        }
  ;

/**
 * Matches an annotation, which is an attribute name, with an optional user
 * value.
 */
annotation[CVC4::PtrCloser<CVC4::Command>* smt_command]
@init {
  std::string key, value;
  std::vector<Expr> pats;
  Expr pat;
}
  : PATTERN_ANNOTATION_BEGIN
    { PARSER_STATE->warning(":pat not supported here; ignored"); }
    annotatedFormulas[pats,pat] '}'
  | attribute[key]
    ( userValue[value]
      { smt_command->reset(
            new SetInfoCommand(key.c_str() + 1, SExpr(value))); }
    | { smt_command->reset(
            new EmptyCommand(std::string("annotation: ") + key)); }
    )
  ;

/**
 * Matches an annotation, which is an attribute name, with an optional user
 * value.
 */
termAnnotation[CVC4::Expr& expr]
@init {
  std::string key, value;
  std::vector<Expr> pats;
  Expr pat;
}
  : PATTERN_ANNOTATION_BEGIN annotatedFormulas[pats,pat] '}'
    { if(expr.getKind() == kind::FORALL || expr.getKind() == kind::EXISTS) {
        pat = MK_EXPR(kind::INST_PATTERN, pats);
        if(expr.getNumChildren() == 3) {
          // we have other user patterns attached to the quantifier
          // already; add this one to the existing list
          pats = expr[2].getChildren();
          pats.push_back(pat);
          expr = MK_EXPR(expr.getKind(), expr[0], expr[1], MK_EXPR(kind::INST_PATTERN_LIST, pats));
        } else {
          // this is the only user pattern for the quantifier
          expr = MK_EXPR(expr.getKind(), expr[0], expr[1], MK_EXPR(kind::INST_PATTERN_LIST, pat));
        }
      } else {
        PARSER_STATE->warning(":pat only supported on quantifiers");
      }
    }
  | ':pat'
    { PARSER_STATE->warning("expected an instantiation pattern after :pat"); }
  | attribute[key] userValue[value]?
    { PARSER_STATE->attributeNotSupported(key); }
  ;

/**
 * Matches an identifier and sets the string reference parameter id.
 * @param id string to hold the identifier
 * @param check what kinds of check to do on the symbol
 * @param type the intended namespace for the identifier
 */
identifier[std::string& id,
		   CVC4::parser::DeclarationCheck check,
           CVC4::parser::SymbolType type]
  : IDENTIFIER
    { id = AntlrInput::tokenText($IDENTIFIER);
      Debug("parser") << "identifier: " << id
                      << " check? " << check
                      << " type? " << type << std::endl;
      PARSER_STATE->checkDeclaration(id, check, type); }
  ;

/**
 * Matches a let-bound identifier and sets the string reference parameter id.
 * @param id string to hold the identifier
 * @param check what kinds of check to do on the symbol
 */
let_identifier[std::string& id,
    		   CVC4::parser::DeclarationCheck check]
  : LET_IDENTIFIER
    { id = AntlrInput::tokenText($LET_IDENTIFIER);
      Debug("parser") << "let_identifier: " << id
                      << " check? " << check << std::endl;
      PARSER_STATE->checkDeclaration(id, check, SYM_VARIABLE); }
  ;

/**
 * Matches an flet-bound identifier and sets the string reference parameter id.
 * @param id string to hold the identifier
 * @param check what kinds of check to do on the symbol
 */
flet_identifier[std::string& id,
    		    CVC4::parser::DeclarationCheck check]
  : FLET_IDENTIFIER
    { id = AntlrInput::tokenText($FLET_IDENTIFIER);
      Debug("parser") << "flet_identifier: " << id
                      << " check? " << check << std::endl;
      PARSER_STATE->checkDeclaration(id, check); }
  ;

// Base SMT-LIB tokens
ASSUMPTION_TOK  : ':assumption';
BENCHMARK_TOK   : 'benchmark';
EXTRAFUNS_TOK   : ':extrafuns';
EXTRAPREDS_TOK  : ':extrapreds';
EXTRASORTS_TOK  : ':extrasorts';
FALSE_TOK       : 'false';
FLET_TOK        : 'flet';
FORMULA_TOK     : ':formula';
ITE_TOK         : 'ite' | 'if_then_else';
LET_TOK         : 'let';
LOGIC_TOK       : ':logic';
LPAREN_TOK      : '(';
NOTES_TOK       : ':notes';
RPAREN_TOK      : ')';
SAT_TOK         : 'sat';
STATUS_TOK      : ':status';
THEORY_TOK      : 'theory';
TRUE_TOK        : 'true';
UNKNOWN_TOK     : 'unknown';
UNSAT_TOK       : 'unsat';

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
IFF_TOK           : 'iff';
IMPLIES_TOK       : 'implies';
LESS_THAN_TOK     : '<';
MINUS_TOK         : '-';
NOT_TOK           : 'not';
OR_TOK            : 'or';
PERCENT_TOK       : '%';
PIPE_TOK          : '|';
PLUS_TOK          : '+';
POUND_TOK         : '#';
SELECT_TOK        : 'select';
STAR_TOK          : '*';
STORE_TOK         : 'store';
TILDE_TOK         : '~';
XOR_TOK           : 'xor';

// Bitvector tokens
BITVECTOR_TOK     : 'BitVec';
CONCAT_TOK        : 'concat';
EXTRACT_TOK       : 'extract';
BVAND_TOK         : 'bvand';
BVOR_TOK          : 'bvor';
BVXOR_TOK         : 'bvxor';
BVNOT_TOK         : 'bvnot';
BVNAND_TOK        : 'bvnand';
BVNOR_TOK         : 'bvnor';
BVXNOR_TOK        : 'bvxnor';
BVCOMP_TOK        : 'bvcomp';
BVMUL_TOK         : 'bvmul';
BVADD_TOK         : 'bvadd';
BVSUB_TOK         : 'bvsub';
BVNEG_TOK         : 'bvneg';
BVUDIV_TOK        : 'bvudiv';
BVUREM_TOK        : 'bvurem';
BVSDIV_TOK        : 'bvsdiv';
BVSREM_TOK        : 'bvsrem';
BVSMOD_TOK        : 'bvsmod';
BVSHL_TOK         : 'bvshl';
BVLSHR_TOK        : 'bvlshr';
BVASHR_TOK        : 'bvashr';
BVULT_TOK         : 'bvult';
BVULE_TOK         : 'bvule';
BVUGT_TOK         : 'bvugt';
BVUGE_TOK         : 'bvuge';
BVSLT_TOK         : 'bvslt';
BVSLE_TOK         : 'bvsle';
BVSGT_TOK         : 'bvsgt';
BVSGE_TOK         : 'bvsge';
REPEAT_TOK        : 'repeat';
ZERO_EXTEND_TOK   : 'zero_extend';
SIGN_EXTEND_TOK   : 'sign_extend';
ROTATE_LEFT_TOK   : 'rotate_left';
ROTATE_RIGHT_TOK  : 'rotate_right';

/**
 * Matches a bit-vector constant of the form bv123
 */
BITVECTOR_BV_CONST
  : 'bv' DIGIT+
  ;

/**
 * Matches a bit-vector constant of the form bit(0|1)
 */
BITVECTOR1_BV_CONST
  : 'bit0' | 'bit1'
  ;


/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER
  :  ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*
  ;

/**
 * Matches an identifier starting with a colon.
 */
ATTR_IDENTIFIER
  :  ':' IDENTIFIER
  ;

/**
 * Matches an identifier starting with a question mark.
 */
LET_IDENTIFIER
  : '?' IDENTIFIER
  ;

/**
 * Matches an identifier starting with a dollar sign.
 */
FLET_IDENTIFIER
  : '$' IDENTIFIER
  ;

/**
 * Matches the value of user-defined annotations or attributes. The
 * only constraint imposed on a user-defined value is that it start
 * with an open brace and end with closed brace.
 */
userValue[std::string& s]
  : USER_VALUE
    { s = AntlrInput::tokenText($USER_VALUE);
      assert(*s.begin() == '{');
      assert(*s.rbegin() == '}');
      // trim whitespace
      s.erase(s.begin(), s.begin() + 1);
      s.erase(s.begin(), std::find_if(s.begin(), s.end(), std::not1(std::ptr_fun<int, int>(std::isspace))));
      s.erase(s.end() - 1);
      s.erase(std::find_if(s.rbegin(), s.rend(), std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
    }
  ;

PATTERN_ANNOTATION_BEGIN
  : ':pat' (' ' | '\t' | '\f' | '\r' | '\n')* '{'
  ;

USER_VALUE
  : '{' ('\\{' | '\\}' | ~('{' | '}'))* '}'
  ;

/**
 * Matches and skips whitespace in the input.
 */
WHITESPACE
  : (' ' | '\t' | '\f' | '\r' | '\n')+
    { SKIP(); }
  ;

/**
 * Matches a numeral from the input (non-empty sequence of digits).
 */
NUMERAL_TOK
  : DIGIT+
  ;

RATIONAL_TOK
  : DIGIT+ '.' DIGIT+
  ;

/**
 * Matches a double quoted string literal. Escaping is supported, and escape
 * character '\' has to be escaped.
 */
STRING_LITERAL
  :  '"' (ESCAPE | ~('"'|'\\'))* '"'
  ;

/**
 * Matches the comments and ignores them
 */
COMMENT
  : ';' (~('\n' | '\r'))*
    { SKIP(); }
  ;


/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment
ALPHA
  :  'a'..'z'
  |  'A'..'Z'
  ;

/**
 * Matches the digits (0-9)
 */
fragment DIGIT :   '0'..'9';
// fragment NON_ZERO_DIGIT : '1'..'9';
// fragment NUMERAL_SEQ : '0' | NON_ZERO_DIGIT DIGIT*;

/**
 * Matches an allowed escaped character.
 */
fragment ESCAPE : '\\' ('"' | '\\' | 'n' | 't' | 'r');

