/*********************                                                        */
/*! \file ast_printer.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The pretty-printer interface for the AST output language
 **
 ** The pretty-printer interface for the AST output language.
 **/

#include "printer/ast/ast_printer.h"
#include "expr/expr.h" // for ExprSetDepth etc..
#include "util/language.h" // for LANG_AST
#include "expr/node_manager.h" // for VarNameAttr
#include "expr/command.h"

#include <iostream>
#include <vector>
#include <string>
#include <typeinfo>

using namespace std;

namespace CVC4 {
namespace printer {
namespace ast {

void AstPrinter::toStream(std::ostream& out, TNode n,
                          int toDepth, bool types) const {
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
    return;
  }

  // variable
  if(n.getMetaKind() == kind::metakind::VARIABLE) {
    if(n.getKind() != kind::VARIABLE &&
       n.getKind() != kind::SORT_TYPE) {
      out << n.getKind() << ':';
    }

    string s;
    if(n.getAttribute(expr::VarNameAttr(), s)) {
      out << s;
    } else {
      out << "var_" << n.getId();
    }
    if(types) {
      // print the whole type, but not *its* type
      out << ":";
      n.getType().toStream(out, -1, false, language::output::LANG_AST);
    }

    return;
  }

  out << '(' << n.getKind();
  if(n.getMetaKind() == kind::metakind::CONSTANT) {
    // constant
    out << ' ';
    kind::metakind::NodeValueConstPrinter::toStream(out, n);
  } else {
    // operator
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      out << ' ';
      if(toDepth != 0) {
        n.getOperator().toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
                                 types, language::output::LANG_AST);
      } else {
        out << "(...)";
      }
    }
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      if(i != iend) {
        out << ' ';
      }
      if(toDepth != 0) {
        (*i).toStream(out, toDepth < 0 ? toDepth : toDepth - 1,
                      types, language::output::LANG_AST);
      } else {
        out << "(...)";
      }
    }
  }
  out << ')';
}/* AstPrinter::toStream() */

template <class T>
static bool tryToStream(std::ostream& out, const Command* c);

void AstPrinter::toStream(std::ostream& out, const Command* c,
                          int toDepth, bool types) const {
  expr::ExprSetDepth::Scope sdScope(out, toDepth);
  expr::ExprPrintTypes::Scope ptScope(out, types);

  if(tryToStream<EmptyCommand>(out, c) ||
     tryToStream<AssertCommand>(out, c) ||
     tryToStream<PushCommand>(out, c) ||
     tryToStream<PopCommand>(out, c) ||
     tryToStream<CheckSatCommand>(out, c) ||
     tryToStream<QueryCommand>(out, c) ||
     tryToStream<QuitCommand>(out, c) ||
     tryToStream<CommandSequence>(out, c) ||
     tryToStream<DeclarationCommand>(out, c) ||
     tryToStream<DefineFunctionCommand>(out, c) ||
     tryToStream<DefineNamedFunctionCommand>(out, c) ||
     tryToStream<SimplifyCommand>(out, c) ||
     tryToStream<GetValueCommand>(out, c) ||
     tryToStream<GetAssignmentCommand>(out, c) ||
     tryToStream<GetAssertionsCommand>(out, c) ||
     tryToStream<SetBenchmarkStatusCommand>(out, c) ||
     tryToStream<SetBenchmarkLogicCommand>(out, c) ||
     tryToStream<SetInfoCommand>(out, c) ||
     tryToStream<GetInfoCommand>(out, c) ||
     tryToStream<SetOptionCommand>(out, c) ||
     tryToStream<GetOptionCommand>(out, c) ||
     tryToStream<DatatypeDeclarationCommand>(out, c)) {
    return;
  }

  Unhandled("don't know how to print a Command of class: %s", typeid(*c).name());

}/* AstPrinter::toStream() */

static void toStream(std::ostream& out, const EmptyCommand* c) {
  out << "EmptyCommand(" << c->getName() << ")";
}

static void toStream(std::ostream& out, const AssertCommand* c) {
  out << "Assert(" << c->getExpr() << ")";
}

static void toStream(std::ostream& out, const PushCommand* c) {
  out << "Push()";
}

static void toStream(std::ostream& out, const PopCommand* c) {
  out << "Pop()";
}

static void toStream(std::ostream& out, const CheckSatCommand* c) {
  BoolExpr e = c->getExpr();
  if(e.isNull()) {
    out << "CheckSat()";
  } else {
    out << "CheckSat(" << e << ")";
  }
}

static void toStream(std::ostream& out, const QueryCommand* c) {
  out << "Query(" << c->getExpr() << ')';
}

static void toStream(std::ostream& out, const QuitCommand* c) {
  out << "Quit()";
}

static void toStream(std::ostream& out, const CommandSequence* c) {
  out << "CommandSequence[" << endl;
  for(CommandSequence::const_iterator i = c->begin();
      i != c->end();
      ++i) {
    out << *i << endl;
  }
  out << "]";
}

static void toStream(std::ostream& out, const DeclarationCommand* c) {
  const vector<string>& declaredSymbols = c->getDeclaredSymbols();
  out << "Declare([";
  copy( declaredSymbols.begin(), declaredSymbols.end() - 1,
        ostream_iterator<string>(out, ", ") );
  out << declaredSymbols.back();
  out << "])";
}

static void toStream(std::ostream& out, const DefineFunctionCommand* c) {
  Expr func = c->getFunction();
  const std::vector<Expr>& formals = c->getFormals();
  Expr formula = c->getFormula();
  out << "DefineFunction( \"" << func << "\", [";
  if(formals.size() > 0) {
    copy( formals.begin(), formals.end() - 1,
          ostream_iterator<Expr>(out, ", ") );
    out << formals.back();
  }
  out << "], << " << formula << " >> )";
}

static void toStream(std::ostream& out, const DefineNamedFunctionCommand* c) {
  out << "DefineNamedFunction( ";
  toStream(out, static_cast<const DefineFunctionCommand*>(c));
  out << " )";
}

static void toStream(std::ostream& out, const SimplifyCommand* c) {
  out << "Simplify( << " << c->getTerm() << " >> )";
}

static void toStream(std::ostream& out, const GetValueCommand* c) {
  out << "GetValue( << " << c->getTerm() << " >> )";
}

static void toStream(std::ostream& out, const GetAssignmentCommand* c) {
  out << "GetAssignment()";
}
static void toStream(std::ostream& out, const GetAssertionsCommand* c) {
  out << "GetAssertions()";
}
static void toStream(std::ostream& out, const SetBenchmarkStatusCommand* c) {
  out << "SetBenchmarkStatus(" << c->getStatus() << ")";
}
static void toStream(std::ostream& out, const SetBenchmarkLogicCommand* c) {
  out << "SetBenchmarkLogic(" << c->getLogic() << ")";
}
static void toStream(std::ostream& out, const SetInfoCommand* c) {
  out << "SetInfo(" << c->getFlag() << ", " << c->getSExpr() << ")";
}

static void toStream(std::ostream& out, const GetInfoCommand* c) {
  out << "GetInfo(" << c->getFlag() << ")";
}
static void toStream(std::ostream& out, const SetOptionCommand* c) {
  out << "SetOption(" << c->getFlag() << ", " << c->getSExpr() << ")";
}

static void toStream(std::ostream& out, const GetOptionCommand* c) {
  out << "GetOption(" << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const DatatypeDeclarationCommand* c) {
  const vector<DatatypeType>& datatypes = c->getDatatypes();
  out << "DatatypeDeclarationCommand([";
  for(vector<DatatypeType>::const_iterator i = datatypes.begin(),
        i_end = datatypes.end();
      i != i_end;
      ++i) {
    out << *i << ";" << endl;
  }
  out << "])";
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c) {
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c));
    return true;
  }
  return false;
}

}/* CVC4::printer::ast namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */

