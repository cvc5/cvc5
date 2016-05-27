/*********************                                                        */
/*! \file ast_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The pretty-printer interface for the AST output language
 **
 ** The pretty-printer interface for the AST output language.
 **/
#include "printer/ast/ast_printer.h"

#include <iostream>
#include <string>
#include <typeinfo>
#include <vector>

#include "expr/expr.h" // for ExprSetDepth etc..
#include "expr/node_manager_attributes.h" // for VarNameAttr
#include "options/language.h" // for LANG_AST
#include "printer/dagification_visitor.h"
#include "smt/command.h"
#include "smt_util/node_visitor.h"
#include "theory/substitutions.h"

using namespace std;

namespace CVC4 {
namespace printer {
namespace ast {

void AstPrinter::toStream(std::ostream& out, TNode n,
                          int toDepth, bool types, size_t dag) const throw() {
  if(dag != 0) {
    DagificationVisitor dv(dag);
    NodeVisitor<DagificationVisitor> visitor;
    visitor.run(dv, n);
    const theory::SubstitutionMap& lets = dv.getLets();
    if(!lets.empty()) {
      out << "(LET ";
      bool first = true;
      for(theory::SubstitutionMap::const_iterator i = lets.begin();
          i != lets.end();
          ++i) {
        if(! first) {
          out << ", ";
        } else {
          first = false;
        }
        toStream(out, (*i).second, toDepth, types, false);
        out << " := ";
        toStream(out, (*i).first, toDepth, types, false);
      }
      out << " IN ";
    }
    Node body = dv.getDagifiedBody();
    toStream(out, body, toDepth, types);
    if(!lets.empty()) {
      out << ')';
    }
  } else {
    toStream(out, n, toDepth, types);
  }
}

void AstPrinter::toStream(std::ostream& out, TNode n,
                          int toDepth, bool types) const throw() {
  // null
  if(n.getKind() == kind::NULL_EXPR) {
    out << "null";
    return;
  }

  // variable
  if(n.getMetaKind() == kind::metakind::VARIABLE) {
    string s;
    if(n.getAttribute(expr::VarNameAttr(), s)) {
      out << s;
    } else {
      out << "var_" << n.getId();
    }
    if(types) {
      // print the whole type, but not *its* type
      out << ":";
      n.getType().toStream(out, language::output::LANG_AST);
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
        toStream(out, n.getOperator(), toDepth < 0 ? toDepth : toDepth - 1, types);
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
        toStream(out, *i, toDepth < 0 ? toDepth : toDepth - 1, types);
      } else {
        out << "(...)";
      }
    }
  }
  out << ')';
}/* AstPrinter::toStream(TNode) */

template <class T>
static bool tryToStream(std::ostream& out, const Command* c) throw();

void AstPrinter::toStream(std::ostream& out, const Command* c,
                          int toDepth, bool types, size_t dag) const throw() {
  expr::ExprSetDepth::Scope sdScope(out, toDepth);
  expr::ExprPrintTypes::Scope ptScope(out, types);
  expr::ExprDag::Scope dagScope(out, dag);

  if(tryToStream<EmptyCommand>(out, c) ||
     tryToStream<AssertCommand>(out, c) ||
     tryToStream<PushCommand>(out, c) ||
     tryToStream<PopCommand>(out, c) ||
     tryToStream<CheckSatCommand>(out, c) ||
     tryToStream<QueryCommand>(out, c) ||
     tryToStream<ResetCommand>(out, c) ||
     tryToStream<ResetAssertionsCommand>(out, c) ||
     tryToStream<QuitCommand>(out, c) ||
     tryToStream<DeclarationSequence>(out, c) ||
     tryToStream<CommandSequence>(out, c) ||
     tryToStream<DeclareFunctionCommand>(out, c) ||
     tryToStream<DeclareTypeCommand>(out, c) ||
     tryToStream<DefineTypeCommand>(out, c) ||
     tryToStream<DefineNamedFunctionCommand>(out, c) ||
     tryToStream<DefineFunctionCommand>(out, c) ||
     tryToStream<SimplifyCommand>(out, c) ||
     tryToStream<GetValueCommand>(out, c) ||
     tryToStream<GetModelCommand>(out, c) ||
     tryToStream<GetAssignmentCommand>(out, c) ||
     tryToStream<GetAssertionsCommand>(out, c) ||
     tryToStream<GetProofCommand>(out, c) ||
     tryToStream<SetBenchmarkStatusCommand>(out, c) ||
     tryToStream<SetBenchmarkLogicCommand>(out, c) ||
     tryToStream<SetInfoCommand>(out, c) ||
     tryToStream<GetInfoCommand>(out, c) ||
     tryToStream<SetOptionCommand>(out, c) ||
     tryToStream<GetOptionCommand>(out, c) ||
     tryToStream<DatatypeDeclarationCommand>(out, c) ||
     tryToStream<CommentCommand>(out, c)) {
    return;
  }

  out << "ERROR: don't know how to print a Command of class: "
      << typeid(*c).name() << endl;

}/* AstPrinter::toStream(Command*) */

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s) throw();

void AstPrinter::toStream(std::ostream& out, const CommandStatus* s) const throw() {

  if(tryToStream<CommandSuccess>(out, s) ||
     tryToStream<CommandFailure>(out, s) ||
     tryToStream<CommandUnsupported>(out, s) ||
     tryToStream<CommandInterrupted>(out, s)) {
    return;
  }

  out << "ERROR: don't know how to print a CommandStatus of class: "
      << typeid(*s).name() << endl;

}/* AstPrinter::toStream(CommandStatus*) */

void AstPrinter::toStream(std::ostream& out, const Model& m) const throw() {
  out << "Model()";
}

void AstPrinter::toStream(std::ostream& out, const Model& m, const Command* c) const throw() {
  // shouldn't be called; only the non-Command* version above should be
  Unreachable();
}

static void toStream(std::ostream& out, const EmptyCommand* c)  throw() {
  out << "EmptyCommand(" << c->getName() << ")";
}

static void toStream(std::ostream& out, const AssertCommand* c) throw() {
  out << "Assert(" << c->getExpr() << ")";
}

static void toStream(std::ostream& out, const PushCommand* c) throw() {
  out << "Push()";
}

static void toStream(std::ostream& out, const PopCommand* c) throw() {
  out << "Pop()";
}

static void toStream(std::ostream& out, const CheckSatCommand* c) throw() {
  Expr e = c->getExpr();
  if(e.isNull()) {
    out << "CheckSat()";
  } else {
    out << "CheckSat(" << e << ")";
  }
}

static void toStream(std::ostream& out, const QueryCommand* c) throw() {
  out << "Query(" << c->getExpr() << ')';
}

static void toStream(std::ostream& out, const ResetCommand* c) throw() {
  out << "Reset()";
}

static void toStream(std::ostream& out, const ResetAssertionsCommand* c) throw() {
  out << "ResetAssertions()";
}

static void toStream(std::ostream& out, const QuitCommand* c) throw() {
  out << "Quit()";
}

static void toStream(std::ostream& out, const DeclarationSequence* c) throw() {
  out << "DeclarationSequence[" << endl;
  for(CommandSequence::const_iterator i = c->begin();
      i != c->end();
      ++i) {
    out << *i << endl;
  }
  out << "]";
}

static void toStream(std::ostream& out, const CommandSequence* c) throw() {
  out << "CommandSequence[" << endl;
  for(CommandSequence::const_iterator i = c->begin();
      i != c->end();
      ++i) {
    out << *i << endl;
  }
  out << "]";
}

static void toStream(std::ostream& out, const DeclareFunctionCommand* c) throw() {
  out << "Declare(" << c->getSymbol() << "," << c->getType() << ")";
}

static void toStream(std::ostream& out, const DefineFunctionCommand* c) throw() {
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

static void toStream(std::ostream& out, const DeclareTypeCommand* c) throw() {
  out << "DeclareType(" << c->getSymbol() << "," << c->getArity() << ","
      << c->getType() << ")";
}

static void toStream(std::ostream& out, const DefineTypeCommand* c) throw() {
  const vector<Type>& params = c->getParameters();
  out << "DefineType(" << c->getSymbol() << ",[";
  if(params.size() > 0) {
    copy( params.begin(), params.end() - 1,
          ostream_iterator<Type>(out, ", ") );
    out << params.back();
  }
  out << "]," << c->getType() << ")";
}

static void toStream(std::ostream& out, const DefineNamedFunctionCommand* c) throw() {
  out << "DefineNamedFunction( ";
  toStream(out, static_cast<const DefineFunctionCommand*>(c));
  out << " )";
}

static void toStream(std::ostream& out, const SimplifyCommand* c) throw() {
  out << "Simplify( << " << c->getTerm() << " >> )";
}

static void toStream(std::ostream& out, const GetValueCommand* c) throw() {
  out << "GetValue( << ";
  const vector<Expr>& terms = c->getTerms();
  copy(terms.begin(), terms.end(), ostream_iterator<Expr>(out, ", "));
  out << " >> )";
}

static void toStream(std::ostream& out, const GetModelCommand* c) throw() {
  out << "GetModel()";
}

static void toStream(std::ostream& out, const GetAssignmentCommand* c) throw() {
  out << "GetAssignment()";
}
static void toStream(std::ostream& out, const GetAssertionsCommand* c) throw() {
  out << "GetAssertions()";
}
static void toStream(std::ostream& out, const GetProofCommand* c) throw() {
  out << "GetProof()";
}
static void toStream(std::ostream& out, const SetBenchmarkStatusCommand* c) throw() {
  out << "SetBenchmarkStatus(" << c->getStatus() << ")";
}
static void toStream(std::ostream& out, const SetBenchmarkLogicCommand* c) throw() {
  out << "SetBenchmarkLogic(" << c->getLogic() << ")";
}
static void toStream(std::ostream& out, const SetInfoCommand* c) throw() {
  out << "SetInfo(" << c->getFlag() << ", " << c->getSExpr() << ")";
}

static void toStream(std::ostream& out, const GetInfoCommand* c) throw() {
  out << "GetInfo(" << c->getFlag() << ")";
}
static void toStream(std::ostream& out, const SetOptionCommand* c) throw() {
  out << "SetOption(" << c->getFlag() << ", " << c->getSExpr() << ")";
}

static void toStream(std::ostream& out, const GetOptionCommand* c) throw() {
  out << "GetOption(" << c->getFlag() << ")";
}

static void toStream(std::ostream& out, const DatatypeDeclarationCommand* c) throw() {
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

static void toStream(std::ostream& out, const CommentCommand* c) throw() {
  out << "CommentCommand([" << c->getComment() << "])";
}

template <class T>
static bool tryToStream(std::ostream& out, const Command* c) throw() {
  if(typeid(*c) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(c));
    return true;
  }
  return false;
}

static void toStream(std::ostream& out, const CommandSuccess* s) throw() {
  if(Command::printsuccess::getPrintSuccess(out)) {
    out << "OK" << endl;
  }
}

static void toStream(std::ostream& out, const CommandInterrupted* s) throw() {
  out << "INTERRUPTED" << endl;
}

static void toStream(std::ostream& out, const CommandUnsupported* s) throw() {
  out << "UNSUPPORTED" << endl;
}

static void toStream(std::ostream& out, const CommandFailure* s) throw() {
  out << s->getMessage() << endl;
}

template <class T>
static bool tryToStream(std::ostream& out, const CommandStatus* s) throw() {
  if(typeid(*s) == typeid(T)) {
    toStream(out, dynamic_cast<const T*>(s));
    return true;
  }
  return false;
}

}/* CVC4::printer::ast namespace */
}/* CVC4::printer namespace */
}/* CVC4 namespace */
