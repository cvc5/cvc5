/*********************                                           -*- C++ -*-  */
/** smt_engine.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "smt/smt_engine.h"
#include "util/exception.h"
#include "util/command.h"
#include "util/output.h"
#include "expr/node_builder.h"

namespace CVC4 {

SmtEngine::SmtEngine(ExprManager* em, Options* opts) throw() :
  d_assertions(),
  d_publicEm(em),
  d_nm(em->getNodeManager()),
  d_opts(opts),
  d_de(),
  d_te(),
  d_prop(d_de, d_te),
  d_cnfConverter(d_nm, opts->d_cnfConversion) {
}

SmtEngine::~SmtEngine() {
}

void SmtEngine::doCommand(Command* c) {
  NodeManagerScope nms(d_nm);
  c->invoke(this);
}

Node SmtEngine::preprocess(const Node& e) {
  return e;
}

Node SmtEngine::processAssertionList() {
  if(d_assertions.size() == 1) {
    return d_assertions[0];
  }

  NodeBuilder<> asserts(AND);
  for(std::vector<Node>::iterator i = d_assertions.begin();
      i != d_assertions.end();
      ++i) {
    asserts << *i;
  }

  d_assertions.clear();
  d_assertions.push_back(asserts);
  return d_assertions[0];
}

static void printAST(std::ostream& out, const Node& n, int indent = 0) {
  for(int i = 0; i < indent; ++i) {
    out << "  ";
  }
  if(n.getKind() == VARIABLE) {
    out << "(VARIABLE " << n.getId();
  } else {
    out << "(" << n.getKind();
    if(n.getNumChildren() > 0) {
      out << std::endl;
    }
    for(Node::iterator i = n.begin(); i != n.end(); ++i) {
      printAST(out, *i, indent + 1);
    }
    if(n.getNumChildren() > 0) {
      for(int i = 0; i < indent; ++i) {
        out << "  ";
      }
    }
  }
  out << ")" << std::endl;
}

Result SmtEngine::check() {
  Debug("smt") << "SMT check()" << std::endl;
  Node asserts = processAssertionList();

  // CNF conversion
  Debug("cnf") << "preprocessing " << asserts << std::endl;
  Node assertsOut = d_cnfConverter.convert(asserts);
  Debug("cnf") << "      and got " << assertsOut << std::endl;

  Debug("smt") << "BEFORE CONVERSION ==" << std::endl;
  printAST(Debug("smt"), asserts);
  Debug("smt") << "AFTER CONVERSION ==" << std::endl;
  printAST(Debug("smt"), assertsOut);
  Debug("smt") << "===================" << std::endl;

  d_prop.solve(assertsOut);
  return Result(Result::VALIDITY_UNKNOWN);
}

Result SmtEngine::quickCheck() {
  Debug("smt") << "SMT quickCheck()" << std::endl;
  processAssertionList();
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEngine::addFormula(const Node& e) {
  Debug("smt") << "push_back assertion " << e << std::endl;
  d_assertions.push_back(e);
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  Debug("smt") << "SMT checkSat(" << e << ")" << std::endl;
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return check();
}

Result SmtEngine::query(const BoolExpr& e) {
  Debug("smt") << "SMT query(" << e << ")" << std::endl;
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(d_nm->mkNode(NOT, e.getNode()));
  addFormula(node_e);
  return check();
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  Debug("smt") << "SMT assertFormula(" << e << ")" << std::endl;
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return quickCheck();
}

Expr SmtEngine::simplify(const Expr& e) {
  Debug("smt") << "SMT simplify(" << e << ")" << std::endl;
  Expr simplify(const Expr& e);
  Unimplemented();
}

}/* CVC4 namespace */
