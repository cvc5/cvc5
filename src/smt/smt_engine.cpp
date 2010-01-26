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
  d_public_em(em),
  d_nm(em->getNodeManager()),
  d_opts(opts),
  d_de(),
  d_te(),
  d_prop(d_de, d_te) {
}

SmtEngine::~SmtEngine() {
}

void SmtEngine::doCommand(Command* c) {
  NodeManagerScope nms(d_nm);
  c->invoke(this);
}

void SmtEngine::orHelper(Node::iterator p, Node::iterator end, NodeBuilder<>& result) {
  if(p == end) {
    return;
  } else if((*p).getKind() == AND) {
    NodeBuilder<> resultPrefix = result;
    result = NodeBuilder<>(AND);

    for(Node::iterator i = (*p).begin(); i != (*p).end(); ++i) {
      NodeBuilder<> r = resultPrefix;

      r << preprocess(*i);
      Node::iterator p2 = p;
      orHelper(++p2, end, r);

      result << r;
    }
  } else {
    result << preprocess(*p);
  }
}

Node SmtEngine::preprocess(const Node& e) {
  if(e.getKind() == NOT) {
    // short-circuit trivial NOTs
    if(e[0].getKind() == TRUE) {
      return d_nm->mkNode(FALSE);
    } else if(e[0].getKind() == FALSE) {
      return d_nm->mkNode(TRUE);
    } else if(e[0].getKind() == NOT) {
      return preprocess(e[0][0]);
    } else {
      Node f = preprocess(e[0]);
      // push NOTs inside of ANDs and ORs
      if(f.getKind() == AND) {
        NodeBuilder<> n(OR);
        for(Node::iterator i = f.begin(); i != f.end(); ++i) {
          if((*i).getKind() == NOT) {
            n << (*i)[0];
          } else {
            n << d_nm->mkNode(NOT, *i);
          }
        }
        return n;
      }
      if(f.getKind() == OR) {
        NodeBuilder<> n(AND);
        for(Node::iterator i = f.begin(); i != f.end(); ++i) {
          if((*i).getKind() == NOT) {
            n << (*i)[0];
          } else {
            n << d_nm->mkNode(NOT, *i);
          }
        }
        return n;
      }
    }
  } else if(e.getKind() == AND) {
    NodeBuilder<> n(AND);
    // flatten ANDs
    for(Node::iterator i = e.begin(); i != e.end(); ++i) {
      Node f = preprocess(*i);
      if((*i).getKind() == AND) {
        for(Node::iterator j = f.begin(); j != f.end(); ++j) {
          n << *j;
        }
      } else {
        n << *i;        
      }
    }
    return n;
  } else if(e.getKind() == OR) {
    NodeBuilder<> n(OR);
    // flatten ORs
    for(Node::iterator i = e.begin(); i != e.end(); ++i) {
      if((*i).getKind() == OR) {
        Node f = preprocess(*i);
        for(Node::iterator j = f.begin(); j != f.end(); ++j) {
          n << *j;
        }
      }
    }

    Node nod = n;
    NodeBuilder<> m(OR);
    orHelper(nod.begin(), nod.end(), m);

    return m;
  }

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

  return asserts;
}

Result SmtEngine::check() {
  Node asserts = processAssertionList();
  d_prop.solve(asserts);
  return Result(Result::VALIDITY_UNKNOWN);
}

Result SmtEngine::quickCheck() {
  processAssertionList();
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEngine::addFormula(const Node& e) {
  Debug("smt") << "push_back assertion " << e << std::endl;
  d_assertions.push_back(e);
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return check();
}

Result SmtEngine::query(const BoolExpr& e) {
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(d_nm->mkNode(NOT, e.getNode()));
  addFormula(node_e);
  return check();
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return quickCheck();
}

Expr SmtEngine::simplify(const Expr& e) {
  Expr simplify(const Expr& e);
  Unimplemented();
}

}/* CVC4 namespace */
