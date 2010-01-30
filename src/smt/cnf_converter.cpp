/*********************                                           -*- C++ -*-  */
/** cnf_converter.cpp
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
 ** A CNF converter for CVC4.
 **/

#include "smt/cnf_converter.h"
#include "expr/node_builder.h"
#include "expr/node.h"
#include "util/output.h"
#include "util/Assert.h"

namespace CVC4 {
namespace smt {

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

Node CnfConverter::convert(const Node& e) {
  if(d_conversion == CNF_DIRECT_EXPONENTIAL) {
    return doConvert(e, NULL);
  }

  NodeBuilder<> b(AND);
  Node f = doConvert(e, &b);

  Debug("cnf") << "side conditions are:\n";
  NodeBuilder<> c = b;
  printAST(Debug("cnf"), c);

  if(f.getKind() == AND) {
    for(Node::iterator i = f.begin(); i != f.end(); ++i) {
      Debug("cnf") << "adding condition:\n";
      printAST(Debug("cnf"), *i);
      b << *i;
    }
  } else {
    Debug("cnf") << "adding condition:\n";
    printAST(Debug("cnf"), f);
    b << f;
  }
  return b;
}

Node CnfConverter::doConvert(const Node& e, NodeBuilder<>* sideConditions) {
  Node n;

  if(conversionMapped(e)) {
    Debug("cnf") << "conversion for " << e << " with id " << e.getId() << " is cached!" << std::endl;
    n = getConversionMap(e);
  } else {
    switch(d_conversion) {

    case CNF_DIRECT_EXPONENTIAL:
      Debug("cnf") << "direct conversion for " << e << " with id " << e.getId() << " is being computed!" << std::endl;
      n = directConvert(e, sideConditions);
      break;

    case CNF_VAR_INTRODUCTION: {
      Debug("cnf") << "var-intro conversion for " << e << " with id " << e.getId() << " is being computed!" << std::endl;
      std::vector<Node> v;
      n = varIntroductionConvert(e, sideConditions);
      Debug("cnf") << "got" << std::endl;
      printAST(Debug("cnf"), n);

      break;
    }

    default:
      Unhandled(d_conversion);
    }

    Debug("cnf") << "mapping conversion " << e << " with id " << e.getId() << " to " << n << " with id " << n.getId() << std::endl;
    mapConversion(e, n);
    Assert(conversionMapped(e));
    Assert(getConversionMap(e) == n);
  }

  Debug("cnf") << "CONVERTED ================" << std::endl;
  printAST(Debug("cnf"), e);
  Debug("cnf") << "TO        ================" << std::endl;
  printAST(Debug("cnf"), n);
  Debug("cnf") << "==========================" << std::endl;

  return n;
}

Node CnfConverter::compressNOT(const Node& e, NodeBuilder<>* sideConditions) {
  Assert(e.getKind() == NOT);

  Node f = doConvert(e[0], sideConditions);

  Debug("stari") << "compress-not " << e.getId() << "\n";

  // short-circuit trivial NOTs
  if(f.getKind() == TRUE) {
    return d_nm->mkNode(FALSE);
  } else if(f.getKind() == FALSE) {
    return d_nm->mkNode(TRUE);
  } else if(f.getKind() == NOT) {
    return doConvert(f[0], sideConditions);
  } else if(f.getKind() == AND) {
    Debug("stari") << "not-converting a NOT AND\nstarted with\n";
    printAST(Debug("stari"), e[0]);
    Debug("stari") << "now have\n";
    printAST(Debug("stari"), f);
    NodeBuilder<> n(OR);
    for(Node::iterator i = f.begin(); i != f.end(); ++i) {
      if((*i).getKind() == NOT) {
        n << (*i)[0];
      } else {
        n << d_nm->mkNode(NOT, *i);
      }
    }
    return n;
  } else if(f.getKind() == OR) {
    NodeBuilder<> n(AND);
    for(Node::iterator i = f.begin(); i != f.end(); ++i) {
      if((*i).getKind() == NOT) {
        n << (*i)[0];
      } else {
        n << d_nm->mkNode(NOT, *i);
      }
    }
    return n;
  } else {
    return d_nm->mkNode(NOT, f);
  }
}


Node CnfConverter::directConvert(const Node& e, NodeBuilder<>* sideConditions) {
  switch(e.getKind()) {

  case NOT:
    return compressNOT(e, sideConditions);

  case AND:
    return flatten<AND>(e, sideConditions);

  case OR: {
    Node n = flatten<OR>(e, sideConditions);

    NodeBuilder<> m(OR);
    Debug("dor") << "calling directOrHelper on\n";
    printAST(Debug("dor"), n);
    directOrHelper(n.begin(), n.end(), m, sideConditions);

    return m;
  }

  case IMPLIES: {
    Assert( e.getNumChildren() == 2 );
    // just turn  x IMPLIES y  into  (NOT x) OR y
    Node x = doConvert(e[0], sideConditions);
    Node y = doConvert(e[1], sideConditions);
    return doConvert(d_nm->mkNode(OR, doConvert(d_nm->mkNode(NOT, x), sideConditions), y), sideConditions);
  }

  case IFF:
    if(e.getNumChildren() == 2) {
      // common case:
      // just turn  x IFF y  into  (x AND y) OR ((NOT x) AND (NOT y))
      Node x = doConvert(e[0], sideConditions);
      Node y = doConvert(e[1], sideConditions);
      Node r = d_nm->mkNode(OR,
                            doConvert(d_nm->mkNode(AND, x, y), sideConditions),
                            doConvert(d_nm->mkNode(AND,
                                                 doConvert(d_nm->mkNode(NOT, x), sideConditions),
                                                 doConvert(d_nm->mkNode(NOT, y), sideConditions)), sideConditions));
      Debug("cnf") << "working on an IFF\n";
      printAST(Debug("cnf"), e);
      Debug("cnf") << "which is\n";
      printAST(Debug("cnf"), r);
      return doConvert(r, sideConditions);
    } else {
      // more than 2 children:
      // treat  x IFF y IFF z  as  (x IFF y) AND (y IFF z) ...
      Node::iterator i = e.begin();
      Node x = doConvert(*i++, sideConditions);
      NodeBuilder<> r(AND);
      while(i != e.end()) {
        Node y = doConvert(*i++, sideConditions);
        // now we just have two:
        // just turn  x IFF y  into  (x AND y) OR ((NOT x) AND (NOT y))
        r << d_nm->mkNode(OR,
                          doConvert(d_nm->mkNode(AND, x, y), sideConditions),
                          doConvert(d_nm->mkNode(AND,
                                                 doConvert(d_nm->mkNode(NOT, x), sideConditions),
                                                 doConvert(d_nm->mkNode(NOT, y), sideConditions)), sideConditions));
        x = y;
      }
      return doConvert(r, sideConditions);
    }

  case XOR:
    Assert( e.getNumChildren() == 2 );
    // just turn  x XOR y  into  (x AND (NOT y)) OR ((NOT x) AND y)
    return doConvert(d_nm->mkNode(OR,
                                  d_nm->mkNode(AND,
                                               e[0],
                                               d_nm->mkNode(NOT, e[1])),
                                  d_nm->mkNode(AND,
                                               d_nm->mkNode(NOT, e[0]),
                                               e[1])), sideConditions);

  default:
    // variable or theory atom
    return e;
  }
}

/**
 * OR:  all ORs and NOTs
 * -- do nothing
 *
 * find an AND.
 * prefix:   a \/ b \/ c
 * and term: d /\ e
 * rest:     f \/ g \/ h
 * 
 * construct:  prefix \/ child
 * 
 * then, process rest.
 * 
 * if rest has no additional ANDs
 * then I get  prefix \/ child \/ rest
 * and I do same with other children
 * 
 * if rest has additional ANDs
 * then I get  (prefix \/ child \/ rest'1) /\ (prefix \/ child \/ rest'2) /\ ...
 * and I do same with other children
 */
void CnfConverter::directOrHelper(Node::iterator p, Node::iterator end, NodeBuilder<>& result, NodeBuilder<>* sideConditions) {
  static int nextID = 0;
  int ID = ++nextID;
  Debug("dor") << "beginning of directOrHelper " << ID << "\n";

  while(p != end) {
    // for each child of the expression:

    Debug("dor") << "CHILD == directOrHelper " << ID << "\n";
    printAST(Debug("dor"), *p);

    // convert the child first
    Node n = doConvert(*p, sideConditions);

    Debug("dor") << "CNV CHILD == directOrHelper " << ID << "\n";
    printAST(Debug("dor"), *p);

    // if the child is an AND
    if(n.getKind() == AND) {
      Debug("dor") << "directOrHelper found AND " << ID << "\n";

      NodeBuilder<> prefix = result;
      result.clear(AND);

      for(Node::iterator i = n.begin(); i != n.end(); ++i) {
        // for each child of the AND
        NodeBuilder<> r = prefix;

        Debug("dor") << "directOrHelper AND " << ID << ", converting\n";
        printAST(Debug("dor"), *i);

        r << doConvert(*i, sideConditions);
        NodeBuilder<> rx = r;
        Debug("dor") << "prefix \\/ child is " << ID << "\n";
        printAST(Debug("dor"), rx);
        Node::iterator p2 = p;
        directOrHelper(++p2, end, r, sideConditions);

        Debug("dor") << "directOrHelper recursion done " << ID << "\n";
        Node rr = r;
        Debug("dor") << "directOrHelper subterm of AND " << ID << "\n";
        printAST(Debug("dor"), rr);

        result << rr;
      }

      Debug("dor") << "end of directOrHelper AND " << ID << "\n";
      NodeBuilder<> resultnb = result;
      printAST(Debug("dor"), resultnb);

      return;
    } else {
      // if it's not an AND, pass it through, it's fine
      result << n;
    }

    Debug("cnf") << "  ** result now " << result << std::endl;

    ++p;
  }

  Debug("dor") << "end of directOrHelper NO AND " << ID << "\n";
  NodeBuilder<> resultnb = result;
  printAST(Debug("dor"), resultnb);
}

Node CnfConverter::varIntroductionConvert(const Node& e, NodeBuilder<>* sideConditions) {
  switch(e.getKind()) {

  case NOT: {
    Node f = compressNOT(e, sideConditions);
    Debug("stari") << "compressNOT:\n";
    printAST(Debug("stari"), e);
    printAST(Debug("stari"), f);
    return f;
  }

  case AND: {
    Node n = flatten<AND>(e, sideConditions);
    Node var = d_nm->mkVar();
    Node notVar = d_nm->mkNode(NOT, var);
    for(Node::iterator i = n.begin(); i != n.end(); ++i) {
      // *i has already been converted by flatten<>()
      if((*i).getKind() == OR) {
        NodeBuilder<> b(OR);
        b << notVar;
        for(Node::iterator j = (*i).begin(); j != (*i).end(); ++j) {
          b << *j;
        }
        *sideConditions << b;
      } else {
        Debug("stari") << "*i should have been flattened:\n";
        printAST(Debug("stari"), *i);
        Node x = convert(*i);
        printAST(Debug("stari"), x);
        //Assert(x == *i);
        *sideConditions << d_nm->mkNode(OR, notVar, *i);
      }
    }

    return var;
  }

  case OR:
    return flatten<OR>(e, sideConditions);

  case IMPLIES: {
    Assert( e.getNumChildren() == 2 );
    // just turn  x IMPLIES y  into  (NOT x) OR y
    Node x = doConvert(e[0], sideConditions);
    Node y = doConvert(e[1], sideConditions);
    return doConvert(d_nm->mkNode(OR, doConvert(d_nm->mkNode(NOT, x), sideConditions), y), sideConditions);
  }

  case IFF:
    if(e.getNumChildren() == 2) {
      // common case:
      // just turn  x IFF y  into  (x AND y) OR ((NOT x) AND (NOT y))
      Node x = doConvert(e[0], sideConditions);
      Node y = doConvert(e[1], sideConditions);
      Node r = d_nm->mkNode(OR,
                            doConvert(d_nm->mkNode(AND, x, y), sideConditions),
                            doConvert(d_nm->mkNode(AND,
                                                 doConvert(d_nm->mkNode(NOT, x), sideConditions),
                                                 doConvert(d_nm->mkNode(NOT, y), sideConditions)), sideConditions));
      Debug("cnf") << "working on an IFF\n";
      printAST(Debug("cnf"), e);
      Debug("cnf") << "which is\n";
      printAST(Debug("cnf"), r);
      return doConvert(r, sideConditions);
    } else {
      // more than 2 children:
      // treat  x IFF y IFF z  as  (x IFF y) AND (y IFF z) ...
      Node::iterator i = e.begin();
      Node x = doConvert(*i++, sideConditions);
      NodeBuilder<> r(AND);
      while(i != e.end()) {
        Node y = doConvert(*i++, sideConditions);
        // now we just have two:
        // just turn  x IFF y  into  (x AND y) OR ((NOT x) AND (NOT y))
        r << d_nm->mkNode(OR,
                          doConvert(d_nm->mkNode(AND, x, y), sideConditions),
                          doConvert(d_nm->mkNode(AND,
                                                 doConvert(d_nm->mkNode(NOT, x), sideConditions),
                                                 doConvert(d_nm->mkNode(NOT, y), sideConditions)), sideConditions));
        x = y;
      }
      return doConvert(r, sideConditions);
    }

  case XOR:
    Assert( e.getNumChildren() == 2 );
    // just turn  x XOR y  into  (x AND (NOT y)) OR ((NOT x) AND y)
    return doConvert(d_nm->mkNode(OR,
                                d_nm->mkNode(AND,
                                             e[0],
                                             d_nm->mkNode(NOT, e[1])),
                                d_nm->mkNode(AND,
                                             d_nm->mkNode(NOT, e[0]),
                                             e[1])), sideConditions);

  default:
    // variable or theory atom
    return e;
  }
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
