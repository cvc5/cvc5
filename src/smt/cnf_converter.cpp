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
  Node n;

  if(conversionMapped(e)) {
    Debug("cnf") << "conversion for " << e << " with id " << e.getId() << " is cached!" << std::endl;
    n = getConversionMap(e);
  } else {
    switch(d_conversion) {
    case CNF_DIRECT_EXPONENTIAL:
      n = directConvert(e);
      break;
    case CNF_VAR_INTRODUCTION:
      n = varIntroductionConvert(e);
      break;
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

Node CnfConverter::compressNOT(const Node& e) {
  Assert(e.getKind() == NOT);

  // short-circuit trivial NOTs
  if(e[0].getKind() == TRUE) {
    return d_nm->mkNode(FALSE);
  } else if(e[0].getKind() == FALSE) {
    return d_nm->mkNode(TRUE);
  } else if(e[0].getKind() == NOT) {
    return convert(e[0][0]);
  } else {
    Node f = convert(e[0]);
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
    return e;
  }
}


Node CnfConverter::directConvert(const Node& e) {
  if(e.getKind() == NOT) {
    return compressNOT(e);
  } else if(e.getKind() == AND) {
    return flatten<AND>(e);
  } else if(e.getKind() == OR) {
    Node n = flatten<OR>(e);

    NodeBuilder<> m(OR);
    directOrHelper(n.begin(), n.end(), m);

    return m;
  }

  return e;
}

void CnfConverter::directOrHelper(Node::iterator p, Node::iterator end, NodeBuilder<>& result) {
  while(p != end) {
    if((*p).getKind() == AND) {
      Debug("cnf") << "orHelper: p      " << *p << std::endl;
      Debug("cnf") << "          end    " << std::endl;
      Debug("cnf") << "          result " << result << std::endl;

      NodeBuilder<> resultPrefix = result;
      result = NodeBuilder<>(AND);

      for(Node::iterator i = (*p).begin(); i != (*p).end(); ++i) {
        NodeBuilder<> r = resultPrefix;

        // is this a double-convert since we did OR flattening before?
        r << convert(*i);
        Node::iterator p2 = p;
        directOrHelper(++p2, end, r);

        result << r;
      }
    } else {
      Debug("cnf") << "orHelper: passing through a conversion of " << *p << std::endl;
      // is this a double-convert since we did OR flattening before?
      result << convert(*p);
    }

    Debug("cnf") << "  ** result now " << result << std::endl;

    ++p;
  }
}

Node CnfConverter::varIntroductionConvert(const Node& e) {
  if(e.getKind() == NOT) {
    return compressNOT(e);
  } else if(e.getKind() == AND) {
    return flatten<AND>(e);
  } else if(e.getKind() == OR) {
    Node n = flatten<OR>(e);

    Debug("cnf") << "about to handle an OR:" << std::endl;
    printAST(Debug("cnf"), n);

    NodeBuilder<> m(AND);
    NodeBuilder<> extras(OR);
    varIntroductionOrHelper(n.begin(), n.end(), m, extras);

    if(m.getNumChildren() > 0) {
      return m << extras;
    } else {
      return extras;
    }
  }

  return e;
}

void CnfConverter::varIntroductionOrHelper(Node::iterator p, Node::iterator end, NodeBuilder<>& result, NodeBuilder<>& extras) {
  while(p != end) {
    if((*p).getKind() == AND) {
      Debug("cnf") << "orHelper: p      " << *p << std::endl;
      printAST(Debug("cnf"), *p);
      Debug("cnf") << "          end    " << std::endl;
      Debug("cnf") << "          result " << result << std::endl;
      Debug("cnf") << "          extras " << extras << std::endl;

      Node var = d_nm->mkVar();
      extras << var;

      Debug("cnf") << "  introduced var " << var << "(" << var.getId() << ")" << std::endl;

      Node notVar = d_nm->mkNode(NOT, var);

      for(Node::iterator i = (*p).begin(); i != (*p).end(); ++i) {
        // is this a double-convert since we did OR flattening before?
        result << d_nm->mkNode(OR, notVar, convert(*i));
      }
    } else {
      // is this a double-convert since we did OR flattening before?
      Debug("cnf") << "orHelper: p      " << *p << std::endl;
      Debug("cnf") << "          end    " << std::endl;
      Debug("cnf") << "          result " << result << std::endl;
      Debug("cnf") << "          extras " << extras << std::endl;
      Debug("cnf") << "   passing through" << std::endl;
      extras << convert(*p);
    }

    Debug("cnf") << "  ** result now " << result << std::endl;
    Debug("cnf") << "  ** extras now " << extras << std::endl;
    ++p;
  }
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
