/*********************                                                        */
/*! \file boolean_terms.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "smt/boolean_terms.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "theory/model.h"
#include "expr/kind.h"
#include "util/hash.h"
#include "util/bool.h"
#include <string>
#include <algorithm>
#include <set>
#include <map>

using namespace std;
using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

static inline bool isBoolean(TNode top, unsigned i) {
  switch(top.getKind()) {
  case kind::NOT:
  case kind::AND:
  case kind::IFF:
  case kind::IMPLIES:
  case kind::OR:
  case kind::XOR:
  case kind::FORALL:
  case kind::EXISTS:
  case kind::REWRITE_RULE:
  case kind::RR_REWRITE:
  case kind::RR_DEDUCTION:
  case kind::RR_REDUCTION:
  case kind::INST_PATTERN:
    return true;

  case kind::ITE:
    if(i == 0) {
      return true;
    }
    return top.getType().isBoolean();

  default:
    return false;
  }
}

const Datatype& BooleanTermConverter::booleanTermsConvertDatatype(const Datatype& dt) throw() {
  return dt;
  // boolean terms not supported in datatypes, yet

  Debug("boolean-terms") << "booleanTermsConvertDatatype: considering " << dt.getName() << endl;
  for(Datatype::const_iterator c = dt.begin(); c != dt.end(); ++c) {
    TypeNode t = TypeNode::fromType((*c).getConstructor().getType());
    for(TypeNode::const_iterator a = t.begin(); a != t.end(); ++a) {
      if((*a).isBoolean()) {
        Datatype newDt(dt.getName() + "'");
        Debug("boolean-terms") << "found a Boolean arg in constructor " << (*c).getName() << endl;
        for(c = dt.begin(); c != dt.end(); ++c) {
          DatatypeConstructor ctor((*c).getName() + "'", (*c).getTesterName() + "'");
          t = TypeNode::fromType((*c).getConstructor().getType());
          for(DatatypeConstructor::const_iterator a = (*c).begin(); a != (*c).end(); ++a) {
            if((*a).getType().getRangeType().isBoolean()) {
              ctor.addArg((*a).getName() + "'", NodeManager::currentNM()->mkBitVectorType(1).toType());
            } else {
              Type argType = (*a).getType().getRangeType();
              if(argType.isDatatype() && DatatypeType(argType).getDatatype() == dt) {
                ctor.addArg((*a).getName() + "'", DatatypeSelfType());
              } else {
                ctor.addArg((*a).getName() + "'", argType);
              }
            }
          }
          newDt.addConstructor(ctor);
        }
        DatatypeType newDtt = NodeManager::currentNM()->toExprManager()->mkDatatypeType(newDt);
        const Datatype& newD = newDtt.getDatatype();
        for(c = dt.begin(); c != dt.end(); ++c) {
          Debug("boolean-terms") << "constructor " << (*c).getConstructor() << ":" << (*c).getConstructor().getType() << " made into " << newD[(*c).getName() + "'"].getConstructor() << ":" << newD[(*c).getName() + "'"].getConstructor().getType() << endl;
          d_booleanTermCache[make_pair(Node::fromExpr((*c).getConstructor()), false)] = Node::fromExpr(newD[(*c).getName() + "'"].getConstructor());
          d_booleanTermCache[make_pair(Node::fromExpr((*c).getTester()), false)] = Node::fromExpr(newD[(*c).getName() + "'"].getTester());
          for(DatatypeConstructor::const_iterator a = (*c).begin(); a != (*c).end(); ++a) {
            d_booleanTermCache[make_pair(Node::fromExpr((*a).getSelector()), false)] = Node::fromExpr(newD[(*c).getName() + "'"].getSelector((*a).getName() + "'"));
          }
        }
        return newD;
      }
    }
  }
  return dt;
}/* BooleanTermConverter::booleanTermsConvertDatatype() */

// look for vars from "vars" that occur in a term-context in n; transfer them to output.
static void collectVarsInTermContext(TNode n, std::set<TNode>& vars, std::set<TNode>& output, bool boolParent, std::hash_set< std::pair<TNode, bool>, PairHashFunction<TNode, bool, TNodeHashFunction, BoolHashFunction> >& alreadySeen) {
  if(vars.empty()) {
    return;
  }
  const pair<TNode, bool> cacheKey(n, boolParent);
  if(alreadySeen.find(cacheKey) != alreadySeen.end()) {
    return;
  }
  alreadySeen.insert(cacheKey);

  if(n.isVar() && vars.find(n) != vars.end() && !boolParent) {
    vars.erase(n);
    output.insert(n);
    if(vars.empty()) {
      return;
    }
  }
  for(size_t i = 0; i < n.getNumChildren(); ++i) {
    collectVarsInTermContext(n[i], vars, output, isBoolean(n, i), alreadySeen);
    if(vars.empty()) {
      return;
    }
  }
}

Node BooleanTermConverter::rewriteBooleanTermsRec(TNode top, bool boolParent, std::map<TNode, Node>& quantBoolVars) throw() {
  Debug("boolean-terms") << "rewriteBooleanTermsRec: " << top << " - boolParent=" << boolParent << endl;

  BooleanTermCache::iterator i = d_booleanTermCache.find(make_pair<Node, bool>(top, boolParent));
  if(i != d_booleanTermCache.end()) {
    return (*i).second.isNull() ? Node(top) : (*i).second;
  }

  Kind k = top.getKind();
  kind::MetaKind mk = top.getMetaKind();

  NodeManager* nm = NodeManager::currentNM();

  Node one = nm->mkConst(BitVector(1u, 1u));
  Node zero = nm->mkConst(BitVector(1u, 0u));

  if(quantBoolVars.find(top) != quantBoolVars.end()) {
    // this Bool variable is quantified over and we're changing it to a BitVector var
    if(boolParent) {
      return quantBoolVars[top].eqNode(one);
    } else {
      return quantBoolVars[top];
    }
  }

  if(!boolParent && top.getType().isBoolean()) {
    // still need to rewrite e.g. function applications over boolean
    Node topRewritten = rewriteBooleanTermsRec(top, true, quantBoolVars);
    Node n = nm->mkNode(kind::ITE, topRewritten, one, zero);
    Debug("boolean-terms") << "constructed ITE: " << n << endl;
    return n;
  }

  if(mk == kind::metakind::CONSTANT) {
    if(k == kind::STORE_ALL) {
      const ArrayStoreAll& asa = top.getConst<ArrayStoreAll>();
      ArrayType arrType = asa.getType();
      TypeNode indexType = TypeNode::fromType(arrType.getIndexType());
      Type constituentType = arrType.getConstituentType();
      if(constituentType.isBoolean()) {
        // we have store_all(true) or store_all(false)
        // just turn it into store_all(1) or store_all(0)
        Node newConst = nm->mkConst(BitVector(1u, asa.getExpr().getConst<bool>() ? 1u : 0u));
        if(indexType.isBoolean()) {
          // change index type to BV(1) also
          indexType = nm->mkBitVectorType(1);
        }
        ArrayStoreAll asaRepl(nm->mkArrayType(indexType, nm->mkBitVectorType(1)).toType(), newConst.toExpr());
        Node n = nm->mkConst(asaRepl);
        Debug("boolean-terms") << " returning new store_all: " << n << endl;
        return n;
      }
      if(indexType.isBoolean()) {
        // must change index type to BV(1)
        indexType = nm->mkBitVectorType(1);
        ArrayStoreAll asaRepl(nm->mkArrayType(indexType, TypeNode::fromType(constituentType)).toType(), asa.getExpr());
        Node n = nm->mkConst(asaRepl);
        Debug("boolean-terms") << " returning new store_all: " << n << endl;
        return n;
      }
    }
    return top;
  } else if(mk == kind::metakind::VARIABLE) {
    TypeNode t = top.getType();
    if(t.isFunction()) {
      for(unsigned i = 0; i < t.getNumChildren() - 1; ++i) {
        if(t[i].isBoolean()) {
          vector<TypeNode> argTypes = t.getArgTypes();
          replace(argTypes.begin(), argTypes.end(), t[i], nm->mkBitVectorType(1));
          TypeNode newType = nm->mkFunctionType(argTypes, t.getRangeType());
          Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()) + "__boolterm__",
                                newType, "a function introduced by Boolean-term conversion",
                                NodeManager::SKOLEM_EXACT_NAME);
          Debug("boolean-terms") << "constructed func: " << n << " of type " << newType << endl;
          top.setAttribute(BooleanTermAttr(), n);
          NodeBuilder<> boundVarsBuilder(kind::BOUND_VAR_LIST);
          NodeBuilder<> bodyBuilder(kind::APPLY_UF);
          bodyBuilder << n;
          for(unsigned j = 0; j < t.getNumChildren() - 1; ++j) {
            Node var = nm->mkBoundVar(t[j]);
            boundVarsBuilder << var;
            if(t[j].isBoolean()) {
              bodyBuilder << nm->mkNode(kind::ITE, var, one, zero);
            } else {
              bodyBuilder << var;
            }
          }
          Node boundVars = boundVarsBuilder;
          Node body = bodyBuilder;
          Node lam = nm->mkNode(kind::LAMBDA, boundVars, body);
          Debug("boolean-terms") << "substituting " << top << " ==> " << lam << endl;
          d_smt.d_theoryEngine->getModel()->addSubstitution(top, lam);
          d_booleanTermCache[make_pair(top, boolParent)] = n;
          return n;
        }
      }
    } else if(t.isArray()) {
      TypeNode indexType = t.getArrayIndexType();
      TypeNode constituentType = t.getArrayConstituentType();
      bool rewrite = false;
      if(indexType.isBoolean()) {
        indexType = nm->mkBitVectorType(1);
        rewrite = true;
      }
      if(constituentType.isBoolean()) {
        constituentType = nm->mkBitVectorType(1);
        rewrite = true;
      }
      if(rewrite) {
        TypeNode newType = nm->mkArrayType(indexType, constituentType);
        Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()),
                              newType, "an array variable introduced by Boolean-term conversion",
                              NodeManager::SKOLEM_EXACT_NAME);
        top.setAttribute(BooleanTermAttr(), n);
        Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
        Node n_zero = nm->mkNode(kind::SELECT, n, zero);
        Node n_one = nm->mkNode(kind::SELECT, n, one);
        Node base = nm->mkConst(ArrayStoreAll(ArrayType(top.getType().toType()), nm->mkConst(false).toExpr()));
        Node repl = nm->mkNode(kind::STORE,
                    nm->mkNode(kind::STORE, base, nm->mkConst(false),
                               nm->mkNode(kind::EQUAL, n_zero, one)), nm->mkConst(true),
                               nm->mkNode(kind::EQUAL, n_one, one));
        Debug("boolean-terms") << "array replacement: " << top << " => " << repl << endl;
        d_smt.d_theoryEngine->getModel()->addSubstitution(top, repl);
        d_booleanTermCache[make_pair(top, boolParent)] = n;
        return n;
      }
      d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
      return top;
    } else if(t.isTuple()) {
      return top;
    } else if(t.isRecord()) {
      return top;
    } else if(t.isDatatype()) {
      return top;// no support for datatypes at present
      const Datatype& dt = t.getConst<Datatype>();
      const Datatype& dt2 = booleanTermsConvertDatatype(dt);
      if(dt != dt2) {
        Assert(d_booleanTermCache.find(make_pair(top, boolParent)) == d_booleanTermCache.end(),
               "Node `%s' already in cache ?!", top.toString().c_str());
        Assert(top.isVar());
        TypeNode newType = TypeNode::fromType(dt2.getDatatypeType());
        Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()),
                              newType, "an array variable introduced by Boolean-term conversion",
                              NodeManager::SKOLEM_EXACT_NAME);
        top.setAttribute(BooleanTermAttr(), n);
        Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
        d_booleanTermCache[make_pair(top, boolParent)] = n;
        return n;
      } else {
        d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
        return top;
      }
    } else if(t.isConstructor()) {
      return top;// no support for datatypes at present
      Assert(!boolParent);
      const Datatype& dt = t[t.getNumChildren() - 1].getConst<Datatype>();
      const Datatype& dt2 = booleanTermsConvertDatatype(dt);
      if(dt != dt2) {
        Assert(d_booleanTermCache.find(make_pair(top, boolParent)) != d_booleanTermCache.end(),
               "constructor `%s' not in cache", top.toString().c_str());
        return d_booleanTermCache[make_pair(top, boolParent)];
      } else {
        d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
        return top;
      }
    } else if(t.isTester() || t.isSelector()) {
      return top;// no support for datatypes at present
      Assert(!boolParent);
      const Datatype& dt = t[0].getConst<Datatype>();
      const Datatype& dt2 = booleanTermsConvertDatatype(dt);
      if(dt != dt2) {
        Assert(d_booleanTermCache.find(make_pair(top, boolParent)) != d_booleanTermCache.end(),
               "tester or selector `%s' not in cache", top.toString().c_str());
        return d_booleanTermCache[make_pair(top, boolParent)];
      } else {
        d_booleanTermCache[make_pair(top, boolParent)] = Node::null();
        return top;
      }
    } else if(t.getNumChildren() > 0) {
      for(TypeNode::iterator i = t.begin(); i != t.end(); ++i) {
        if((*i).isBoolean()) {
          vector<TypeNode> argTypes(t.begin(), t.end());
          replace(argTypes.begin(), argTypes.end(), *i, nm->mkBitVectorType(1));
          TypeNode newType = nm->mkTypeNode(t.getKind(), argTypes);
          Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()),
                                newType, "a variable introduced by Boolean-term conversion",
                                NodeManager::SKOLEM_EXACT_NAME);
          Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
          top.setAttribute(BooleanTermAttr(), n);
          d_booleanTermCache[make_pair(top, boolParent)] = n;
          return n;
        }
      }
    }
    return top;
  }
  switch(k) {
  case kind::LAMBDA:
    Unreachable("not expecting a LAMBDA in boolean-term conversion: %s", top.toString().c_str());

  case kind::BOUND_VAR_LIST:
    return top;

  case kind::REWRITE_RULE:
  case kind::RR_REWRITE:
  case kind::RR_DEDUCTION:
  case kind::RR_REDUCTION:
    // not yet supported
    return top;

  case kind::FORALL:
  case kind::EXISTS: {
    Debug("bt") << "looking at quantifier -> " << top << endl;
    set<TNode> ourVars;
    for(TNode::iterator i = top[0].begin(); i != top[0].end(); ++i) {
      if((*i).getType().isBoolean()) {
        ourVars.insert(*i);
      }
    }
    if(ourVars.empty()) {
      // Simple case, quantifier doesn't quantify over Boolean vars,
      // no special handling needed for quantifier.  Fall through.
      Debug("bt") << "- quantifier simple case (1), no Boolean vars bound" << endl;
    } else {
      set<TNode> output;
      hash_set< pair<TNode, bool>, PairHashFunction<TNode, bool, TNodeHashFunction, BoolHashFunction> > alreadySeen;
      collectVarsInTermContext(top[1], ourVars, output, true, alreadySeen);
      if(output.empty()) {
        // Simple case, quantifier quantifies over Boolean vars, but they
        // don't occur in term context.  Fall through.
        Debug("bt") << "- quantifier simple case (2), Boolean vars bound but not used in term context" << endl;
      } else {
        Debug("bt") << "- quantifier case (3), Boolean vars bound and used in term context" << endl;
        // We have Boolean vars appearing in term context.  Convert their
        // types in the quantifier.
        for(set<TNode>::const_iterator i = output.begin(); i != output.end(); ++i) {
          Node newVar = nm->mkBoundVar((*i).toString(), nm->mkBitVectorType(1));
          Assert(quantBoolVars.find(*i) == quantBoolVars.end(), "bad quantifier: shares a bound var with another quantifier (don't do that!)");
          quantBoolVars[*i] = newVar;
        }
        vector<TNode> boundVars;
        for(TNode::iterator i = top[0].begin(); i != top[0].end(); ++i) {
          map<TNode, Node>::const_iterator j = quantBoolVars.find(*i);
          if(j == quantBoolVars.end()) {
            boundVars.push_back(*i);
          } else {
            boundVars.push_back((*j).second);
          }
        }
        Node boundVarList = nm->mkNode(kind::BOUND_VAR_LIST, boundVars);
        Node body = rewriteBooleanTermsRec(top[1], true, quantBoolVars);
        Node quant = nm->mkNode(top.getKind(), boundVarList, body);
        Debug("bt") << "rewrote quantifier to -> " << quant << endl;
        d_booleanTermCache[make_pair(top, true)] = quant;
        d_booleanTermCache[make_pair(top, false)] = quant.iteNode(one, zero);
        return quant;
      }
    }
    /* intentional fall-through for some cases above */
  }

  default:
    NodeBuilder<> b(k);
    Debug("bt") << "looking at: " << top << endl;
    if(mk == kind::metakind::PARAMETERIZED) {
      if(kindToTheoryId(k) != THEORY_BV &&
         k != kind::APPLY_TYPE_ASCRIPTION &&
         k != kind::TUPLE_SELECT &&
         k != kind::TUPLE_UPDATE &&
         k != kind::RECORD_SELECT &&
         k != kind::RECORD_UPDATE &&
         k != kind::RECORD) {
        Debug("bt") << "rewriting: " << top.getOperator() << endl;
        b << rewriteBooleanTermsRec(top.getOperator(), false, quantBoolVars);
        Debug("bt") << "got: " << b.getOperator() << endl;
      } else {
        b << top.getOperator();
      }
    }
    for(unsigned i = 0; i < top.getNumChildren(); ++i) {
      Debug("bt") << "rewriting: " << top[i] << endl;
      b << rewriteBooleanTermsRec(top[i], isBoolean(top, i), quantBoolVars);
      Debug("bt") << "got: " << b[b.getNumChildren() - 1] << endl;
    }
    Node n = b;
    Debug("boolean-terms") << "constructed: " << n << endl;
    if(boolParent &&
       n.getType().isBitVector() &&
       n.getType().getBitVectorSize() == 1) {
      n = nm->mkNode(kind::EQUAL, n, one);
    }
    d_booleanTermCache[make_pair(top, boolParent)] = n;
    return n;
  }
}/* BooleanTermConverter::rewriteBooleanTermsRec() */

}/* CVC4::smt namespace */
}/* CVC4 namespace */
