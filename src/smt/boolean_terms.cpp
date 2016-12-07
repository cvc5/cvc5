/*********************                                                        */
/*! \file boolean_terms.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "smt/boolean_terms.h"

#include <algorithm>
#include <map>
#include <set>
#include <stack>
#include <string>

#include "expr/kind.h"
#include "expr/node_manager_attributes.h"
#include "options/boolean_term_conversion_mode.h"
#include "options/booleans_options.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "util/ntuple.h"

using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::booleans;

namespace CVC4 {
namespace smt {

BooleanTermConverter::BooleanTermConverter(SmtEngine& smt) :
  d_smt(smt),
  d_ff(),
  d_tt(),
  d_ffDt(),
  d_ttDt(),
  d_varCache(smt.d_userContext),
  d_termCache(smt.d_userContext),
  d_typeCache(),
  d_datatypeCache(),
  d_datatypeReverseCache() {

  // set up our "false" and "true" conversions based on command-line option
  if(options::booleanTermConversionMode() == BOOLEAN_TERM_CONVERT_TO_BITVECTORS ||
     options::booleanTermConversionMode() == BOOLEAN_TERM_CONVERT_NATIVE) {
    d_ff = NodeManager::currentNM()->mkConst(BitVector(1u, 0u));
    d_tt = NodeManager::currentNM()->mkConst(BitVector(1u, 1u));
  }
  if(options::booleanTermConversionMode() == BOOLEAN_TERM_CONVERT_TO_BITVECTORS) {
    d_ffDt = d_ff;
    d_ttDt = d_tt;
  } else {
    Datatype spec("BooleanTerm");
    // don't change the order; false is assumed to come first by the model postprocessor
    spec.addConstructor(DatatypeConstructor("BT_False"));
    spec.addConstructor(DatatypeConstructor("BT_True"));
    const Datatype& dt = NodeManager::currentNM()->toExprManager()->mkDatatypeType(spec).getDatatype();
    d_ffDt = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, Node::fromExpr(dt["BT_False"].getConstructor()));
    d_ttDt = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, Node::fromExpr(dt["BT_True"].getConstructor()));
    // mark this datatype type as being special for Boolean term conversion
    TypeNode::fromType(dt.getDatatypeType()).setAttribute(BooleanTermAttr(), Node::null());
    if(options::booleanTermConversionMode() == BOOLEAN_TERM_CONVERT_TO_DATATYPES) {
      Assert(d_ff.isNull() && d_tt.isNull());
      d_ff = d_ffDt;
      d_tt = d_ttDt;
    }
  }

  // assert that we set it up correctly
  Assert(!d_ff.isNull() && !d_tt.isNull());
  Assert(!d_ffDt.isNull() && !d_ttDt.isNull());
  Assert(d_ff != d_tt);
  Assert(d_ff.getType() == d_tt.getType());
  Assert(d_ffDt != d_ttDt);
  Assert(d_ffDt.getType() == d_ttDt.getType());

}/* BooleanTermConverter::BooleanTermConverter() */

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

// This function rewrites "in" as an "as"---this is actually expected
// to be for model-substitution, so the "in" is a Boolean-term-converted
// node, and "as" is the original.  See how it's used in function
// handling, below.
//
// Note this isn't the case any longer, and parts of what's below have
// been repurposed for *forward* conversion, meaning this works in either
// direction.
Node BooleanTermConverter::rewriteAs(TNode in, TypeNode as, std::map< TypeNode, bool >& processing) throw() {
  Debug("boolean-terms2") << "Rewrite as " << in << " " << as << std::endl;
  if(in.getType() == as) {
    return in;
  }
  if(in.getType().isBoolean()) {
    Assert(d_tt.getType() == as);
    return NodeManager::currentNM()->mkNode(kind::ITE, in, d_tt, d_ff);
  }
  if(as.isBoolean() && in.getType().isBitVector() && in.getType().getBitVectorSize() == 1) {
    return NodeManager::currentNM()->mkNode(kind::EQUAL, NodeManager::currentNM()->mkConst(BitVector(1u, 1u)), in);
  }
  TypeNode in_t = in.getType();
  if( processing.find( in_t )==processing.end() ){
    processing[in_t] = true;
    if(in.getType().isParametricDatatype() &&
      in.getType().isInstantiatedDatatype()) {
      // We have something here like (Pair Bool Bool)---need to dig inside
      // and make it (Pair BV1 BV1)
      Assert(as.isParametricDatatype() && as.isInstantiatedDatatype());
      const Datatype* dt2 = &as[0].getDatatype();
      std::vector<TypeNode> fromParams, toParams;
      for(unsigned i = 0; i < dt2->getNumParameters(); ++i) {
        fromParams.push_back(TypeNode::fromType(dt2->getParameter(i)));
        toParams.push_back(as[i + 1]);
      }
      const Datatype* dt1;
      if(d_datatypeCache.find(dt2) != d_datatypeCache.end()) {
        dt1 = d_datatypeCache[dt2];
      } else {
        dt1 = d_datatypeReverseCache[dt2];
      }
      Assert(dt1 != NULL, "expected datatype in cache");
      Assert(*dt1 == in.getType()[0].getDatatype(), "improper rewriteAs() between datatypes");
      Node out;
      for(size_t i = 0; i < dt1->getNumConstructors(); ++i) {
        DatatypeConstructor ctor = (*dt1)[i];
        NodeBuilder<> appctorb(kind::APPLY_CONSTRUCTOR);
        appctorb << (*dt2)[i].getConstructor();
        for(size_t j = 0; j < ctor.getNumArgs(); ++j) {
          TypeNode asType = TypeNode::fromType(SelectorType((*dt2)[i][j].getSelector().getType()).getRangeType());
          asType = asType.substitute(fromParams.begin(), fromParams.end(), toParams.begin(), toParams.end());
          appctorb << rewriteAs(NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR_TOTAL, ctor[j].getSelector(), in), asType, processing);
        }
        Node appctor = appctorb;
        if(i == 0) {
          out = appctor;
        } else {
          Node newOut = NodeManager::currentNM()->mkNode(kind::ITE, ctor.getTester(), appctor, out);
          out = newOut;
        }
      }
      processing.erase( in_t );
      return out;
    }
    if(in.getType().isDatatype()) {
      if(as.isBoolean() && in.getType().hasAttribute(BooleanTermAttr())) {
        processing.erase( in_t );
        return NodeManager::currentNM()->mkNode(kind::EQUAL, d_ttDt, in);
      }
      Assert(as.isDatatype());
      const Datatype* dt2 = &as.getDatatype();
      const Datatype* dt1;
      if(d_datatypeCache.find(dt2) != d_datatypeCache.end()) {
        dt1 = d_datatypeCache[dt2];
      } else {
        dt1 = d_datatypeReverseCache[dt2];
      }
      Assert(dt1 != NULL, "expected datatype in cache");
      Assert(*dt1 == in.getType().getDatatype(), "improper rewriteAs() between datatypes");
      Node out;
      for(size_t i = 0; i < dt1->getNumConstructors(); ++i) {
        DatatypeConstructor ctor = (*dt1)[i];
        NodeBuilder<> appctorb(kind::APPLY_CONSTRUCTOR);
        appctorb << (*dt2)[i].getConstructor();
        for(size_t j = 0; j < ctor.getNumArgs(); ++j) {
          appctorb << rewriteAs(NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR_TOTAL, ctor[j].getSelector(), in), TypeNode::fromType(SelectorType((*dt2)[i][j].getSelector().getType()).getRangeType()), processing);
        }
        Node appctor = appctorb;
        if(i == 0) {
          out = appctor;
        } else {
          Node newOut = NodeManager::currentNM()->mkNode(kind::ITE, ctor.getTester(), appctor, out);
          out = newOut;
        }
      }
      processing.erase( in_t );
      return out;
    }
    if(in.getType().isArray()) {
      // convert in to in'
      // e.g. in : (Array Int Bool)
      // for in' : (Array Int (_ BitVec 1))
      // then subs  in  |=>  \array_lambda ( \lambda (x:Int) . [convert (read a' x) x]
      Assert(as.isArray());
      Assert(as.getArrayIndexType() == in.getType().getArrayIndexType());
      Assert(as.getArrayConstituentType() != in.getType().getArrayConstituentType());
      Node x = NodeManager::currentNM()->mkBoundVar(as.getArrayIndexType());
      Node boundvars = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, x);
      Node sel = NodeManager::currentNM()->mkNode(kind::SELECT, in, x);
      Node selprime = rewriteAs(sel, as.getArrayConstituentType(), processing);
      Node lam = NodeManager::currentNM()->mkNode(kind::LAMBDA, boundvars, selprime);
      Node out = NodeManager::currentNM()->mkNode(kind::ARRAY_LAMBDA, lam);
      Assert(out.getType() == as);
      processing.erase( in_t );
      return out;
    }
    Unhandled(in);
  }else{
    Message() << "Type " << in_t << " involving Boolean sort is not supported." << std::endl;
    exit( 0 );
  }
}

const Datatype& BooleanTermConverter::convertDatatype(const Datatype& dt) throw() {
  const Datatype*& out = d_datatypeCache[&dt];
  if(out != NULL) {
    return *out;
  }

  Debug("boolean-terms") << "convertDatatype: considering " << dt.getName() << endl;
  for(Datatype::const_iterator c = dt.begin(); c != dt.end(); ++c) {
    TypeNode t = TypeNode::fromType((*c).getConstructor().getType());
    for(TypeNode::const_iterator a = t.begin(); a != t.end(); ++a) {
      TypeNode converted = convertType(*a, true);
      Debug("boolean-terms") << "GOT: " << converted << ":" << converted.getId() << endl;
      if(*a != converted) {
        SortConstructorType mySelfType;
        set<Type> unresolvedTypes;
        if(dt.isParametric()) {
          mySelfType = NodeManager::currentNM()->toExprManager()->mkSortConstructor(dt.getName() + "'", dt.getNumParameters());
          unresolvedTypes.insert(mySelfType);
        }
        vector<Datatype> newDtVector;
        if(dt.isParametric()) {
          newDtVector.push_back(Datatype(dt.getName() + "'", dt.getParameters(), false));
        } else {
          newDtVector.push_back(Datatype(dt.getName() + "'", false));
        }
        Datatype& newDt = newDtVector.front();
        Debug("boolean-terms") << "found a Boolean arg in constructor " << (*c).getName() << endl;
        for(c = dt.begin(); c != dt.end(); ++c) {
          DatatypeConstructor ctor((*c).getName() + "'", (*c).getTesterName() + "'");
          t = TypeNode::fromType((*c).getConstructor().getType());
          for(DatatypeConstructor::const_iterator a = (*c).begin(); a != (*c).end(); ++a) {
            Type argType = (*a).getType().getRangeType();
            if(argType.isDatatype() && DatatypeType(argType).getDatatype() == dt) {
              Debug("boolean-terms") << "argtype " << argType << " is self" << endl;
              if(dt.isParametric()) {
                Debug("boolean-terms") << "is-parametric self is " << mySelfType << endl;
                ctor.addArg((*a).getName() + "'", mySelfType.instantiate(DatatypeType(argType).getDatatype().getParameters()));
              } else {
                ctor.addArg((*a).getName() + "'", DatatypeSelfType());
              }
            } else {
              Debug("boolean-terms") << "argtype " << argType << " is NOT self" << endl;
              converted = convertType(TypeNode::fromType(argType), true);
              if(TypeNode::fromType(argType) != converted) {
                ctor.addArg((*a).getName() + "'", converted.toType());
              } else {
                ctor.addArg((*a).getName() + "'", argType);
              }
            }
          }
          newDt.addConstructor(ctor);
        }
        vector<DatatypeType> newDttVector =
          NodeManager::currentNM()->toExprManager()->mkMutualDatatypeTypes(newDtVector, unresolvedTypes);
        DatatypeType& newDtt = newDttVector.front();
        const Datatype& newD = newDtt.getDatatype();
        for(c = dt.begin(); c != dt.end(); ++c) {
          Debug("boolean-terms") << "constructor " << (*c).getConstructor() << ":" << (*c).getConstructor().getType() << " made into " << newD[(*c).getName() + "'"].getConstructor() << ":" << newD[(*c).getName() + "'"].getConstructor().getType() << endl;
          const DatatypeConstructor *newC;
          Node::fromExpr((*(newC = &newD[(*c).getName() + "'"])).getConstructor()).setAttribute(BooleanTermAttr(), Node::fromExpr((*c).getConstructor()));// other attr?
          Debug("boolean-terms") << "mapped " << newD[(*c).getName() + "'"].getConstructor() << " to " << (*c).getConstructor() << endl;
          d_varCache[Node::fromExpr((*c).getConstructor())] = Node::fromExpr(newD[(*c).getName() + "'"].getConstructor());
          d_varCache[Node::fromExpr((*c).getTester())] = Node::fromExpr(newD[(*c).getName() + "'"].getTester());
          for(DatatypeConstructor::const_iterator a = (*c).begin(); a != (*c).end(); ++a) {
            Node::fromExpr((*newC)[(*a).getName() + "'"].getSelector()).setAttribute(BooleanTermAttr(), Node::fromExpr((*a).getSelector()));// other attr?
            d_varCache[Node::fromExpr((*a).getSelector())] = Node::fromExpr(newD[(*c).getName() + "'"].getSelector((*a).getName() + "'"));
          }
        }
        out = &newD;
        d_datatypeReverseCache[&newD] = &dt;
        return newD;
      }
    }
  }

  // this is identity; don't need the reverse cache
  out = &dt;
  return dt;

}/* BooleanTermConverter::convertDatatype() */

TypeNode BooleanTermConverter::convertType(TypeNode type, bool datatypesContext) {
  Debug("boolean-terms") << "CONVERT-TYPE[" << type << ":" << type.getId() << ", " << datatypesContext << "]" << endl;
  // This function recursively converts the type.
  if(type.isBoolean()) {
    return datatypesContext ? d_ttDt.getType() : d_tt.getType();
  }
  const pair<TypeNode, bool> cacheKey(type, datatypesContext);
  if(d_typeCache.find(cacheKey) != d_typeCache.end()) {
    TypeNode out = d_typeCache[cacheKey];
    return out.isNull() ? type : out;
  }
  TypeNode& outNode = d_typeCache[cacheKey];
  if(type.getKind() == kind::DATATYPE_TYPE ||
     type.getKind() == kind::PARAMETRIC_DATATYPE) {
    bool parametric = (type.getKind() == kind::PARAMETRIC_DATATYPE);
    const Datatype& dt = parametric ? type[0].getDatatype() : type.getDatatype();
    TypeNode out = TypeNode::fromType(convertDatatype(dt).getDatatypeType());
    Debug("boolean-terms") << "AFTER, got "<< out << " param:" << parametric << endl;
    if(parametric) {
      // re-parameterize the translation
      vector<TypeNode> params = type.getParamTypes();
      for(size_t i = 0; i < params.size(); ++i) {
        Debug("boolean-terms") << "in loop, got "<< params[i] << endl;
        params[i] = convertType(params[i], true);
        Debug("boolean-terms") << "in loop, convert to "<< params[i] << endl;
      }
      params.insert(params.begin(), out[0]);
      out = NodeManager::currentNM()->mkTypeNode(kind::PARAMETRIC_DATATYPE, params);
      Debug("boolean-terms") << "got OUT: " << out << endl;
    }
    if(out != type) {
      outNode = out;// cache it
      Debug("boolean-terms") << "OUT is same as TYPE" << endl;
    } else Debug("boolean-terms") << "OUT is DIFFERENT FROM TYPE" << endl;
    return out;
  }
  if(!type.isSort() && type.getNumChildren() > 0) {
    Debug("boolean-terms") << "here at A for " << type << ":" << type.getId() << endl;
    // This should handle tuples and arrays ok.
    // Might handle function types too, but they can't go
    // in other types, so it doesn't matter.
    NodeBuilder<> b(type.getKind());
    if(type.getMetaKind() == kind::metakind::PARAMETERIZED) {
      b << type.getOperator();
    }
    for(TypeNode::iterator i = type.begin(); i != type.end(); ++i) {
      b << convertType(*i, false);
    }
    TypeNode out = b;
    if(out != type) {
      outNode = out;// cache it
    }
    Debug("boolean-terms") << "here at B, returning " << out << ":" << out.getId() << endl;
    return out;
  }
  // leave the cache at Null
  return type;
}/* BooleanTermConverter::convertType() */

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

Node BooleanTermConverter::rewriteBooleanTermsRec(TNode top, theory::TheoryId parentTheory, std::map<TNode, Node>& quantBoolVars) throw() {

  stack< triple<TNode, theory::TheoryId, bool> > worklist;
  worklist.push(triple<TNode, theory::TheoryId, bool>(top, parentTheory, false));
  stack< NodeBuilder<> > result;
  //AJR: not sure what the significance of "TUPLE" is here, seems to be a placeholder.  Since TUPLE is no longer a kind, replacing this with "AND".
  //result.push(NodeBuilder<>(kind::TUPLE));
  result.push(NodeBuilder<>(kind::AND));

  NodeManager* nm = NodeManager::currentNM();

  while(!worklist.empty()) {
    top = worklist.top().first;
    parentTheory = worklist.top().second;
    bool& childrenPushed = worklist.top().third;

    Kind k = top.getKind();
    kind::MetaKind mk = top.getMetaKind();

    // we only distinguish between datatypes, booleans, and "other", and we
    // don't even distinguish datatypes except when in "native" conversion
    // mode
    if(parentTheory != theory::THEORY_BOOL) {
      if(options::booleanTermConversionMode() != BOOLEAN_TERM_CONVERT_NATIVE ||
         parentTheory != theory::THEORY_DATATYPES) {
        parentTheory = theory::THEORY_BUILTIN;
      }
    }

    if(!childrenPushed) {
      Debug("boolean-terms") << "rewriteBooleanTermsRec: " << top << " - parentTheory=" << parentTheory << endl;

      BooleanTermVarCache::iterator i = d_varCache.find(top);
      if(i != d_varCache.end()) {
        result.top() << ((*i).second.isNull() ? Node(top) : (*i).second);
        worklist.pop();
        goto next_worklist;
      }
      BooleanTermCache::iterator j = d_termCache.find(pair<Node, theory::TheoryId>(top, parentTheory));
      if(j != d_termCache.end()) {
        result.top() << ((*j).second.isNull() ? Node(top) : (*j).second);
        worklist.pop();
        goto next_worklist;
      }

      if(quantBoolVars.find(top) != quantBoolVars.end()) {
        // this Bool variable is quantified over and we're changing it to a BitVector var
        if(parentTheory == theory::THEORY_BOOL) {
          result.top() << quantBoolVars[top].eqNode(d_tt);
        } else {
          result.top() << quantBoolVars[top];
        }
        worklist.pop();
        goto next_worklist;
      }

      if(parentTheory != theory::THEORY_BOOL && top.getType().isBoolean() && top.getKind()!=kind::SEP_STAR && top.getKind()!=kind::SEP_WAND) {
        // still need to rewrite e.g. function applications over boolean
        Node topRewritten = rewriteBooleanTermsRec(top, theory::THEORY_BOOL, quantBoolVars);
        Node n;
        if(parentTheory == theory::THEORY_DATATYPES) {
          n = nm->mkNode(kind::ITE, topRewritten, d_ttDt, d_ffDt);
        } else {
          n = nm->mkNode(kind::ITE, topRewritten, d_tt, d_ff);
        }
        Debug("boolean-terms") << "constructed ITE: " << n << endl;
        result.top() << n;
        worklist.pop();
        goto next_worklist;
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
            if(indexType.isBoolean()) {
              // change index type to BV(1) also
              indexType = d_tt.getType();
            }
            ArrayStoreAll asaRepl(nm->mkArrayType(indexType, d_tt.getType()).toType(),
                                  (asa.getExpr().getConst<bool>() ? d_tt : d_ff).toExpr());
            Node n = nm->mkConst(asaRepl);
            Debug("boolean-terms") << " returning new store_all: " << n << endl;
            result.top() << n;
            worklist.pop();
            goto next_worklist;
          }
          if(indexType.isBoolean()) {
            // must change index type to BV(1)
            indexType = d_tt.getType();
            ArrayStoreAll asaRepl(nm->mkArrayType(indexType, TypeNode::fromType(constituentType)).toType(), asa.getExpr());
            Node n = nm->mkConst(asaRepl);
            Debug("boolean-terms") << " returning new store_all: " << n << endl;
            result.top() << n;
            worklist.pop();
            goto next_worklist;
          }
        }
        result.top() << top;
        worklist.pop();
        goto next_worklist;
      } else if(mk == kind::metakind::VARIABLE) {
        TypeNode t = top.getType();
        if(t.isFunction()) {
          for(unsigned i = 0; i < t.getNumChildren(); ++i) {
            TypeNode newType = convertType(t[i], false);
            // is this the return type?  (allowed to be Bool)
            bool returnType = (i == t.getNumChildren() - 1);
            if(newType != t[i] && (!t[i].isBoolean() || !returnType)) {
              vector<TypeNode> argTypes = t.getArgTypes();
              for(unsigned j = 0; j < argTypes.size(); ++j) {
                argTypes[j] = convertType(argTypes[j], false);
              }
              TypeNode rangeType = t.getRangeType();
              if(!rangeType.isBoolean()) {
                rangeType = convertType(rangeType, false);
              }
              TypeNode newType = nm->mkFunctionType(argTypes, rangeType);
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
                if(t[j] != argTypes[j]) {
                  std::map< TypeNode, bool > processing;
                  bodyBuilder << rewriteAs(var, argTypes[j], processing);
                } else {
                  bodyBuilder << var;
                }
              }
              Node boundVars = boundVarsBuilder;
              Node body = bodyBuilder;
              if(t.getRangeType() != rangeType) {
                std::map< TypeNode, bool > processing;
                Node convbody = rewriteAs(body, t.getRangeType(), processing);
                body = convbody;
              }
              Node lam = nm->mkNode(kind::LAMBDA, boundVars, body);
              Debug("boolean-terms") << "substituting " << top << " ==> " << lam << endl;
              d_smt.d_theoryEngine->getModel()->addSubstitution(top, lam);
              d_varCache[top] = n;
              result.top() << n;
              worklist.pop();
              goto next_worklist;
            }
          }
        } else if(t.isArray()) {
          TypeNode indexType = convertType(t.getArrayIndexType(), false);
          TypeNode constituentType = convertType(t.getArrayConstituentType(), false);
          if(indexType != t.getArrayIndexType() && constituentType == t.getArrayConstituentType()) {
            TypeNode newType = nm->mkArrayType(indexType, constituentType);
            Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()) + "'",
                                  newType, "an array variable introduced by Boolean-term conversion",
                                  NodeManager::SKOLEM_EXACT_NAME);
            top.setAttribute(BooleanTermAttr(), n);
            Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
            Node n_ff = nm->mkNode(kind::SELECT, n, d_ff);
            Node n_tt = nm->mkNode(kind::SELECT, n, d_tt);
            Node base = nm->mkConst(ArrayStoreAll(ArrayType(top.getType().toType()), (*TypeEnumerator(n_ff.getType())).toExpr()));
            Node repl = nm->mkNode(kind::STORE,
                                   nm->mkNode(kind::STORE, base, nm->mkConst(true),
                                              n_tt),
                                   nm->mkConst(false), n_ff);
            Debug("boolean-terms") << "array replacement: " << top << " => " << repl << endl;
            d_smt.d_theoryEngine->getModel()->addSubstitution(top, repl);
            d_varCache[top] = n;
            result.top() << n;
            worklist.pop();
            goto next_worklist;
          } else if(indexType == t.getArrayIndexType() && constituentType != t.getArrayConstituentType()) {
            TypeNode newType = nm->mkArrayType(indexType, constituentType);
            Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()) + "'",
                                  newType, "an array variable introduced by Boolean-term conversion",
                                  NodeManager::SKOLEM_EXACT_NAME);
            top.setAttribute(BooleanTermAttr(), n);
            Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
            d_smt.d_theoryEngine->getModel()->addSubstitution(top, n);
            d_varCache[top] = n;
            result.top() << n;
            worklist.pop();
            goto next_worklist;
          } else if(indexType != t.getArrayIndexType() && constituentType != t.getArrayConstituentType()) {
            TypeNode newType = nm->mkArrayType(indexType, constituentType);
            Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()) + "'",
                                  newType, "an array variable introduced by Boolean-term conversion",
                                  NodeManager::SKOLEM_EXACT_NAME);
            top.setAttribute(BooleanTermAttr(), n);
            Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
            Node n_ff = nm->mkNode(kind::SELECT, n, d_ff);
            Node n_tt = nm->mkNode(kind::SELECT, n, d_tt);
            Node base = nm->mkConst(ArrayStoreAll(ArrayType(top.getType().toType()), nm->mkConst(false).toExpr()));
            Node repl = nm->mkNode(kind::STORE,
                                   nm->mkNode(kind::STORE, base, nm->mkConst(false),
                                              nm->mkNode(kind::EQUAL, n_ff, d_tt)), nm->mkConst(true),
                                   nm->mkNode(kind::EQUAL, n_tt, d_tt));
            Debug("boolean-terms") << "array replacement: " << top << " => " << repl << endl;
            d_smt.d_theoryEngine->getModel()->addSubstitution(top, repl);
            d_varCache[top] = n;
            result.top() << n;
            worklist.pop();
            goto next_worklist;
          }
          d_varCache[top] = Node::null();
          result.top() << top;
          worklist.pop();
          goto next_worklist;
        } else if(t.isDatatype() || t.isParametricDatatype()) {
          Debug("boolean-terms") << "found a var of datatype type" << endl;
          TypeNode newT = convertType(t, parentTheory == theory::THEORY_DATATYPES);
          if(t != newT) {
            Assert(d_varCache.find(top) == d_varCache.end(),
                   "Node `%s' already in cache ?!", top.toString().c_str());
            Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()) + "'",
                                  newT, "a datatype variable introduced by Boolean-term conversion",
                                  NodeManager::SKOLEM_EXACT_NAME);
            Debug("boolean-terms") << "adding subs: " << top << " :=> " << n << endl;
            top.setAttribute(BooleanTermAttr(), n);
            d_smt.d_theoryEngine->getModel()->addSubstitution(top, n);
            Debug("boolean-terms") << "constructed: " << n << " of type " << newT << endl;
            d_varCache[top] = n;
            result.top() << n;
            worklist.pop();
            goto next_worklist;
          } else {
            d_varCache[top] = Node::null();
            result.top() << top;
            worklist.pop();
            goto next_worklist;
          }
        } else if(t.isConstructor()) {
          Assert(parentTheory != theory::THEORY_BOOL);
          Assert(t[t.getNumChildren() - 1].getKind() == kind::DATATYPE_TYPE ||
                 t[t.getNumChildren() - 1].getKind() == kind::PARAMETRIC_DATATYPE);
          const Datatype& dt = t[t.getNumChildren() - 1].getKind() == kind::DATATYPE_TYPE ?
            t[t.getNumChildren() - 1].getDatatype() :
            t[t.getNumChildren() - 1][0].getDatatype();
          TypeNode dt2type = convertType(TypeNode::fromType(dt.getDatatypeType()), parentTheory == theory::THEORY_DATATYPES);
          const Datatype& dt2 = (dt2type.getKind() == kind::DATATYPE_TYPE ? dt2type : dt2type[0]).getDatatype();
          if(dt != dt2) {
            Assert(d_varCache.find(top) != d_varCache.end(),
                   "constructor `%s' not in cache", top.toString().c_str());
            result.top() << d_varCache[top].get();
            worklist.pop();
            goto next_worklist;
          }
          d_varCache[top] = Node::null();
          result.top() << top;
          worklist.pop();
          goto next_worklist;
        } else if(t.isTester() || t.isSelector()) {
          Assert(parentTheory != theory::THEORY_BOOL);
          const Datatype& dt = t[0].getKind() == kind::DATATYPE_TYPE ?
            t[0].getDatatype() :
            t[0][0].getDatatype();
          TypeNode dt2type = convertType(TypeNode::fromType(dt.getDatatypeType()), parentTheory == theory::THEORY_DATATYPES);
          const Datatype& dt2 = (dt2type.getKind() == kind::DATATYPE_TYPE ? dt2type : dt2type[0]).getDatatype();
          if(dt != dt2) {
            Assert(d_varCache.find(top) != d_varCache.end(),
                   "tester or selector `%s' not in cache", top.toString().c_str());
            result.top() << d_varCache[top].get();
            worklist.pop();
            goto next_worklist;
          } else {
            d_varCache[top] = Node::null();
            result.top() << top;
            worklist.pop();
            goto next_worklist;
          }
        } else if(!t.isSort() && t.getNumChildren() > 0) {
          if( t.getKind()!=kind::SEP_STAR && t.getKind()!=kind::SEP_WAND ){
            for(TypeNode::iterator i = t.begin(); i != t.end(); ++i) {
              if((*i).isBoolean()) {
                vector<TypeNode> argTypes(t.begin(), t.end());
                replace(argTypes.begin(), argTypes.end(), *i, d_tt.getType());
                TypeNode newType = nm->mkTypeNode(t.getKind(), argTypes);
                Node n = nm->mkSkolem(top.getAttribute(expr::VarNameAttr()),
                                      newType, "a variable introduced by Boolean-term conversion",
                                      NodeManager::SKOLEM_EXACT_NAME);
                Debug("boolean-terms") << "constructed: " << n << " of type " << newType << endl;
                top.setAttribute(BooleanTermAttr(), n);
                d_varCache[top] = n;
                result.top() << n;
                worklist.pop();
                goto next_worklist;
              }
            }
          }
        }
        result.top() << top;
        worklist.pop();
        goto next_worklist;
      }
      switch(k) {
      //case kind::INST_ATTRIBUTE:
      case kind::BOUND_VAR_LIST:
        result.top() << top;
        worklist.pop();
        goto next_worklist;

      case kind::REWRITE_RULE:
      case kind::RR_REWRITE:
      case kind::RR_DEDUCTION:
      case kind::RR_REDUCTION:
      case kind::SEP_STAR:
      case kind::SEP_WAND:
        // not yet supported
        result.top() << top;
        worklist.pop();
        goto next_worklist;

      case kind::FORALL:
      case kind::EXISTS: {
        Debug("bt") << "looking at quantifier -> " << top << endl;
        set<TNode> ourVars;
        set<TNode> output;
        for(TNode::iterator i = top[0].begin(); i != top[0].end(); ++i) {
          if((*i).getType().isBoolean()) {
            ourVars.insert(*i);
          } else if(convertType((*i).getType(), false) != (*i).getType()) {
            output.insert(*i);
          }
        }
        if(ourVars.empty() && output.empty()) {
          // Simple case, quantifier doesn't quantify over Boolean vars,
          // no special handling needed for quantifier.  Fall through.
          Debug("bt") << "- quantifier simple case (1), no Boolean vars bound" << endl;
        } else {
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
              Node newVar = nm->mkBoundVar((*i).toString(), convertType((*i).getType(), false));
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
            Node body = rewriteBooleanTermsRec(top[1], theory::THEORY_BOOL, quantBoolVars);
            Node quant;
            if( top.getNumChildren()==3 ){
              Node ipl = rewriteBooleanTermsRec(top[2], theory::THEORY_BOOL, quantBoolVars);
              quant = nm->mkNode(top.getKind(), boundVarList, body, ipl );
            }else{
              quant = nm->mkNode(top.getKind(), boundVarList, body);
            }
            Debug("bt") << "rewrote quantifier to -> " << quant << endl;
            d_termCache[make_pair(top, theory::THEORY_BOOL)] = quant;
            d_termCache[make_pair(top, theory::THEORY_BUILTIN)] = quant.iteNode(d_tt, d_ff);
            d_termCache[make_pair(top, theory::THEORY_DATATYPES)] = quant.iteNode(d_tt, d_ff);
            result.top() << quant;
            worklist.pop();
            goto next_worklist;
          }
        }
        /* intentional fall-through for some cases above */
      }

      default:
        result.push(NodeBuilder<>(k));
        Debug("bt") << "looking at: " << top << endl;
        // rewrite the operator, as necessary
        if(mk == kind::metakind::PARAMETERIZED) {
          if(k == kind::APPLY_TYPE_ASCRIPTION) {
            Node asc = nm->mkConst(AscriptionType(convertType(TypeNode::fromType(top.getOperator().getConst<AscriptionType>().getType()), parentTheory == theory::THEORY_DATATYPES).toType()));
            result.top() << asc;
            Debug("boolean-terms") << "setting " << top.getOperator() << ":" << top.getOperator().getId() << " to point to " << asc << ":" << asc.getId() << endl;
            asc.setAttribute(BooleanTermAttr(), top.getOperator());
          } else if(kindToTheoryId(k) != THEORY_BV &&
                    k != kind::TUPLE_UPDATE &&
                    k != kind::RECORD_UPDATE &&
                    k != kind::DIVISIBLE &&
        // Theory parametric functions go here
        k != kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR &&
        k != kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT &&
        k != kind::FLOATINGPOINT_TO_FP_REAL &&
        k != kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR &&
        k != kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR &&
        k != kind::FLOATINGPOINT_TO_UBV &&
        k != kind::FLOATINGPOINT_TO_SBV &&
        k != kind::FLOATINGPOINT_TO_REAL
        ) {
            Debug("bt") << "rewriting: " << top.getOperator() << endl;
            result.top() << rewriteBooleanTermsRec(top.getOperator(), theory::THEORY_BUILTIN, quantBoolVars);
            Debug("bt") << "got: " << result.top().getOperator() << endl;
          } else {
            result.top() << top.getOperator();
          }
        }
        // push children
        for(int i = top.getNumChildren() - 1; i >= 0; --i) {
          Debug("bt") << "rewriting: " << top[i] << endl;
          worklist.push(triple<TNode, theory::TheoryId, bool>(top[i], top.getKind() == kind::CHAIN ? parentTheory : ((isBoolean(top, i) || top.getKind()==kind::INST_ATTRIBUTE) ? theory::THEORY_BOOL : (top.getKind() == kind::APPLY_CONSTRUCTOR ? theory::THEORY_DATATYPES : theory::THEORY_BUILTIN)), false));
          //b << rewriteBooleanTermsRec(top[i], isBoolean(top, i) ? , quantBoolVars);
          //Debug("bt") << "got: " << b[b.getNumChildren() - 1] << endl;
        }
        childrenPushed = true;
      }
    } else {
      Node n = result.top();
      result.pop();
      Debug("boolean-terms") << "constructed: " << n << " of type " << n.getType() << endl;
      if(parentTheory == theory::THEORY_BOOL) {
        if(n.getType().isBitVector() &&
           n.getType().getBitVectorSize() == 1) {
          n = nm->mkNode(kind::EQUAL, n, d_tt);
        } else if(n.getType().isDatatype() &&
                  n.getType().hasAttribute(BooleanTermAttr())) {
          n = nm->mkNode(kind::EQUAL, n, d_ttDt);
        }
      }
      d_termCache[make_pair(top, parentTheory)] = n;
      result.top() << n;
      worklist.pop();
      goto next_worklist;
    }

  next_worklist:
    ;
  }

  Assert(worklist.size() == 0);
  Assert(result.size() == 1);
  Node retval = result.top()[0];
  result.top().clear();
  result.pop();
  return retval;

}/* BooleanTermConverter::rewriteBooleanTermsRec() */

}/* CVC4::smt namespace */
}/* CVC4 namespace */
