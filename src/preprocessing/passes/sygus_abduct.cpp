/*********************                                                        */
/*! \file sygus_abduct.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus inference module
 **/

#include "preprocessing/passes/sygus_abduct.h"

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_util.h"
#include "expr/node_algorithm.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

SygusAbduct::SygusAbduct(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sygus-infer"){};

PreprocessingPassResult SygusAbduct::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager * nm = NodeManager::currentNM();
  Trace("sygus-infer") << "Run sygus abduct..." << std::endl;
  std::unordered_set<Node, NodeHashFunction> symset;
  std::vector< Node >& asserts = assertionsToPreprocess->ref();
  for( unsigned i=0, size = asserts.size(); i<size; i++ )
  {
    expr::getSymbols( asserts[i], symset );
  }
  std::vector< Node > syms;
  std::vector< Node > vars;
  std::vector< Node > varlist;
  std::vector< TypeNode > varlistTypes;
  for( const Node& s : symset )
  {
    std::stringstream ss;
    ss << s;
    TypeNode tn =s.getType();
    Node vlv = nm->mkBoundVar(ss.str(),tn);
    varlist.push_back(vlv);
    varlistTypes.push_back(tn);
    Node var = nm->mkBoundVar(tn);
    syms.push_back(s);
    vars.push_back(var);
  }
  // make the abduction predicate to synthesize
  TypeNode abdType = nm->mkPredicateType( varlistTypes );
  Node abd = nm->mkBoundVar("A",abdType);
  std::vector< Node > achildren;
  achildren.push_back(abd);
  achildren.insert(achildren.end(),vars.begin(),vars.end());
  Node abdApp = nm->mkNode(APPLY_UF,achildren);
  // set the sygus bound variable list
  Node abvl = nm->mkNode(BOUND_VAR_LIST,varlist);
  abd.setAttribute(theory::SygusSynthFunVarListAttribute(),abvl);  
  
  Node input = asserts.size()==1 ? asserts[0] : nm->mkNode( AND, asserts );
  input = input.substitute(syms.begin(),syms.end(),vars.begin(),vars.end());
  // A(x) => ~input( x )
  input = nm->mkNode( OR, abdApp.negate(), input.negate() );
  
  Node res = input.negate();
  if( !vars.empty() )
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
    // exists x. ~( A( x ) => ~input( x ) )
    res = nm->mkNode(EXISTS, bvl, res);
  }
  
  // sygus attribute
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  theory::SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, instAttr);
  
  Node fbvl = nm->mkNode(BOUND_VAR_LIST,abd);
  
  // forall A. exists x. ~( A( x ) => ~input( x ) )
  res = nm->mkNode(FORALL, fbvl, res, instAttrList );
  
  Node trueNode = nm->mkConst(true);
  
  assertionsToPreprocess->replace(0, res);
  for (unsigned i = 1, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i, trueNode);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
