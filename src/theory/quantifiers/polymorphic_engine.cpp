/*********************                                                        */
/*! \file rewrite_engine.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewrite engine module
 **
 ** This class manages rewrite rules for quantifiers
 **/

#include "theory/quantifiers/polymorphic_engine.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/inst_match_generator.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/term_database.h"
#include "expr/node_manager_attributes.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

PolymorphicEngine::PolymorphicEngine( context::Context* c, QuantifiersEngine* qe ) : QuantifiersModule(qe) {
}

bool PolymorphicEngine::needsCheck( Theory::Effort e ) { return e>=Theory::EFFORT_LAST_CALL; }

Node substituteAll(TNode n,
                   std::hash_map<TypeNode, TypeNode, TypeNode::HashFunction>& ty_subst,
                   std::hash_map<TNode, TNode, TNodeHashFunction>& subst){

  Trace("para-substitute") << "substitute:" << n << std::endl;

  // in cache?
  typename std::hash_map<TNode, TNode, TNodeHashFunction>::const_iterator i = subst.find(n);
  if(i != subst.end()) {
    return (*i).second;
  }

  // otherwise compute
  if(n.getKind() == kind::BOUND_VARIABLE){
    TypeNode ty = n.getType().substitute(ty_subst);
    Node n2 = n;
    if(ty != n.getType() ){
      string name;
      if(n.getAttribute(expr::VarNameAttr(), name)) {
        n2 = NodeManager::currentNM()->mkBoundVar(name,ty);
      } else {
        n2 = NodeManager::currentNM()->mkBoundVar(ty);
      };
      Trace("para-substitute") << "BoundVar " << n << " becomes " << n2 << std::endl;
    };
    subst[n] = n2;
    return n2;
  } else if (n.getType().isFunction() && NodeManager::currentNM()->isPolymorphicFunctionInstance(n)){
    TypeNode sig = n.getType().substitute(ty_subst);
    Node n2 = n;
    if(sig != n.getType() ){
      n2 = NodeManager::currentNM()->instanciatePolymorphicFunction(
                                                                   NodeManager::currentNM()->getPolymorphicFunction(n),sig);
    }
    Trace("para-substitute") << "PolymorphicFunction " << n << " becomes " << n2 << std::endl;
    subst[n] = n2;
    return n2;
  } else {

    Kind kind = n.getKind();
    if(kind == kind::EQUAL && n[0].getType().substitute(ty_subst).isBoolean() ){
      kind = kind::IFF;
    }

    NodeBuilder<> nb(kind);
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      // push the operator
      nb << substituteAll(n.getOperator(),ty_subst,subst);
    }
    for(TNode::const_iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      nb << substituteAll(*i,ty_subst,subst);
    }
    Node n2 = nb;
    Trace("para-substitute") << "Application " << n << " becomes " << n2 << std::endl;
    subst[n] = n2;
    return n2;
  }
}

void PolymorphicEngine::check( Theory::Effort e, unsigned quant_e ){

  std::hash_map<TypeNode, TypeNode, TypeNode::HashFunction> ty_subst = ty_subst;

  for(std::vector< Node >::const_iterator lemma = d_lemma.begin(); lemma != d_lemma.end(); ++lemma){
          Trace("para") << "try instantiate lemma:" << *lemma << std::endl;
          TNode bv = (*lemma)[0];
          TNode body = (*lemma)[1];

          std::map< TypeNode, std::vector< Node > >& type_map = d_quantEngine->getTermDatabase()->d_type_map;

          std::vector< std::map< TypeNode, std::vector< Node > >::const_iterator > next_ty(bv.getNumChildren());

          size_t v_id=0;
          next_ty[0] = type_map.begin();
          while (true){
            Assert( v_id < bv.getNumChildren() );
            if(v_id == 0){ ty_subst.clear(); }

            if ( next_ty[v_id] == type_map.end () ) {
              if(v_id == 0) break;
              --v_id;
            } else {

              ty_subst[ bv[v_id].getType() ] = next_ty[v_id]->first;
              Trace("para") << bv[v_id].getType() << "->" << next_ty[v_id]->first << ", ";

              ++next_ty[v_id];

              if ( v_id + 1 == bv.getNumChildren() ){
                Trace("para") << std::endl;

                std::hash_map<TypeNode, TypeNode, TypeNode::HashFunction> ty_subst2 = ty_subst;
                std::hash_map<TNode, TNode, TNodeHashFunction> subst;

                d_quantEngine->addLemma(substituteAll(body,ty_subst2,subst));
              } else {
                ++v_id;
                next_ty[v_id] = type_map.begin();
              }
            }

          }
  }
};

/* Called for new quantifiers */
void PolymorphicEngine::registerQuantifier( Node q ){
  if(TermDb::isPolymorphic(q)){
      Trace("para") << "register new lemma:" << q << std::endl;
      d_lemma.push_back(q);
    }

};
void PolymorphicEngine::assertNode( Node n ){};

