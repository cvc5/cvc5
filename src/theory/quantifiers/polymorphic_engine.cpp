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
#include "theory/quantifiers/inst_match_generator.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/term_database.h"
#include "expr/node_manager_attributes.h"
#include "expr/datatype.h"
#include "options/quantifiers_options.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

PolymorphicEngine::PolymorphicEngine( context::Context* c, QuantifiersEngine* qe ) : QuantifiersModule(qe) {

}

void PolymorphicEngine::presolve() {
  // clear caches on every new call to presolve
  d_doneType.clear();
  d_ntermsProcessed.clear();
  d_csttrigger.clear();
}

bool PolymorphicEngine::needsCheck( Theory::Effort e ) { 
  return e>=Theory::EFFORT_LAST_CALL; 
}

Node substituteAll( TNode n,
                    std::unordered_map<TypeNode, TypeNode, TypeNode::HashFunction>& ty_subst,
                    std::unordered_map<TNode, TNode, TNodeHashFunction>& subst ){

  Trace("para-substitute") << "substitute:" << n << std::endl;

  // in cache?
  typename std::unordered_map<TNode, TNode, TNodeHashFunction>::const_iterator i = subst.find(n);
  if(i != subst.end()) {
    return (*i).second;
  }

  // otherwise compute
  /** Bound variable */
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
    /** As for algebraic datatype */
  } else if (n.getKind() == kind::ASCRIPTION_TYPE) {
    TypeNode ty = TypeNode::fromType(n.getConst<AscriptionType>().getType());
    TypeNode ty2 = ty.substitute(ty_subst);
    Node n2 = n;
    if (ty != ty2){
      n2 = NodeManager::currentNM()->mkConst(AscriptionType(ty2.toType()));
    };
    subst[n] = n2;
    return n2;
    /** After this point we should be able to take the type of the node */
    /** polymorphic function */
  } else if (n.getType().isFunction() &&
             NodeManager::currentNM()->isPolymorphicFunctionInstance(n)){
    TypeNode sig = n.getType().substitute(ty_subst);
    Node n2 = n;
    if(sig != n.getType() ){
      n2 = NodeManager::currentNM()->instantiatePolymorphicFunction(
                                                                   NodeManager::currentNM()->getPolymorphicFunction(n),sig);
    }
    Trace("para-substitute") << "PolymorphicFunction " << n << " becomes " << n2 << std::endl;
    subst[n] = n2;
    return n2;
  } else if ( n.getNumChildren() == 0 &&
              n.getMetaKind() != kind::metakind::PARAMETERIZED
              ){
    subst[n] = n;
    Trace("para-substitute") << "Constant " << n << " stays as " << n << std::endl;
    return n;
  } else {

    Kind kind = n.getKind();

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

void PolymorphicEngine::instantiate( paralemma& lemma,
                                     std::unordered_map<TypeNode, TypeNode, TypeNode::HashFunction>& ty_subst,
                                     size_t v_id,
                                     bool todo_used,
                                     std::unordered_set<TypeNode, TypeNode::HashFunction>& doneType,
                                     std::unordered_set<TypeNode, TypeNode::HashFunction>& todoType ){
  Assert( v_id < lemma.bv.getNumChildren() );

  std::unordered_set<TypeNode, TypeNode::HashFunction>* iterType = &doneType;
  for(int i=0; i<=1; i++){

    if(!todo_used && i==0 && v_id + 1 == lemma.bv.getNumChildren()) continue;

    if(i==0){
      iterType = &doneType;
    } else {
      iterType = &todoType;
      todo_used = true;
    }

    for(std::unordered_set<TypeNode, TypeNode::HashFunction>::const_iterator next_ty = iterType->begin();
        next_ty != iterType->end(); next_ty++){

      ty_subst[ lemma.bv[v_id].getType() ] = *next_ty;
      Trace("para") << lemma.bv[v_id].getType() << (i==0? "->" : ">>") << *next_ty << ", ";

      if ( v_id + 1 == lemma.bv.getNumChildren() ){
        Assert( todo_used );
        Trace("para") << std::endl;

        std::unordered_map<TypeNode, TypeNode, TypeNode::HashFunction> ty_subst2 = ty_subst;
        std::unordered_map<TNode, TNode, TNodeHashFunction> subst;

        Node lem = substituteAll(lemma.body,ty_subst2,subst);
        Trace("para") << "  -instantiated to:" << lem << std::endl;
        lem = NodeManager::currentNM()->mkNode( OR, lemma.origlemma.negate(), lem );
        Assert ( lem.getType(true).isBoolean());

        if(lemma.polymorphicConstants.empty()){
          Trace("para") << "  -no polymorphic constants out of binder" << std::endl;
          d_quantEngine->addLemma(lem);
        } else {
          //put the lemma on hold, wait for one of the polymorphic constant instantiated to appear
          for(std::unordered_set<TNode,TNodeHashFunction>::const_iterator cst = lemma.polymorphicConstants.begin();
              cst != lemma.polymorphicConstants.end(); cst++){
            Node cst_inst = substituteAll(*cst,ty_subst2,subst);
            if(getTermDatabase()->isTermAdded(cst_inst)){
              Trace("para") << "  -already present: " << cst_inst << std::endl;
              d_quantEngine->addLemma(lem);
              break; // we don't need to add more terms
            } else {
              Trace("para") << "  -wait for: " << cst_inst << std::endl;
              d_csttrigger[cst_inst].push_back(lem);
            }
          }
        }
      } else {
        instantiate(lemma, ty_subst, v_id+1, todo_used, doneType, todoType);
      }
    }
  }
}

void PolymorphicEngine::check( Theory::Effort e, unsigned quant_e ){

  std::unordered_set<TypeNode, TypeNode::HashFunction> todoType;

  Trace("para") << "[Para] pending lemmas = " << d_lemma.size() << std::endl;

  for( std::map< TypeNode, std::vector< Node > >::const_iterator ty = d_quantEngine->getTermDatabase()->d_type_map.begin(),
         end = d_quantEngine->getTermDatabase()->d_type_map.end(); ty !=end; ty++){
    TypeNode curr = ty->first;
    unsigned termsProcessed = 0;
    // get num terms we have called newTerm on
    std::map< TypeNode, unsigned >::iterator ntp_it = d_ntermsProcessed.find( curr );
    if( ntp_it!=d_ntermsProcessed.end() ){
      termsProcessed = ntp_it->second;
    }
    Trace("para") << "Check type " << curr << " with " << ty->second.size();
    Trace("para") << " ground terms (" << termsProcessed << ") already processed.." << std::endl;
    // call newTerm for unprocessed terms
    for( unsigned j=termsProcessed; j<ty->second.size(); j++ ){
      newTerm( ty->second[j] );    
    }
    d_ntermsProcessed[curr] = ty->second.size();
    if( d_doneType.find(curr) == d_doneType.end() ){
      Trace("para") << "  to process : " << curr << std::endl;
      todoType.insert(curr);
    }
  }

  if( !todoType.empty() ){

    std::unordered_map<TypeNode, TypeNode, TypeNode::HashFunction> ty_subst = ty_subst;

    for(size_t i = 0; i < d_lemma.size(); i++){
      Trace("para") << "try instantiate lemma:" << d_lemma[i].origlemma << std::endl;

      ty_subst.clear();

      instantiate(d_lemma[i], ty_subst, 0, false, d_doneType, todoType);
    }


    d_doneType.insert(todoType.begin(),todoType.end());
  }
}

bool hasPolymorphicTypeVariable(const TypeNode& type) {

  // otherwise compute
  for(TypeNode::const_iterator i = type.begin(),
        iend = type.end(); i != iend; ++i) {
    if(NodeManager::currentNM()->isPolymorphicTypeVar(*i) ||
       hasPolymorphicTypeVariable(*i) ){
      return true;
    }
  }
  return false;
}

/** Test if any polymorphic function is under quantifiers (usual one, which bind term variable) */
void findPolymorphicConstants(TNode n, std::unordered_set<TNode, TNodeHashFunction> &csts){

  // otherwise compute
  /** Bound variable */
  if(n.getKind() == kind::FORALL){
    return;
  } else if (n.getKind() == kind::ASCRIPTION_TYPE) {
    return;
    /** After this point we should be able to take the type of the node */
    /** polymorphic function */
  } else {

    if ( hasPolymorphicTypeVariable(n.getType()) ){
      csts.insert(n);
    }

    for(TNode::const_iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      findPolymorphicConstants(*i,csts);
    }
    return;
  }
}


paralemma::paralemma(Node lemma) {
  Assert( TermDb::isPolymorphic(lemma) );

  bv = lemma[0];
  origlemma = lemma;
  body = lemma[1];

  findPolymorphicConstants(body,polymorphicConstants);
}


/* Called for new quantifiers */
void PolymorphicEngine::registerQuantifier( Node q ){
  if( TermDb::isPolymorphic(q) ){
    Trace("para") << "[Para] register quantifier:" << q << std::endl;
    d_lemma.push_back(paralemma(q));

    if( d_doneType.size()!=0 ){
      std::unordered_map<TypeNode, TypeNode, TypeNode::HashFunction> ty_subst = ty_subst;
      std::unordered_set<TypeNode, TypeNode::HashFunction> empty;
      instantiate(d_lemma.back(), ty_subst, 0, false, empty, d_doneType);
    }
  }
}

void PolymorphicEngine::assertNode( Node n ){

}

void PolymorphicEngine::newTerm( Node cst_inst ){
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction>::iterator v = d_csttrigger.find(cst_inst);
  if( v!=d_csttrigger.end() ){
    Trace("para") << "[Para] new_term:" << cst_inst << std::endl;
    for(std::vector<Node>::const_iterator lem = v->second.begin();
        lem != v->second.end(); lem++){
      Trace("para") << " - add: " << *lem << std::endl;
      d_quantEngine->addLemma(*lem);
    }
    d_csttrigger.erase(v);
  }else{
    Trace("para") << "[Para] new_term ignored : " << cst_inst << std::endl;
  }
}

