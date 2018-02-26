/*********************                                                        */
/*! \file quantifiers_attributes.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of QuantifiersAttributes class
 **/

#include "theory/quantifiers/quantifiers_attributes.h"

#include "theory/quantifiers_engine.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/ce_guided_instantiation.h"
#include "theory/quantifiers/fun_def_engine.h"
#include "theory/quantifiers/rewrite_engine.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

QuantAttributes::QuantAttributes( QuantifiersEngine * qe ) : 
d_quantEngine(qe) {

}  
  
void QuantAttributes::setUserAttribute( const std::string& attr, Node n, std::vector< Node >& node_values, std::string str_value ){
  Trace("quant-attr-debug") << "Set " << attr << " " << n << std::endl;
  if( attr=="axiom" ){
    Trace("quant-attr-debug") << "Set axiom " << n << std::endl;
    AxiomAttribute aa;
    n.setAttribute( aa, true );
  }else if( attr=="conjecture" ){
    Trace("quant-attr-debug") << "Set conjecture " << n << std::endl;
    ConjectureAttribute ca;
    n.setAttribute( ca, true );
  }else if( attr=="fun-def" ){
    Trace("quant-attr-debug") << "Set function definition " << n << std::endl;
    FunDefAttribute fda;
    n.setAttribute( fda, true );
  }else if( attr=="sygus" ){
    Trace("quant-attr-debug") << "Set sygus " << n << std::endl;
    SygusAttribute ca;
    n.setAttribute( ca, true );
  } else if (attr == "sygus-synth-grammar") {
    Assert( node_values.size()==1 );
    Trace("quant-attr-debug") << "Set sygus synth grammar " << n << " to "
                              << node_values[0] << std::endl;
    SygusSynthGrammarAttribute ssg;
    n.setAttribute(ssg, node_values[0]);
  }else if( attr=="sygus-synth-fun-var-list" ){
    Assert( node_values.size()==1 );
    Trace("quant-attr-debug") << "Set sygus synth fun var list to " << n << " to "  << node_values[0] << std::endl;
    SygusSynthFunVarListAttribute ssfvla;
    n.setAttribute( ssfvla, node_values[0] );
  }else if( attr=="synthesis" ){
    Trace("quant-attr-debug") << "Set synthesis " << n << std::endl;
    SynthesisAttribute ca;
    n.setAttribute( ca, true );
  }else if( attr=="quant-inst-max-level" ){
    Assert( node_values.size()==1 );
    uint64_t lvl = node_values[0].getConst<Rational>().getNumerator().getLong();
    Trace("quant-attr-debug") << "Set instantiation level " << n << " to " << lvl << std::endl;
    QuantInstLevelAttribute qila;
    n.setAttribute( qila, lvl );
  }else if( attr=="rr-priority" ){
    Assert( node_values.size()==1 );
    uint64_t lvl = node_values[0].getConst<Rational>().getNumerator().getLong();
    Trace("quant-attr-debug") << "Set rewrite rule priority " << n << " to " << lvl << std::endl;
    RrPriorityAttribute rrpa;
    n.setAttribute( rrpa, lvl );
  }else if( attr=="quant-elim" ){
    Trace("quant-attr-debug") << "Set quantifier elimination " << n << std::endl;
    QuantElimAttribute qea;
    n.setAttribute( qea, true );
  }else if( attr=="quant-elim-partial" ){
    Trace("quant-attr-debug") << "Set partial quantifier elimination " << n << std::endl;
    QuantElimPartialAttribute qepa;
    n.setAttribute( qepa, true );
  }
}

bool QuantAttributes::checkRewriteRule( Node q ) {
  return !getRewriteRule( q ).isNull();
}

Node QuantAttributes::getRewriteRule( Node q ) {
  if (q.getKind() == FORALL && q.getNumChildren() == 3
      && q[2][0].getNumChildren() > 0
      && q[2][0][0].getKind() == REWRITE_RULE)
  {
    return q[2][0][0];
  }else{
    return Node::null();
  }
}

bool QuantAttributes::checkFunDef( Node q ) {
  return !getFunDefHead( q ).isNull();
}

bool QuantAttributes::checkFunDefAnnotation( Node ipl ) {
  if( !ipl.isNull() ){
    for( unsigned i=0; i<ipl.getNumChildren(); i++ ){
      if( ipl[i].getKind()==INST_ATTRIBUTE ){
        if( ipl[i][0].getAttribute(FunDefAttribute()) ){
          return true;
        }
      }
    }
  }
  return false;
}

Node QuantAttributes::getFunDefHead( Node q ) {
  //&& q[1].getKind()==EQUAL && q[1][0].getKind()==APPLY_UF &&
  if( q.getKind()==FORALL && q.getNumChildren()==3 ){
    Node ipl = q[2];
    for (unsigned i = 0; i < ipl.getNumChildren(); i++)
    {
      if (ipl[i].getKind() == INST_ATTRIBUTE
          && ipl[i][0].getAttribute(FunDefAttribute()))
      {
        return ipl[i][0];
      }
    }
  }
  return Node::null();
}
Node QuantAttributes::getFunDefBody( Node q ) {
  Node h = getFunDefHead( q );
  if( !h.isNull() ){
    if( q[1].getKind()==EQUAL ){
      if( q[1][0]==h ){
        return q[1][1];
      }else if( q[1][1]==h ){
        return q[1][0];
      }
    }else{
      Node atom = q[1].getKind()==NOT ? q[1][0] : q[1];
      bool pol = q[1].getKind()!=NOT;
      if( atom==h ){
        return NodeManager::currentNM()->mkConst( pol );
      }
    }
  }
  return Node::null();
}

bool QuantAttributes::checkSygusConjecture( Node q ) {
  return ( q.getKind()==FORALL && q.getNumChildren()==3 ) ? checkSygusConjectureAnnotation( q[2] ) : false;
}

bool QuantAttributes::checkSygusConjectureAnnotation( Node ipl ){
  if( !ipl.isNull() ){
    for( unsigned i=0; i<ipl.getNumChildren(); i++ ){
      if( ipl[i].getKind()==INST_ATTRIBUTE ){
        Node avar = ipl[i][0];
        if( avar.getAttribute(SygusAttribute()) ){
          return true;
        }
      }
    }
  }
  return false;
}

bool QuantAttributes::checkQuantElimAnnotation( Node ipl ) {
  if( !ipl.isNull() ){
    for( unsigned i=0; i<ipl.getNumChildren(); i++ ){
      if( ipl[i].getKind()==INST_ATTRIBUTE ){
        Node avar = ipl[i][0];
        if( avar.getAttribute(QuantElimAttribute()) ){
          return true;
        }
      }
    }
  }
  return false;
}

void QuantAttributes::computeAttributes( Node q ) {
  computeQuantAttributes( q, d_qattr[q] );
  if( !d_qattr[q].d_rr.isNull() ){
    if( d_quantEngine->getRewriteEngine()==NULL ){
      Trace("quant-warn") << "WARNING : rewrite engine is null, and we have : " << q << std::endl;
    }
    //set rewrite engine as owner
    d_quantEngine->setOwner( q, d_quantEngine->getRewriteEngine(), 2 );
  }
  if( d_qattr[q].isFunDef() ){
    Node f = d_qattr[q].d_fundef_f;
    if( d_fun_defs.find( f )!=d_fun_defs.end() ){
      Message() << "Cannot define function " << f << " more than once." << std::endl;
      AlwaysAssert(false);
    }
    d_fun_defs[f] = true;
    d_quantEngine->setOwner( q, d_quantEngine->getFunDefEngine(), 2 );
  }
  if( d_qattr[q].d_sygus ){
    if( d_quantEngine->getCegInstantiation()==NULL ){
      Trace("quant-warn") << "WARNING : ceg instantiation is null, and we have : " << q << std::endl;
    }
    d_quantEngine->setOwner( q, d_quantEngine->getCegInstantiation(), 2 );
  }
  if( d_qattr[q].d_synthesis ){
    if( d_quantEngine->getCegInstantiation()==NULL ){
      Trace("quant-warn") << "WARNING : ceg instantiation is null, and we have : " << q << std::endl;
    }
    d_quantEngine->setOwner( q, d_quantEngine->getCegInstantiation(), 2 );
  }
}

void QuantAttributes::computeQuantAttributes( Node q, QAttributes& qa ){
  Trace("quant-attr-debug") << "Compute attributes for " << q << std::endl;
  if( q.getNumChildren()==3 ){
    qa.d_ipl = q[2];
    for( unsigned i=0; i<q[2].getNumChildren(); i++ ){
      Trace("quant-attr-debug") << "Check : " << q[2][i] << " " << q[2][i].getKind() << std::endl;
      if( q[2][i].getKind()==INST_PATTERN || q[2][i].getKind()==INST_NO_PATTERN ){
        qa.d_hasPattern = true;
      }else if( q[2][i].getKind()==INST_ATTRIBUTE ){
        Node avar = q[2][i][0];
        if( avar.getAttribute(AxiomAttribute()) ){
          Trace("quant-attr") << "Attribute : axiom : " << q << std::endl;
          qa.d_axiom = true;
        }
        if( avar.getAttribute(ConjectureAttribute()) ){
          Trace("quant-attr") << "Attribute : conjecture : " << q << std::endl;
          qa.d_conjecture = true;
        }
        if( avar.getAttribute(FunDefAttribute()) ){
          Trace("quant-attr") << "Attribute : function definition : " << q << std::endl;
          //get operator directly from pattern
          qa.d_fundef_f = q[2][i][0].getOperator();
        }
        if( avar.getAttribute(SygusAttribute()) ){
          //not necessarily nested existential
          //Assert( q[1].getKind()==NOT );
          //Assert( q[1][0].getKind()==FORALL );
          Trace("quant-attr") << "Attribute : sygus : " << q << std::endl;
          qa.d_sygus = true;
        }
        if( avar.getAttribute(SynthesisAttribute()) ){
          Trace("quant-attr") << "Attribute : synthesis : " << q << std::endl;
          qa.d_synthesis = true;
        }
        if( avar.hasAttribute(QuantInstLevelAttribute()) ){
          qa.d_qinstLevel = avar.getAttribute(QuantInstLevelAttribute());
          Trace("quant-attr") << "Attribute : quant inst level " << qa.d_qinstLevel << " : " << q << std::endl;
        }
        if( avar.hasAttribute(RrPriorityAttribute()) ){
          qa.d_rr_priority = avar.getAttribute(RrPriorityAttribute());
          Trace("quant-attr") << "Attribute : rr priority " << qa.d_rr_priority << " : " << q << std::endl;
        }
        if( avar.getAttribute(QuantElimAttribute()) ){
          Trace("quant-attr") << "Attribute : quantifier elimination : " << q << std::endl;
          qa.d_quant_elim = true;
          //don't set owner, should happen naturally
        }
        if( avar.getAttribute(QuantElimPartialAttribute()) ){
          Trace("quant-attr") << "Attribute : quantifier elimination partial : " << q << std::endl;
          qa.d_quant_elim = true;
          qa.d_quant_elim_partial = true;
          //don't set owner, should happen naturally
        }
        if( avar.hasAttribute(QuantIdNumAttribute()) ){
          qa.d_qid_num = avar;
          Trace("quant-attr") << "Attribute : id number " << qa.d_qid_num.getAttribute(QuantIdNumAttribute()) << " : " << q << std::endl;
        }
        if( avar.getKind()==REWRITE_RULE ){
          Trace("quant-attr") << "Attribute : rewrite rule : " << q << std::endl;
          Assert( i==0 );
          qa.d_rr = avar;
        }
      }
    }
  }
}

bool QuantAttributes::isConjecture( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return false;
  }else{
    return it->second.d_conjecture;
  }
}

bool QuantAttributes::isAxiom( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return false;
  }else{
    return it->second.d_axiom;
  }
}

bool QuantAttributes::isFunDef( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return false;
  }else{
    return it->second.isFunDef();
  }
}

bool QuantAttributes::isSygus( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return false;
  }else{
    return it->second.d_sygus;
  }
}

bool QuantAttributes::isSynthesis( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return false;
  }else{
    return it->second.d_synthesis;
  }
}

int QuantAttributes::getQuantInstLevel( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return -1;
  }else{
    return it->second.d_qinstLevel;
  }
}

int QuantAttributes::getRewriteRulePriority( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return -1;
  }else{
    return it->second.d_rr_priority;
  }
}

bool QuantAttributes::isQuantElim( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return false;
  }else{
    return it->second.d_quant_elim;
  }
}

bool QuantAttributes::isQuantElimPartial( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return false;
  }else{
    return it->second.d_quant_elim_partial;
  }
}

int QuantAttributes::getQuantIdNum( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it!=d_qattr.end() ){
    if( !it->second.d_qid_num.isNull() ){
      return it->second.d_qid_num.getAttribute(QuantIdNumAttribute());
    }
  }
  return -1;
}

Node QuantAttributes::getQuantIdNumNode( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return Node::null();
  }else{
    return it->second.d_qid_num;
  }
}

void QuantAttributes::setInstantiationLevelAttr(Node n, Node qn, uint64_t level)
{
  Trace("inst-level-debug2") << "IL : " << n << " " << qn << " " << level
                             << std::endl;
  // if not from the vector of terms we instantiatied
  if (qn.getKind() != BOUND_VARIABLE && n != qn)
  {
    // if this is a new term, without an instantiation level
    if (!n.hasAttribute(InstLevelAttribute()))
    {
      InstLevelAttribute ila;
      n.setAttribute(ila, level);
      Trace("inst-level-debug") << "Set instantiation level " << n << " to "
                                << level << std::endl;
      Assert(n.getNumChildren() == qn.getNumChildren());
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        setInstantiationLevelAttr(n[i], qn[i], level);
      }
    }
  }
}

void QuantAttributes::setInstantiationLevelAttr(Node n, uint64_t level)
{
  if (!n.hasAttribute(InstLevelAttribute()))
  {
    InstLevelAttribute ila;
    n.setAttribute(ila, level);
    Trace("inst-level-debug") << "Set instantiation level " << n << " to "
                              << level << std::endl;
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      setInstantiationLevelAttr(n[i], level);
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
