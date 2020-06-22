/*********************                                                        */
/*! \file quantifiers_attributes.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of QuantifiersAttributes class
 **/

#include "theory/quantifiers/quantifiers_attributes.h"

#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool QAttributes::isStandard() const
{
  return !d_sygus && !d_quant_elim && !isFunDef() && d_name.isNull();
}

QuantAttributes::QuantAttributes( QuantifiersEngine * qe ) : 
d_quantEngine(qe) {

}  
  
void QuantAttributes::setUserAttribute( const std::string& attr, Node n, std::vector< Node >& node_values, std::string str_value ){
  Trace("quant-attr-debug") << "Set " << attr << " " << n << std::endl;
  if (attr == "fun-def")
  {
    Trace("quant-attr-debug") << "Set function definition " << n << std::endl;
    FunDefAttribute fda;
    n.setAttribute( fda, true );
  }else if( attr=="sygus" ){
    Trace("quant-attr-debug") << "Set sygus " << n << std::endl;
    SygusAttribute ca;
    n.setAttribute( ca, true );
  }
  else if (attr == "quant-name")
  {
    Trace("quant-attr-debug") << "Set quant-name " << n << std::endl;
    QuantNameAttribute qna;
    n.setAttribute(qna, true);
  } else if (attr == "sygus-synth-grammar") {
    Assert(node_values.size() == 1);
    Trace("quant-attr-debug") << "Set sygus synth grammar " << n << " to "
                              << node_values[0] << std::endl;
    SygusSynthGrammarAttribute ssg;
    n.setAttribute(ssg, node_values[0]);
  }else if( attr=="sygus-synth-fun-var-list" ){
    Assert(node_values.size() == 1);
    Trace("quant-attr-debug") << "Set sygus synth fun var list to " << n << " to "  << node_values[0] << std::endl;
    SygusSynthFunVarListAttribute ssfvla;
    n.setAttribute( ssfvla, node_values[0] );
  }else if( attr=="quant-inst-max-level" ){
    Assert(node_values.size() == 1);
    uint64_t lvl = node_values[0].getConst<Rational>().getNumerator().getLong();
    Trace("quant-attr-debug") << "Set instantiation level " << n << " to " << lvl << std::endl;
    QuantInstLevelAttribute qila;
    n.setAttribute( qila, lvl );
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
      else if (q[1][0].getType().isReal())
      {
        // solve for h in the equality
        std::map<Node, Node> msum;
        if (ArithMSum::getMonomialSumLit(q[1], msum))
        {
          Node veq;
          int res = ArithMSum::isolate(h, msum, veq, EQUAL);
          if (res != 0)
          {
            Assert(veq.getKind() == EQUAL);
            return res == 1 ? veq[1] : veq[0];
          }
        }
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
  QAttributes& qa = d_qattr[q];
  if (qa.isFunDef())
  {
    Node f = qa.d_fundef_f;
    if( d_fun_defs.find( f )!=d_fun_defs.end() ){
      Message() << "Cannot define function " << f << " more than once." << std::endl;
      AlwaysAssert(false);
    }
    d_fun_defs[f] = true;
  }
  // set ownership of quantified formula q based on the computed attributes
  d_quantEngine->setOwner(q, qa);
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
        if (avar.hasAttribute(SygusSideConditionAttribute()))
        {
          qa.d_sygusSideCondition =
              avar.getAttribute(SygusSideConditionAttribute());
          Trace("quant-attr")
              << "Attribute : sygus side condition : "
              << qa.d_sygusSideCondition << " : " << q << std::endl;
        }
        if (avar.getAttribute(QuantNameAttribute()))
        {
          Trace("quant-attr") << "Attribute : quantifier name : " << avar
                              << " for " << q << std::endl;
          qa.d_name = avar;
        }
        if( avar.hasAttribute(QuantInstLevelAttribute()) ){
          qa.d_qinstLevel = avar.getAttribute(QuantInstLevelAttribute());
          Trace("quant-attr") << "Attribute : quant inst level " << qa.d_qinstLevel << " : " << q << std::endl;
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
      }
    }
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

int QuantAttributes::getQuantInstLevel( Node q ) {
  std::map< Node, QAttributes >::iterator it = d_qattr.find( q );
  if( it==d_qattr.end() ){
    return -1;
  }else{
    return it->second.d_qinstLevel;
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
