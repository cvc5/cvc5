/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of sygus utilities for theory of datatypes
 **
 ** Implementation of sygus utilities for theory of datatypes
 **/


#include "theory/datatypes/datatypes_sygus.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "expr/node_manager.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

void SygusSplit::getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits ) {
  Assert( dt.isSygus() );
  Trace("sygus-split") << "Get sygus splits " << n << std::endl;
  TypeNode typ, ptyp;
  std::map< int, Kind > arg_kind, parg_kind;
  std::map< Kind, int > kinds, pkinds;
  std::map< int, Node > arg_const, parg_const;
  std::map< Node, int > consts, pconsts;

  //get the kinds for child datatype
  Trace("sygus-split") << "Operations for child : " << std::endl;
  getSygusKinds( dt, arg_kind, kinds, arg_const, consts );
  typ = TypeNode::fromType(dt.getSygusType());

  //compute the redundant operators
  TypeNode tnn = n.getType();
  if( d_sygus_nred.find( tnn )==d_sygus_nred.end() ){
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      bool nred = true;
      std::map< int, Kind >::iterator it = arg_kind.find( i );
      if( it!=arg_kind.end() ){
        Kind dk;
        if( isAntisymmetric( it->second, dk ) ){
          std::map< Kind, int >::iterator ita = kinds.find( dk );
          if( ita!=kinds.end() ){
            Trace("sygus-split-debug") << "Possible redundant operator : " << it->second << " with " << dk << std::endl;
            //check for type mismatches
            bool success = true;
            unsigned j = ita->second;
            for( unsigned k=0; k<2; k++ ){
              unsigned ko = k==0 ? 1 : 0;
              TypeNode tni = TypeNode::fromType( ((SelectorType)dt[i][k].getType()).getRangeType() );
              TypeNode tnj = TypeNode::fromType( ((SelectorType)dt[j][ko].getType()).getRangeType() );
              if( tni!=tnj ){
                Trace("sygus-split-debug") << "Argument types " << tni << " and " << tnj << " are not equal." << std::endl;
                success = false;
                break;
              }
            }
            if( success ){
              Trace("sygus-split") << "* Sygus norm " << dt.getName() << " : do not consider any " << arg_kind[i] << " terms." << std::endl;
              nred = false;
            }
          }
        }
      }
      d_sygus_nred[tnn].push_back( nred );
    }
  }


  //get parent information, if possible
  Node op;
  int csIndex;
  int sIndex;
  if( n.getKind()==APPLY_SELECTOR_TOTAL ){
    op = n.getOperator();
    Expr selectorExpr = op.toExpr();
    const Datatype& pdt = Datatype::datatypeOf(selectorExpr);
    Assert( pdt.isSygus() );
    csIndex = Datatype::cindexOf(selectorExpr);
    sIndex = Datatype::indexOf(selectorExpr);

    std::map< int, std::vector< bool > >::iterator it = d_sygus_pc_nred[op].find( sIndex );
    if( it==d_sygus_pc_nred[op].end() ){
      Trace("sygus-split") << "  Constructor, selector index : " << csIndex << " " << sIndex << std::endl;

      Trace("sygus-split") << "Operations for parent : " << std::endl;
      getSygusKinds( pdt, parg_kind, pkinds, parg_const, pconsts );
      ptyp = TypeNode::fromType(pdt.getSygusType());
      bool parentKind = parg_kind.find( csIndex )!=parg_kind.end();
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        bool addSplit = d_sygus_nred[tnn][i];
        if( addSplit && parentKind ){
          if( arg_kind.find( i )!=arg_kind.end() ){
            addSplit = considerSygusSplitKind( dt, pdt, arg_kind[i], parg_kind[csIndex], sIndex, kinds, pkinds, consts, pconsts );
            if( !addSplit ){
              Trace("sygus-nf") << "* Sygus norm " << pdt.getName() << " : do not consider " << dt.getName() << "::" << arg_kind[i];
              Trace("sygus-nf") << " as argument " << sIndex << " of " << arg_kind[csIndex] << "." << std::endl;
            }
          }else if( arg_const.find( i )!=arg_const.end() ){
            addSplit = considerSygusSplitConst( dt, pdt, arg_const[i], parg_kind[csIndex], sIndex, kinds, pkinds, consts, pconsts );
          }
        }
        d_sygus_pc_nred[op][sIndex].push_back( addSplit );
      }
    }
  }

  for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
    bool addSplit = d_sygus_nred[tnn][i];
    if( addSplit ){
      if( !op.isNull() ){
        addSplit = d_sygus_pc_nred[op][sIndex][i];
      }
      if( addSplit ){
        Node test = DatatypesRewriter::mkTester( n, i, dt );
        splits.push_back( test );
      }
    }
  }
  Assert( !splits.empty() );
}

void SygusSplit::getSygusKinds( const Datatype& dt, std::map< int, Kind >& arg_kind, std::map< Kind, int >& kinds,
                                                    std::map< int, Node >& arg_const, std::map< Node, int >& consts ) {
  for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
    Expr sop = dt[i].getSygusOp();
    Assert( !sop.isNull() );
    Trace("sygus-split") << "  Operator #" << i << " : " << sop;
    if( sop.getKind() == kind::BUILTIN ){
      Kind sk = NodeManager::operatorToKind( Node::fromExpr( sop ) );
      Trace("sygus-split") << ", kind = " << sk;
      kinds[sk] = i;
      arg_kind[i] = sk;
    }else if( sop.isConst() ){
      Node n = Node::fromExpr( sop );
      Trace("sygus-split") << ", constant";
      consts[n] = i;
      arg_const[i] = n;
    }
    Trace("sygus-split") << std::endl;
  }
}

bool SygusSplit::isAssoc( Kind k ) {
  return k==PLUS || k==MULT || k==AND || k==OR || k==XOR || k==IFF ||
         k==BITVECTOR_PLUS || k==BITVECTOR_MULT || k==BITVECTOR_AND || k==BITVECTOR_OR || k==BITVECTOR_XOR || k==BITVECTOR_CONCAT;
}

bool SygusSplit::isAntisymmetric( Kind k, Kind& dk ) {
  if( k==GT ){
    dk = LT;
    return true;
  }else if( k==GEQ ){
    dk = LEQ;
    return true;
  }else if( k==BITVECTOR_UGT ){
    dk = BITVECTOR_ULT;
    return true;
  }else if( k==BITVECTOR_UGE ){
    dk = BITVECTOR_ULE;
    return true;
  }else if( k==BITVECTOR_SGT ){
    dk = BITVECTOR_SLT;
    return true;
  }else if( k==BITVECTOR_SGE ){
    dk = BITVECTOR_SLE;
    return true;
  }else{
    return false;
  }
}

bool SygusSplit::isIdempotentArg( Node n, Kind ik, int arg ) {
  TypeNode tn = n.getType();
  if( n==getTypeValue( tn, 0 ) ){
    if( ik==PLUS || ik==BITVECTOR_PLUS || ik==BITVECTOR_OR || ik==OR ){
      return true;
    }else if( ik==BITVECTOR_SHL || ik==BITVECTOR_LSHR ){
      return arg==1;
    }
  }else if( n==getTypeValue( tn, 1 ) ){
    if( ik==MULT || ik==BITVECTOR_MULT ){
      return true;
    }else if( ik==DIVISION || ik==BITVECTOR_UDIV || ik==BITVECTOR_SDIV ){
      return arg==1;
    }
  }else if( n==getTypeMaxValue( tn ) ){
    if( ik==BITVECTOR_AND ){
      return true;
    }
  }
  return false;
}


bool SygusSplit::isSingularArg( Node n, Kind ik, int arg ) {
  TypeNode tn = n.getType();
  if( n==getTypeValue( tn, 0 ) ){
    if( ik==MULT || ik==BITVECTOR_MULT || ik==BITVECTOR_AND || ik==AND ){
      return true;
    }else if( ik==DIVISION || ik==BITVECTOR_UDIV || ik==BITVECTOR_SDIV ){
      return arg==0;
    }
  }else if( n==getTypeMaxValue( tn ) ){
    if( ik==BITVECTOR_OR ){
      return true;
    }
  }
  return false;
}


Node SygusSplit::getTypeValue( TypeNode tn, int val ) {
  std::map< int, Node >::iterator it = d_type_value[tn].find( val );
  if( it==d_type_value[tn].end() ){
    Node n;
    if( tn.isInteger() || tn.isReal() ){
      Rational c(val);
      n = NodeManager::currentNM()->mkConst( c );
    }else if( tn.isBitVector() ){
      unsigned int uv = val;
      BitVector bval(tn.getConst<BitVectorSize>(), uv);
      n = NodeManager::currentNM()->mkConst<BitVector>(bval);
    }else if( tn.isBoolean() ){
      if( val==0 || val==1 ){
        n = NodeManager::currentNM()->mkConst( val==1 );
      }
    }
    d_type_value[tn][val] = n;
    return n;
  }else{
    return it->second;
  }
}

Node SygusSplit::getTypeMaxValue( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_type_max_value.find( tn );
  if( it==d_type_max_value.end() ){
    Node n;
    if( tn.isBitVector() ){
      n = bv::utils::mkOnes(tn.getConst<BitVectorSize>());
    }
    d_type_max_value[tn] = n;
    return n;
  }else{
    return it->second;
  }
}
bool SygusSplit::considerSygusSplitKind( const Datatype& dt, const Datatype& pdt, Kind k, Kind parent, int arg,
                                         std::map< Kind, int >& kinds, std::map< Kind, int >& pkinds,
                                         std::map< Node, int >& consts, std::map< Node, int >& pconsts ) {
  Assert( kinds.find( k )!=kinds.end() );
  Assert( pkinds.find( parent )!=pkinds.end() );
  Trace("sygus-split") << "Consider sygus split kind " << k << ", parent = " << parent << ", arg = " << arg << "?" << std::endl;
  if( k==parent ){
    //check for associativity
    if( isAssoc( k ) ){
      //if the operator is associative, then a repeated occurrence should only occur in the leftmost argument position
      int firstArg = -1;
      int c = pkinds[k];
      for( unsigned i=0; i<pdt[c].getNumArgs(); i++ ){
        TypeNode tni = TypeNode::fromType( ((SelectorType)pdt[c][i].getType()).getRangeType() );
        if( datatypes::DatatypesRewriter::isTypeDatatype( tni ) ){
          const Datatype& adt = ((DatatypeType)(tni).toType()).getDatatype();
          if( adt==dt ){
            firstArg = i;
            break;
          }
        }
      }
      Assert( firstArg!=-1 );
      Trace("sygus-split-debug") << "Associative, with first arg = " << firstArg << std::endl;
      return arg==firstArg;
    }
  }
  if( parent==NOT ){
     //negation normal form
    /*
    if( k==NOT || k==ITE || ( k==AND && kinds.find( OR )!=kinds.end() ) || ( k==OR && kinds.find( AND )!=kinds.end() ) ||
        ( k==IFF && kinds.find( XOR )!=kinds.end() ) || ( k==XOR && kinds.find( IFF )!=kinds.end() ) ){
      return false;
    }
    */
  }
  /*
  if( parent==MINUS ){

  }
  */
  return true;
}

bool SygusSplit::considerSygusSplitConst( const Datatype& dt, const Datatype& pdt, Node c, Kind parent, int arg,
                                               std::map< Kind, int >& kinds, std::map< Kind, int >& pkinds,
                                               std::map< Node, int >& consts, std::map< Node, int >& pconsts ) {
  Trace("sygus-split") << "Consider sygus split const " << c << ", parent = " << parent << ", arg = " << arg << "?" << std::endl;
  return true;
}
