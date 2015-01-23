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

#include "theory/quantifiers/options.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

bool SygusSplit::isRegistered( TypeNode tn ) {
  return d_register.find( tn )!=d_register.end();
}

int SygusSplit::getKindArg( TypeNode tn, Kind k ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< Kind, int > >::iterator itt = d_kinds.find( tn );
  if( itt!=d_kinds.end() ){
    std::map< Kind, int >::iterator it = itt->second.find( k );
    if( it!=itt->second.end() ){
      return it->second;
    }
  }
  return -1;
}

int SygusSplit::getConstArg( TypeNode tn, Node n ){
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< Node, int > >::iterator itt = d_consts.find( tn );
  if( itt!=d_consts.end() ){
    std::map< Node, int >::iterator it = itt->second.find( n );
    if( it!=itt->second.end() ){
      return it->second;
    }
  }
  return -1;
}

int SygusSplit::getOpArg( TypeNode tn, Node n ) {
  std::map< Node, int >::iterator it = d_ops[tn].find( n );
  if( it!=d_ops[tn].end() ){
    return it->second;
  }else{
    return -1;
  }
}

bool SygusSplit::hasKind( TypeNode tn, Kind k ) {
  return getKindArg( tn, k )!=-1;
}
bool SygusSplit::hasConst( TypeNode tn, Node n ) {
  return getConstArg( tn, n )!=-1;
}
bool SygusSplit::hasOp( TypeNode tn, Node n ) {
  return getOpArg( tn, n )!=-1;
}

bool SygusSplit::isKindArg( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Kind > >::iterator itt = d_arg_kind.find( tn );
  if( itt!=d_arg_kind.end() ){
    return itt->second.find( i )!=itt->second.end();
  }else{
    return false;
  }
}

bool SygusSplit::isConstArg( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Node > >::iterator itt = d_arg_const.find( tn );
  if( itt!=d_arg_const.end() ){
    return itt->second.find( i )!=itt->second.end();
  }else{
    return false;
  }
}

void SygusSplit::getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits, std::vector< Node >& lemmas ) {
  Assert( dt.isSygus() );
  if( d_splits.find( n )==d_splits.end() ){
    Trace("sygus-split") << "Get sygus splits " << n << std::endl;
    //get the kinds for child datatype
    TypeNode tnn = n.getType();
    registerSygusType( tnn, dt );

    //get parent information, if possible
    int csIndex = -1;
    int sIndex = -1;
    Node arg1;
    Kind parentKind = UNDEFINED_KIND;
    bool isPComm = false;
    TypeNode tnnp;
    if( n.getKind()==APPLY_SELECTOR_TOTAL ){
      Node op = n.getOperator();
      Expr selectorExpr = op.toExpr();
      const Datatype& pdt = Datatype::datatypeOf(selectorExpr);
      Assert( pdt.isSygus() );
      csIndex = Datatype::cindexOf(selectorExpr);
      sIndex = Datatype::indexOf(selectorExpr);
      tnnp = n[0].getType();
      //register the constructors that are redundant children of argument sIndex of constructor index csIndex of dt
      registerSygusTypeConstructorArg( tnn, dt, tnnp, pdt, csIndex, sIndex );


      //relationships between arguments
      if( isKindArg( tnnp, csIndex ) ){
        parentKind = d_arg_kind[tnnp][csIndex];
        isPComm = isComm( parentKind );
        if( sIndex==1 ){
          //if commutative, normalize based on term ordering (the constructor index of left arg must be less than or equal to the right arg)
          Trace("sygus-split-debug") << "Commutative operator : " << parentKind << std::endl;
          if( pdt[csIndex].getNumArgs()==2 && isArgDatatype( pdt[csIndex], 0, dt ) ){
            registerSygusTypeConstructorArg( tnn, dt, tnnp, pdt, csIndex, 0 );
            arg1 = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( pdt[csIndex][0].getSelector() ), n[0] );
          }
        }
      }
      
      // we are splitting on a term that may later have no semantics : guard this case
      Node ptest = DatatypesRewriter::mkTester( n[0], csIndex, pdt ).negate();
      Trace("sygus-split-debug") << "Parent guard : " << ptest << std::endl;
      d_splits[n].push_back( ptest );
    }

    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      Trace("sygus-split-debug2") << "Add split " << n << " : constructor " << i << " : ";
      Assert( d_sygus_nred.find( tnn )!=d_sygus_nred.end() );
      bool addSplit = d_sygus_nred[tnn][i];
      if( addSplit ){
        if( csIndex!=-1 ){
          Assert( d_sygus_pc_nred[tnn][csIndex].find( sIndex )!=d_sygus_pc_nred[tnn][csIndex].end() );
          addSplit = d_sygus_pc_nred[tnn][csIndex][sIndex][i];
        }
        if( addSplit ){
          Node test = DatatypesRewriter::mkTester( n, i, dt );
          if( options::sygusNormalFormArg() ){
            //strengthen first argument
            if( !arg1.isNull() ){
              //arguments that can be removed
              std::map< int, bool > rem_arg;
              if( isComm( parentKind ) ){
                for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
                  if( d_sygus_pc_nred[tnn][csIndex][0][j] ){
                    if( isPComm && j>i ){
                      //based on commutativity 
                      // use term ordering : constructor index of first argument is not greater than constructor index of second argument
                      rem_arg[j] = true;
                    }else{
                      if( parentKind!=UNDEFINED_KIND && dt[i].getNumArgs()==0 && dt[j].getNumArgs()==0 ){
                        Node nr = NodeManager::currentNM()->mkNode( parentKind, dt[j].getSygusOp(), dt[i].getSygusOp() );
                        Node nrr = Rewriter::rewrite( nr );
                        Trace("sygus-split-debug") << "  Test constant args : " << nr << " rewrites to " << nrr << std::endl;
                        //based on rewriting
                        // if rewriting the two arguments gives an operator that is in the parent syntax, remove the redundancy
                        if( hasOp( tnnp, nrr ) ){
                          Trace("sygus-nf") << "* Sygus norm : simplify based on rewrite " << nr << " -> " << nrr << std::endl;
                          rem_arg[j] = true;
                        }                                                          
                      }
                    }
                  }
                }
              }
            
              if( !rem_arg.empty() ){
                std::vector< Node > lem_c;
                for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
                  if( d_sygus_pc_nred[tnn][csIndex][0][j] && rem_arg.find( j )==rem_arg.end() ){
                    lem_c.push_back( DatatypesRewriter::mkTester( arg1, j, dt ) );
                  }
                }
                if( lem_c.empty() ){
                  test = Node::null();
                  Trace("sygus-split-debug2") << "redundant based on first argument" << std::endl;
                }else{
                  Node argStr = lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( OR, lem_c );
                  Trace("sygus-str") << "...strengthen corresponding first argument of " << test << " : " << argStr << std::endl;
                  test = NodeManager::currentNM()->mkNode( AND, test, argStr );
                }
              }
            }
          }
          if( !test.isNull() ){
            d_splits[n].push_back( test );
            Trace("sygus-split-debug2") << "SUCCESS" << std::endl;
            Trace("sygus-split") << "Disjunct #" << d_splits[n].size() << " : " << test << std::endl;
          }
        }else{
          Trace("sygus-split-debug2") << "redundant argument" << std::endl;
        }
      }else{
        Trace("sygus-split-debug2") << "redundant operator" << std::endl;
      }
    }
    
    if( d_splits[n].empty() ){
      //possible
      
      Assert( false );
    }
  }
  //copy to splits
  splits.insert( splits.end(), d_splits[n].begin(), d_splits[n].end() );
}

void SygusSplit::registerSygusType( TypeNode tn, const Datatype& dt ) {
  if( d_register.find( tn )==d_register.end() ){
    Trace("sygus-split") << "Register sygus type " << dt.getName() << "..." << std::endl;
    d_register[tn] = true;
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      Expr sop = dt[i].getSygusOp();
      Assert( !sop.isNull() );
      Node n = Node::fromExpr( sop );
      Trace("sygus-split") << "  Operator #" << i << " : " << sop;
      if( sop.getKind() == kind::BUILTIN ){
        Kind sk = NodeManager::operatorToKind( n );
        Trace("sygus-split") << ", kind = " << sk;
        d_kinds[tn][sk] = i;
        d_arg_kind[tn][i] = sk;
      }else if( sop.isConst() ){
        Trace("sygus-split") << ", constant";
        d_consts[tn][n] = i;
        d_arg_const[tn][i] = n;
      }
      d_ops[tn][n] = i;
      Trace("sygus-split") << std::endl;
    }

    //compute the redundant operators
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      bool nred = true;
      std::map< int, Kind >::iterator it = d_arg_kind[tn].find( i );
      if( it!=d_arg_kind[tn].end() ){
        Kind dk;
        if( isAntisymmetric( it->second, dk ) ){
          std::map< Kind, int >::iterator ita = d_kinds[tn].find( dk );
          if( ita!=d_kinds[tn].end() ){
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
              Trace("sygus-nf") << "* Sygus norm " << dt.getName() << " : do not consider any " << d_arg_kind[tn][i] << " terms." << std::endl;
              nred = false;
            }
          }
        }
        //NAND,NOR
      }
      d_sygus_nred[tn].push_back( nred );
    }
  }
}

void SygusSplit::registerSygusTypeConstructorArg( TypeNode tnn, const Datatype& dt, TypeNode tnnp, const Datatype& pdt, int csIndex, int sIndex ) {
  std::map< int, std::vector< bool > >::iterator it = d_sygus_pc_nred[tnn][csIndex].find( sIndex );
  if( it==d_sygus_pc_nred[tnn][csIndex].end() ){
    registerSygusType( tnnp, pdt );
    Trace("sygus-split") << "Register type constructor arg " << dt.getName() << " " << csIndex << " " << sIndex << std::endl;
    //get parent kind
    bool hasParentKind = false;
    Kind parentKind;
    if( isKindArg( tnnp, csIndex ) ){
      hasParentKind = true;
      parentKind = d_arg_kind[tnnp][csIndex];
    }
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      bool addSplit = d_sygus_nred[tnn][i];
      if( addSplit && hasParentKind ){
        if( d_arg_kind.find( tnn )!=d_arg_kind.end() && d_arg_kind[tnn].find( i )!=d_arg_kind[tnn].end() ){
          addSplit = considerSygusSplitKind( dt, pdt, tnn, tnnp, d_arg_kind[tnn][i], parentKind, sIndex );
          if( !addSplit ){
            Trace("sygus-nf") << "* Sygus norm " << pdt.getName() << " : do not consider " << dt.getName() << "::" << d_arg_kind[tnn][i];
            Trace("sygus-nf") << " as argument " << sIndex << " of " << parentKind << "." << std::endl;
          }
        }else if( d_arg_const.find( tnn )!=d_arg_const.end() && d_arg_const[tnn].find( i )!=d_arg_const[tnn].end() ){
          addSplit = considerSygusSplitConst( dt, pdt, tnn, tnnp, d_arg_const[tnn][i], parentKind, sIndex );
          if( !addSplit ){
            Trace("sygus-nf") << "* Sygus norm " << pdt.getName() << " : do not consider constant " << dt.getName() << "::" << d_arg_const[tnn][i];
            Trace("sygus-nf") << " as argument " << sIndex << " of " << parentKind << "." << std::endl;
          }
        }
      }
      d_sygus_pc_nred[tnn][csIndex][sIndex].push_back( addSplit );
    }
  }
}

bool SygusSplit::isAssoc( Kind k ) {
  return k==PLUS || k==MULT || k==AND || k==OR || k==XOR || k==IFF ||
         k==BITVECTOR_PLUS || k==BITVECTOR_MULT || k==BITVECTOR_AND || k==BITVECTOR_OR || k==BITVECTOR_XOR || k==BITVECTOR_XNOR || k==BITVECTOR_CONCAT;
}

bool SygusSplit::isComm( Kind k ) {
  return k==PLUS || k==MULT || k==AND || k==OR || k==XOR || k==IFF ||
         k==BITVECTOR_PLUS || k==BITVECTOR_MULT || k==BITVECTOR_AND || k==BITVECTOR_OR || k==BITVECTOR_XOR || k==BITVECTOR_XNOR;
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
bool SygusSplit::considerSygusSplitKind( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Kind k, Kind parent, int arg ) {
  Assert( hasKind( tn, k ) );
  Assert( hasKind( tnp, parent ) );
  Trace("sygus-split") << "Consider sygus split kind " << k << ", parent = " << parent << ", arg = " << arg << "?" << std::endl;
  int c = getKindArg( tn, k );
  int pc = getKindArg( tnp, parent );
  if( k==parent ){
    //check for associativity
    if( isAssoc( k ) ){
      //if the operator is associative, then a repeated occurrence should only occur in the leftmost argument position
      int firstArg = getFirstArgOccurrence( pdt[pc], dt );
      Assert( firstArg!=-1 );
      Trace("sygus-split-debug") << "Associative, with first arg = " << firstArg << std::endl;
      return arg==firstArg;
    }
  }
  //push
  if( parent==NOT || parent==BITVECTOR_NOT ){
     //negation normal form
    if( parent==k && isArgDatatype( dt[c], 0, pdt ) ){
      return false;
    }
    Kind nk = UNDEFINED_KIND;
    Kind reqk = UNDEFINED_KIND;
    std::map< int, Kind > reqk_arg; //TODO
    if( parent==NOT ){
      if( k==AND ) { 
        nk = OR;reqk = NOT;
      }else if( k==OR ){ 
        nk = AND;reqk = NOT;
      }else if( k==IFF ) { 
        nk = XOR;
      }else if( k==XOR ) { 
        nk = IFF;
      }
    }
    if( parent==BITVECTOR_NOT ){
      if( k==BITVECTOR_AND ) { 
        nk = BITVECTOR_OR;reqk = BITVECTOR_NOT;
      }else if( k==BITVECTOR_OR ){ 
        nk = BITVECTOR_AND;reqk = BITVECTOR_NOT;
      }else if( k==BITVECTOR_XNOR ) { 
        nk = BITVECTOR_XOR;
      }else if( k==BITVECTOR_XOR ) { 
        nk = BITVECTOR_XNOR;
      }
    }
    if( nk!=UNDEFINED_KIND ){
      Trace("sygus-split-debug") << "Push " << parent << " over " << k << " to " << nk;
      if( reqk!=UNDEFINED_KIND ){
        Trace("sygus-split-debug") << ", reqk = " << reqk;
      }
      Trace("sygus-split-debug") << "?" << std::endl;
      int pcr = getKindArg( tnp, nk );
      if( pcr!=-1 ){
        Assert( pcr<(int)pdt.getNumConstructors() );
        //must have same number of arguments
        if( pdt[pcr].getNumArgs()==dt[c].getNumArgs() ){
          bool success = true;
          std::map< int, TypeNode > childTypes;
          for( unsigned i=0; i<pdt[pcr].getNumArgs(); i++ ){
            TypeNode tna = getArgType( pdt[pcr], i );
            Assert( datatypes::DatatypesRewriter::isTypeDatatype( tna ) );
            if( reqk!=UNDEFINED_KIND ){
              //child must have a NOT
              int nindex = getKindArg( tna, reqk );
              if( nindex!=-1 ){
                const Datatype& adt = ((DatatypeType)(tn).toType()).getDatatype();
                childTypes[i] = getArgType( adt[nindex], 0 );
              }else{
                Trace("sygus-split-debug") << "...argument " << i << " does not have " << reqk << "." << std::endl;
                success = false;
                break;
              }
            }else{
              childTypes[i] = tna;
            }
          }
          if( success ){
            //children types of reduced operator must match types of original
            for( unsigned i=0; i<pdt[pcr].getNumArgs(); i++ ){
              if( getArgType( dt[c], i )!=childTypes[i] ){
                Trace("sygus-split-debug") << "...arg " << i << " type mismatch." << std::endl;
                success = false;
                break;
              }
            }
            if( !success ){
              //check based on commutativity TODO
            }
            if( success ){
              Trace("sygus-split-debug") << "...success" << std::endl;
              return false;
            }
          }
        }else{
          Trace("sygus-split-debug") << "...#arg mismatch." << std::endl;
        }
      }else{
        Trace("sygus-split-debug") << "...operator not available." << std::endl;
      }
    }
  }

  /*
  if( parent==MINUS ){

  }
  */
  return true;
}

bool SygusSplit::considerSygusSplitConst( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Node c, Kind parent, int arg ) {
  Assert( hasConst( tn, c ) );
  Assert( hasKind( tnp, parent ) );
  int pc = getKindArg( tnp, parent );
  Trace("sygus-split") << "Consider sygus split const " << c << ", parent = " << parent << ", arg = " << arg << "?" << std::endl;
  if( isIdempotentArg( c, parent, arg ) ){
    Trace("sygus-split-debug") << "  " << c << " is idempotent arg " << arg << " of " << parent << "..." << std::endl;
    if( pdt[pc].getNumArgs()==2 ){
      int oarg = arg==0 ? 1 : 0;
      TypeNode otn = TypeNode::fromType( ((SelectorType)pdt[pc][oarg].getType()).getRangeType() );
      if( otn==tnp ){
        return false;
      }
    }
  }else if( isSingularArg( c, parent, arg ) ){
    Trace("sygus-split-debug") << "  " << c << " is singular arg " << arg << " of " << parent << "..." << std::endl;
    if( hasConst( tnp, c ) ){
      return false;
    }
  }
  //single argument rewrite
  if( pdt[pc].getNumArgs()==1 ){
    Node cr = NodeManager::currentNM()->mkNode( parent, c );
    cr = Rewriter::rewrite( cr );
    Trace("sygus-split-debug") << "  " << parent << " applied to " << c << " rewrites to " << cr << std::endl;
    if( hasConst( tnp, cr ) ){
      return false;
    }
  }

  return true;
}

int SygusSplit::getFirstArgOccurrence( const DatatypeConstructor& c, const Datatype& dt ) {
  for( unsigned i=0; i<c.getNumArgs(); i++ ){
    if( isArgDatatype( c, i, dt ) ){
      return i;
    }
  }
  return -1;
}

bool SygusSplit::isArgDatatype( const DatatypeConstructor& c, int i, const Datatype& dt ) {
  TypeNode tni = getArgType( c, i );
  if( datatypes::DatatypesRewriter::isTypeDatatype( tni ) ){
    const Datatype& adt = ((DatatypeType)(tni).toType()).getDatatype();
    if( adt==dt ){
      return true;
    }
  }
  return false;
}

TypeNode SygusSplit::getArgType( const DatatypeConstructor& c, int i ) {
  Assert( i>=0 && i<(int)c.getNumArgs() );
  return TypeNode::fromType( ((SelectorType)c[i].getType()).getRangeType() );
}

