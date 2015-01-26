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

Node SygusSplit::getVar( TypeNode tn, int i ) {
  while( i>=(int)d_fv[tn].size() ){
    std::stringstream ss;
    TypeNode vtn = tn;
    if( datatypes::DatatypesRewriter::isTypeDatatype( tn ) ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      ss << "fv_" << dt.getName() << "_" << i;
      Assert( d_register.find( tn )!=d_register.end() );
      if( !d_register[tn].isNull() ){
        vtn = d_register[tn];
      }
    }else{
      ss << "fv_" << tn << "_" << i;
    }
    Assert( !vtn.isNull() );
    Node v = NodeManager::currentNM()->mkSkolem( ss.str(), vtn, "for sygus normal form testing" );
    d_fv_stype[v] = tn;
    d_fv[tn].push_back( v );
  }
  return d_fv[tn][i];
}

Node SygusSplit::getVarInc( TypeNode tn, std::map< TypeNode, int >& var_count ) {
  std::map< TypeNode, int >::iterator it = var_count.find( tn );
  if( it==var_count.end() ){
    var_count[tn] = 1;
    return getVar( tn, 0 );
  }else{
    int index = it->second;
    var_count[tn]++;
    return getVar( tn, index );
  }
}

void SygusSplit::getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits, std::vector< Node >& lemmas ) {
  Assert( dt.isSygus() );
  if( d_splits.find( n )==d_splits.end() ){
    Trace("sygus-split") << "Get sygus splits " << n << std::endl;
    //get the kinds for child datatype
    TypeNode tnn = n.getType();
    registerSygusType( tnn );

    //get parent information, if possible
    int csIndex = -1;
    int sIndex = -1;
    Node arg1;
    TypeNode tn1;
    TypeNode tnnp;
    Node ptest;
    if( n.getKind()==APPLY_SELECTOR_TOTAL ){
      Node op = n.getOperator();
      Expr selectorExpr = op.toExpr();
      const Datatype& pdt = Datatype::datatypeOf(selectorExpr);
      Assert( pdt.isSygus() );
      csIndex = Datatype::cindexOf(selectorExpr);
      sIndex = Datatype::indexOf(selectorExpr);
      TypeNode tnnp = n[0].getType();
      //register the constructors that are redundant children of argument sIndex of constructor index csIndex of dt
      registerSygusTypeConstructorArg( tnn, dt, tnnp, pdt, csIndex, sIndex );

      if( sIndex==1 && pdt[csIndex].getNumArgs()==2 ){
        arg1 = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( pdt[csIndex][0].getSelector() ), n[0] );
        tn1 = arg1.getType();
        if( !DatatypesRewriter::isTypeDatatype( tn1 ) ){
          arg1 = Node::null();
        }
      }
      // we are splitting on a term that may later have no semantics : guard this case
      ptest = DatatypesRewriter::mkTester( n[0], csIndex, pdt );
      Trace("sygus-split-debug") << "Parent guard : " << ptest << std::endl;
    }

    std::vector< Node > ptest_c;
    bool narrow = false;
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      Trace("sygus-split-debug2") << "Add split " << n << " : constructor " << dt[i].getName() << " : ";
      Assert( d_sygus_nred.find( tnn )!=d_sygus_nred.end() );
      bool addSplit = d_sygus_nred[tnn][i];
      if( addSplit ){
        if( csIndex!=-1 ){
          Assert( d_sygus_pc_nred[tnn][csIndex].find( sIndex )!=d_sygus_pc_nred[tnn][csIndex].end() );
          addSplit = d_sygus_pc_nred[tnn][csIndex][sIndex][i];
        }
        if( addSplit ){
          //check based on generic rewriting  TODO
          //std::vector< int > csIndices;
          //std::vector< int > sIndices;
          //csIndices.push_back( i );
          //TypeNode tng;
          //Node g = getGeneric( n, csIndices, sIndices, tng );
          //Trace("sygus-split-debug") << "Generic template " << n << " " << dt[i].getName() << " is " << g << ", sygus type : " << tng << std::endl;
          //if( isGenericRedundant( tng, g ) ){
          //  addSplit = false;
          //  Trace("sygus-split-debug2") << "generic redundant" << std::endl;
          //}

          std::vector< Node > test_c;
          Node test = DatatypesRewriter::mkTester( n, i, dt );
          test_c.push_back( test );
          //check if we can strengthen the first argument
          if( !arg1.isNull() ){
            const Datatype& dt1 = ((DatatypeType)(tn1).toType()).getDatatype();
            std::map< int, std::vector< int > >::iterator it = d_sygus_pc_arg_pos[tnn][csIndex].find( i );
            if( it!=d_sygus_pc_arg_pos[tnn][csIndex].end() ){
              Assert( !it->second.empty() );
              std::vector< Node > lem_c;
              for( unsigned j=0; j<it->second.size(); j++ ){
                lem_c.push_back( DatatypesRewriter::mkTester( arg1, it->second[j], dt1 ) );
              }
              Node argStr = lem_c.size()==1 ? lem_c[0] : NodeManager::currentNM()->mkNode( OR, lem_c );
              Trace("sygus-str") << "...strengthen corresponding first argument of " << test << " : " << argStr << std::endl;
              test_c.push_back( argStr );
              narrow = true;
            }
          }
          //add fairness constraint
          if( options::ceGuidedInstFair()==quantifiers::CEGQI_FAIR_DT_SIZE ){
            Node szl = NodeManager::currentNM()->mkNode( DT_SIZE, n );
            Node szr = NodeManager::currentNM()->mkNode( DT_SIZE, DatatypesRewriter::getInstCons( n, dt, i ) );
            szr = Rewriter::rewrite( szr );
            test_c.push_back( szl.eqNode( szr ) );
          }
          test = test_c.size()==1 ? test_c[0] : NodeManager::currentNM()->mkNode( AND, test_c );
          d_splits[n].push_back( test );
          Trace("sygus-split-debug2") << "SUCCESS" << std::endl;
          Trace("sygus-split-debug") << "Disjunct #" << d_splits[n].size() << " : " << test << std::endl;
        }else{
          Trace("sygus-split-debug2") << "redundant argument" << std::endl;
          narrow = true;
        }
      }else{
        Trace("sygus-split-debug2") << "redundant operator" << std::endl;
        narrow = true;
      }
      if( !ptest.isNull() ){
        ptest_c.push_back( DatatypesRewriter::mkTester( n, i, dt ) );
      }
    }
    if( narrow && !ptest.isNull() ){
      Node split = d_splits[n].empty() ? NodeManager::currentNM()->mkConst( false ) :
                                        ( d_splits[n].size()==1 ? d_splits[n][0] : NodeManager::currentNM()->mkNode( OR, d_splits[n] ) );
      if( !d_splits[n].empty() ){
        d_splits[n].clear();
        split = NodeManager::currentNM()->mkNode( AND, ptest, split );
      }
      d_splits[n].push_back( split );
      if( !ptest_c.empty() ){
        ptest = NodeManager::currentNM()->mkNode( AND, ptest.negate(), NodeManager::currentNM()->mkNode( OR, ptest_c ) );
      }
      d_splits[n].push_back( ptest );
    }else{
      Assert( !d_splits[n].empty() );
    }

  }
  //copy to splits
  splits.insert( splits.end(), d_splits[n].begin(), d_splits[n].end() );
}

void SygusSplit::registerSygusType( TypeNode tn ) {
  if( d_register.find( tn )==d_register.end() ){
    if( !DatatypesRewriter::isTypeDatatype( tn ) ){
      d_register[tn] = TypeNode::null();
    }else{
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      Trace("sygus-split") << "Register type " << dt.getName() << "..." << std::endl;
      d_register[tn] = TypeNode::fromType( dt.getSygusType() );
      if( d_register[tn].isNull() ){
        Trace("sygus-split") << "...not sygus." << std::endl;
      }else{
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
          if( options::sygusNormalForm() ){
            Trace("sygus-split-debug") << "Is " << dt[i].getName() << " a redundant operator?" << std::endl;
            std::map< int, Kind >::iterator it = d_arg_kind[tn].find( i );
            if( it!=d_arg_kind[tn].end() ){
              Kind dk;
              if( isAntisymmetric( it->second, dk ) ){
                int j = getKindArg( tn, dk );
                if( j!=-1 ){
                  Trace("sygus-split-debug") << "Possible redundant operator : " << it->second << " with " << dk << std::endl;
                  //check for type mismatches
                  bool success = true;
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
              //if( it->second==MINUS || it->second==BITVECTOR_SUB ){
              //}
              //NAND,NOR
            }
            if( nred ){
              Trace("sygus-split-debug") << "Check " << dt[i].getName() << " based on generic rewriting" << std::endl;
              std::map< TypeNode, int > var_count;
              std::map< int, Node > pre;
              Node g = mkGeneric( dt, i, var_count, pre );
              nred = !isGenericRedundant( tn, g );
              Trace("sygus-split-debug") << "...done check " << dt[i].getName() << " based on generic rewriting" << std::endl;
            }
          }
          d_sygus_nred[tn].push_back( nred );
        }
      }
      Trace("sygus-split-debug") << "...done register type " << dt.getName() << std::endl;
    }
  }
}

void SygusSplit::registerSygusTypeConstructorArg( TypeNode tnn, const Datatype& dt, TypeNode tnnp, const Datatype& pdt, int csIndex, int sIndex ) {
  std::map< int, std::vector< bool > >::iterator it = d_sygus_pc_nred[tnn][csIndex].find( sIndex );
  if( it==d_sygus_pc_nred[tnn][csIndex].end() ){
    d_sygus_pc_nred[tnn][csIndex][sIndex].clear();
    registerSygusType( tnn );
    registerSygusType( tnnp );
    Trace("sygus-split") << "Register type constructor arg " << dt.getName() << " " << csIndex << " " << sIndex << std::endl;
    if( !options::sygusNormalForm() ){
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        d_sygus_pc_nred[tnn][csIndex][sIndex].push_back( true );
      }
    }else{
      // calculate which constructors we should consider based on normal form for terms
      //get parent kind
      bool hasParentKind = false;
      Kind parentKind;
      if( isKindArg( tnnp, csIndex ) ){
        hasParentKind = true;
        parentKind = d_arg_kind[tnnp][csIndex];
      }
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        Assert( d_sygus_nred.find( tnn )!=d_sygus_nred.end() );
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
          if( addSplit ){
            if( pdt[csIndex].getNumArgs()==1 ){
              //generic rewriting
              std::map< int, Node > prec;
              std::map< TypeNode, int > var_count;
              Node gc = mkGeneric( dt, i, var_count, prec );
              std::map< int, Node > pre;
              pre[sIndex] = gc;
              Node g = mkGeneric( pdt, csIndex, var_count, pre );
              addSplit = !isGenericRedundant( tnnp, g );
            }
          }
        }
        d_sygus_pc_nred[tnn][csIndex][sIndex].push_back( addSplit );
      }
      if( options::sygusNormalFormArg() ){
        //compute argument relationships for 2-arg constructors
        if( isKindArg( tnnp, csIndex ) && pdt[csIndex].getNumArgs()==2 ){
          int osIndex = sIndex==0 ? 1 : 0;
          TypeNode tnno = getArgType( pdt[csIndex], osIndex );
          if( DatatypesRewriter::isTypeDatatype( tnno ) ){
            const Datatype& dto = ((DatatypeType)(tnno).toType()).getDatatype();
            registerSygusTypeConstructorArg( tnno, dto, tnnp, pdt, csIndex, osIndex );
            //compute relationships when doing 0-arg
            if( sIndex==0 ){
              Assert( d_sygus_pc_nred[tnn][csIndex].find( sIndex )!=d_sygus_pc_nred[tnn][csIndex].end() );
              Assert( d_sygus_pc_nred[tnno][csIndex].find( osIndex )!=d_sygus_pc_nred[tnno][csIndex].end() );

              Kind parentKind = d_arg_kind[tnnp][csIndex];
              bool isPComm = isComm( parentKind );
              std::map< int, bool > larg_consider;
              for( unsigned i=0; i<dto.getNumConstructors(); i++ ){
                if( d_sygus_pc_nred[tnno][csIndex][osIndex][i] ){
                  //arguments that can be removed
                  std::map< int, bool > rem_arg;
                  //collect information about this index
                  bool isSingularConst = isConstArg( tnno, i ) && isSingularArg( d_arg_const[tnno][i], parentKind, 1 );
                  bool argConsider = false;
                  for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
                    if( d_sygus_pc_nred[tnn][csIndex][sIndex][j] ){
                      Trace("sygus-split-debug") << "Check redundancy of " << dt[j].getSygusOp() << " and " << dto[i].getSygusOp() << " under " << parentKind << std::endl;
                      bool rem = false;
                      if( isPComm && j>i && tnn==tnno ){
                        //based on commutativity
                        // use term ordering : constructor index of first argument is not greater than constructor index of second argument
                        rem = true;
                        Trace("sygus-nf") << "* Sygus norm : commutativity of " << parentKind << " : consider " << dt[j].getSygusOp() << " before " << dto[i].getSygusOp() << std::endl;
                      }else if( isSingularConst && argConsider ){
                        rem = true;
                        Trace("sygus-nf") << "* Sygus norm : RHS singularity arg " << dto[i].getSygusOp() << " of " << parentKind;
                        Trace("sygus-nf") << " : do not consider " << dt[j].getSygusOp() << " as first arg." << std::endl;
                      }else if( isConstArg( tnn, j ) && isSingularArg( d_arg_const[tnn][j], parentKind, 0 ) && larg_consider.find( j )!=larg_consider.end() ){
                        rem = true;
                        Trace("sygus-nf") << "* Sygus norm : LHS singularity arg " << dt[j].getSygusOp() << " of " << parentKind;
                        Trace("sygus-nf") << " : do not consider " << dto[i].getSygusOp() << " as second arg." << std::endl;
                      }else{
                        if( parentKind!=UNDEFINED_KIND ){
                          //&& dto[i].getNumArgs()==0 && dt[j].getNumArgs()==0 ){
                          std::map< TypeNode, int > var_count;
                          std::map< int, Node > pre;
                          Node g1 = mkGeneric( dt, j, var_count, pre );
                          Node g2 = mkGeneric( dto, i, var_count, pre );
                          Node g = NodeManager::currentNM()->mkNode( parentKind, g1, g2 );
                          if( isGenericRedundant( tnnp, g ) ){
                            rem = true;
                          }
                        }
                      }
                      if( rem ){
                        rem_arg[j] = true;
                      }else{
                        argConsider = true;
                        larg_consider[j] = true;
                      }
                    }
                  }
                  if( !rem_arg.empty() ){
                    d_sygus_pc_arg_pos[tnno][csIndex][i].clear();
                    Trace("sygus-split-debug") << "Possibilities for first argument of " << parentKind << ", when second argument is " << dto[i].getName() << " : " << std::endl;
                    for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
                      if( d_sygus_pc_nred[tnn][csIndex][sIndex][j] && rem_arg.find( j )==rem_arg.end() ){
                        d_sygus_pc_arg_pos[tnno][csIndex][i].push_back( j );
                        Trace("sygus-split-debug") << "  " << dt[j].getName() << std::endl;
                      }
                    }
                    //if there are no possibilities for first argument, then this child is redundant
                    if( d_sygus_pc_arg_pos[tnno][csIndex][i].empty() ){
                      Trace("sygus-nf") << "* Sygus norm " << pdt.getName() << " : do not consider constant " << dt.getName() << "::" << dto[i].getName();
                      Trace("sygus-nf") << " as argument " << osIndex << " of " << parentKind << " (based on arguments)." << std::endl;
                      d_sygus_pc_nred[tnno][csIndex][osIndex][i] = false;
                    }
                  }
                }
              }
            }
          }
        }
      }
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
    if( ik==PLUS || ik==OR || ik==XOR || ik==BITVECTOR_PLUS || ik==BITVECTOR_OR || ik==BITVECTOR_XOR ){
      return true;
    }else if( ik==MINUS || ik==BITVECTOR_SHL || ik==BITVECTOR_LSHR || ik==BITVECTOR_SUB ){
      return arg==1;
    }
  }else if( n==getTypeValue( tn, 1 ) ){
    if( ik==MULT || ik==BITVECTOR_MULT ){
      return true;
    }else if( ik==DIVISION || ik==BITVECTOR_UDIV || ik==BITVECTOR_SDIV ){
      return arg==1;
    }
  }else if( n==getTypeMaxValue( tn ) ){
    if( ik==IFF || ik==BITVECTOR_AND || ik==BITVECTOR_XNOR ){
      return true;
    }
  }
  return false;
}


bool SygusSplit::isSingularArg( Node n, Kind ik, int arg ) {
  TypeNode tn = n.getType();
  if( n==getTypeValue( tn, 0 ) ){
    if( ik==AND || ik==MULT || ik==BITVECTOR_AND || ik==BITVECTOR_MULT ){
      return true;
    }else if( ik==DIVISION || ik==BITVECTOR_UDIV || ik==BITVECTOR_SDIV ){
      return arg==0;
    }
  }else if( n==getTypeMaxValue( tn ) ){
    if( ik==OR || ik==BITVECTOR_OR ){
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
      if( val==0 ){
        n = NodeManager::currentNM()->mkConst( false );
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
    }else if( tn.isBoolean() ){
      n = NodeManager::currentNM()->mkConst( true );
    }
    d_type_max_value[tn] = n;
    return n;
  }else{
    return it->second;
  }
}

//this function gets all easy redundant cases, before consulting rewriters
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
  if( parent==NOT || parent==BITVECTOR_NOT || parent==UMINUS || parent==BITVECTOR_NEG ){
     //negation normal form
    if( parent==k && isArgDatatype( dt[c], 0, pdt ) ){
      return false;
    }
    Kind nk = UNDEFINED_KIND;
    Kind reqk = UNDEFINED_KIND;  //required kind for all children
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
    if( parent==UMINUS ){
      if( k==PLUS ){
        nk = PLUS;reqk = UMINUS;
      }
    }
    if( parent==BITVECTOR_NEG ){
      if( k==PLUS ){
        nk = PLUS;reqk = BITVECTOR_NEG;
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
  return true;
}

//this function gets all easy redundant cases, before consulting rewriters
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

Node SygusSplit::getGeneric( Node n, std::vector< int >& csIndices, std::vector< int >& sIndices, TypeNode& tng ) {
  if( n.getKind()==APPLY_SELECTOR_TOTAL ){
    Node op = n.getOperator();
    Expr selectorExpr = op.toExpr();
    csIndices.push_back( Datatype::cindexOf(selectorExpr) );
    sIndices.push_back( Datatype::indexOf(selectorExpr) );
    return getGeneric( n[0], csIndices, sIndices, tng );
  }else{
    tng = n.getType();
    Assert( DatatypesRewriter::isTypeDatatype( tng ) );
    const Datatype& dt = ((DatatypeType)(tng).toType()).getDatatype();
    Assert( csIndices.size()==sIndices.size()+1 );
    std::reverse( csIndices.begin(), csIndices.end() );
    std::reverse( sIndices.begin(), sIndices.end() );
    Trace("sygus-generic") << "Traversed under " << sIndices.size() << " selectors." << std::endl;
    std::map< TypeNode, int > var_count;
    return getGeneric2( dt, var_count, csIndices, sIndices, 0 );
  }
}

Node SygusSplit::getGeneric2( const Datatype& dt, std::map< TypeNode, int >& var_count, std::vector< int >& csIndices, std::vector< int >& sIndices, unsigned index ) {
  Assert( index<csIndices.size() );
  std::vector< Node > children;
  int c = csIndices[index];
  int s = index<sIndices.size() ? sIndices[index] : -1;
  Assert( c>=0 && c<(int)dt.getNumConstructors() );
  Assert( dt.isSygus() );
  Assert( !dt[c].getSygusOp().isNull() );
  Node op = Node::fromExpr( dt[c].getSygusOp() );
  if( op.getKind()!=BUILTIN ){
    children.push_back( op );
  }
  Trace("sygus-generic") << "Construct for " << dt[c].getName() << ", arg " << s << ", op " << op << std::endl;
  std::map< int, Node > pre;
  if( s!=-1 ){
    TypeNode tna = getArgType( dt[c], s );
    Assert( DatatypesRewriter::isTypeDatatype( tna ) );
    const Datatype& adt = ((DatatypeType)(tna).toType()).getDatatype();
    pre[s] = getGeneric2( adt, var_count, csIndices, sIndices, index+1 );
  }
  return mkGeneric( dt, c, var_count, pre );
}

Node SygusSplit::mkGeneric( const Datatype& dt, int c, std::map< TypeNode, int >& var_count, std::map< int, Node >& pre ) {
  Assert( c>=0 && c<(int)dt.getNumConstructors() );
  Assert( dt.isSygus() );
  Assert( !dt[c].getSygusOp().isNull() );
  std::vector< Node > children;
  Node op = Node::fromExpr( dt[c].getSygusOp() );
  if( op.getKind()!=BUILTIN ){
    children.push_back( op );
  }
  for( int i=0; i<(int)dt[c].getNumArgs(); i++ ){
    TypeNode tna = getArgType( dt[c], i );
    registerSygusType( tna );
    Assert( d_register.find( tna )!=d_register.end() );
    Node a;
    std::map< int, Node >::iterator it = pre.find( i );
    if( it!=pre.end() ){
      a = it->second;
    }else{
      a = getVarInc( tna, var_count );
    }
    Assert( !a.isNull() );
    Assert( a.getType()==d_register[tna] );
    children.push_back( a );
  }
  if( Trace.isOn("sygus-split-debug3") ){
    Trace("sygus-split-debug3") << "mkGeneric " << dt[c].getName() << ", op = " << op << " with arguments : " << std::endl;
    for( unsigned i=0; i<children.size(); i++ ){
      Trace("sygus-split-debug3") << "  " << children[i] << std::endl;
    }
  }
  if( op.getKind()==BUILTIN ){
    return NodeManager::currentNM()->mkNode( op, children );
  }else{
    if( children.size()==1 ){
      return children[0];
    }else{
      return NodeManager::currentNM()->mkNode( APPLY, children );
    }
  }
}

bool SygusSplit::isGenericRedundant( TypeNode tn, Node g ) {
  //everything added to this cache should be mutually exclusive cases
  std::map< Node, bool >::iterator it = d_gen_redundant[tn].find( g );
  if( it==d_gen_redundant[tn].end() ){
    Trace("sygus-gnf") << "Register generic for " << tn << " : " << g << std::endl;
    Node gr = Rewriter::rewrite( g );
    //replace variables in order left to right
    std::map< TypeNode, int > var_count;
    std::map< Node, Node > subs;
    gr = getSygusNormalized( gr, var_count, subs );
    Trace("sygus-gnf-debug") << "Generic " << g << " rewrites to " << gr << std::endl;
    std::map< Node, Node >::iterator itg = d_gen_terms[tn].find( gr );
    bool red = true;
    if( itg==d_gen_terms[tn].end() ){
      red = false;
      d_gen_terms[tn][gr] = g;
      Trace("sygus-gnf-debug") << "...not redundant." << std::endl;
    }else{
      Trace("sygus-gnf-debug") << "...redundant." << std::endl;
      Trace("sygus-nf") << "* Sygus normal form : simplify since " << g << " and " << itg->second << " both rewrite to " << gr << std::endl;
    }
    d_gen_redundant[tn][g] = red;
    return red;
  }else{
    return it->second;
  }
}

Node SygusSplit::getSygusNormalized( Node n, std::map< TypeNode, int >& var_count, std::map< Node, Node >& subs ) {
  return n;
  if( n.getKind()==SKOLEM ){
    std::map< Node, Node >::iterator its = subs.find( n );
    if( its!=subs.end() ){
      return its->second;
    }else{
      std::map< Node, TypeNode >::iterator it = d_fv_stype.find( n );
      if( it!=d_fv_stype.end() ){
        Node v = getVarInc( it->second, var_count );
        subs[n] = v;
        return v;
      }else{
        return n;
      }
    }
  }else{
    if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = getSygusNormalized( n[i], var_count, subs );
        childChanged = childChanged || nc!=n[i];
        children.push_back( nc );
      }
      if( childChanged ){
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    return n;
  }
}
