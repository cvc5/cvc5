/*********************                                                        */
/*! \file macros.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sort inference module
 **
 ** This class implements quantifiers macro definitions.
 **/

#include <vector>

#include "theory/quantifiers/macros.h"
#include "theory/rewriter.h"
#include "proof/proof_manager.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;


bool QuantifierMacros::simplify( std::vector< Node >& assertions, bool doRewrite ){
  Trace("macros") << "Find macros..." << std::endl;
  //first, collect macro definitions
  for( size_t i=0; i<assertions.size(); i++ ){
    processAssertion( assertions[i] );
  }
  bool retVal = false;
  if( doRewrite && !d_macro_defs.empty() ){
    //now, rewrite based on macro definitions
    for( size_t i=0; i<assertions.size(); i++ ){
      Node curr = simplify( assertions[i] );
      if( curr!=assertions[i] ){
        curr = Rewriter::rewrite( curr );
        Trace("macros-rewrite") << "Rewrite " << assertions[i] << " to " << curr << std::endl;
        PROOF( ProofManager::currentPM()->addDependence(curr, assertions[i]); );
        assertions[i] = curr;
        retVal = true;
      }
    }
  }
  return retVal;
}

void QuantifierMacros::processAssertion( Node n ) {
  if( n.getKind()==AND ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      processAssertion( n[i] );
    }
  }else if( n.getKind()==FORALL ){
    std::vector< Node > args;
    for( size_t j=0; j<n[0].getNumChildren(); j++ ){
      args.push_back( n[0][j] );
    }
    //look at the body of the quantifier for macro definition
    process( n[1], true, args, n );
  }
}

bool QuantifierMacros::contains( Node n, Node n_s ){
  if( n==n_s ){
    return true;
  }else{
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      if( contains( n[i], n_s ) ){
        return true;
      }
    }
    return false;
  }
}

bool QuantifierMacros::containsBadOp( Node n, Node op ){
  if( n.getKind()==APPLY_UF ){
    Node nop = n.getOperator();
    if( nop==op || d_macro_defs.find( nop )!=d_macro_defs.end()  ){
      return true;
    }
  }
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    if( containsBadOp( n[i], op ) ){
      return true;
    }
  }
  return false;
}

bool QuantifierMacros::isMacroLiteral( Node n, bool pol ){
  return pol && ( n.getKind()==EQUAL || n.getKind()==IFF );
}

bool QuantifierMacros::isBoundVarApplyUf( Node n ) {
  Assert( n.getKind()==APPLY_UF );
  TypeNode tn = n.getOperator().getType();
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( n[i].getKind()!=BOUND_VARIABLE ){
      return false;
    }
    if( n[i].getType()!=tn[i] ){
      return false;
    }
    for( unsigned j=0; j<i; j++ ){
      if( n[j]==n[i] ){
        return false;
      }
    }
  }
  return true;
}

void QuantifierMacros::getMacroCandidates( Node n, std::vector< Node >& candidates ){
  if( n.getKind()==APPLY_UF ){
    if( isBoundVarApplyUf( n ) ){
      candidates.push_back( n );
    }
  }else if( n.getKind()==PLUS ){
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      getMacroCandidates( n[i], candidates );
    }
  }else if( n.getKind()==MULT ){
    //if the LHS is a constant
    if( n.getNumChildren()==2 && n[0].isConst() ){
      getMacroCandidates( n[1], candidates );
    }
  }
}

Node QuantifierMacros::solveInEquality( Node n, Node lit ){
  if( lit.getKind()==IFF || lit.getKind()==EQUAL ){
    //return the opposite side of the equality if defined that way
    for( int i=0; i<2; i++ ){
      if( lit[i]==n ){
        return lit[ i==0 ? 1 : 0];
      }
    }
    //must solve for term n in the literal lit
    if( lit[0].getType().isInteger() || lit[0].getType().isReal() ){
      Node coeff;
      Node term;
      //could be solved for on LHS
      if( lit[0].getKind()==MULT && lit[0][1]==n ){
        Assert( lit[0][0].isConst() );
        term = lit[1];
        coeff = lit[0][0];
      }else{
        Assert( lit[1].getKind()==PLUS );
        std::vector< Node > plus_children;
        //find monomial with n
        for( size_t j=0; j<lit[1].getNumChildren(); j++ ){
          if( lit[1][j]==n ){
            Assert( coeff.isNull() );
            coeff = NodeManager::currentNM()->mkConst( Rational(1) );
          }else if( lit[1][j].getKind()==MULT && lit[1][j][1]==n ){
            Assert( coeff.isNull() );
            Assert( lit[1][j][0].isConst() );
            coeff = lit[1][j][0];
          }else{
            plus_children.push_back( lit[1][j] );
          }
        }
        if( !coeff.isNull() ){
          term = NodeManager::currentNM()->mkNode( PLUS, plus_children );
          term = NodeManager::currentNM()->mkNode( MINUS, lit[0], term );
        }
      }
      if( !coeff.isNull() ){
        coeff = NodeManager::currentNM()->mkConst( Rational(1) / coeff.getConst<Rational>() );
        term = NodeManager::currentNM()->mkNode( MULT, coeff, term );
        term = Rewriter::rewrite( term );
        return term;
      }
    }
  }
  Trace("macros-debug") << "Cannot find for " << lit << " " << n << std::endl;
  return Node::null();
}

bool QuantifierMacros::getFreeVariables( Node n, std::vector< Node >& v_quant, std::vector< Node >& vars, bool retOnly ){
  if( std::find( v_quant.begin(), v_quant.end(), n )!=v_quant.end() ){
    if( std::find( vars.begin(), vars.end(), n )==vars.end() ){
      if( retOnly ){
        return true;
      }else{
        vars.push_back( n );
      }
    }
  }
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    if( getFreeVariables( n[i], v_quant, vars, retOnly ) ){
      return true;
    }
  }
  return false;
}

bool QuantifierMacros::getSubstitution( std::vector< Node >& v_quant, std::map< Node, Node >& solved,
                                        std::vector< Node >& vars, std::vector< Node >& subs, bool reqComplete ){
  bool success = true;
  for( size_t a=0; a<v_quant.size(); a++ ){
    if( !solved[ v_quant[a] ].isNull() ){
      vars.push_back( v_quant[a] );
      subs.push_back( solved[ v_quant[a] ] );
    }else{
      if( reqComplete ){
        success = false;
        break;
      }
    }
  }
  return success;
}

void QuantifierMacros::process( Node n, bool pol, std::vector< Node >& args, Node f ){
  if( n.getKind()==NOT ){
    process( n[0], !pol, args, f );
  }else if( n.getKind()==AND || n.getKind()==OR ){
    //bool favorPol = (n.getKind()==AND)==pol;
    //conditional?
  }else if( n.getKind()==ITE ){
    //can not do anything
  }else if( n.getKind()==APPLY_UF ){
    //predicate case
    if( isBoundVarApplyUf( n ) ){
      Node n_def = NodeManager::currentNM()->mkConst( pol );
      Trace("macros-quant") << "Macro found for " << f << std::endl;
      Trace("macros") << "* " << n_def << " is a macro for " << n.getOperator() << std::endl;
      d_macro_defs[ n.getOperator() ] = n_def;
    }
  }else{
    //literal case
    if( isMacroLiteral( n, pol ) ){
      std::vector< Node > candidates;
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        getMacroCandidates( n[i], candidates );
      }
      for( size_t i=0; i<candidates.size(); i++ ){
        Node m = candidates[i];
        Node op = m.getOperator();
        if( d_macro_defs.find( op )==d_macro_defs.end() ){
          std::vector< Node > fvs;
          getFreeVariables( m, args, fvs, false );
          //get definition and condition
          Node n_def = solveInEquality( m, n ); //definition for the macro
          //definition must exist and not contain any free variables apart from fvs
          if( !n_def.isNull() && !getFreeVariables( n_def, args, fvs, true )  && !containsBadOp( n_def, op ) ){
            Node n_cond;  //condition when this definition holds
            //conditional must not contain any free variables apart from fvs
            if( n_cond.isNull() || !getFreeVariables( n_cond, args, fvs, true ) ){
              Trace("macros-debug") << m << " is possible macro in " << f << std::endl;
              //now we must rewrite candidates[i] to a term of form g( x1, ..., xn ) where
              // x1 ... xn are distinct variables
              if( d_macro_basis[op].empty() ){
                for( size_t a=0; a<m.getNumChildren(); a++ ){
                  std::stringstream ss;
                  ss << "mda_" << op << "";
                  Node v = NodeManager::currentNM()->mkSkolem( ss.str(), m[a].getType(), "created during macro definition recognition" );
                  d_macro_basis[op].push_back( v );
                }
              }
              std::map< Node, Node > solved;
              for( size_t a=0; a<m.getNumChildren(); a++ ){
                solved[m[a]] = d_macro_basis[op][a];
              }
              std::vector< Node > vars;
              std::vector< Node > subs;
              if( getSubstitution( fvs, solved, vars, subs, true ) ){
                n_def = n_def.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
                Trace("macros-quant") << "Macro found for " << f << std::endl;
                Trace("macros") << "* " << n_def << " is a macro for " << op << std::endl;
                d_macro_defs[op] = n_def;
                return;
              }
            }
          }
        }
      }
    }
  }
}

Node QuantifierMacros::simplify( Node n ){
  Trace("macros-debug") << "simplify " << n << std::endl;
  std::vector< Node > children;
  bool childChanged = false;
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    Node nn = simplify( n[i] );
    children.push_back( nn );
    childChanged = childChanged || nn!=n[i];
  }
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( d_macro_defs.find( op )!=d_macro_defs.end() && !d_macro_defs[op].isNull() ){
      //do substitution if necessary
      std::map< Node, std::vector< Node > >::iterator it = d_macro_basis.find( op );
      Node ret = d_macro_defs[op];
      if( it!=d_macro_basis.end() ){
        ret = ret.substitute( it->second.begin(), it->second.end(), children.begin(), children.end() );
      }
      return ret;
    }
  }
  if( childChanged ){
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      children.insert( children.begin(), n.getOperator() );
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), children );
  }else{
    return n;
  }
}
