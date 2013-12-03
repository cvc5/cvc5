/*********************                                                        */
/*! \file macros.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;
using namespace CVC4::context;

bool QuantifierMacros::simplify( std::vector< Node >& assertions, bool doRewrite ){
  //first, collect macro definitions
  for( size_t i=0; i<assertions.size(); i++ ){
    if( assertions[i].getKind()==FORALL ){
      std::vector< Node > args;
      for( size_t j=0; j<assertions[i][0].getNumChildren(); j++ ){
        args.push_back( assertions[i][0][j] );
      }
      //look at the body of the quantifier for macro definition
      process( assertions[i][1], true, args, assertions[i] );
    }
  }
  //create macro defs
  for( std::map< Node, std::vector< std::pair< Node, Node > > >::iterator it = d_macro_def_cases.begin();
       it != d_macro_def_cases.end(); ++it ){
    //create ite based on case definitions
    Node val;
    for( size_t i=0; i<it->second.size(); ++i ){
      if( it->second[i].first.isNull() ){
        Assert( i==0 );
        val = it->second[i].second;
      }else{
        //if value is null, must generate it
        if( val.isNull() ){
          std::stringstream ss;
          ss << "mdo_" << it->first << "_$$";
          Node op = NodeManager::currentNM()->mkSkolem( ss.str(), it->first.getType(), "op created during macro definitions" );
          //will be defined in terms of fresh operator
          std::vector< Node > children;
          children.push_back( op );
          children.insert( children.end(), d_macro_basis[ it->first ].begin(), d_macro_basis[ it->first ].end() );
          val = NodeManager::currentNM()->mkNode( APPLY_UF, children );
        }
        val = NodeManager::currentNM()->mkNode( ITE, it->second[i].first, it->second[i].second, val );
      }
    }
    d_macro_defs[ it->first ] = val;
    Trace("macros-def") << "* " << val << " is a macro for " << it->first << std::endl;
  }
  //now simplify bodies
  for( std::map< Node, Node >::iterator it = d_macro_defs.begin(); it != d_macro_defs.end(); ++it ){
    d_macro_defs[ it->first ] = Rewriter::rewrite( simplify( it->second ) );
  }
  bool retVal = false;
  if( doRewrite && !d_macro_defs.empty() ){
    //now, rewrite based on macro definitions
    for( size_t i=0; i<assertions.size(); i++ ){
      Node prev = assertions[i];
      assertions[i] = simplify( assertions[i] );
      if( prev!=assertions[i] ){
        assertions[i] = Rewriter::rewrite( assertions[i] );
        Trace("macros-rewrite") << "Rewrite " << prev << " to " << assertions[i] << std::endl;
        retVal = true;
      }
    }
  }
  return retVal;
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

bool QuantifierMacros::containsBadOp( Node n, Node n_op ){
  if( n!=n_op ){
    if( n.getKind()==APPLY_UF ){
      Node op = n.getOperator();
      if( op==n_op.getOperator() ){
        return true;
      }
      if( d_macro_def_cases.find( op )!=d_macro_def_cases.end() && !d_macro_def_cases[op].empty() ){
        return true;
      }
    }
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      if( containsBadOp( n[i], n_op ) ){
        return true;
      }
    }
  }
  return false;
}

bool QuantifierMacros::isMacroLiteral( Node n, bool pol ){
  return pol && ( n.getKind()==EQUAL || n.getKind()==IFF );
}

void QuantifierMacros::getMacroCandidates( Node n, std::vector< Node >& candidates ){
  if( n.getKind()==APPLY_UF ){
    candidates.push_back( n );
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

bool QuantifierMacros::isConsistentDefinition( Node op, Node cond, Node def ){
  if( d_macro_def_cases[op].empty() || ( cond.isNull() && !d_macro_def_cases[op][0].first.isNull() ) ){
    return true;
  }else{
    return false;
  }
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
  }else if( n.getKind()==AND || n.getKind()==OR || n.getKind()==IMPLIES ){
    //bool favorPol = (n.getKind()==AND)==pol;
    //conditional?
  }else if( n.getKind()==ITE ){
    //can not do anything
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
        if( !containsBadOp( n, m ) ){
          std::vector< Node > fvs;
          getFreeVariables( m, args, fvs, false );
          //get definition and condition
          Node n_def = solveInEquality( m, n ); //definition for the macro
          //definition must exist and not contain any free variables apart from fvs
          if( !n_def.isNull() && !getFreeVariables( n_def, args, fvs, true ) ){
            Node n_cond;  //condition when this definition holds
            //conditional must not contain any free variables apart from fvs
            if( n_cond.isNull() || !getFreeVariables( n_cond, args, fvs, true ) ){
              Trace("macros") << m << " is possible macro in " << f << std::endl;
              //now we must rewrite candidates[i] to a term of form g( x1, ..., xn ) where
              // x1 ... xn are distinct variables
              if( d_macro_basis[op].empty() ){
                for( size_t a=0; a<m.getNumChildren(); a++ ){
                  std::stringstream ss;
                  ss << "mda_" << op << "_$$";
                  Node v = NodeManager::currentNM()->mkSkolem( ss.str(), m[a].getType(), "created during macro definition recognition" );
                  d_macro_basis[op].push_back( v );
                }
              }
              std::vector< Node > eq;
              for( size_t a=0; a<m.getNumChildren(); a++ ){
                eq.push_back( m[a] );
              }
              //solve system of equations "d_macro_basis[op] = m" for variables in fvs
              std::map< Node, Node > solved;
              //solve obvious cases first
              for( size_t a=0; a<eq.size(); a++ ){
                if( std::find( fvs.begin(), fvs.end(), eq[a] )!=fvs.end() ){
                  if( solved[ eq[a] ].isNull() ){
                    solved[ eq[a] ] = d_macro_basis[op][a];
                  }
                }
              }
              //now, apply substitution for obvious cases
              std::vector< Node > vars;
              std::vector< Node > subs;
              getSubstitution( fvs, solved, vars, subs, false );
              for( size_t a=0; a<eq.size(); a++ ){
                eq[a] = eq[a].substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
              }

              Trace("macros-eq") << "Solve system of equations : " << std::endl;
              for( size_t a=0; a<m.getNumChildren(); a++ ){
                if( d_macro_basis[op][a]!=eq[a] ){
                  Trace("macros-eq") << "   " << d_macro_basis[op][a] << " = " << eq[a] << std::endl;
                }
              }
              Trace("macros-eq") << " for ";
              for( size_t a=0; a<fvs.size(); a++ ){
                if( solved[ fvs[a] ].isNull() ){
                  Trace("macros-eq") << fvs[a] << " ";
                }
              }
              Trace("macros-eq") << std::endl;
              //DO_THIS


              vars.clear();
              subs.clear();
              if( getSubstitution( fvs, solved, vars, subs, true ) ){
                //build condition
                std::vector< Node > conds;
                if( !n_cond.isNull() ){
                  //must apply substitution obtained from solving system of equations to original condition
                  n_cond = n_cond.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
                  conds.push_back( n_cond );
                }
                for( size_t a=0; a<eq.size(); a++ ){
                  //collect conditions based on solving argument's system of equations
                  if( d_macro_basis[op][a]!=eq[a] ){
                    conds.push_back( NodeManager::currentNM()->mkNode( eq[a].getType().isBoolean() ? IFF : EQUAL, d_macro_basis[op][a], eq[a] ) );
                  }
                }
                //build the condition
                if( !conds.empty() ){
                  n_cond = conds.size()==1 ? conds[0] : NodeManager::currentNM()->mkNode( AND, conds );
                }
                //apply the substitution to the
                n_def = n_def.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
                //now see if definition is consistent with others
                if( isConsistentDefinition( op, n_cond, n_def ) ){
                  //must clear if it is a base definition
                  if( n_cond.isNull() ){
                    d_macro_def_cases[ op ].clear();
                  }
                  d_macro_def_cases[ op ].push_back( std::pair< Node, Node >( n_cond, n_def ) );
                }
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
      //do substitution
      Node ret = d_macro_defs[op];
      ret = ret.substitute( d_macro_basis[op].begin(), d_macro_basis[op].end(), children.begin(), children.end() );
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
