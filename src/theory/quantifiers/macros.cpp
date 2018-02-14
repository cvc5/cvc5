/*********************                                                        */
/*! \file macros.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sort inference module
 **
 ** This class implements quantifiers macro definitions.
 **/

#include "theory/quantifiers/macros.h"

#include <vector>

#include "options/quantifiers_modes.h"
#include "options/quantifiers_options.h"
#include "proof/proof_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;


QuantifierMacros::QuantifierMacros( QuantifiersEngine * qe ) : d_qe( qe ){
  d_ground_macros = false;
}
  
bool QuantifierMacros::simplify( std::vector< Node >& assertions, bool doRewrite ){
  unsigned rmax = options::macrosQuantMode()==MACROS_QUANT_MODE_ALL ? 2 : 1;
  for( unsigned r=0; r<rmax; r++ ){
    d_ground_macros = (r==0);
    Trace("macros") << "Find macros, ground=" << d_ground_macros << "..." << std::endl;
    //first, collect macro definitions
    std::vector< Node > macro_assertions;
    for( int i=0; i<(int)assertions.size(); i++ ){
      Trace("macros-debug") << "  process assertion " << assertions[i] << std::endl;
      if( processAssertion( assertions[i] ) ){
        PROOF( 
          if( std::find( macro_assertions.begin(), macro_assertions.end(), assertions[i] )==macro_assertions.end() ){
            macro_assertions.push_back( assertions[i] );
          }
        );
        //process this assertion again
        i--;
      }
    }
    Trace("macros") << "...finished process, #new def = " << d_macro_defs_new.size() << std::endl;
    if( doRewrite && !d_macro_defs_new.empty() ){
      bool retVal = false;
      Trace("macros") << "Do simplifications..." << std::endl;
      //now, rewrite based on macro definitions
      for( unsigned i=0; i<assertions.size(); i++ ){
        Node curr = simplify( assertions[i] );
        if( curr!=assertions[i] ){
          curr = Rewriter::rewrite( curr );
          Trace("macros-rewrite") << "Rewrite " << assertions[i] << " to " << curr << std::endl;
          //for now, it is dependent upon all assertions involving macros, this is an over-approximation.
          //a more fine-grained unsat core computation would require caching dependencies for each subterm of the formula, 
          // which is expensive.
          PROOF( 
            ProofManager::currentPM()->addDependence(curr, assertions[i]); 
            for( unsigned j=0; j<macro_assertions.size(); j++ ){
              if( macro_assertions[j]!=assertions[i] ){
                ProofManager::currentPM()->addDependence(curr,macro_assertions[j]);
              }
            }
          );
          assertions[i] = curr;
          retVal = true;
        }
      }
      d_macro_defs_new.clear();
      if( retVal ){
        return true;
      }
    }
  }
  if( Trace.isOn("macros-warn") ){
    for( unsigned i=0; i<assertions.size(); i++ ){
      debugMacroDefinition( assertions[i], assertions[i] );
    }
  }
  return false;
}

bool QuantifierMacros::processAssertion( Node n ) {
  if( n.getKind()==AND ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( processAssertion( n[i] ) ){
        return true;
      }
    }
  }else if( n.getKind()==FORALL && d_quant_macros.find( n )==d_quant_macros.end() ){
    std::vector< Node > args;
    for( size_t j=0; j<n[0].getNumChildren(); j++ ){
      args.push_back( n[0][j] );
    }
    Node nproc = n[1];
    if( !d_macro_defs_new.empty() ){
      nproc = simplify( nproc );
      if( nproc!=n[1] ){
        nproc = Rewriter::rewrite( nproc );
      }
    }
    //look at the body of the quantifier for macro definition
    if( process( nproc, true, args, n ) ){
      d_quant_macros[n] = true;
      return true;
    }
  }
  return false;
}

bool QuantifierMacros::containsBadOp( Node n, Node op, std::vector< Node >& opc, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==APPLY_UF ){
      Node nop = n.getOperator();
      if( nop==op || d_macro_defs.find( nop )!=d_macro_defs.end()  ){
        return true;
      }
      if( std::find( opc.begin(), opc.end(), nop )==opc.end() ){
        opc.push_back( nop );
      }
    }else if( d_ground_macros && n.getKind()==FORALL ){
      return true;
    }
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      if( containsBadOp( n[i], op, opc, visited ) ){
        return true;
      }
    }
  }
  return false;
}

bool QuantifierMacros::isMacroLiteral( Node n, bool pol ){
  return pol && n.getKind()==EQUAL;
}

bool QuantifierMacros::isGroundUfTerm( Node f, Node n ) {
  Node icn = d_qe->getTermUtil()->substituteBoundVariablesToInstConstants(n, f);
  Trace("macros-debug2") << "Get free variables in " << icn << std::endl;
  std::vector< Node > var;
  d_qe->getTermUtil()->getVarContainsNode( f, icn, var );
  Trace("macros-debug2") << "Get trigger variables for " << icn << std::endl;
  std::vector< Node > trigger_var;
  inst::Trigger::getTriggerVariables( icn, f, trigger_var );
  Trace("macros-debug2") << "Done." << std::endl;
  //only if all variables are also trigger variables
  return trigger_var.size()>=var.size();
}

bool QuantifierMacros::isBoundVarApplyUf( Node n ) {
  Assert( n.getKind()==APPLY_UF );
  TypeNode tno = n.getOperator().getType();
  std::map< Node, bool > vars;
  // allow if a vector of unique variables of the same type as UF arguments
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( n[i].getKind()!=BOUND_VARIABLE ){
      return false;
    }
    if( n[i].getType()!=tno[i] ){
      return false;
    }
    if( vars.find( n[i] )==vars.end() ){
      vars[n[i]] = true;
    }else{
      return false;
    }
  }
  return true;
}

void QuantifierMacros::getMacroCandidates( Node n, std::vector< Node >& candidates, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==APPLY_UF ){
      if( isBoundVarApplyUf( n ) ){
        candidates.push_back( n );
      }
    }else if( n.getKind()==PLUS ){
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        getMacroCandidates( n[i], candidates, visited );
      }
    }else if( n.getKind()==MULT ){
      //if the LHS is a constant
      if( n.getNumChildren()==2 && n[0].isConst() ){
        getMacroCandidates( n[1], candidates, visited );
      }
    }else if( n.getKind()==NOT ){
      getMacroCandidates( n[0], candidates, visited );
    }
  }
}

Node QuantifierMacros::solveInEquality( Node n, Node lit ){
  if( lit.getKind()==EQUAL ){
    //return the opposite side of the equality if defined that way
    for( int i=0; i<2; i++ ){
      if( lit[i]==n ){
        return lit[i==0 ? 1 : 0];
      }else if( lit[i].getKind()==NOT && lit[i][0]==n ){
        return lit[i==0 ? 1 : 0].negate();
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
          term = plus_children.size()==1 ? plus_children[0] : NodeManager::currentNM()->mkNode( PLUS, plus_children );
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

bool QuantifierMacros::getFreeVariables( Node n, std::vector< Node >& v_quant, std::vector< Node >& vars, bool retOnly, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
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
      if( getFreeVariables( n[i], v_quant, vars, retOnly, visited ) ){
        return true;
      }
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

bool QuantifierMacros::process( Node n, bool pol, std::vector< Node >& args, Node f ){
  Trace("macros-debug") << "  process " << n << std::endl;
  if( n.getKind()==NOT ){
    return process( n[0], !pol, args, f );
  }else if( n.getKind()==AND || n.getKind()==OR ){
    //bool favorPol = (n.getKind()==AND)==pol;
    //conditional?
  }else if( n.getKind()==ITE ){
    //can not do anything
  }else if( n.getKind()==APPLY_UF ){
    //predicate case
    if( isBoundVarApplyUf( n ) ){
      Node op = n.getOperator();
      if( d_macro_defs.find( op )==d_macro_defs.end() ){
        Node n_def = NodeManager::currentNM()->mkConst( pol );
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          std::stringstream ss;
          ss << "mda_" << op << "";
          Node v = NodeManager::currentNM()->mkSkolem( ss.str(), n[i].getType(), "created during macro definition recognition" );
          d_macro_basis[op].push_back( v );
        }
        //contains no ops
        std::vector< Node > op_contains;
        //add the macro
        addMacro( op, n_def, op_contains );
        return true;
      }
    }
  }else{
    //literal case
    if( isMacroLiteral( n, pol ) ){
      Trace("macros-debug") << "Check macro literal : " << n << std::endl;
      std::map< Node, bool > visited;
      std::vector< Node > candidates;
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        getMacroCandidates( n[i], candidates, visited );
      }
      for( size_t i=0; i<candidates.size(); i++ ){
        Node m = candidates[i];
        Node op = m.getOperator();
        Trace("macros-debug") << "Check macro candidate : " << m << std::endl;
        if( d_macro_defs.find( op )==d_macro_defs.end() ){
          std::vector< Node > fvs;
          visited.clear();
          getFreeVariables( m, args, fvs, false, visited );
          //get definition and condition
          Node n_def = solveInEquality( m, n ); //definition for the macro
          if( !n_def.isNull() ){
            Trace("macros-debug") << m << " is possible macro in " << f << std::endl;
            Trace("macros-debug") << "  corresponding definition is : " << n_def << std::endl;
            visited.clear();
            //definition must exist and not contain any free variables apart from fvs
            if( !getFreeVariables( n_def, args, fvs, true, visited ) ){
              Trace("macros-debug") << "...free variables are contained." << std::endl;
              visited.clear();
              //cannot contain a defined operator, opc is list of functions it contains
              std::vector< Node > opc;
              if( !containsBadOp( n_def, op, opc, visited ) ){
                Trace("macros-debug") << "...does not contain bad (recursive) operator." << std::endl;
                //must be ground UF term if mode is GROUND_UF
                if( options::macrosQuantMode()!=MACROS_QUANT_MODE_GROUND_UF || isGroundUfTerm( f, n_def ) ){
                  Trace("macros-debug") << "...respects ground-uf constraint." << std::endl;
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
                    addMacro( op, n_def, opc );
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return false;
}

Node QuantifierMacros::simplify( Node n ){
  if( n.getNumChildren()==0 ){
    return n;
  }else{
    std::map< Node, Node >::iterator itn = d_simplify_cache.find( n );
    if( itn!=d_simplify_cache.end() ){
      return itn->second;
    }else{
      Node ret = n;
      Trace("macros-debug") << "  simplify " << n << std::endl;
      std::vector< Node > children;
      bool childChanged = false;
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        Node nn = simplify( n[i] );
        children.push_back( nn );
        childChanged = childChanged || nn!=n[i];
      }
      bool retSet = false;
      if( n.getKind()==APPLY_UF ){
        Node op = n.getOperator();
        std::map< Node, Node >::iterator it = d_macro_defs.find( op );
        if( it!=d_macro_defs.end() && !it->second.isNull() ){
          //only apply if children are subtypes of arguments
          bool success = true;
          // FIXME : this can be eliminated when we have proper typing rules
          std::vector< Node > cond;
          TypeNode tno = op.getType();
          for( unsigned i=0; i<children.size(); i++ ){
            Node etc = TypeNode::getEnsureTypeCondition( children[i], tno[i] );
            if( etc.isNull() ){
              //if this does fail, we are incomplete, since we are eliminating quantified formula corresponding to op, 
              //  and not ensuring it applies to n when its types are correct.
              //Assert( false );
              success = false;
              break;
            }else if( !etc.isConst() ){
              cond.push_back( etc );
            }
            Assert( children[i].getType().isSubtypeOf( tno[i] ) );
          }
          if( success ){
            //do substitution if necessary
            ret = it->second;
            std::map< Node, std::vector< Node > >::iterator itb = d_macro_basis.find( op );
            if( itb!=d_macro_basis.end() ){
              ret = ret.substitute( itb->second.begin(), itb->second.end(), children.begin(), children.end() );
            }
            if( !cond.empty() ){
              Node cc = cond.size()==1 ? cond[0] : NodeManager::currentNM()->mkNode( kind::AND, cond );
              ret = NodeManager::currentNM()->mkNode( kind::ITE, cc, ret, n );
            }
            retSet = true;
          }
        }
      }
      if( !retSet && childChanged ){
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.insert( children.begin(), n.getOperator() );
        }
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
      d_simplify_cache[n] = ret;
      return ret;
    }
  }
}

void QuantifierMacros::debugMacroDefinition( Node oo, Node n ) {
  //for debugging, ensure that all previous definitions have been eliminated
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( d_macro_defs.find( op )!=d_macro_defs.end() ){
      if( d_macro_defs.find( oo )!=d_macro_defs.end() ){
        Trace("macros-warn") << "BAD DEFINITION for macro " << oo << " : " << d_macro_defs[oo] << std::endl;
      }else{
        Trace("macros-warn") << "BAD ASSERTION " << oo << std::endl;
      }
      Trace("macros-warn") << "  contains defined function " << op << "!!!" << std::endl;
    }
  }
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    debugMacroDefinition( oo, n[i] );
  }
}

void QuantifierMacros::finalizeDefinitions() {
  bool doDefs = false;
  if( Trace.isOn("macros-warn") ){
    doDefs = true;
  }
  if( options::incrementalSolving() || options::produceModels() || doDefs ){
    Trace("macros") << "Store as defined functions..." << std::endl;
    //also store as defined functions
    for( std::map< Node, Node >::iterator it = d_macro_defs.begin(); it != d_macro_defs.end(); ++it ){
      Trace("macros-def") << "Macro definition for " << it->first << " : " << it->second << std::endl;
      Trace("macros-def") << "  basis is : ";
      std::vector< Node > nargs;
      std::vector< Expr > args;
      for( unsigned i=0; i<d_macro_basis[it->first].size(); i++ ){
        Node bv = NodeManager::currentNM()->mkBoundVar( d_macro_basis[it->first][i].getType() );
        Trace("macros-def") << d_macro_basis[it->first][i] << " ";
        nargs.push_back( bv );
        args.push_back( bv.toExpr() );
      }
      Trace("macros-def") << std::endl;
      Node sbody = it->second.substitute( d_macro_basis[it->first].begin(), d_macro_basis[it->first].end(), nargs.begin(), nargs.end() );
      smt::currentSmtEngine()->defineFunction( it->first.toExpr(), args, sbody.toExpr() );

      if( Trace.isOn("macros-warn") ){
        debugMacroDefinition( it->first, sbody );
      }
    }
    Trace("macros") << "done." << std::endl;
  }
}

void QuantifierMacros::addMacro( Node op, Node n, std::vector< Node >& opc ) {
  Trace("macros") << "* " << n << " is a macro for " << op << ", #op contain = " << opc.size() << std::endl;
  d_simplify_cache.clear();
  d_macro_defs[op] = n;
  d_macro_defs_new[op] = n;
  //substitute into all previous
  std::vector< Node > dep_ops;
  dep_ops.push_back( op );
  Trace("macros-debug") << "...substitute into " << d_macro_def_contains[op].size() << " previous definitions." << std::endl;
  for( unsigned i=0; i<d_macro_def_contains[op].size(); i++ ){
    Node cop = d_macro_def_contains[op][i];
    Node def = d_macro_defs[cop];
    def = simplify( def );
    d_macro_defs[cop] = def;
    if( d_macro_defs_new.find( cop )!=d_macro_defs_new.end() ){
      d_macro_defs_new[cop] = def;
    }
    dep_ops.push_back( cop );
  }
  //store the contains op information
  for( unsigned i=0; i<opc.size(); i++ ){
    for( unsigned j=0; j<dep_ops.size(); j++ ){
      Node dop = dep_ops[j];
      if( std::find( d_macro_def_contains[opc[i]].begin(), d_macro_def_contains[opc[i]].end(), dop )==d_macro_def_contains[opc[i]].end() ){
        d_macro_def_contains[opc[i]].push_back( dop );
      }
    }
  }
}
