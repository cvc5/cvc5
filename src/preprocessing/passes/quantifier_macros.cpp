/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Yoni Zohar, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sort inference module.
 *
 * This class implements quantifiers macro definitions.
 */

#include "preprocessing/passes/quantifier_macros.h"

#include <vector>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "proof/proof_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace cvc5::theory;
using namespace cvc5::theory::quantifiers;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

QuantifierMacros::QuantifierMacros(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "quantifier-macros"),
      d_ground_macros(false)
{
}

PreprocessingPassResult QuantifierMacros::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  bool success;
  do
  {
    success = simplify(assertionsToPreprocess);
  } while (success);
  finalizeDefinitions();
  clearMaps();
  return PreprocessingPassResult::NO_CONFLICT;
}

void QuantifierMacros::clearMaps()
{
  d_macroDefs.clear();
  d_macroDefsNew.clear();
  d_quant_macros.clear();
  d_ground_macros = false;
}

bool QuantifierMacros::simplify(AssertionPipeline* ap)
{
  const std::vector<Node>& assertions = ap->ref();
  unsigned rmax =
      options::macrosQuantMode() == options::MacrosQuantMode::ALL ? 2 : 1;
  for( unsigned r=0; r<rmax; r++ ){
    d_ground_macros = (r==0);
    Trace("macros") << "Find macros, ground=" << d_ground_macros << "..." << std::endl;
    //first, collect macro definitions
    std::vector< Node > macro_assertions;
    for( int i=0; i<(int)assertions.size(); i++ ){
      Trace("macros-debug") << "  process assertion " << assertions[i] << std::endl;
      if( processAssertion( assertions[i] ) ){
        if (options::unsatCores()
            && std::find(macro_assertions.begin(),
                         macro_assertions.end(),
                         assertions[i])
                   == macro_assertions.end())
        {
          macro_assertions.push_back(assertions[i]);
        }
        //process this assertion again
        i--;
      }
    }
    Trace("macros") << "...finished process, #new def = "
                    << d_macroDefsNew.size() << std::endl;
    if (!d_macroDefsNew.empty())
    {
      bool retVal = false;
      Trace("macros") << "Do simplifications..." << std::endl;
      //now, rewrite based on macro definitions
      for (size_t i = 0, nassert = assertions.size(); i < nassert; i++)
      {
        Node curr = assertions[i].substitute(d_macroDefsNew.begin(),
                                             d_macroDefsNew.end());
        if( curr!=assertions[i] ){
          curr = Rewriter::rewrite( curr );
          Trace("macros-rewrite") << "Rewrite " << assertions[i] << " to " << curr << std::endl;
          // for now, it is dependent upon all assertions involving macros, this
          // is an over-approximation. a more fine-grained unsat core
          // computation would require caching dependencies for each subterm of
          // the formula, which is expensive.
          if (options::unsatCores())
          {
            ProofManager::currentPM()->addDependence(curr, assertions[i]);
            for (unsigned j = 0; j < macro_assertions.size(); j++)
            {
              if (macro_assertions[j] != assertions[i])
              {
                ProofManager::currentPM()->addDependence(curr,
                                                         macro_assertions[j]);
              }
            }
          }
          ap->replace(i, curr);
          retVal = true;
        }
      }
      d_macroDefsNew.clear();
      if( retVal ){
        return true;
      }
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
    std::vector<Node> args(n[0].begin(), n[0].end());
    Node nproc = n[1];
    if (!d_macroDefsNew.empty())
    {
      nproc = nproc.substitute(d_macroDefsNew.begin(), d_macroDefsNew.end());
      nproc = Rewriter::rewrite(nproc);
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
      if (nop == op || d_macroDefs.find(nop) != d_macroDefs.end())
      {
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

bool QuantifierMacros::isGroundUfTerm(Node q, Node n)
{
  Node icn = d_preprocContext->getTheoryEngine()
                 ->getQuantifiersEngine()
                 ->getQuantifiersRegistry()
                 .substituteBoundVariablesToInstConstants(n, q);
  Trace("macros-debug2") << "Get free variables in " << icn << std::endl;
  std::vector< Node > var;
  quantifiers::TermUtil::computeInstConstContainsForQuant(q, icn, var);
  Trace("macros-debug2") << "Get trigger variables for " << icn << std::endl;
  std::vector< Node > trigger_var;
  inst::PatternTermSelector::getTriggerVariables(icn, q, trigger_var);
  Trace("macros-debug2") << "Done." << std::endl;
  //only if all variables are also trigger variables
  return trigger_var.size()>=var.size();
}

bool QuantifierMacros::isBoundVarApplyUf( Node n ) {
  Assert(n.getKind() == APPLY_UF);
  TypeNode tno = n.getOperator().getType();
  std::map< Node, bool > vars;
  // allow if a vector of unique variables of the same type as UF arguments
  for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
  {
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
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(lit, msum))
    {
      Node veq_c;
      Node val;
      int res = ArithMSum::isolate(n, msum, veq_c, val, EQUAL);
      if (res != 0 && veq_c.isNull())
      {
        return val;
      }
    }
  }
  Trace("macros-debug") << "Cannot find for " << lit << " " << n << std::endl;
  return Node::null();
}

bool QuantifierMacros::process( Node n, bool pol, std::vector< Node >& args, Node f ){
  Trace("macros-debug") << "  process " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  if( n.getKind()==NOT ){
    return process( n[0], !pol, args, f );
  }else if( n.getKind()==APPLY_UF ){
    //predicate case
    if( isBoundVarApplyUf( n ) ){
      Node op = n.getOperator();
      if (d_macroDefs.find(op) == d_macroDefs.end())
      {
        Node n_def = nm->mkConst(pol);
        //add the macro
        return addMacroEq(n, n_def);
      }
    }
  }
  else if (pol && n.getKind() == EQUAL)
  {
    //literal case
    Trace("macros-debug") << "Check macro literal : " << n << std::endl;
    std::map<Node, bool> visited;
    std::vector<Node> candidates;
    for (size_t i = 0; i < n.getNumChildren(); i++)
    {
      getMacroCandidates(n[i], candidates, visited);
    }
    for (const Node& m : candidates)
    {
      Node op = m.getOperator();
      Trace("macros-debug") << "Check macro candidate : " << m << std::endl;
      if (d_macroDefs.find(op) != d_macroDefs.end())
      {
        continue;
      }
      // get definition and condition
      Node n_def = solveInEquality(m, n);  // definition for the macro
      if (n_def.isNull())
      {
        continue;
      }
      Trace("macros-debug") << m << " is possible macro in " << f << std::endl;
      Trace("macros-debug")
          << "  corresponding definition is : " << n_def << std::endl;
      visited.clear();
      // cannot contain a defined operator, opc is list of functions it contains
      std::vector<Node> opc;
      if (!containsBadOp(n_def, op, opc, visited))
      {
        Trace("macros-debug")
            << "...does not contain bad (recursive) operator." << std::endl;
        // must be ground UF term if mode is GROUND_UF
        if (options::macrosQuantMode() != options::MacrosQuantMode::GROUND_UF
            || isGroundUfTerm(f, n_def))
        {
          Trace("macros-debug")
              << "...respects ground-uf constraint." << std::endl;
          if (addMacroEq(m, n_def))
          {
            return true;
          }
        }
      }
    }
  }
  return false;
}

void QuantifierMacros::finalizeDefinitions() {
  if (options::incrementalSolving() || options::produceModels())
  {
    Trace("macros-def") << "Store as defined functions..." << std::endl;
    //also store as defined functions
    SmtEngine* smt = d_preprocContext->getSmt();
    for (const std::pair<const Node, Node>& m : d_macroDefs)
    {
      Trace("macros-def") << "Macro definition for " << m.first << " : "
                          << m.second << std::endl;
      Trace("macros-def") << "  basis is : ";
      std::vector<Node> args(m.second[0].begin(), m.second[0].end());
      Node sbody = m.second[1];
      smt->defineFunction(m.first, args, sbody);
    }
    Trace("macros-def") << "done." << std::endl;
  }
}

bool QuantifierMacros::addMacroEq(Node n, Node ndef)
{
  Assert(n.getKind() == APPLY_UF);
  NodeManager* nm = NodeManager::currentNM();
  Trace("macros-debug") << "Add macro eq for " << n << std::endl;
  Trace("macros-debug") << "  def: " << ndef << std::endl;
  std::vector<Node> vars;
  std::vector<Node> fvars;
  for (const Node& nc : n)
  {
    vars.push_back(nc);
    Node v = nm->mkBoundVar(nc.getType());
    fvars.push_back(v);
  }
  Node fdef =
      ndef.substitute(vars.begin(), vars.end(), fvars.begin(), fvars.end());
  fdef = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, fvars), fdef);
  // If the definition has a free variable, it is malformed. This can happen
  // if the right hand side of a macro definition contains a variable not
  // contained in the left hand side
  if (expr::hasFreeVar(fdef))
  {
    return false;
  }
  TNode op = n.getOperator();
  TNode fdeft = fdef;
  for (std::pair<const Node, Node>& prev : d_macroDefsNew)
  {
    d_macroDefsNew[prev.first] = prev.second.substitute(op, fdeft);
  }
  Assert(op.getType().isComparableTo(fdef.getType()));
  d_macroDefs[op] = fdef;
  d_macroDefsNew[op] = fdef;
  Trace("macros") << "(macro " << op << " " << fdef[0] << " " << fdef[1] << ")"
                  << std::endl;
  return true;
}

}  // passes
}  // preprocessing
}  // namespace cvc5
