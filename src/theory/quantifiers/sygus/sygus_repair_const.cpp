/*********************                                                        */
/*! \file sygus_repair_const.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_repair_const
 **/

#include "theory/quantifiers/sygus/sygus_repair_const.h"

#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "options/base_options.h"
#include "printer/printer.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusRepairConst::SygusRepairConst(QuantifiersEngine* qe)
    : d_qe(qe), d_allow_constant_grammar(false)
{
  d_tds = d_qe->getTermDatabaseSygus();
}

void SygusRepairConst::initialize(Node base_inst, const std::vector< Node >& candidates) 
{
  Trace("sygus-repair-const") << "SygusRepairConst::initialize" << std::endl;
  Trace("sygus-repair-const") << "  conjecture : " << base_inst << std::endl;
  d_base_inst = base_inst;
  
  // compute whether there are "allow all constant" types in the variables of q
  std::map<TypeNode, bool > tprocessed;
  for( const Node& v : candidates )
  {
    TypeNode tn = v.getType();
    // do the type traversal of the sygus type
    registerSygusType( tn, tprocessed );
  }
  Trace("sygus-repair-const") << "  allow constants : " << d_allow_constant_grammar << std::endl;
}

// recursion depth bounded by number of types in grammar (small)
void SygusRepairConst::registerSygusType(TypeNode tn, std::map<TypeNode, bool >& tprocessed)
{
  if (tprocessed.find(tn) == tprocessed.end())
  {
    tprocessed[tn] = true;
    Assert(tn.isDatatype());
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    Assert(dt.isSygus());
    // check if this datatype allows all constants
    if( dt.getSygusAllowConst() )
    {
      d_allow_constant_grammar = true;
    }
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DatatypeConstructor& dtc = dt[i];
      // recurse on all subfields
      for (unsigned j = 0, nargs = dtc.getNumArgs(); j < nargs; j++)
      {
        TypeNode tnc = d_tds->getArgType(dtc, j);
        registerSygusType(tnc,tprocessed);
      }
    }
  }
}

bool SygusRepairConst::repairSolution(const std::vector<Node>& candidates,
                                      const std::vector<Node>& candidate_values,
                                      std::vector<Node>& repair_cv)
{
  Assert(candidates.size() == candidate_values.size());

  // if no grammar type allows constants, no repair is possible
  if (d_base_inst.isNull() || !d_allow_constant_grammar)
  {
    return false;
  }
  if( Trace.isOn("sygus-repair-const") )
  {
    Trace("sygus-repair-const") << "Repair candidate solutions..." << std::endl;
    for( unsigned i=0,size=candidates.size(); i<size; i++ )
    {
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, candidate_values[i]);
      Trace("sygus-repair-const") << "  " << candidates[i] << " -> " << ss.str() << std::endl;
    }
    Trace("sygus-repair-const") << "Getting candidate skeletons : " << std::endl;
  }
  NodeManager * nm = NodeManager::currentNM();
  bool changed = false;
  std::vector< Node > candidate_skeletons;
  std::map<TypeNode, int> free_var_count;
  std::vector< Node > sk_vars;
  for (unsigned i = 0, size = candidates.size(); i < size; i++)
  {
    Node cv = candidate_values[i];
    // get the most general candidate skeleton of cv
    std::unordered_map<TNode, Node, TNodeHashFunction> visited;
    std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
    std::vector<TNode> visit;
    TNode cur;
    visit.push_back(cv);
    do {
      cur = visit.back();
      visit.pop_back();
      it = visited.find(cur);

      if (it == visited.end()) {
        visited[cur] = Node::null();
        // if it is a constant over a type that allows all constants
        TypeNode tn = cur.getType();
        Assert( tn.isDatatype() );
        const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
        Assert(dt.isSygus());
        if( dt.getSygusAllowConst() )
        {
          Node op = cur.getOperator();
          unsigned cindex = Datatype::indexOf( op.toExpr() );
          if( dt[cindex].getNumArgs()==0 )
          {
            Node sygusOp = Node::fromExpr( dt[cindex].getSygusOp() );
            if( sygusOp.isConst() )
            {
              Node sk_var = d_tds->getFreeVarInc(tn,free_var_count);
              sk_vars.push_back( sk_var );
              // replace it by the next free variable
              visited[cur] = sk_var;
            }
          }
        }
        visit.push_back(cur);
        for (const Node& cn : cur) {
          visit.push_back(cn);
        }
      } else if (it->second.isNull()) {
        Node ret = cur;
        bool childChanged = false;
        std::vector<Node> children;
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
          children.push_back(cur.getOperator());
        }
        for (const Node& cn : cur) {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
        if (childChanged) {
          ret = nm->mkNode(cur.getKind(), children);
        }
        visited[cur] = ret;
      }
    } while (!visit.empty());
    Assert(visited.find(cv) != visited.end());
    Assert(!visited.find(cv)->second.isNull());
    Node skeleton = visited[cv];
    if( Trace.isOn("sygus-repair-const") )
    {
      Printer * p = Printer::getPrinter(options::outputLanguage());
      std::stringstream ss;
      p->toStreamSygus(ss, cv);
      Trace("sygus-repair-const") << "Solution #" << i << " : " << ss.str() << std::endl;
      if( skeleton==cv )
      {
        Trace("sygus-repair-const") << "...solution unchanged" << std::endl;
      }
      else
      {
        std::stringstream sss;
        p->toStreamSygus(sss, skeleton);
        Trace("sygus-repair-const") << "...inferred skeleton : " << sss.str() << std::endl;
      }
    }
    candidate_skeletons.push_back( skeleton );
    changed = changed || skeleton!=cv;
  }

  if (changed)
  {
    Trace("sygus-repair-const") << "Substitute solution skeletons..." << std::endl;
    //make the quantified satisfiability query
    Node body = d_base_inst.negate();
    body = body.substitute( candidates.begin(), candidates.end(), candidate_skeletons.begin(), candidate_skeletons.end() );
    Trace("sygus-repair-const-debug") << "...got : " << body << std::endl;

    Trace("sygus-repair-const") << "Unfold the specification..." << std::endl;
    body = d_tds->evaluateWithUnfolding(body);
    Trace("sygus-repair-const-debug") << "...got : " << body << std::endl;
    
    Trace("sygus-repair-const") << "Introduce first-order vars..." << std::endl;
    // now, we must replace all terms of the form eval( z_i, t1...tn ) with
    // a fresh first-order variable w_i, where z_i is a variable introduced in
    // the skeleton inference step above.
    std::map< Node, Node > var_to_fovar;
    std::unordered_map<TNode, Node, TNodeHashFunction> visited;
    std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
    std::vector<TNode> visit;
    TNode cur;
    visit.push_back(body);
    do {
      cur = visit.back();
      visit.pop_back();
      it = visited.find(cur);

      if (it == visited.end()) {
        visited[cur] = Node::null();
        if( cur.getKind()==APPLY_UF && cur.getNumChildren()>0 )
        {
          Node v = cur[0];
          if( std::find( sk_vars.begin(), sk_vars.end(), v )!=sk_vars.end() )
          {
            std::map< Node, Node >::iterator itf = var_to_fovar.find( v );
            if( itf==var_to_fovar.end() )
            {
              Node sk_fov = nm->mkSkolem("k",cur.getType() );
              var_to_fovar[v] = sk_fov;
              itf = var_to_fovar.find( v );
            }
            visited[cur] = itf->second;
          }
        }
        if( visited[cur].isNull() )
        {
          visit.push_back(cur);
          for (const Node& cn : cur) {
            visit.push_back(cn);
          }
        }
      } else if (it->second.isNull()) {
        Node ret = cur;
        bool childChanged = false;
        std::vector<Node> children;
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
          children.push_back(cur.getOperator());
        }
        for (const Node& cn : cur) {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
        if (childChanged) {
          ret = nm->mkNode(cur.getKind(), children);
        }
        visited[cur] = ret;
      }
    } while (!visit.empty());
    Assert(visited.find(body) != visited.end());
    Assert(!visited.find(body)->second.isNull());
    Node fo_body = visited[body];
    Trace("sygus-repair-const-debug") << "...got : " << fo_body << std::endl;
    
  }

  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
