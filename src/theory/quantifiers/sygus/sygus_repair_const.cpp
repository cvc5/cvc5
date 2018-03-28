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

void SygusRepairConst::initialize(Node q) 
{
  Assert( q.getKind()==FORALL );
  Trace("sygus-repair-cons") << "SygusRepairConst::initialize" << std::endl;
  Trace("sygus-repair-cons") << "  conjecture : " << q << std::endl;
  d_embed_quant = q;
  
  // compute whether there are "allow all constant" types in the variables of q
  std::map<TypeNode, bool > tprocessed;
  for( const Node& v : q[0] )
  {
    TypeNode tn = v.getType();
    // do the type traversal of the sygus type
    registerSygusType( tn, tprocessed );
  }
  Trace("sygus-repair-cons") << "  allow constants : " << d_allow_constant_grammar << std::endl;
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
  if (d_embed_quant.isNull() || !d_allow_constant_grammar)
  {
    return false;
  }
  if( Trace.isOn("sygus-repair-cons") )
  {
    Trace("sygus-repair-cons") << "Repair candidate solutions..." << std::endl;
    for( unsigned i=0,size=candidates.size(); i<size; i++ )
    {
      Trace("sygus-repair-cons") << "  " << candidates[i] << " -> " << candidate_values[i] << std::endl;
    }
    Trace("sygus-repair-cons") << "Getting candidate skeletons : " << std::endl;
  }
  bool changed = false;
  std::vector< Node > candidate_skeletons;
  std::map<TypeNode, int> free_var_count;
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
          Node sygusOp = Node::fromExpr( dt[cindex].getSygusOp() );
          if( sygusOp.isConst() )
          {
            // replace it by the next free variable
            Node var = d_tds->getFreeVarInc(tn,free_var_count);
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
          ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
        }
        visited[cur] = ret;
      }
    } while (!visit.empty());
    Assert(visited.find(cv) != visited.end());
    Assert(!visited.find(cv)->second.isNull());
    Node skeleton = visited[cv];
    if( Trace.isOn("sygus-repair-cons") )
    {
      Trace("sygus-repair-cons") << "Solution #" << i << " : " << cv << std::endl;
      if( skeleton==cv )
      {
        Trace("sygus-repair-cons") << "...solution unchanged" << std::endl;
      }
      else
      {
        Trace("sygus-repair-cons") << "...inferred skeleton : " << skeleton << std::endl;
      }
    }
    candidate_skeletons.push_back( skeleton );
    changed = changed || skeleton!=cv;
  }

  if (changed)
  {
    //make the 
    
  }

  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
