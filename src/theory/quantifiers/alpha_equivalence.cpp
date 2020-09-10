/*********************                                                        */
/*! \file alpha_equivalence.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Alpha equivalence checking
 **
 **/

#include "theory/quantifiers/alpha_equivalence.h"

#include "theory/quantifiers_engine.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

struct sortTypeOrder {
  expr::TermCanonize* d_tu;
  bool operator() (TypeNode i, TypeNode j) {
    return d_tu->getIdForType( i )<d_tu->getIdForType( j );
  }
};

Node AlphaEquivalenceNode::registerNode(Node q, Node t)
{
  AlphaEquivalenceNode* aen = this;
  std::vector<Node> tt;
  std::vector<int> arg_index;
  tt.push_back(t);
  std::map< Node, bool > visited;
  while( !tt.empty() ){
    if( tt.size()==arg_index.size()+1 ){
      Node tb = tt.back();
      Node op;
      if (tb.hasOperator())
      {
        if (visited.find(tb) == visited.end())
        {
          visited[tb] = true;
          op = tb.getOperator();
          arg_index.push_back( 0 );
        }
        else
        {
          op = tb;
          arg_index.push_back( -1 );
        }
      }
      else
      {
        op = tb;
        arg_index.push_back( 0 );
      }
      Trace("aeq-debug") << op << " ";
      aen = &(aen->d_children[op][tb.getNumChildren()]);
    }else{
      Node tb = tt.back();
      int i = arg_index.back();
      if (i == -1 || i == (int)tb.getNumChildren())
      {
        tt.pop_back();
        arg_index.pop_back();
      }
      else
      {
        tt.push_back(tb[i]);
        arg_index[arg_index.size()-1]++;
      }
    }
  }
  Trace("aeq-debug") << std::endl;
  if( aen->d_quant.isNull() ){
    aen->d_quant = q;
  }
  return aen->d_quant;
}

Node AlphaEquivalenceTypeNode::registerNode(Node q,
                                            Node t,
                                            std::vector<TypeNode>& typs,
                                            std::map<TypeNode, int>& typ_count)
{
  AlphaEquivalenceTypeNode* aetn = this;
  unsigned index = 0;
  while (index < typs.size())
  {
    TypeNode curr = typs[index];
    Assert(typ_count.find(curr) != typ_count.end());
    Trace("aeq-debug") << "[" << curr << " " << typ_count[curr] << "] ";
    aetn = &(aetn->d_children[curr][typ_count[curr]]);
    index = index + 1;
  }
  Trace("aeq-debug") << " : ";
  return aetn->d_data.registerNode(q, t);
}

Node AlphaEquivalenceDb::addTerm(Node q)
{
  Assert(q.getKind() == FORALL);
  Trace("aeq") << "Alpha equivalence : register " << q << std::endl;
  //construct canonical quantified formula
  Node t = d_tc->getCanonicalTerm(q[1], true);
  Trace("aeq") << "  canonical form: " << t << std::endl;
  //compute variable type counts
  std::map< TypeNode, int > typ_count;
  std::vector< TypeNode > typs;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    TypeNode tn = q[0][i].getType();
    typ_count[tn]++;
    if( std::find( typs.begin(), typs.end(), tn )==typs.end() ){
      typs.push_back( tn );
    }
  }
  sortTypeOrder sto;
  sto.d_tu = d_tc;
  std::sort( typs.begin(), typs.end(), sto );
  Trace("aeq-debug") << "  ";
  Node ret = d_ae_typ_trie.registerNode(q, t, typs, typ_count);
  Trace("aeq") << "  ...result : " << ret << std::endl;
  return ret;
}

AlphaEquivalence::AlphaEquivalence(QuantifiersEngine* qe)
    : d_aedb(qe->getTermCanonize())
{
}

Node AlphaEquivalence::reduceQuantifier(Node q)
{
  Assert(q.getKind() == FORALL);
  Trace("aeq") << "Alpha equivalence : register " << q << std::endl;
  Node ret = d_aedb.addTerm(q);
  Node lem;
  if (ret != q)
  {
    // do not reduce annotated quantified formulas based on alpha equivalence
    if (q.getNumChildren() == 2)
    {
      // lemma ( q <=> d_quant )
      Trace("alpha-eq") << "Alpha equivalent : " << std::endl;
      Trace("alpha-eq") << "  " << q << std::endl;
      Trace("alpha-eq") << "  " << ret << std::endl;
      lem = q.eqNode(ret);
    }
  }
  return lem;
}
