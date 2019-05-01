/*********************                                                        */
/*! \file fp_ic_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The ExtRewPre preprocessing pass
 **
 ** Applies the extended rewriter to assertions
 **/

#include "preprocessing/passes/fp_ic_pass.h"

#include "options/quantifiers_options.h"
#include "expr/node_algorithm.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

FpIcPre::FpIcPre(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "fp-ic-pre"){};

int FpIcPre::getCtnIndex( Node x, Node n)
{
  int ctnIndex = -1;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( expr::hasSubterm(n[i],x) ){
      if( ctnIndex==-1 ){
        ctnIndex = i;
      }else{
        return -1;
      }
    }
  }
  return ctnIndex;
}
Node FpIcPre::solve( Node x, Node p, std::vector< Node >& ics, int ctnIndex, bool useIc ){
  Trace("fp-ic-solve") << "Solve for " << x << " in " << p << ", ctnIndex=" << ctnIndex << std::endl;
  NodeManager * nm = NodeManager::currentNM();
  Kind pk = p.getKind();
  if( pk==NOT ){
    Kind pck = p[0].getKind();
    Kind fk = pck==FLOATINGPOINT_LEQ ? FLOATINGPOINT_GT : 
              ( pck==FLOATINGPOINT_GEQ ? FLOATINGPOINT_LT :
              ( pck==FLOATINGPOINT_GT ? FLOATINGPOINT_LEQ :
              ( pck==FLOATINGPOINT_LT ? FLOATINGPOINT_GEQ : UNDEFINED_KIND ) ) );
    if( fk==UNDEFINED_KIND ){
      Trace("fp-ic-solve") << " ....failed to handle negation." << std::endl;
      return Node::null();
    }else{
      Node pf = nm->mkNode( fk, p[0][0], p[0][1] );
      return solve(x,pf,ics,ctnIndex,useIc);
    }
  }
  if( ctnIndex==-1 ){
    ctnIndex = getCtnIndex(x,p);
    Trace("fp-ic-solve") << "...got ctnIndex " << ctnIndex << std::endl;
    if( ctnIndex==-1 ){
      Trace("fp-ic-solve") << " ....failed to find contains index." << std::endl;
      return Node::null();
    }
  }
  Node tx = p[ctnIndex];
  if( tx.getKind()==FLOATINGPOINT_NEG && pk==EQUAL ){
    Node eq = tx[0].eqNode(nm->mkNode(FLOATINGPOINT_NEG,p[1-ctnIndex]));
    return solve(x,eq,ics,0,useIc);
  }
  if( tx==x ){
    Node t = p[1-ctnIndex];
    if( pk==EQUAL || pk==FLOATINGPOINT_LEQ || pk==FLOATINGPOINT_GEQ ){
      Trace("fp-ic-solve") << "....success: " << t << std::endl;
      return t;
    }else{
      //Node k = nm->mkSkolem("k_strict", t.getType());
      //Trace("fp-ic-solve") << "....success: " << k << std::endl;
      Trace("fp-ic-solve") << " ....unknown predicate " << pk << std::endl;
      return Node::null();
    }
  }
  int tCtnIndex = getCtnIndex(x,tx);
  if( tCtnIndex==-1 ){
      Trace("fp-ic-solve") << " ....failed to find contains index in term." << std::endl;
    return Node::null();
  }
  Node k = nm->mkSkolem("k", tx[tCtnIndex].getType());
  Node eq = tx[tCtnIndex].eqNode(k);
  
  Kind txk = tx.getKind();
  Node ic;
  if( pk==EQUAL ){
    Node t = p[1-ctnIndex];
    if( txk==FLOATINGPOINT_MULT ){
      Node s = tx[3-tCtnIndex];
      if( !useIc ){
        // x*s = t ---> x = t/s
        Node res = nm->mkNode( FLOATINGPOINT_DIV, tx[0], t, s );
        Node eqd = tx[tCtnIndex].eqNode(res);
        return solve(x,eqd,ics,0,useIc);
      }
      //(define-fun IC ((s FP) (t FP)) Bool (or (= t (fp.mul R s (fp.div RTP t s))) (= t (fp.mul R s (fp.div RTN t s))) (and (fp.isInfinite s) (fp.isInfinite t)) (and (fp.isZero s) (fp.isZero t))))
      Node eq1 = t.eqNode( nm->mkNode( FLOATINGPOINT_MULT, tx[0], s, 
                             nm->mkNode( FLOATINGPOINT_DIV, nm->mkConst<RoundingMode>(roundTowardPositive), t, s ) ) );
      Node eq2 = t.eqNode( nm->mkNode( FLOATINGPOINT_MULT, tx[0], s, 
                             nm->mkNode( FLOATINGPOINT_DIV, nm->mkConst<RoundingMode>(roundTowardNegative), t, s ) ) );
      Node sc1 = nm->mkNode( AND, nm->mkNode( FLOATINGPOINT_ISINF, t ), nm->mkNode( FLOATINGPOINT_ISINF, s ) );
      Node sc2 = nm->mkNode( AND, nm->mkNode( FLOATINGPOINT_ISZ, t ), nm->mkNode( FLOATINGPOINT_ISZ, s ) );
      ic = nm->mkNode( OR, eq1, eq2, sc1, sc2 );
      ic = nm->mkNode( IMPLIES, ic, nm->mkNode( FLOATINGPOINT_MULT, tx[0], k, s ).eqNode(t) );
    }else if( txk==FLOATINGPOINT_DIV && tCtnIndex==1 ){
      Node s = tx[3-tCtnIndex];
      if( !useIc ){
        // x/s = t ---> x = t*s
        Node res = nm->mkNode( FLOATINGPOINT_MULT, tx[0], t, s );
        Node eqd = tx[tCtnIndex].eqNode(res);
        return solve(x,eqd,ics,0,useIc);
      }
      //(define-fun IC ((s FP) (t FP)) Bool (or (= t (fp.div R (fp.mul RTP s t) s)) (= t (fp.div R (fp.mul RTN s t) s)) (ite (fp.isInfinite s) (fp.isZero t) (and (fp.isInfinite t) (fp.isZero s)))))
      Node eq1 = t.eqNode( nm->mkNode( FLOATINGPOINT_DIV, tx[0], 
                             nm->mkNode( FLOATINGPOINT_MULT, nm->mkConst<RoundingMode>(roundTowardPositive), s, t ), s ) );
      Node eq2 = t.eqNode( nm->mkNode( FLOATINGPOINT_DIV, tx[0], 
                             nm->mkNode( FLOATINGPOINT_MULT, nm->mkConst<RoundingMode>(roundTowardNegative), s, t ), s ) );
      Node sc = nm->mkNode( ITE, nm->mkNode( FLOATINGPOINT_ISINF, s ), nm->mkNode( FLOATINGPOINT_ISZ, t ), 
                                 nm->mkNode( AND,  nm->mkNode( FLOATINGPOINT_ISINF, t ), nm->mkNode( FLOATINGPOINT_ISZ, s ) ) );
      ic = nm->mkNode( OR, eq1, eq2, sc );
      ic = nm->mkNode( IMPLIES, ic, nm->mkNode( FLOATINGPOINT_DIV, tx[0], k, s ).eqNode(t) );
    }else if( txk==FLOATINGPOINT_DIV && tCtnIndex==2 ){
      Node s = tx[3-tCtnIndex];
      if( !useIc ){
        // s/x = t ---> x = s/t
        Node res = nm->mkNode( FLOATINGPOINT_DIV, tx[0], s, t );
        Node eqd = tx[tCtnIndex].eqNode(res);
        return solve(x,eqd,ics,0,useIc);
      }
      //(define-fun IC ((s FP) (t FP)) Bool (or (= t (fp.div R s (fp.div RTP s t))) (= t (fp.div R s (fp.div RTN s t))) (and (fp.isInfinite s) (fp.isInfinite t)) (and (fp.isZero s) (fp.isZero t))))
      Node eq1 = t.eqNode( nm->mkNode( FLOATINGPOINT_DIV, tx[0], s, 
                             nm->mkNode( FLOATINGPOINT_DIV, nm->mkConst<RoundingMode>(roundTowardPositive), t, s ) ) );
      Node eq2 = t.eqNode( nm->mkNode( FLOATINGPOINT_DIV, tx[0], s, 
                             nm->mkNode( FLOATINGPOINT_DIV, nm->mkConst<RoundingMode>(roundTowardNegative), t, s ) ) );
      Node sc1 = nm->mkNode( AND, nm->mkNode( FLOATINGPOINT_ISINF, t ), nm->mkNode( FLOATINGPOINT_ISINF, s ) );
      Node sc2 = nm->mkNode( AND, nm->mkNode( FLOATINGPOINT_ISZ, t ), nm->mkNode( FLOATINGPOINT_ISZ, s ) );
      ic = nm->mkNode( OR, eq1, eq2, sc1, sc2 );
      ic = nm->mkNode( IMPLIES, ic, nm->mkNode( FLOATINGPOINT_DIV, tx[0], s, k ).eqNode(t) );
    }else if( txk==FLOATINGPOINT_PLUS ){
      Node s = tx[3-tCtnIndex];
      if( !useIc ){
        // s+x = t ---> x = t-s
        Node res = nm->mkNode( FLOATINGPOINT_SUB, tx[0], t, s );
        Node eqd = tx[tCtnIndex].eqNode(res);
        return solve(x,eqd,ics,0,useIc);
      }
      //(define-fun IC ((s FP) (t FP)) Bool (or (= t (fp.add R s (fp.sub RTP t s))) (= t (fp.add R s (fp.sub RTN t s))) (= s t)))
      Node eq1 = t.eqNode( nm->mkNode( FLOATINGPOINT_PLUS, tx[0], s, 
                             nm->mkNode( FLOATINGPOINT_SUB, nm->mkConst<RoundingMode>(roundTowardPositive), t, s ) ) );
      Node eq2 = t.eqNode( nm->mkNode( FLOATINGPOINT_PLUS, tx[0], s, 
                             nm->mkNode( FLOATINGPOINT_SUB, nm->mkConst<RoundingMode>(roundTowardNegative), t, s ) ) );
      Node sc = t.eqNode(s);
      ic = nm->mkNode( OR, eq1, eq2, sc );
      ic = nm->mkNode( IMPLIES, ic, nm->mkNode( FLOATINGPOINT_PLUS, tx[0], s, k ).eqNode(t) );
    }
  }else if( pk==LEQ ){
    if( txk==FLOATINGPOINT_PLUS ){
      //proc = true;
      // TODO
    }
  }
  if( !ic.isNull() ){
    Trace("fp-ic-req") << "CHOICE: " << pk << "/" << txk << ", index : " << ctnIndex << "/" << tCtnIndex << std::endl;
    Trace("fp-ic-req") << "...IC: " << ic << std::endl;
    ics.push_back(ic);
    return solve(x,eq,ics,0,useIc);
  }else{
    Trace("fp-ic-req") << "REQUIRES: " << pk << "/" << txk << ", index : " << ctnIndex << "/" << tCtnIndex << std::endl;
    return Node::null();
  }
}

class FpInst 
{
public:
  std::vector< Node > d_ics;
  Node d_res;
};

void instantiate( Node q, std::vector< Node >& vars, std::vector< Node >& subs, 
                  std::vector< Node >& ics, std::unordered_set< Node, NodeHashFunction >& ilemmas, 
                  std::map< unsigned, std::map< unsigned, FpInst > >& fpMap )
{
  unsigned i = subs.size();
  if( i==q[0].getNumChildren() ){
    for( const Node& ic : ics )
    {
      Node sic = ic.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      ilemmas.insert(sic);
    }
    Node inst = q[1].substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    Node ilem = NodeManager::currentNM()->mkNode( OR, q.negate(), inst );
    ilemmas.insert(ilem);
    return;
  }
  for( const std::pair< unsigned, FpInst >& p : fpMap[i] )
  {
    const FpInst& fi = p.second;
    if( !fi.d_res.isNull() ){
      subs.push_back(fi.d_res);
      for( const Node ic : fi.d_ics ){
        ics.push_back(ic);
      }
      instantiate(q,vars,subs,ics,ilemmas, fpMap);
      for( const Node ic : fi.d_ics ){
        ics.pop_back();
      }
      subs.pop_back();
    }
  }
}

PreprocessingPassResult FpIcPre::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector< Node > quants;
  TNode cur;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node n = (*assertionsToPreprocess)[i];
    
    // search for quantifiers
    visit.push_back(n);
    do {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end()) {
        visited.insert(cur);
        if( cur.getKind()==FORALL ){
          quants.push_back(cur);
        }
        for (const Node& cn : cur ){
          visit.push_back(cn);
        }
      }
    } while (!visit.empty());
  }
  
  std::unordered_set< Node, NodeHashFunction > ilemmas;
  for( const Node& q : quants )
  {
    Trace("fp-ic") << "FP-IC: Quantified formula : " << q << std::endl;
    std::vector< Node > qlits;
    if( q[1].getKind()==OR ){
      for( const Node& ql : q[1] ){
        qlits.push_back(ql.negate());
      }
    }else{
      qlits.push_back(q[1].negate());
    }
    std::map< unsigned, std::map< unsigned, FpInst > > fpMap;
    for( unsigned i=0; i<qlits.size(); i++ ){
      Node ql = qlits[i];
      Trace("fp-ic") << "- literal to solve: " << ql << std::endl;
      for( unsigned j=0; j<q[0].getNumChildren(); j++ ){
        fpMap[j][i].d_res = solve( q[0][j], ql, fpMap[j][i].d_ics, -1, options::fpIcPreIc() );
      }
    }
    // add product of instantiations
    std::vector< Node > vars;
    for( const Node& v : q[0] ){
      vars.push_back(v);
    }
    std::vector< Node > subs;
    std::vector< Node > ics;
    instantiate( q, vars, subs, ics, ilemmas, fpMap );
  }
  if( !ilemmas.empty() ){
    std::vector< Node > newAssertions;
    newAssertions.push_back((*assertionsToPreprocess)[0]);
    for( const Node& lem : ilemmas ){
      Trace("fp-ic") << "**** Generated lemma: " << lem << std::endl;
      Trace("fp-ic-lemma") << "(assert " << lem << ")" << std::endl;
      newAssertions.push_back(lem);
    }
    Node newA = NodeManager::currentNM()->mkNode( AND, newAssertions);
    Trace("fp-ic") << "Replace : " << (*assertionsToPreprocess)[0] << std::endl;
    Trace("fp-ic") << "With: " << newA << std::endl;
    assertionsToPreprocess->replace(0, newA);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
