/*********************                                                        */
/*! \file quantifiers_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of QuantifiersRewriter class
 **/

#include "theory/quantifiers/quantifiers_rewriter.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/bv_inverter.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/strings/theory_strings_utils.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

std::ostream& operator<<(std::ostream& out, RewriteStep s)
{
  switch (s)
  {
    case COMPUTE_ELIM_SYMBOLS: out << "COMPUTE_ELIM_SYMBOLS"; break;
    case COMPUTE_MINISCOPING: out << "COMPUTE_MINISCOPING"; break;
    case COMPUTE_AGGRESSIVE_MINISCOPING:
      out << "COMPUTE_AGGRESSIVE_MINISCOPING";
      break;
    case COMPUTE_EXT_REWRITE: out << "COMPUTE_EXT_REWRITE"; break;
    case COMPUTE_PROCESS_TERMS: out << "COMPUTE_PROCESS_TERMS"; break;
    case COMPUTE_PRENEX: out << "COMPUTE_PRENEX"; break;
    case COMPUTE_VAR_ELIMINATION: out << "COMPUTE_VAR_ELIMINATION"; break;
    case COMPUTE_COND_SPLIT: out << "COMPUTE_COND_SPLIT"; break;
    default: out << "UnknownRewriteStep"; break;
  }
  return out;
}

bool QuantifiersRewriter::isLiteral( Node n ){
  switch( n.getKind() ){
  case NOT:
    return n[0].getKind()!=NOT && isLiteral( n[0] );
    break;
  case OR:
  case AND:
  case IMPLIES:
  case XOR:
  case ITE:
    return false;
    break;
  case EQUAL:
    //for boolean terms
    return !n[0].getType().isBoolean();
    break;
  default:
    break;
  }
  return true;
}

void QuantifiersRewriter::addNodeToOrBuilder( Node n, NodeBuilder<>& t ){
  if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      t << n[i];
    }
  }else{
    t << n;
  }
}

void QuantifiersRewriter::computeArgs(const std::vector<Node>& args,
                                      std::map<Node, bool>& activeMap,
                                      Node n,
                                      std::map<Node, bool>& visited)
{
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==BOUND_VARIABLE ){
      if( std::find( args.begin(), args.end(), n )!=args.end() ){
        activeMap[ n ] = true;
      }
    }else{
      if (n.hasOperator())
      {
        computeArgs(args, activeMap, n.getOperator(), visited);
      }
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        computeArgs( args, activeMap, n[i], visited );
      }
    }
  }
}

void QuantifiersRewriter::computeArgVec(const std::vector<Node>& args,
                                        std::vector<Node>& activeArgs,
                                        Node n)
{
  Assert(activeArgs.empty());
  std::map< Node, bool > activeMap;
  std::map< Node, bool > visited;
  computeArgs( args, activeMap, n, visited );
  if( !activeMap.empty() ){
    for( unsigned i=0; i<args.size(); i++ ){
      if( activeMap.find( args[i] )!=activeMap.end() ){
        activeArgs.push_back( args[i] );
      }
    }
  }
}

void QuantifiersRewriter::computeArgVec2(const std::vector<Node>& args,
                                         std::vector<Node>& activeArgs,
                                         Node n,
                                         Node ipl)
{
  Assert(activeArgs.empty());
  std::map< Node, bool > activeMap;
  std::map< Node, bool > visited;
  computeArgs( args, activeMap, n, visited );
  if( !activeMap.empty() ){
    //collect variables in inst pattern list only if we cannot eliminate quantifier
    computeArgs( args, activeMap, ipl, visited );
    for( unsigned i=0; i<args.size(); i++ ){
      if( activeMap.find( args[i] )!=activeMap.end() ){
        activeArgs.push_back( args[i] );
      }
    }
  }
}

RewriteResponse QuantifiersRewriter::preRewrite(TNode in) {
  if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
    Trace("quantifiers-rewrite-debug") << "pre-rewriting " << in << std::endl;
    std::vector< Node > args;
    Node body = in;
    bool doRewrite = false;
    while( body.getNumChildren()==2 && body.getKind()==body[1].getKind() ){
      for( unsigned i=0; i<body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }
      body = body[1];
      doRewrite = true;
    }
    if( doRewrite ){
      std::vector< Node > children;
      for( unsigned i=0; i<body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }      
      children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,args) );
      children.push_back( body[1] );
      if( body.getNumChildren()==3 ){
        children.push_back( body[2] );
      }
      Node n = NodeManager::currentNM()->mkNode( in.getKind(), children );
      if( in!=n ){
        Trace("quantifiers-pre-rewrite") << "*** pre-rewrite " << in << std::endl;
        Trace("quantifiers-pre-rewrite") << " to " << std::endl;
        Trace("quantifiers-pre-rewrite") << n << std::endl;
      }
      return RewriteResponse(REWRITE_DONE, n);
    }
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse QuantifiersRewriter::postRewrite(TNode in) {
  Trace("quantifiers-rewrite-debug") << "post-rewriting " << in << std::endl;
  RewriteStatus status = REWRITE_DONE;
  Node ret = in;
  RewriteStep rew_op = COMPUTE_LAST;
  //get the body
  if( in.getKind()==EXISTS ){
    std::vector< Node > children;
    children.push_back( in[0] );
    children.push_back( in[1].negate() );
    if( in.getNumChildren()==3 ){
      children.push_back( in[2] );
    }
    ret = NodeManager::currentNM()->mkNode( FORALL, children );
    ret = ret.negate();
    status = REWRITE_AGAIN_FULL;
  }else if( in.getKind()==FORALL ){
    if( in[1].isConst() && in.getNumChildren()==2 ){
      return RewriteResponse( status, in[1] );
    }else{
      //compute attributes
      QAttributes qa;
      QuantAttributes::computeQuantAttributes( in, qa );
      for (unsigned i = 0; i < COMPUTE_LAST; ++i)
      {
        RewriteStep op = static_cast<RewriteStep>(i);
        if( doOperation( in, op, qa ) ){
          ret = computeOperation( in, op, qa );
          if( ret!=in ){
            rew_op = op;
            status = REWRITE_AGAIN_FULL;
            break;
          }
        }
      }
    }
  }
  //print if changed
  if( in!=ret ){
    Trace("quantifiers-rewrite") << "*** rewrite (op=" << rew_op << ") " << in << std::endl;
    Trace("quantifiers-rewrite") << " to " << std::endl;
    Trace("quantifiers-rewrite") << ret << std::endl;
  }
  return RewriteResponse( status, ret );
}

bool QuantifiersRewriter::addCheckElimChild( std::vector< Node >& children, Node c, Kind k, std::map< Node, bool >& lit_pol, bool& childrenChanged ){
  if( ( k==OR || k==AND ) && options::elimTautQuant() ){
    Node lit = c.getKind()==NOT ? c[0] : c;
    bool pol = c.getKind()!=NOT;
    std::map< Node, bool >::iterator it = lit_pol.find( lit );
    if( it==lit_pol.end() ){
      lit_pol[lit] = pol;
      children.push_back( c );
    }else{
      childrenChanged = true;
      if( it->second!=pol ){
        return false;
      }
    }
  }else{
    children.push_back( c );
  }
  return true;
}

// eliminates IMPLIES/XOR, removes duplicates/infers tautologies of AND/OR, and computes NNF
Node QuantifiersRewriter::computeElimSymbols( Node body ) {
  Kind ok = body.getKind();
  Kind k = ok;
  bool negAllCh = false;
  bool negCh1 = false;
  if( ok==IMPLIES ){
    k = OR;
    negCh1 = true;
  }else if( ok==XOR ){
    k = EQUAL;
    negCh1 = true;
  }else if( ok==NOT ){
    if( body[0].getKind()==NOT ){
      return computeElimSymbols( body[0][0] );
    }else if( body[0].getKind()==OR || body[0].getKind()==IMPLIES ){
      k = AND;   
      negAllCh = true;
      negCh1 = body[0].getKind()==IMPLIES;
      body = body[0];
    }else if( body[0].getKind()==AND ){
      k = OR;
      negAllCh = true;
      body = body[0];
    }else if( body[0].getKind()==XOR || ( body[0].getKind()==EQUAL && body[0][0].getType().isBoolean() ) ){
      k = EQUAL;
      negCh1 = ( body[0].getKind()==EQUAL );
      body = body[0];
    }else if( body[0].getKind()==ITE ){
      k = body[0].getKind();
      negAllCh = true;
      negCh1 = true;
      body = body[0];
    }else{
      return body;
    }
  }else if( ( ok!=EQUAL || !body[0].getType().isBoolean() ) && ok!=ITE && ok!=AND && ok!=OR ){
    //a literal
    return body;
  }
  bool childrenChanged = false;
  std::vector< Node > children;
  std::map< Node, bool > lit_pol;
  for( unsigned i=0; i<body.getNumChildren(); i++ ){
    Node c = computeElimSymbols( ( i==0 && negCh1 )!=negAllCh ? body[i].negate() : body[i] );
    bool success = true;
    if( c.getKind()==k && ( k==OR || k==AND ) ){
      //flatten
      childrenChanged = true;
      for( unsigned j=0; j<c.getNumChildren(); j++ ){
        if( !addCheckElimChild( children, c[j], k, lit_pol, childrenChanged ) ){
          success = false;
          break;
        }
      }
    }else{
      success = addCheckElimChild( children, c, k, lit_pol, childrenChanged );
    }
    if( !success ){
      // tautology
      Assert(k == OR || k == AND);
      return NodeManager::currentNM()->mkConst( k==OR );
    }
    childrenChanged = childrenChanged || c!=body[i];
  }
  if( childrenChanged || k!=ok ){
    return ( children.size()==1 && k!=NOT ) ? children[0] : NodeManager::currentNM()->mkNode( k, children );
  }else{
    return body;
  }
}

void QuantifiersRewriter::computeDtTesterIteSplit( Node n, std::map< Node, Node >& pcons, std::map< Node, std::map< int, Node > >& ncons,
                                                   std::vector< Node >& conj ){
  if( n.getKind()==ITE && n[0].getKind()==APPLY_TESTER && n[1].getType().isBoolean() ){
    Trace("quantifiers-rewrite-ite-debug") << "Split tester condition : " << n << std::endl;
    Node x = n[0][0];
    std::map< Node, Node >::iterator itp = pcons.find( x );
    if( itp!=pcons.end() ){
      Trace("quantifiers-rewrite-ite-debug") << "...condition already set " << itp->second << std::endl;
      computeDtTesterIteSplit( n[ itp->second==n[0] ? 1 : 2 ], pcons, ncons, conj );
    }else{
      Node tester = n[0].getOperator();
      int index = datatypes::utils::indexOf(tester);
      std::map< int, Node >::iterator itn = ncons[x].find( index );
      if( itn!=ncons[x].end() ){
        Trace("quantifiers-rewrite-ite-debug") << "...condition negated " << itn->second << std::endl;
        computeDtTesterIteSplit( n[ 2 ], pcons, ncons, conj );
      }else{
        for( unsigned i=0; i<2; i++ ){
          if( i==0 ){
            pcons[x] = n[0];
          }else{
            pcons.erase( x );
            ncons[x][index] = n[0].negate();
          }
          computeDtTesterIteSplit( n[i+1], pcons, ncons, conj );
        }
        ncons[x].erase( index );
      }
    }
  }else{
    NodeManager* nm = NodeManager::currentNM();
    Trace("quantifiers-rewrite-ite-debug") << "Return value : " << n << std::endl;
    std::vector< Node > children;
    children.push_back( n );
    std::vector< Node > vars;
    //add all positive testers
    for( std::map< Node, Node >::iterator it = pcons.begin(); it != pcons.end(); ++it ){
      children.push_back( it->second.negate() );
      vars.push_back( it->first );
    }
    //add all negative testers
    for( std::map< Node, std::map< int, Node > >::iterator it = ncons.begin(); it != ncons.end(); ++it ){
      Node x = it->first;
      //only if we haven't settled on a positive tester
      if( std::find( vars.begin(), vars.end(), x )==vars.end() ){
        //check if we have exhausted all options but one
        const DType& dt = x.getType().getDType();
        std::vector< Node > nchildren;
        int pos_cons = -1;
        for( int i=0; i<(int)dt.getNumConstructors(); i++ ){
          std::map< int, Node >::iterator itt = it->second.find( i );
          if( itt==it->second.end() ){
            pos_cons = pos_cons==-1 ? i : -2;
          }else{
            nchildren.push_back( itt->second.negate() );
          }
        }
        if( pos_cons>=0 ){
          Node tester = dt[pos_cons].getTester();
          children.push_back(nm->mkNode(APPLY_TESTER, tester, x).negate());
        }else{
          children.insert( children.end(), nchildren.begin(), nchildren.end() );
        }
      }
    }
    //make condition/output pair
    Node c = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( OR, children );
    conj.push_back( c );
  }
}

Node QuantifiersRewriter::computeProcessTerms( Node body, std::vector< Node >& new_vars, std::vector< Node >& new_conds, Node q, QAttributes& qa ){
  std::map< Node, Node > cache;
  if( qa.isFunDef() ){
    Node h = QuantAttributes::getFunDefHead( q );
    Assert(!h.isNull());
    // if it is a function definition, rewrite the body independently
    Node fbody = QuantAttributes::getFunDefBody( q );
    Trace("quantifiers-rewrite-debug") << "Decompose " << h << " / " << fbody << " as function definition for " << q << "." << std::endl;
    if (!fbody.isNull())
    {
      Node r = computeProcessTerms2(fbody,
                                    cache,
                                    new_vars,
                                    new_conds,
                                    false);
      Assert(new_vars.size() == h.getNumChildren());
      return Rewriter::rewrite(NodeManager::currentNM()->mkNode(EQUAL, h, r));
    }
    // It can happen that we can't infer the shape of the function definition,
    // for example: forall xy. f( x, y ) = 1 + f( x, y ), this is rewritten to
    // forall xy. false.
  }
  return computeProcessTerms2(body,
                              cache,
                              new_vars,
                              new_conds,
                              options::elimExtArithQuant());
}

Node QuantifiersRewriter::computeProcessTerms2(Node body,
                                               std::map<Node, Node>& cache,
                                               std::vector<Node>& new_vars,
                                               std::vector<Node>& new_conds,
                                               bool elimExtArith)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("quantifiers-rewrite-term-debug2")
      << "computeProcessTerms " << body << std::endl;
  std::map< Node, Node >::iterator iti = cache.find( body );
  if( iti!=cache.end() ){
    return iti->second;
  }
  bool changed = false;
  std::vector<Node> children;
  for (size_t i = 0; i < body.getNumChildren(); i++)
  {
    // do the recursive call on children
    Node nn =
        computeProcessTerms2(body[i], cache, new_vars, new_conds, elimExtArith);
    children.push_back(nn);
    changed = changed || nn != body[i];
  }

  // make return value
  Node ret;
  if (changed)
  {
    if (body.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.insert(children.begin(), body.getOperator());
    }
    ret = nm->mkNode(body.getKind(), children);
  }
  else
  {
    ret = body;
  }

  Trace("quantifiers-rewrite-term-debug2")
      << "Returning " << ret << " for " << body << std::endl;
  // do context-independent rewriting
  if (ret.getKind() == EQUAL
      && options::iteLiftQuant() != options::IteLiftQuantMode::NONE)
  {
    for (size_t i = 0; i < 2; i++)
    {
      if (ret[i].getKind() == ITE)
      {
        Node no = i == 0 ? ret[1] : ret[0];
        if (no.getKind() != ITE)
        {
          bool doRewrite =
              options::iteLiftQuant() == options::IteLiftQuantMode::ALL;
          std::vector<Node> childrenIte;
          childrenIte.push_back(ret[i][0]);
          for (size_t j = 1; j <= 2; j++)
          {
            // check if it rewrites to a constant
            Node nn = nm->mkNode(EQUAL, no, ret[i][j]);
            nn = Rewriter::rewrite(nn);
            childrenIte.push_back(nn);
            if (nn.isConst())
            {
              doRewrite = true;
            }
          }
          if (doRewrite)
          {
            ret = nm->mkNode(ITE, childrenIte);
            break;
          }
        }
      }
    }
  }
  else if (ret.getKind() == SELECT && ret[0].getKind() == STORE)
  {
    Node st = ret[0];
    Node index = ret[1];
    std::vector<Node> iconds;
    std::vector<Node> elements;
    while (st.getKind() == STORE)
    {
      iconds.push_back(index.eqNode(st[1]));
      elements.push_back(st[2]);
      st = st[0];
    }
    ret = nm->mkNode(SELECT, st, index);
    // conditions
    for (int i = (iconds.size() - 1); i >= 0; i--)
    {
      ret = nm->mkNode(ITE, iconds[i], elements[i], ret);
    }
  }
  else if (elimExtArith)
  {
    if (ret.getKind() == INTS_DIVISION_TOTAL
        || ret.getKind() == INTS_MODULUS_TOTAL)
    {
      Node num = ret[0];
      Node den = ret[1];
      if (den.isConst())
      {
        const Rational& rat = den.getConst<Rational>();
        Assert(!num.isConst());
        if (rat != 0)
        {
          Node intVar = nm->mkBoundVar(nm->integerType());
          new_vars.push_back(intVar);
          Node cond;
          if (rat > 0)
          {
            cond = nm->mkNode(
                AND,
                nm->mkNode(LEQ, nm->mkNode(MULT, den, intVar), num),
                nm->mkNode(
                    LT,
                    num,
                    nm->mkNode(
                        MULT,
                        den,
                        nm->mkNode(PLUS, intVar, nm->mkConst(Rational(1))))));
          }
          else
          {
            cond = nm->mkNode(
                AND,
                nm->mkNode(LEQ, nm->mkNode(MULT, den, intVar), num),
                nm->mkNode(
                    LT,
                    num,
                    nm->mkNode(
                        MULT,
                        den,
                        nm->mkNode(PLUS, intVar, nm->mkConst(Rational(-1))))));
          }
          new_conds.push_back(cond.negate());
          if (ret.getKind() == INTS_DIVISION_TOTAL)
          {
            ret = intVar;
          }
          else
          {
            ret = nm->mkNode(MINUS, num, nm->mkNode(MULT, den, intVar));
          }
        }
      }
    }
    else if (ret.getKind() == TO_INTEGER || ret.getKind() == IS_INTEGER)
    {
      Node intVar = nm->mkBoundVar(nm->integerType());
      new_vars.push_back(intVar);
      new_conds.push_back(
          nm->mkNode(
                AND,
                nm->mkNode(LT,
                           nm->mkNode(MINUS, ret[0], nm->mkConst(Rational(1))),
                           intVar),
                nm->mkNode(LEQ, intVar, ret[0]))
              .negate());
      if (ret.getKind() == TO_INTEGER)
      {
        ret = intVar;
      }
      else
      {
        ret = ret[0].eqNode(intVar);
      }
    }
  }
  cache[body] = ret;
  return ret;
}

Node QuantifiersRewriter::computeExtendedRewrite(Node q)
{
  Node body = q[1];
  // apply extended rewriter
  ExtendedRewriter er;
  Node bodyr = er.extendedRewrite(body);
  if (body != bodyr)
  {
    std::vector<Node> children;
    children.push_back(q[0]);
    children.push_back(bodyr);
    if (q.getNumChildren() == 3)
    {
      children.push_back(q[2]);
    }
    return NodeManager::currentNM()->mkNode(FORALL, children);
  }
  return q;
}

Node QuantifiersRewriter::computeCondSplit(Node body,
                                           const std::vector<Node>& args,
                                           QAttributes& qa)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind bk = body.getKind();
  if (options::iteDtTesterSplitQuant() && bk == ITE
      && body[0].getKind() == APPLY_TESTER)
  {
    Trace("quantifiers-rewrite-ite-debug") << "DTT split : " << body << std::endl;
    std::map< Node, Node > pcons;
    std::map< Node, std::map< int, Node > > ncons;
    std::vector< Node > conj;
    computeDtTesterIteSplit( body, pcons, ncons, conj );
    Assert(!conj.empty());
    if( conj.size()>1 ){
      Trace("quantifiers-rewrite-ite") << "*** Split ITE (datatype tester) " << body << " into : " << std::endl;
      for( unsigned i=0; i<conj.size(); i++ ){
        Trace("quantifiers-rewrite-ite") << "   " << conj[i] << std::endl;
      }
      return nm->mkNode(AND, conj);
    }
  }
  if (!options::condVarSplitQuant())
  {
    return body;
  }
  Trace("cond-var-split-debug")
      << "Conditional var elim split " << body << "?" << std::endl;

  if (bk == ITE
      || (bk == EQUAL && body[0].getType().isBoolean()
          && options::condVarSplitQuantAgg()))
  {
    Assert(!qa.isFunDef());
    bool do_split = false;
    unsigned index_max = bk == ITE ? 0 : 1;
    std::vector<Node> tmpArgs = args;
    for (unsigned index = 0; index <= index_max; index++)
    {
      if (hasVarElim(body[index], true, tmpArgs)
          || hasVarElim(body[index], false, tmpArgs))
      {
        do_split = true;
        break;
      }
    }
    if (do_split)
    {
      Node pos;
      Node neg;
      if (bk == ITE)
      {
        pos = nm->mkNode(OR, body[0].negate(), body[1]);
        neg = nm->mkNode(OR, body[0], body[2]);
      }
      else
      {
        pos = nm->mkNode(OR, body[0].negate(), body[1]);
        neg = nm->mkNode(OR, body[0], body[1].negate());
      }
      Trace("cond-var-split-debug") << "*** Split (conditional variable eq) "
                                    << body << " into : " << std::endl;
      Trace("cond-var-split-debug") << "   " << pos << std::endl;
      Trace("cond-var-split-debug") << "   " << neg << std::endl;
      return nm->mkNode(AND, pos, neg);
    }
  }

  if (bk == OR)
  {
    unsigned size = body.getNumChildren();
    bool do_split = false;
    unsigned split_index = 0;
    for (unsigned i = 0; i < size; i++)
    {
      // check if this child is a (conditional) variable elimination
      Node b = body[i];
      if (b.getKind() == AND)
      {
        std::vector<Node> vars;
        std::vector<Node> subs;
        std::vector<Node> tmpArgs = args;
        for (unsigned j = 0, bsize = b.getNumChildren(); j < bsize; j++)
        {
          if (getVarElimLit(b[j], false, tmpArgs, vars, subs))
          {
            Trace("cond-var-split-debug") << "Variable elimination in child #"
                                          << j << " under " << i << std::endl;
            // Figure out if we should split
            // Currently we split if the aggressive option is set, or
            // if the top-level OR is binary.
            if (options::condVarSplitQuantAgg() || size == 2)
            {
              do_split = true;
            }
            // other splitting criteria go here

            if (do_split)
            {
              split_index = i;
              break;
            }
            vars.clear();
            subs.clear();
            tmpArgs = args;
          }
        }
      }
      if (do_split)
      {
        break;
      }
    }
    if (do_split)
    {
      std::vector<Node> children;
      for (TNode bc : body)
      {
        children.push_back(bc);
      }
      std::vector<Node> split_children;
      for (TNode bci : body[split_index])
      {
        children[split_index] = bci;
        split_children.push_back(nm->mkNode(OR, children));
      }
      // split the AND child, for example:
      //  ( x!=a ^ P(x) ) V Q(x) ---> ( x!=a V Q(x) ) ^ ( P(x) V Q(x) )
      return nm->mkNode(AND, split_children);
    }
  }

  return body;
}

bool QuantifiersRewriter::isVarElim(Node v, Node s)
{
  Assert(v.getKind() == BOUND_VARIABLE);
  return !expr::hasSubterm(s, v) && s.getType().isSubtypeOf(v.getType());
}

Node QuantifiersRewriter::getVarElimLitBv(Node lit,
                                          const std::vector<Node>& args,
                                          Node& var)
{
  if (Trace.isOn("quant-velim-bv"))
  {
    Trace("quant-velim-bv") << "Bv-Elim : " << lit << " varList = { ";
    for (const Node& v : args)
    {
      Trace("quant-velim-bv") << v << " ";
    }
    Trace("quant-velim-bv") << "} ?" << std::endl;
  }
  Assert(lit.getKind() == EQUAL);
  // TODO (#1494) : linearize the literal using utility

  // compute a subset active_args of the bound variables args that occur in lit
  std::vector<Node> active_args;
  computeArgVec(args, active_args, lit);

  BvInverter binv;
  for (const Node& cvar : active_args)
  {
    // solve for the variable on this path using the inverter
    std::vector<unsigned> path;
    Node slit = binv.getPathToPv(lit, cvar, path);
    if (!slit.isNull())
    {
      Node slv = binv.solveBvLit(cvar, lit, path, nullptr);
      Trace("quant-velim-bv") << "...solution : " << slv << std::endl;
      if (!slv.isNull())
      {
        var = cvar;
        // if this is a proper variable elimination, that is, var = slv where
        // var is not in the free variables of slv, then we can return this
        // as the variable elimination for lit.
        if (isVarElim(var, slv))
        {
          return slv;
        }
      }
    }
    else
    {
      Trace("quant-velim-bv") << "...non-invertible path." << std::endl;
    }
  }

  return Node::null();
}

Node QuantifiersRewriter::getVarElimLitString(Node lit,
                                              const std::vector<Node>& args,
                                              Node& var)
{
  Assert(lit.getKind() == EQUAL);
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0; i < 2; i++)
  {
    if (lit[i].getKind() == STRING_CONCAT)
    {
      TypeNode stype = lit[i].getType();
      for (unsigned j = 0, nchildren = lit[i].getNumChildren(); j < nchildren;
           j++)
      {
        if (std::find(args.begin(), args.end(), lit[i][j]) != args.end())
        {
          var = lit[i][j];
          Node slv = lit[1 - i];
          std::vector<Node> preL(lit[i].begin(), lit[i].begin() + j);
          std::vector<Node> postL(lit[i].begin() + j + 1, lit[i].end());
          Node tpre = strings::utils::mkConcat(preL, stype);
          Node tpost = strings::utils::mkConcat(postL, stype);
          Node slvL = nm->mkNode(STRING_LENGTH, slv);
          Node tpreL = nm->mkNode(STRING_LENGTH, tpre);
          Node tpostL = nm->mkNode(STRING_LENGTH, tpost);
          slv = nm->mkNode(
              STRING_SUBSTR,
              slv,
              tpreL,
              nm->mkNode(MINUS, slvL, nm->mkNode(PLUS, tpreL, tpostL)));
          // forall x. r ++ x ++ t = s => P( x )
          //   is equivalent to
          // r ++ s' ++ t = s => P( s' ) where
          // s' = substr( s, |r|, |s|-(|t|+|r|) ).
          // We apply this only if r,t,s do not contain free variables.
          if (!expr::hasFreeVar(slv))
          {
            return slv;
          }
        }
      }
    }
  }

  return Node::null();
}

bool QuantifiersRewriter::getVarElimLit(Node lit,
                                        bool pol,
                                        std::vector<Node>& args,
                                        std::vector<Node>& vars,
                                        std::vector<Node>& subs)
{
  if (lit.getKind() == NOT)
  {
    return getVarElimLit(lit[0], !pol, args, vars, subs);
  }
  NodeManager* nm = NodeManager::currentNM();
  Trace("var-elim-quant-debug")
      << "Eliminate : " << lit << ", pol = " << pol << "?" << std::endl;
  if (lit.getKind() == APPLY_TESTER && pol && lit[0].getKind() == BOUND_VARIABLE
      && options::dtVarExpandQuant())
  {
    Trace("var-elim-dt") << "Expand datatype variable based on : " << lit
                         << std::endl;
    std::vector<Node>::iterator ita =
        std::find(args.begin(), args.end(), lit[0]);
    if (ita != args.end())
    {
      vars.push_back(lit[0]);
      Node tester = lit.getOperator();
      int index = datatypes::utils::indexOf(tester);
      const DType& dt = datatypes::utils::datatypeOf(tester);
      const DTypeConstructor& c = dt[index];
      std::vector<Node> newChildren;
      newChildren.push_back(c.getConstructor());
      std::vector<Node> newVars;
      for (unsigned j = 0, nargs = c.getNumArgs(); j < nargs; j++)
      {
        TypeNode tn = c[j].getRangeType();
        Node v = nm->mkBoundVar(tn);
        newChildren.push_back(v);
        newVars.push_back(v);
      }
      subs.push_back(nm->mkNode(APPLY_CONSTRUCTOR, newChildren));
      Trace("var-elim-dt") << "...apply substitution " << subs[0] << "/"
                           << vars[0] << std::endl;
      args.erase(ita);
      args.insert(args.end(), newVars.begin(), newVars.end());
      return true;
    }
  }
  // all eliminations below guarded by varElimQuant()
  if (!options::varElimQuant())
  {
    return false;
  }

  if (lit.getKind() == EQUAL)
  {
    if (pol || lit[0].getType().isBoolean())
    {
      for (unsigned i = 0; i < 2; i++)
      {
        bool tpol = pol;
        Node v_slv = lit[i];
        if (v_slv.getKind() == NOT)
        {
          v_slv = v_slv[0];
          tpol = !tpol;
        }
        std::vector<Node>::iterator ita =
            std::find(args.begin(), args.end(), v_slv);
        if (ita != args.end())
        {
          if (isVarElim(v_slv, lit[1 - i]))
          {
            Node slv = lit[1 - i];
            if (!tpol)
            {
              Assert(slv.getType().isBoolean());
              slv = slv.negate();
            }
            Trace("var-elim-quant")
                << "Variable eliminate based on equality : " << v_slv << " -> "
                << slv << std::endl;
            vars.push_back(v_slv);
            subs.push_back(slv);
            args.erase(ita);
            return true;
          }
        }
      }
    }
  }
  else if (lit.getKind() == APPLY_TESTER && pol
           && lit[0].getKind() == BOUND_VARIABLE && options::dtVarExpandQuant())
  {
    Trace("var-elim-dt") << "Expand datatype variable based on : " << lit
                         << std::endl;
    Node tester = lit.getOperator();
    unsigned index = datatypes::utils::indexOf(tester);
    Node s = datatypeExpand(index, lit[0], args);
    if (!s.isNull())
    {
      vars.push_back(lit[0]);
      subs.push_back(s);
      Trace("var-elim-dt") << "...apply substitution " << s << "/" << lit[0]
                           << std::endl;
      return true;
    }
  }
  if (lit.getKind() == BOUND_VARIABLE)
  {
    std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), lit );
    if( ita!=args.end() ){
      Trace("var-elim-bool") << "Variable eliminate : " << lit << std::endl;
      vars.push_back( lit );
      subs.push_back( NodeManager::currentNM()->mkConst( pol ) );
      args.erase( ita );
      return true;
    }
  }
  if (lit.getKind() == EQUAL && lit[0].getType().isReal() && pol)
  {
    // for arithmetic, solve the equality
    std::map< Node, Node > msum;
    if (ArithMSum::getMonomialSumLit(lit, msum))
    {
      for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
        if( !itm->first.isNull() ){
          std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), itm->first );
          if( ita!=args.end() ){
            Assert(pol);
            Node veq_c;
            Node val;
            int ires = ArithMSum::isolate(itm->first, msum, veq_c, val, EQUAL);
            if (ires != 0 && veq_c.isNull() && isVarElim(itm->first, val))
            {
              Trace("var-elim-quant")
                  << "Variable eliminate based on solved equality : "
                  << itm->first << " -> " << val << std::endl;
              vars.push_back(itm->first);
              subs.push_back(val);
              args.erase(ita);
              return true;
            }
          }
        }
      }
    }
  }
  if (lit.getKind() == EQUAL && pol)
  {
    Node var;
    Node slv;
    TypeNode tt = lit[0].getType();
    if (tt.isBitVector())
    {
      slv = getVarElimLitBv(lit, args, var);
    }
    else if (tt.isStringLike())
    {
      slv = getVarElimLitString(lit, args, var);
    }
    if (!slv.isNull())
    {
      Assert(!var.isNull());
      std::vector<Node>::iterator ita =
          std::find(args.begin(), args.end(), var);
      Assert(ita != args.end());
      Trace("var-elim-quant")
          << "Variable eliminate based on theory-specific solving : " << var
          << " -> " << slv << std::endl;
      Assert(!expr::hasSubterm(slv, var));
      Assert(slv.getType().isSubtypeOf(var.getType()));
      vars.push_back(var);
      subs.push_back(slv);
      args.erase(ita);
      return true;
    }
  }
  return false;
}

Node QuantifiersRewriter::datatypeExpand(unsigned index,
                                         Node v,
                                         std::vector<Node>& args)
{
  if (!v.getType().isDatatype())
  {
    return Node::null();
  }
  std::vector<Node>::iterator ita = std::find(args.begin(), args.end(), v);
  if (ita == args.end())
  {
    return Node::null();
  }
  const DType& dt = v.getType().getDType();
  Assert(index < dt.getNumConstructors());
  const DTypeConstructor& c = dt[index];
  std::vector<Node> newChildren;
  newChildren.push_back(c.getConstructor());
  std::vector<Node> newVars;
  for (unsigned j = 0, nargs = c.getNumArgs(); j < nargs; j++)
  {
    TypeNode tn = c.getArgType(j);
    Node vn = NodeManager::currentNM()->mkBoundVar(tn);
    newChildren.push_back(vn);
    newVars.push_back(vn);
  }
  args.erase(ita);
  args.insert(args.end(), newVars.begin(), newVars.end());
  return NodeManager::currentNM()->mkNode(APPLY_CONSTRUCTOR, newChildren);
}

bool QuantifiersRewriter::getVarElim(Node n,
                                     bool pol,
                                     std::vector<Node>& args,
                                     std::vector<Node>& vars,
                                     std::vector<Node>& subs)
{
  Kind nk = n.getKind();
  if (nk == NOT)
  {
    return getVarElim(n[0], !pol, args, vars, subs);
  }
  else if ((nk == AND && pol) || (nk == OR && !pol))
  {
    for (const Node& cn : n)
    {
      if (getVarElim(cn, pol, args, vars, subs))
      {
        return true;
      }
    }
    return false;
  }
  return getVarElimLit(n, pol, args, vars, subs);
}

bool QuantifiersRewriter::hasVarElim(Node n, bool pol, std::vector<Node>& args)
{
  std::vector< Node > vars;
  std::vector< Node > subs;
  return getVarElim(n, pol, args, vars, subs);
}

bool QuantifiersRewriter::getVarElimIneq(Node body,
                                         std::vector<Node>& args,
                                         std::vector<Node>& bounds,
                                         std::vector<Node>& subs,
                                         QAttributes& qa)
{
  // elimination based on inequalities
  std::map<Node, std::map<bool, std::map<Node, bool> > > num_bounds;
  QuantPhaseReq qpr(body);
  for (const std::pair<const Node, bool>& pr : qpr.d_phase_reqs)
  {
    // an inequality that is entailed with a given polarity
    Node lit = pr.first;
    if (lit.getKind() != GEQ)
    {
      continue;
    }
    bool pol = pr.second;
    Trace("var-elim-quant-debug") << "Process inequality bounds : " << lit
                                  << ", pol = " << pol << "..." << std::endl;
    // solve the inequality
    std::map<Node, Node> msum;
    if (!ArithMSum::getMonomialSumLit(lit, msum))
    {
      // not an inequality, cannot use
      continue;
    }
    for (const std::pair<const Node, Node>& m : msum)
    {
      if (!m.first.isNull())
      {
        std::vector<Node>::iterator ita =
            std::find(args.begin(), args.end(), m.first);
        if (ita != args.end())
        {
          // store that this literal is upper/lower bound for itm->first
          Node veq_c;
          Node val;
          int ires =
              ArithMSum::isolate(m.first, msum, veq_c, val, lit.getKind());
          if (ires != 0 && veq_c.isNull())
          {
            bool is_upper = pol != (ires == 1);
            Trace("var-elim-ineq-debug")
                << lit << " is a " << (is_upper ? "upper" : "lower")
                << " bound for " << m.first << std::endl;
            Trace("var-elim-ineq-debug")
                << "  pol/ires = " << pol << " " << ires << std::endl;
            num_bounds[m.first][is_upper][lit] = pol;
          }
          else
          {
            Trace("var-elim-ineq-debug")
                << "...ineligible " << m.first
                << " since it cannot be solved for (" << ires << ", " << veq_c
                << ")." << std::endl;
            num_bounds[m.first][true].clear();
            num_bounds[m.first][false].clear();
          }
        }
        else
        {
          // compute variables in itm->first, these are not eligible for
          // elimination
          std::unordered_set<Node, NodeHashFunction> fvs;
          expr::getFreeVariables(m.first, fvs);
          for (const Node& v : fvs)
          {
            Trace("var-elim-ineq-debug")
                << "...ineligible " << v
                << " since it is contained in monomial." << std::endl;
            num_bounds[v][true].clear();
            num_bounds[v][false].clear();
          }
        }
      }
    }
  }

  // collect all variables that have only upper/lower bounds
  std::map<Node, bool> elig_vars;
  for (const std::pair<const Node, std::map<bool, std::map<Node, bool> > >& nb :
       num_bounds)
  {
    if (nb.second.find(true) == nb.second.end())
    {
      Trace("var-elim-ineq-debug")
          << "Variable " << nb.first << " has only lower bounds." << std::endl;
      elig_vars[nb.first] = false;
    }
    else if (nb.second.find(false) == nb.second.end())
    {
      Trace("var-elim-ineq-debug")
          << "Variable " << nb.first << " has only upper bounds." << std::endl;
      elig_vars[nb.first] = true;
    }
  }
  if (elig_vars.empty())
  {
    return false;
  }
  std::vector<Node> inactive_vars;
  std::map<Node, std::map<int, bool> > visited;
  std::map<Node, int> exclude;
  for (const std::pair<Node, bool>& pr : qpr.d_phase_reqs)
  {
    if (pr.first.getKind() == GEQ)
    {
      exclude[pr.first] = pr.second ? -1 : 1;
      Trace("var-elim-ineq-debug")
          << "...exclude " << pr.first << " at polarity " << exclude[pr.first]
          << std::endl;
    }
  }
  // traverse the body, invalidate variables if they occur in places other than
  // the bounds they occur in
  std::unordered_map<TNode, std::unordered_set<int>, TNodeHashFunction>
      evisited;
  std::vector<TNode> evisit;
  std::vector<int> evisit_pol;
  TNode ecur;
  int ecur_pol;
  evisit.push_back(body);
  evisit_pol.push_back(1);
  if (!qa.d_ipl.isNull())
  {
    // do not eliminate variables that occur in the annotation
    evisit.push_back(qa.d_ipl);
    evisit_pol.push_back(0);
  }
  do
  {
    ecur = evisit.back();
    evisit.pop_back();
    ecur_pol = evisit_pol.back();
    evisit_pol.pop_back();
    std::unordered_set<int>& epp = evisited[ecur];
    if (epp.find(ecur_pol) == epp.end())
    {
      epp.insert(ecur_pol);
      if (elig_vars.find(ecur) != elig_vars.end())
      {
        // variable contained in a place apart from bounds, no longer eligible
        // for elimination
        elig_vars.erase(ecur);
        Trace("var-elim-ineq-debug") << "...found occurrence of " << ecur
                                     << ", mark ineligible" << std::endl;
      }
      else
      {
        bool rec = true;
        bool pol = ecur_pol >= 0;
        bool hasPol = ecur_pol != 0;
        if (hasPol)
        {
          std::map<Node, int>::iterator itx = exclude.find(ecur);
          if (itx != exclude.end() && itx->second == ecur_pol)
          {
            // already processed this literal as a bound
            rec = false;
          }
        }
        if (rec)
        {
          for (unsigned j = 0, size = ecur.getNumChildren(); j < size; j++)
          {
            bool newHasPol;
            bool newPol;
            QuantPhaseReq::getPolarity(ecur, j, hasPol, pol, newHasPol, newPol);
            evisit.push_back(ecur[j]);
            evisit_pol.push_back(newHasPol ? (newPol ? 1 : -1) : 0);
          }
        }
      }
    }
  } while (!evisit.empty() && !elig_vars.empty());

  bool ret = false;
  for (const std::pair<Node, bool>& ev : elig_vars)
  {
    Node v = ev.first;
    Trace("var-elim-ineq-debug")
        << v << " is eligible for elimination." << std::endl;
    // do substitution corresponding to infinite projection, all literals
    // involving unbounded variable go to true/false
    for (const std::pair<const Node, bool>& nb : num_bounds[v][elig_vars[v]])
    {
      Trace("var-elim-ineq-debug")
          << "  subs : " << nb.first << " -> " << nb.second << std::endl;
      bounds.push_back(nb.first);
      subs.push_back(NodeManager::currentNM()->mkConst(nb.second));
    }
    // eliminate from args
    std::vector<Node>::iterator ita = std::find(args.begin(), args.end(), v);
    Assert(ita != args.end());
    args.erase(ita);
    ret = true;
  }
  return ret;
}

Node QuantifiersRewriter::computeVarElimination( Node body, std::vector< Node >& args, QAttributes& qa ){
  if (!options::varElimQuant() && !options::dtVarExpandQuant()
      && !options::varIneqElimQuant())
  {
    return body;
  }
  Node prev;
  while (prev != body && !args.empty())
  {
    prev = body;

    std::vector<Node> vars;
    std::vector<Node> subs;
    // standard variable elimination
    if (options::varElimQuant())
    {
      getVarElim(body, false, args, vars, subs);
    }
    // variable elimination based on one-direction inequalities
    if (vars.empty() && options::varIneqElimQuant())
    {
      getVarElimIneq(body, args, vars, subs, qa);
    }
    // if we eliminated a variable, update body and reprocess
    if (!vars.empty())
    {
      Trace("var-elim-quant-debug")
          << "VE " << vars.size() << "/" << args.size() << std::endl;
      Assert(vars.size() == subs.size());
      // remake with eliminated nodes
      body =
          body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      body = Rewriter::rewrite(body);
      if (!qa.d_ipl.isNull())
      {
        qa.d_ipl = qa.d_ipl.substitute(
            vars.begin(), vars.end(), subs.begin(), subs.end());
      }
      Trace("var-elim-quant") << "Return " << body << std::endl;
    }
  }
  return body;
}

Node QuantifiersRewriter::computePrenex( Node body, std::vector< Node >& args, std::vector< Node >& nargs, bool pol, bool prenexAgg ){
  NodeManager* nm = NodeManager::currentNM();
  Kind k = body.getKind();
  if (k == FORALL)
  {
    if( ( pol || prenexAgg ) && ( options::prenexQuantUser() || body.getNumChildren()==2 ) ){
      std::vector< Node > terms;
      std::vector< Node > subs;
      //for doing prenexing of same-signed quantifiers
      //must rename each variable that already exists
      for (const Node& v : body[0])
      {
        terms.push_back(v);
        subs.push_back(nm->mkBoundVar(v.getType()));
      }
      if( pol ){
        args.insert( args.end(), subs.begin(), subs.end() );
      }else{
        nargs.insert( nargs.end(), subs.begin(), subs.end() );
      }
      Node newBody = body[1];
      newBody = newBody.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
      return newBody;
    }
  //must remove structure
  }
  else if (prenexAgg && k == ITE && body.getType().isBoolean())
  {
    Node nn = nm->mkNode(AND,
                         nm->mkNode(OR, body[0].notNode(), body[1]),
                         nm->mkNode(OR, body[0], body[2]));
    return computePrenex( nn, args, nargs, pol, prenexAgg );
  }
  else if (prenexAgg && k == EQUAL && body[0].getType().isBoolean())
  {
    Node nn = nm->mkNode(AND,
                         nm->mkNode(OR, body[0].notNode(), body[1]),
                         nm->mkNode(OR, body[0], body[1].notNode()));
    return computePrenex( nn, args, nargs, pol, prenexAgg );
  }else if( body.getType().isBoolean() ){
    Assert(k != EXISTS);
    bool childrenChanged = false;
    std::vector< Node > newChildren;
    for (size_t i = 0, nchild = body.getNumChildren(); i < nchild; i++)
    {
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( body, i, true, pol, newHasPol, newPol );
      if (!newHasPol)
      {
        newChildren.push_back( body[i] );
        continue;
      }
      Node n = computePrenex(body[i], args, nargs, newPol, prenexAgg);
      newChildren.push_back(n);
      childrenChanged = n != body[i] || childrenChanged;
    }
    if( childrenChanged ){
      if (k == NOT && newChildren[0].getKind() == NOT)
      {
        return newChildren[0][0];
      }
      return nm->mkNode(k, newChildren);
    }
  }
  return body;
}

Node QuantifiersRewriter::computePrenexAgg(Node n,
                                           std::map<Node, Node>& visited)
{
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv!=visited.end() ){
    return itv->second;
  }
  if (!expr::hasClosure(n))
  {
    // trivial
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node ret = n;
  if (n.getKind() == NOT)
  {
    ret = computePrenexAgg(n[0], visited).negate();
  }
  else if (n.getKind() == FORALL)
  {
    std::vector<Node> children;
    children.push_back(computePrenexAgg(n[1], visited));
    std::vector<Node> args;
    args.insert(args.end(), n[0].begin(), n[0].end());
    // for each child, strip top level quant
    for (unsigned i = 0; i < children.size(); i++)
    {
      if (children[i].getKind() == FORALL)
      {
        args.insert(args.end(), children[i][0].begin(), children[i][0].end());
        children[i] = children[i][1];
      }
    }
    // keep the pattern
    std::vector<Node> iplc;
    if (n.getNumChildren() == 3)
    {
      iplc.insert(iplc.end(), n[2].begin(), n[2].end());
    }
    Node nb = children.size() == 1 ? children[0] : nm->mkNode(OR, children);
    ret = mkForall(args, nb, iplc, true);
  }
  else
  {
    std::vector<Node> args;
    std::vector<Node> nargs;
    Node nn = computePrenex(n, args, nargs, true, true);
    if (n != nn)
    {
      Node nnn = computePrenexAgg(nn, visited);
      // merge prenex
      if (nnn.getKind() == FORALL)
      {
        args.insert(args.end(), nnn[0].begin(), nnn[0].end());
        nnn = nnn[1];
        // pos polarity variables are inner
        if (!args.empty())
        {
          nnn = mkForall(args, nnn, true);
        }
        args.clear();
      }
      else if (nnn.getKind() == NOT && nnn[0].getKind() == FORALL)
      {
        nargs.insert(nargs.end(), nnn[0][0].begin(), nnn[0][0].end());
        nnn = nnn[0][1].negate();
      }
      if (!nargs.empty())
      {
        nnn = mkForall(nargs, nnn.negate(), true).negate();
      }
      if (!args.empty())
      {
        nnn = mkForall(args, nnn, true);
      }
      ret = nnn;
    }
    else
    {
      Assert(args.empty());
      Assert(nargs.empty());
    }
  }
  visited[n] = ret;
  return ret;
}

Node QuantifiersRewriter::computeSplit( std::vector< Node >& args, Node body, QAttributes& qa ) {
  Assert(body.getKind() == OR);
  size_t var_found_count = 0;
  size_t eqc_count = 0;
  size_t eqc_active = 0;
  std::map< Node, int > var_to_eqc;
  std::map< int, std::vector< Node > > eqc_to_var;
  std::map< int, std::vector< Node > > eqc_to_lit;

  std::vector<Node> lits;

  for( unsigned i=0; i<body.getNumChildren(); i++ ){
    //get variables contained in the literal
    Node n = body[i];
    std::vector< Node > lit_args;
    computeArgVec( args, lit_args, n );
    if( lit_args.empty() ){
      lits.push_back( n );
    }else {
      //collect the equivalence classes this literal belongs to, and the new variables it contributes
      std::vector< int > eqcs;
      std::vector< Node > lit_new_args;
      //for each variable in literal
      for( unsigned j=0; j<lit_args.size(); j++) {
        //see if the variable has already been found
        if (var_to_eqc.find(lit_args[j])!=var_to_eqc.end()) {
          int eqc = var_to_eqc[lit_args[j]];
          if (std::find(eqcs.begin(), eqcs.end(), eqc)==eqcs.end()) {
            eqcs.push_back(eqc);
          }
        }else{
          var_found_count++;
          lit_new_args.push_back(lit_args[j]);
        }
      }
      if (eqcs.empty()) {
        eqcs.push_back(eqc_count);
        eqc_count++;
        eqc_active++;
      }

      int eqcz = eqcs[0];
      //merge equivalence classes with eqcz
      for (unsigned j=1; j<eqcs.size(); j++) {
        int eqc = eqcs[j];
        //move all variables from equivalence class
        for (unsigned k=0; k<eqc_to_var[eqc].size(); k++) {
          Node v = eqc_to_var[eqc][k];
          var_to_eqc[v] = eqcz;
          eqc_to_var[eqcz].push_back(v);
        }
        eqc_to_var.erase(eqc);
        //move all literals from equivalence class
        for (unsigned k=0; k<eqc_to_lit[eqc].size(); k++) {
          Node l = eqc_to_lit[eqc][k];
          eqc_to_lit[eqcz].push_back(l);
        }
        eqc_to_lit.erase(eqc);
        eqc_active--;
      }
      //add variables to equivalence class
      for (unsigned j=0; j<lit_new_args.size(); j++) {
        var_to_eqc[lit_new_args[j]] = eqcz;
        eqc_to_var[eqcz].push_back(lit_new_args[j]);
      }
      //add literal to equivalence class
      eqc_to_lit[eqcz].push_back(n);
    }
  }
  if ( eqc_active>1 || !lits.empty() || var_to_eqc.size()!=args.size() ){
    NodeManager* nm = NodeManager::currentNM();
    Trace("clause-split-debug") << "Split quantified formula with body " << body << std::endl;
    Trace("clause-split-debug") << "   Ground literals: " << std::endl;
    for( size_t i=0; i<lits.size(); i++) {
      Trace("clause-split-debug") << "      " << lits[i] << std::endl;
    }
    Trace("clause-split-debug") << std::endl;
    Trace("clause-split-debug") << "Equivalence classes: " << std::endl;
    for (std::map< int, std::vector< Node > >::iterator it = eqc_to_lit.begin(); it != eqc_to_lit.end(); ++it ){
      Trace("clause-split-debug") << "   Literals: " << std::endl;
      for (size_t i=0; i<it->second.size(); i++) {
        Trace("clause-split-debug") << "      " << it->second[i] << std::endl;
      }
      int eqc = it->first;
      Trace("clause-split-debug") << "   Variables: " << std::endl;
      for (size_t i=0; i<eqc_to_var[eqc].size(); i++) {
        Trace("clause-split-debug") << "      " << eqc_to_var[eqc][i] << std::endl;
      }
      Trace("clause-split-debug") << std::endl;
      Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, eqc_to_var[eqc]);
      Node bd =
          it->second.size() == 1 ? it->second[0] : nm->mkNode(OR, it->second);
      Node fa = nm->mkNode(FORALL, bvl, bd);
      lits.push_back(fa);
    }
    Assert(!lits.empty());
    Node nf = lits.size()==1 ? lits[0] : NodeManager::currentNM()->mkNode(OR,lits);
    Trace("clause-split-debug") << "Made node : " << nf << std::endl;
    return nf;
  }else{
    return mkForAll( args, body, qa );
  }
}

Node QuantifiersRewriter::mkForAll( std::vector< Node >& args, Node body, QAttributes& qa ){
  if( args.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
    children.push_back( body );
    if( !qa.d_ipl.isNull() ){
      children.push_back( qa.d_ipl );
    }
    return NodeManager::currentNM()->mkNode( kind::FORALL, children );
  }
}

Node QuantifiersRewriter::mkForall( std::vector< Node >& args, Node body, bool marked ) {
  std::vector< Node > iplc;
  return mkForall( args, body, iplc, marked );
}

Node QuantifiersRewriter::mkForall( std::vector< Node >& args, Node body, std::vector< Node >& iplc, bool marked ) {
  if( args.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
    children.push_back( body );
    if( marked ){
      Node avar = NodeManager::currentNM()->mkSkolem( "id", NodeManager::currentNM()->booleanType() );
      QuantIdNumAttribute ida;
      avar.setAttribute(ida,0);
      iplc.push_back( NodeManager::currentNM()->mkNode( INST_ATTRIBUTE, avar ) );
    }
    if( !iplc.empty() ){
      children.push_back( NodeManager::currentNM()->mkNode( INST_PATTERN_LIST, iplc ) );
    }
    return NodeManager::currentNM()->mkNode( FORALL, children );
  }
}

//computes miniscoping, also eliminates variables that do not occur free in body
Node QuantifiersRewriter::computeMiniscoping( std::vector< Node >& args, Node body, QAttributes& qa ){
  NodeManager* nm = NodeManager::currentNM();
  if( body.getKind()==FORALL ){
    //combine prenex
    std::vector< Node > newArgs;
    newArgs.insert( newArgs.end(), args.begin(), args.end() );
    for( unsigned i=0; i<body[0].getNumChildren(); i++ ){
      newArgs.push_back( body[0][i] );
    }
    return mkForAll( newArgs, body[1], qa );
  }else if( body.getKind()==AND ){
    // aggressive miniscoping implies that structural miniscoping should
    // be applied first
    if (options::miniscopeQuant() || options::aggressiveMiniscopeQuant())
    {
      // Break apart the quantifed formula
      // forall x. P1 ^ ... ^ Pn ---> forall x. P1 ^ ... ^ forall x. Pn
      NodeBuilder<> t(kind::AND);
      std::vector<Node> argsc;
      for (unsigned i = 0, nchild = body.getNumChildren(); i < nchild; i++)
      {
        if (argsc.empty())
        {
          // If not done so, we must create fresh copy of args. This is to
          // ensure that quantified formulas do not reuse variables.
          for (const Node& v : args)
          {
            argsc.push_back(nm->mkBoundVar(v.getType()));
          }
        }
        Node b = body[i];
        Node bodyc =
            b.substitute(args.begin(), args.end(), argsc.begin(), argsc.end());
        if (b == bodyc)
        {
          // Did not contain variables in args, thus it is ground. Since we did
          // not use them, we keep the variables argsc for the next child.
          t << b;
        }
        else
        {
          t << computeMiniscoping(argsc, bodyc, qa);
          // We used argsc, clear so we will construct a fresh copy above.
          argsc.clear();
        }
      }
      Node retVal = t;
      return retVal;
    }
  }else if( body.getKind()==OR ){
    if( options::quantSplit() ){
      //splitting subsumes free variable miniscoping, apply it with higher priority
      return computeSplit( args, body, qa );
    }
    else if (options::miniscopeQuantFreeVar()
             || options::aggressiveMiniscopeQuant())
    {
      // aggressive miniscoping implies that free variable miniscoping should
      // be applied first
      Node newBody = body;
      NodeBuilder<> body_split(kind::OR);
      NodeBuilder<> tb(kind::OR);
      for (const Node& trm : body)
      {
        if (expr::hasSubterm(trm, args))
        {
          tb << trm;
        }else{
          body_split << trm;
        }
      }
      if( tb.getNumChildren()==0 ){
        return body_split;
      }else if( body_split.getNumChildren()>0 ){
        newBody = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
        std::vector< Node > activeArgs;
        computeArgVec2( args, activeArgs, newBody, qa.d_ipl );
        body_split << mkForAll( activeArgs, newBody, qa );
        return body_split.getNumChildren()==1 ? body_split.getChild( 0 ) : body_split;
      }
    }
  }else if( body.getKind()==NOT ){
    Assert(isLiteral(body[0]));
  }
  //remove variables that don't occur
  std::vector< Node > activeArgs;
  computeArgVec2( args, activeArgs, body, qa.d_ipl );
  return mkForAll( activeArgs, body, qa );
}

Node QuantifiersRewriter::computeAggressiveMiniscoping( std::vector< Node >& args, Node body ){
  std::map<Node, std::vector<Node> > varLits;
  std::map<Node, std::vector<Node> > litVars;
  if (body.getKind() == OR) {
    Trace("ag-miniscope") << "compute aggressive miniscoping on " << body << std::endl;
    for (size_t i = 0; i < body.getNumChildren(); i++) {
      std::vector<Node> activeArgs;
      computeArgVec(args, activeArgs, body[i]);
      for (unsigned j = 0; j < activeArgs.size(); j++) {
        varLits[activeArgs[j]].push_back(body[i]);
      }
      std::vector<Node>& lit_body_i = litVars[body[i]];
      std::vector<Node>::iterator lit_body_i_begin = lit_body_i.begin();
      std::vector<Node>::const_iterator active_begin = activeArgs.begin();
      std::vector<Node>::const_iterator active_end = activeArgs.end();
      lit_body_i.insert(lit_body_i_begin, active_begin, active_end);
    }
    //find the variable in the least number of literals
    Node bestVar;
    for( std::map< Node, std::vector<Node> >::iterator it = varLits.begin(); it != varLits.end(); ++it ){
      if( bestVar.isNull() || varLits[bestVar].size()>it->second.size() ){
        bestVar = it->first;
      }
    }
    Trace("ag-miniscope-debug") << "Best variable " << bestVar << " occurs in " << varLits[bestVar].size() << "/ " << body.getNumChildren() << " literals." << std::endl;
    if( !bestVar.isNull() && varLits[bestVar].size()<body.getNumChildren() ){
      //we can miniscope
      Trace("ag-miniscope") << "Miniscope on " << bestVar << std::endl;
      //make the bodies
      std::vector<Node> qlit1;
      qlit1.insert( qlit1.begin(), varLits[bestVar].begin(), varLits[bestVar].end() );
      std::vector<Node> qlitt;
      //for all literals not containing bestVar
      for( size_t i=0; i<body.getNumChildren(); i++ ){
        if( std::find( qlit1.begin(), qlit1.end(), body[i] )==qlit1.end() ){
          qlitt.push_back( body[i] );
        }
      }
      //make the variable lists
      std::vector<Node> qvl1;
      std::vector<Node> qvl2;
      std::vector<Node> qvsh;
      for( unsigned i=0; i<args.size(); i++ ){
        bool found1 = false;
        bool found2 = false;
        for( size_t j=0; j<varLits[args[i]].size(); j++ ){
          if( !found1 && std::find( qlit1.begin(), qlit1.end(), varLits[args[i]][j] )!=qlit1.end() ){
            found1 = true;
          }else if( !found2 && std::find( qlitt.begin(), qlitt.end(), varLits[args[i]][j] )!=qlitt.end() ){
            found2 = true;
          }
          if( found1 && found2 ){
            break;
          }
        }
        if( found1 ){
          if( found2 ){
            qvsh.push_back( args[i] );
          }else{
            qvl1.push_back( args[i] );
          }
        }else{
          Assert(found2);
          qvl2.push_back( args[i] );
        }
      }
      Assert(!qvl1.empty());
      //check for literals that only contain shared variables
      std::vector<Node> qlitsh;
      std::vector<Node> qlit2;
      for( size_t i=0; i<qlitt.size(); i++ ){
        bool hasVar2 = false;
        for( size_t j=0; j<litVars[qlitt[i]].size(); j++ ){
          if( std::find( qvl2.begin(), qvl2.end(), litVars[qlitt[i]][j] )!=qvl2.end() ){
            hasVar2 = true;
            break;
          }
        }
        if( hasVar2 ){
          qlit2.push_back( qlitt[i] );
        }else{
          qlitsh.push_back( qlitt[i] );
        }
      }
      varLits.clear();
      litVars.clear();
      Trace("ag-miniscope-debug") << "Split into literals : " << qlit1.size() << " / " << qlit2.size() << " / " << qlitsh.size();
      Trace("ag-miniscope-debug") << ", variables : " << qvl1.size() << " / " << qvl2.size() << " / " << qvsh.size() << std::endl;
      Node n1 = qlit1.size()==1 ? qlit1[0] : NodeManager::currentNM()->mkNode( OR, qlit1 );
      n1 = computeAggressiveMiniscoping( qvl1, n1 );
      qlitsh.push_back( n1 );
      if( !qlit2.empty() ){
        Node n2 = qlit2.size()==1 ? qlit2[0] : NodeManager::currentNM()->mkNode( OR, qlit2 );
        n2 = computeAggressiveMiniscoping( qvl2, n2 );
        qlitsh.push_back( n2 );
      }
      Node n = NodeManager::currentNM()->mkNode( OR, qlitsh );
      if( !qvsh.empty() ){
        Node bvl = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, qvsh);
        n = NodeManager::currentNM()->mkNode( FORALL, bvl, n );
      }
      Trace("ag-miniscope") << "Return " << n << " for " << body << std::endl;
      return n;
    }
  }
  QAttributes qa;
  return mkForAll( args, body, qa );
}

bool QuantifiersRewriter::doOperation(Node q,
                                      RewriteStep computeOption,
                                      QAttributes& qa)
{
  bool is_strict_trigger =
      qa.d_hasPattern
      && options::userPatternsQuant() == options::UserPatMode::TRUST;
  bool is_std = qa.isStandard() && !is_strict_trigger;
  if (computeOption == COMPUTE_ELIM_SYMBOLS)
  {
    return true;
  }
  else if (computeOption == COMPUTE_MINISCOPING)
  {
    return is_std;
  }
  else if (computeOption == COMPUTE_AGGRESSIVE_MINISCOPING)
  {
    return options::aggressiveMiniscopeQuant() && is_std;
  }
  else if (computeOption == COMPUTE_EXT_REWRITE)
  {
    return options::extRewriteQuant();
  }
  else if (computeOption == COMPUTE_PROCESS_TERMS)
  {
    return options::elimExtArithQuant()
           || options::iteLiftQuant() != options::IteLiftQuantMode::NONE;
  }
  else if (computeOption == COMPUTE_COND_SPLIT)
  {
    return (options::iteDtTesterSplitQuant() || options::condVarSplitQuant())
           && !is_strict_trigger;
  }
  else if (computeOption == COMPUTE_PRENEX)
  {
    return options::prenexQuant() != options::PrenexQuantMode::NONE
           && !options::aggressiveMiniscopeQuant() && is_std;
  }
  else if (computeOption == COMPUTE_VAR_ELIMINATION)
  {
    return (options::varElimQuant() || options::dtVarExpandQuant()) && is_std;
  }
  else
  {
    return false;
  }
}

//general method for computing various rewrites
Node QuantifiersRewriter::computeOperation(Node f,
                                           RewriteStep computeOption,
                                           QAttributes& qa)
{
  Trace("quantifiers-rewrite-debug") << "Compute operation " << computeOption << " on " << f << " " << qa.d_qid_num << std::endl;
  std::vector< Node > args;
  for( unsigned i=0; i<f[0].getNumChildren(); i++ ){
    args.push_back( f[0][i] );
  }
  Node n = f[1];
  if( computeOption==COMPUTE_ELIM_SYMBOLS ){
    n = computeElimSymbols( n );
  }else if( computeOption==COMPUTE_MINISCOPING ){
    if (options::prenexQuant() == options::PrenexQuantMode::NORMAL)
    {
      if( !qa.d_qid_num.isNull() ){
        //already processed this, return self
        return f;
      }
    }
    //return directly
    return computeMiniscoping( args, n, qa );
  }else if( computeOption==COMPUTE_AGGRESSIVE_MINISCOPING ){
    return computeAggressiveMiniscoping( args, n );
  }
  else if (computeOption == COMPUTE_EXT_REWRITE)
  {
    return computeExtendedRewrite(f);
  }
  else if (computeOption == COMPUTE_PROCESS_TERMS)
  {
    std::vector< Node > new_conds;
    n = computeProcessTerms( n, args, new_conds, f, qa );
    if( !new_conds.empty() ){
      new_conds.push_back( n );
      n = NodeManager::currentNM()->mkNode( OR, new_conds );
    }
  }
  else if (computeOption == COMPUTE_COND_SPLIT)
  {
    n = computeCondSplit(n, args, qa);
  }
  else if (computeOption == COMPUTE_PRENEX)
  {
    if (options::prenexQuant() == options::PrenexQuantMode::NORMAL)
    {
      //will rewrite at preprocess time
      return f;
    }
    else
    {
      std::vector< Node > nargs;
      n = computePrenex( n, args, nargs, true, false );
      Assert(nargs.empty());
    }
  }
  else if (computeOption == COMPUTE_VAR_ELIMINATION)
  {
    n = computeVarElimination( n, args, qa );
  }
  Trace("quantifiers-rewrite-debug") << "Compute Operation: return " << n << ", " << args.size() << std::endl;
  if( f[1]==n && args.size()==f[0].getNumChildren() ){
    return f;
  }else{
    if( args.empty() ){
      return n;
    }else{
      std::vector< Node > children;
      children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
      children.push_back( n );
      if( !qa.d_ipl.isNull() && args.size()==f[0].getNumChildren() ){
        children.push_back( qa.d_ipl );
      }
      return NodeManager::currentNM()->mkNode(kind::FORALL, children );
    }
  }
}

bool QuantifiersRewriter::isPrenexNormalForm( Node n ) {
  if( n.getKind()==FORALL ){
    return n[1].getKind()!=FORALL && isPrenexNormalForm( n[1] );
  }else if( n.getKind()==NOT ){
    return n[0].getKind()!=NOT && isPrenexNormalForm( n[0] );
  }else{
    return !expr::hasClosure(n);
  }
}

Node QuantifiersRewriter::preSkolemizeQuantifiers( Node n, bool polarity, std::vector< TypeNode >& fvTypes, std::vector< TNode >& fvs ){
  Trace("pre-sk") << "Pre-skolem " << n << " " << polarity << " " << fvs.size() << endl;
  if( n.getKind()==kind::NOT ){
    Node nn = preSkolemizeQuantifiers( n[0], !polarity, fvTypes, fvs );
    return nn.negate();
  }else if( n.getKind()==kind::FORALL ){
    if (n.getNumChildren() == 3)
    {
      // Do not pre-skolemize quantified formulas with three children.
      // This includes non-standard quantified formulas
      // like recursive function definitions, or sygus conjectures, and
      // quantified formulas with triggers.
      return n;
    }
    else if (polarity)
    {
      if( options::preSkolemQuant() && options::preSkolemQuantNested() ){
        vector< Node > children;
        children.push_back( n[0] );
        //add children to current scope
        std::vector< TypeNode > fvt;
        std::vector< TNode > fvss;
        fvt.insert( fvt.begin(), fvTypes.begin(), fvTypes.end() );
        fvss.insert( fvss.begin(), fvs.begin(), fvs.end() );
        for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
          fvt.push_back( n[0][i].getType() );
          fvss.push_back( n[0][i] );
        }
        //process body
        children.push_back( preSkolemizeQuantifiers( n[1], polarity, fvt, fvss ) );
        //return processed quantifier
        return NodeManager::currentNM()->mkNode( kind::FORALL, children );
      }
    }else{
      //process body
      Node nn = preSkolemizeQuantifiers( n[1], polarity, fvTypes, fvs );
      std::vector< Node > sk;
      Node sub;
      std::vector< unsigned > sub_vars;
      //return skolemized body
      return Skolemize::mkSkolemizedBody(
          n, nn, fvTypes, fvs, sk, sub, sub_vars);
    }
  }else{
    //check if it contains a quantifier as a subterm
    //if so, we will write this node
    if (expr::hasClosure(n))
    {
      if( ( n.getKind()==kind::ITE && n.getType().isBoolean() ) || ( n.getKind()==kind::EQUAL && n[0].getType().isBoolean() ) ){
        if( options::preSkolemQuantAgg() ){
          Node nn;
          //must remove structure
          if( n.getKind()==kind::ITE ){
            nn = NodeManager::currentNM()->mkNode( kind::AND,
                  NodeManager::currentNM()->mkNode( kind::OR, n[0].notNode(), n[1] ),
                  NodeManager::currentNM()->mkNode( kind::OR, n[0], n[2] ) );
          }else if( n.getKind()==kind::EQUAL ){
            nn = NodeManager::currentNM()->mkNode( kind::AND,
                  NodeManager::currentNM()->mkNode( kind::OR, n[0].notNode(), n.getKind()==kind::XOR ? n[1].notNode() : n[1] ),
                  NodeManager::currentNM()->mkNode( kind::OR, n[0], n.getKind()==kind::XOR ? n[1] : n[1].notNode() ) );
          }
          return preSkolemizeQuantifiers( nn, polarity, fvTypes, fvs );
        }
      }else if( n.getKind()==kind::AND || n.getKind()==kind::OR ){
        vector< Node > children;
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          children.push_back( preSkolemizeQuantifiers( n[i], polarity, fvTypes, fvs ) );
        }
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
  }
  return n;
}

TrustNode QuantifiersRewriter::preprocess(Node n, bool isInst)
{
  Node prev = n;

  if( options::preSkolemQuant() ){
    if( !isInst || !options::preSkolemQuantNested() ){
      Trace("quantifiers-preprocess-debug") << "Pre-skolemize " << n << "..." << std::endl;
      //apply pre-skolemization to existential quantifiers
      std::vector< TypeNode > fvTypes;
      std::vector< TNode > fvs;
      n = preSkolemizeQuantifiers( prev, true, fvTypes, fvs );
    }
  }
  //pull all quantifiers globally
  if (options::prenexQuant() == options::PrenexQuantMode::NORMAL)
  {
    Trace("quantifiers-prenex") << "Prenexing : " << n << std::endl;
    std::map<Node, Node> visited;
    n = computePrenexAgg(n, visited);
    n = Rewriter::rewrite( n );
    Trace("quantifiers-prenex") << "Prenexing returned : " << n << std::endl;
    //Assert( isPrenexNormalForm( n ) );
  }
  if( n!=prev ){       
    Trace("quantifiers-preprocess") << "Preprocess " << prev << std::endl;
    Trace("quantifiers-preprocess") << "..returned " << n << std::endl;
    return TrustNode::mkTrustRewrite(prev, n, nullptr);
  }
  return TrustNode::null();
}

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
