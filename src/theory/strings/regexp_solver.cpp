/*********************                                                        */
/*! \file regexp_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the regular expression solver for the theory of strings.
 **/

#include "theory/strings/regexp_solver.h"

#include <cmath>

#include "options/strings_options.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/theory_strings.h"
#include "theory/theory_model.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

RegExpSolver::RegExpSolver(TheoryStrings& p, context::Context* c,
                             context::UserContext* u)
    : d_parent(p),
      d_regexp_memberships(c),
      d_regexp_ucached(u),
      d_regexp_ccached(c),
      d_pos_memberships(c),
      d_neg_memberships(c),
      d_inter_cache(c),
      d_inter_index(c),
      d_processed_memberships(c),
      d_regexp_ant(c)
{
  d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
  std::vector< Node > nvec;
  d_emptyRegexp = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false ); 
}

unsigned RegExpSolver::getNumMemberships( Node n, bool isPos ) {
  if( isPos ){
    NodeIntMap::const_iterator it = d_pos_memberships.find( n );
    if( it!=d_pos_memberships.end() ){
      return (*it).second;
    }
  }else{
    NodeIntMap::const_iterator it = d_neg_memberships.find( n );
    if( it!=d_neg_memberships.end() ){
      return (*it).second;
    }
  }
  return 0;
}

Node RegExpSolver::getMembership( Node n, bool isPos, unsigned i ) {
  return isPos ? d_pos_memberships_data[n][i] : d_neg_memberships_data[n][i];
}

Node RegExpSolver::mkRegExpAntec(Node atom, Node ant) {
  if(d_regexp_ant.find(atom) == d_regexp_ant.end()) {
    return NodeManager::currentNM()->mkNode(kind::AND, ant, atom);
  } else {
    Node n = d_regexp_ant[atom];
    return NodeManager::currentNM()->mkNode(kind::AND, ant, n);
  }
}

void RegExpSolver::check() {
  bool addedLemma = false;
  bool changed = false;
  std::vector< Node > processed;
  std::vector< Node > cprocessed;

  Trace("regexp-debug") << "Checking Memberships ... " << std::endl;
  //TODO: Opt for normal forms
  for( NodeIntMap::const_iterator itr_xr = d_pos_memberships.begin(); itr_xr != d_pos_memberships.end(); ++itr_xr ){
    bool spflag = false;
    Node x = (*itr_xr).first;
    Trace("regexp-debug") << "Checking Memberships for " << x << std::endl;
    if(d_inter_index.find(x) == d_inter_index.end()) {
      d_inter_index[x] = 0;
    }
    int cur_inter_idx = d_inter_index[x];
    unsigned n_pmem = (*itr_xr).second;
    Assert( getNumMemberships( x, true )==n_pmem );
    if( cur_inter_idx != (int)n_pmem ) {
      if( n_pmem == 1) {
        d_inter_cache[x] = getMembership( x, true, 0 );
        d_inter_index[x] = 1;
        Trace("regexp-debug") << "... only one choice " << std::endl;
      } else if(n_pmem > 1) {
        Node r;
        if(d_inter_cache.find(x) != d_inter_cache.end()) {
          r = d_inter_cache[x];
        }
        if(r.isNull()) {
          r = getMembership( x, true, 0 );
          cur_inter_idx = 1;
        }

        unsigned k_start = cur_inter_idx;
        Trace("regexp-debug") << "... staring from : " << cur_inter_idx << ", we have " << n_pmem << std::endl;
        for(unsigned k = k_start; k<n_pmem; k++) {
          Node r2 = getMembership( x, true, k );
          r = d_regexp_opr.intersect(r, r2, spflag);
          if(spflag) {
            break;
          } else if(r == d_emptyRegexp) {
            std::vector< Node > vec_nodes;
            for( unsigned kk=0; kk<=k; kk++ ){
              Node rr = getMembership( x, true, kk );
              Node n = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, x, rr);
              vec_nodes.push_back( n );
            }
            Node conc;
            d_parent.sendInference(vec_nodes, conc, "INTERSECT CONFLICT", true);
            addedLemma = true;
            break;
          }
          if(d_parent.inConflict()) {
            break;
          }
        }
        //updates
        if(!d_parent.inConflict() && !spflag) {
          d_inter_cache[x] = r;
          d_inter_index[x] = (int)n_pmem;
        }
      }
    }
  }

  Trace("regexp-debug") << "... No Intersect Conflict in Memberships, addedLemma: " << addedLemma << std::endl;
  if(!addedLemma) {
    NodeManager* nm = NodeManager::currentNM();
    for( unsigned i=0; i<d_regexp_memberships.size(); i++ ) {
      //check regular expression membership
      Node assertion = d_regexp_memberships[i];
      Trace("regexp-debug") << "Check : " << assertion << " " << (d_regexp_ucached.find(assertion) == d_regexp_ucached.end()) << " " << (d_regexp_ccached.find(assertion) == d_regexp_ccached.end()) << std::endl;
      if( d_regexp_ucached.find(assertion) == d_regexp_ucached.end()
        && d_regexp_ccached.find(assertion) == d_regexp_ccached.end() ) {
        Trace("strings-regexp") << "We have regular expression assertion : " << assertion << std::endl;
        Node atom = assertion.getKind()==kind::NOT ? assertion[0] : assertion;
        bool polarity = assertion.getKind()!=kind::NOT;
        bool flag = true;
        Node x = atom[0];
        Node r = atom[1];
        std::vector< Node > rnfexp;

        if (!x.isConst())
        {
          x = d_parent.getNormalString(x, rnfexp);
          changed = true;
        }
        if (!d_regexp_opr.checkConstRegExp(r))
        {
          r = getNormalSymRegExp(r, rnfexp);
          changed = true;
        }
        Trace("strings-regexp-nf") << "Term " << atom << " is normalized to "
                                   << x << " IN " << r << std::endl;
        if (changed)
        {
          Node tmp =
              Rewriter::rewrite(nm->mkNode(kind::STRING_IN_REGEXP, x, r));
          if (!polarity)
          {
            tmp = tmp.negate();
          }
          if (tmp == d_true)
          {
            d_regexp_ccached.insert(assertion);
            continue;
          }
          else if (tmp == d_false)
          {
            Node antec = mkRegExpAntec(assertion, d_parent.mkExplain(rnfexp));
            Node conc = Node::null();
            d_parent.sendLemma(antec, conc, "REGEXP NF Conflict");
            addedLemma = true;
            break;
          }
        }

        if( polarity ) {
          flag = checkPDerivative(x, r, atom, addedLemma, rnfexp);
        } else {
          if(! options::stringExp()) {
            throw LogicException("Strings Incomplete (due to Negative Membership) by default, try --strings-exp option.");
          }
        }
        if(flag) {
          //check if the term is atomic
          Node xr = d_parent.getRepresentative( x );
          //Trace("strings-regexp") << xr << " is rep of " << x << std::endl;
          //Assert( d_normal_forms.find( xr )!=d_normal_forms.end() );
          Trace("strings-regexp")
              << "Unroll/simplify membership of atomic term " << xr
              << std::endl;
          // if so, do simple unrolling
          std::vector<Node> nvec;

          if (nvec.empty())
          {
            d_regexp_opr.simplify(atom, nvec, polarity);
          }
          Node antec = assertion;
          if (d_regexp_ant.find(assertion) != d_regexp_ant.end())
          {
            antec = d_regexp_ant[assertion];
            for (std::vector<Node>::const_iterator itr = nvec.begin();
                 itr < nvec.end();
                 itr++)
            {
              if (itr->getKind() == kind::STRING_IN_REGEXP)
              {
                if (d_regexp_ant.find(*itr) == d_regexp_ant.end())
                {
                  d_regexp_ant[*itr] = antec;
                }
              }
            }
          }
          antec = NodeManager::currentNM()->mkNode(
              kind::AND, antec, d_parent.mkExplain(rnfexp));
          Node conc = nvec.size() == 1
                          ? nvec[0]
                          : NodeManager::currentNM()->mkNode(kind::AND, nvec);
          conc = Rewriter::rewrite(conc);
          d_parent.sendLemma(antec, conc, "REGEXP_Unfold");
          addedLemma = true;
          if (changed)
          {
            cprocessed.push_back(assertion);
          }
          else
          {
            processed.push_back(assertion);
          }
          // d_regexp_ucached[assertion] = true;
        }
      }
      if(d_parent.inConflict()) {
        break;
      }
    }
  }
  if( addedLemma ) {
    if( !d_parent.inConflict() ){
      for( unsigned i=0; i<processed.size(); i++ ) {
        Trace("strings-regexp") << "...add " << processed[i] << " to u-cache." << std::endl;
        d_regexp_ucached.insert(processed[i]);
      }
      for( unsigned i=0; i<cprocessed.size(); i++ ) {
        Trace("strings-regexp") << "...add " << cprocessed[i] << " to c-cache." << std::endl;
        d_regexp_ccached.insert(cprocessed[i]);
      }
    }
  }
}

bool RegExpSolver::checkPDerivative( Node x, Node r, Node atom, bool &addedLemma, std::vector< Node > &nf_exp ) {
  
  Node antnf = d_parent.mkExplain(nf_exp);

  if(d_parent.areEqual(x, d_emptyString)) {
    Node exp;
    switch(d_regexp_opr.delta(r, exp)) {
      case 0: {
        Node antec = mkRegExpAntec(atom, x.eqNode(d_emptyString));
        antec = NodeManager::currentNM()->mkNode(kind::AND, antec, antnf);
        d_parent.sendLemma(antec, exp, "RegExp Delta");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
      case 1: {
        d_regexp_ccached.insert(atom);
        break;
      }
      case 2: {
        Node antec = mkRegExpAntec(atom, x.eqNode(d_emptyString));
        antec = NodeManager::currentNM()->mkNode(kind::AND, antec, antnf);
        Node conc = Node::null();
        d_parent.sendLemma(antec, conc, "RegExp Delta CONFLICT");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
      default:
        //Impossible
        break;
    }
  } else {
    /*Node xr = getRepresentative( x );
    if(x != xr) {
      Node n = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, xr, r);
      Node nn = Rewriter::rewrite( n );
      if(nn == d_true) {
        d_regexp_ccached.insert(atom);
        return false;
      } else if(nn == d_false) {
        Node antec = mkRegExpAntec(atom, x.eqNode(xr));
        Node conc = Node::null();
        sendLemma(antec, conc, "RegExp Delta CONFLICT");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
    }*/
    Node sREant = mkRegExpAntec(atom, d_true);
    sREant = NodeManager::currentNM()->mkNode(kind::AND, sREant, antnf);
    if(deriveRegExp( x, r, sREant )) {
      addedLemma = true;
      d_regexp_ccached.insert(atom);
      return false;
    }
  }
  return true;
}

CVC4::String RegExpSolver::getHeadConst( Node x ) {
  if( x.isConst() ) {
    return x.getConst< String >();
  } else if( x.getKind() == kind::STRING_CONCAT ) {
    if( x[0].isConst() ) {
      return x[0].getConst< String >();
    } else {
      return d_emptyString.getConst< String >();
    }
  } else {
    return d_emptyString.getConst< String >();
  }
}

bool RegExpSolver::deriveRegExp( Node x, Node r, Node ant ) {
  // TODO cstr in vre
  Assert(x != d_emptyString);
  Trace("regexp-derive") << "RegExpSolver::deriveRegExp: x=" << x << ", r= " << r << std::endl;
  //if(x.isConst()) {
  //  Node n = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r );
  //  Node r = Rewriter::rewrite( n );
  //  if(n != r) {
  //    sendLemma(ant, r, "REGEXP REWRITE");
  //    return true;
  //  }
  //}
  CVC4::String s = getHeadConst( x );
  if( !s.isEmptyString() && d_regexp_opr.checkConstRegExp( r ) ) {
    Node conc = Node::null();
    Node dc = r;
    bool flag = true;
    for(unsigned i=0; i<s.size(); ++i) {
      CVC4::String c = s.substr(i, 1);
      Node dc2;
      int rt = d_regexp_opr.derivativeS(dc, c, dc2);
      dc = dc2;
      if(rt == 0) {
        //TODO
      } else if(rt == 2) {
        // CONFLICT
        flag = false;
        break;
      }
    }
    // send lemma
    if(flag) {
      if(x.isConst()) {
        Assert(false, "Impossible: RegExpSolver::deriveRegExp: const string in const regular expression.");
        return false;
      } else {
        Assert( x.getKind() == kind::STRING_CONCAT );
        std::vector< Node > vec_nodes;
        for(unsigned int i=1; i<x.getNumChildren(); ++i ) {
          vec_nodes.push_back( x[i] );
        }
        Node left =  TheoryStringsRewriter::mkConcat( STRING_CONCAT, vec_nodes );
        left = Rewriter::rewrite( left );
        conc = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, left, dc );

        /*std::vector< Node > sdc;
        d_regexp_opr.simplify(conc, sdc, true);
        if(sdc.size() == 1) {
          conc = sdc[0];
        } else {
          conc = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, conc));
        }*/
      }
    }
    d_parent.sendLemma(ant, conc, "RegExp-Derive");
    return true;
  } else {
    return false;
  }
}

void RegExpSolver::addMembership(Node assertion) {
  bool polarity = assertion.getKind() != kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Node x = atom[0];
  Node r = atom[1];
  if(polarity) {
    int index = 0;
    NodeIntMap::const_iterator it = d_pos_memberships.find( x );
    if( it!=d_pos_memberships.end() ){
      index = (*it).second;
      for( int k=0; k<index; k++ ){
        if( k<(int)d_pos_memberships_data[x].size() ){
          if( d_pos_memberships_data[x][k]==r ){
            return;
          }
        }else{
          break;
        }
      }
    }
    d_pos_memberships[x] = index + 1;
    if( index<(int)d_pos_memberships_data[x].size() ){
      d_pos_memberships_data[x][index] = r;
    }else{
      d_pos_memberships_data[x].push_back( r );
    }
  } else if(!options::stringIgnNegMembership()) {
    /*if(options::stringEIT() && d_regexp_opr.checkConstRegExp(r)) {
      int rt;
      Node r2 = d_regexp_opr.complement(r, rt);
      Node a = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, x, r2);
    }*/
    int index = 0;
    NodeIntMap::const_iterator it = d_neg_memberships.find( x );
    if( it!=d_neg_memberships.end() ){
      index = (*it).second;
      for( int k=0; k<index; k++ ){
        if( k<(int)d_neg_memberships_data[x].size() ){
          if( d_neg_memberships_data[x][k]==r ){
            return;
          }
        }else{
          break;
        }
      }
    }
    d_neg_memberships[x] = index + 1;
    if( index<(int)d_neg_memberships_data[x].size() ){
      d_neg_memberships_data[x][index] = r;
    }else{
      d_neg_memberships_data[x].push_back( r );
    }
  }
  // old
  if(polarity || !options::stringIgnNegMembership()) {
    d_regexp_memberships.push_back( assertion );
  }
}

Node RegExpSolver::getNormalSymRegExp(Node r, std::vector<Node> &nf_exp) {
  Node ret = r;
  switch( r.getKind() ) {
    case kind::REGEXP_EMPTY:
    case kind::REGEXP_SIGMA:
      break;
    case kind::STRING_TO_REGEXP: {
      if(!r[0].isConst()) {
        Node tmp = d_parent.getNormalString( r[0], nf_exp );
        if(tmp != r[0]) {
          ret = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, tmp);
        }
      }
      break;
    }
    case kind::REGEXP_CONCAT:
    case kind::REGEXP_UNION:
    case kind::REGEXP_INTER:
    case kind::REGEXP_STAR:
    {
      std::vector< Node > vec_nodes;
      for (const Node& cr : r)
      {
        vec_nodes.push_back(getNormalSymRegExp(cr, nf_exp));
      }
      ret = Rewriter::rewrite(
          NodeManager::currentNM()->mkNode(r.getKind(), vec_nodes));
      break;
    }
    //case kind::REGEXP_PLUS:
    //case kind::REGEXP_OPT:
    //case kind::REGEXP_RANGE:
    default: {
      Trace("strings-error") << "Unsupported term: " << r << " in normalization SymRegExp." << std::endl;
      Assert( false );
      //return Node::null();
    }
  }
  return ret;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
