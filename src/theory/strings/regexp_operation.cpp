/*********************                                                        */
/*! \file regexp_operation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symbolic Regular Expresion Operations
 **
 ** Symbolic Regular Expresion Operations
 **/

#include "theory/strings/regexp_operation.h"

#include "expr/kind.h"
#include "options/strings_options.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/theory_strings_utils.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

RegExpOpr::RegExpOpr()
    : d_emptyString(NodeManager::currentNM()->mkConst(::CVC4::String(""))),
      d_true(NodeManager::currentNM()->mkConst(true)),
      d_false(NodeManager::currentNM()->mkConst(false)),
      d_emptySingleton(NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP,
                                                        d_emptyString)),
      d_emptyRegexp(NodeManager::currentNM()->mkNode(kind::REGEXP_EMPTY,
                                                     std::vector<Node>{})),
      d_zero(NodeManager::currentNM()->mkConst(::CVC4::Rational(0))),
      d_one(NodeManager::currentNM()->mkConst(::CVC4::Rational(1))),
      d_sigma(NodeManager::currentNM()->mkNode(kind::REGEXP_SIGMA,
                                               std::vector<Node>{})),
      d_sigma_star(NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, d_sigma))
{
  d_lastchar = utils::getAlphabetCardinality() - 1;
}

RegExpOpr::~RegExpOpr() {}

bool RegExpOpr::checkConstRegExp( Node r ) {
  Assert(r.getType().isRegExp());
  Trace("strings-regexp-cstre")
      << "RegExpOpr::checkConstRegExp /" << mkString(r) << "/" << std::endl;
  RegExpConstType rct = getRegExpConstType(r);
  return rct != RE_C_VARIABLE;
}

RegExpConstType RegExpOpr::getRegExpConstType(Node r)
{
  Assert(r.getType().isRegExp());
  std::unordered_map<Node, RegExpConstType, NodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(r);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_constCache.find(cur);

    Kind ck = cur.getKind();
    if (it == d_constCache.end())
    {
      if (ck == STRING_TO_REGEXP)
      {
        Node tmp = Rewriter::rewrite(cur[0]);
        d_constCache[cur] =
            tmp.isConst() ? RE_C_CONRETE_CONSTANT : RE_C_VARIABLE;
      }
      else if (ck == REGEXP_SIGMA || ck == REGEXP_RANGE)
      {
        d_constCache[cur] = RE_C_CONSTANT;
      }
      else if (!isRegExpKind(ck))
      {
        // non-regular expression applications, e.g. function applications
        // with regular expression return type are treated as variables.
        d_constCache[cur] = RE_C_VARIABLE;
      }
      else
      {
        d_constCache[cur] = RE_C_UNKNOWN;
        visit.push_back(cur);
        if (ck == REGEXP_LOOP)
        {
          // only add the first child of loop
          visit.push_back(cur[0]);
        }
        else
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      }
    }
    else if (it->second == RE_C_UNKNOWN)
    {
      RegExpConstType ret = ck == REGEXP_COMPLEMENT ? RE_C_CONSTANT : RE_C_CONRETE_CONSTANT;
      for (const Node& cn : cur)
      {
        it = d_constCache.find(cn);
        Assert(it != d_constCache.end());
        if (it->second > ret)
        {
          ret = it->second;
        }
      }
      d_constCache[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_constCache.find(r) != d_constCache.end());
  return d_constCache[r];
}

bool RegExpOpr::isRegExpKind(Kind k)
{
  return k == REGEXP_EMPTY || k == REGEXP_SIGMA || k == STRING_TO_REGEXP
         || k == REGEXP_CONCAT || k == REGEXP_UNION || k == REGEXP_INTER
         || k == REGEXP_STAR || k == REGEXP_PLUS || k == REGEXP_OPT
         || k == REGEXP_RANGE || k == REGEXP_LOOP || k == REGEXP_RV
         || k == REGEXP_COMPLEMENT;
}

// 0-unknown, 1-yes, 2-no
int RegExpOpr::delta( Node r, Node &exp ) {
  Trace("regexp-delta") << "RegExp-Delta starts with /" << mkString( r ) << "/" << std::endl;
  int ret = 0;
  if( d_delta_cache.find( r ) != d_delta_cache.end() ) {
    ret = d_delta_cache[r].first;
    exp = d_delta_cache[r].second;
  } else {
    Kind k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        ret = 2;
        break;
      }
      case kind::REGEXP_SIGMA: {
        ret = 2;
        break;
      }
      case kind::STRING_TO_REGEXP: {
        Node tmp = Rewriter::rewrite(r[0]);
        if(tmp.isConst()) {
          if(tmp == d_emptyString) {
            ret = 1;
          } else {
            ret = 2;
          }
        } else {
          ret = 0;
          if(tmp.getKind() == kind::STRING_CONCAT) {
            for(unsigned i=0; i<tmp.getNumChildren(); i++) {
              if(tmp[i].isConst()) {
                ret = 2; break;
              }
            }

          }
          if(ret == 0) {
            exp = r[0].eqNode(d_emptyString);
          }
        }
        break;
      }
      case kind::REGEXP_CONCAT: {
        bool flag = false;
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node exp2;
          int tmp = delta( r[i], exp2 );
          if(tmp == 2) {
            ret = 2;
            break;
          } else if(tmp == 0) {
            vec_nodes.push_back( exp2 );
            flag = true;
          }
        }
        if(ret != 2) {
          if(!flag) {
            ret = 1;
          } else {
            exp = vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode(kind::AND, vec_nodes);
          }
        }
        break;
      }
      case kind::REGEXP_UNION: {
        bool flag = false;
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node exp2;
          int tmp = delta( r[i], exp2 );
          if(tmp == 1) {
            ret = 1;
            break;
          } else if(tmp == 0) {
            vec_nodes.push_back( exp2 );
            flag = true;
          }
        }
        if(ret != 1) {
          if(!flag) {
            ret = 2;
          } else {
            exp = vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode(kind::OR, vec_nodes);
          }
        }
        break;
      }
      case kind::REGEXP_INTER: {
        bool flag = false;
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node exp2;
          int tmp = delta( r[i], exp2 );
          if(tmp == 2) {
            ret = 2;
            break;
          } else if(tmp == 0) {
            vec_nodes.push_back( exp2 );
            flag = true;
          }
        }
        if(ret != 2) {
          if(!flag) {
            ret = 1;
          } else {
            exp = vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode(kind::AND, vec_nodes);
          }
        }
        break;
      }
      case kind::REGEXP_STAR: {
        ret = 1;
        break;
      }
      case kind::REGEXP_PLUS: {
        ret = delta( r[0], exp );
        break;
      }
      case kind::REGEXP_OPT: {
        ret = 1;
        break;
      }
      case kind::REGEXP_RANGE: {
        ret = 2;
        break;
      }
      case kind::REGEXP_LOOP: {
        if(r[1] == d_zero) {
          ret = 1;
        } else {
          ret = delta(r[0], exp);
        }
        break;
      }
      case kind::REGEXP_COMPLEMENT:
      {
        int tmp = delta(r[0], exp);
        // flip the result if known
        tmp = tmp == 0 ? 0 : (3 - tmp);
        exp = exp.isNull() ? exp : exp.negate();
        break;
      }
      default: {
        Assert(!isRegExpKind(k));
        break;
      }
    }
    if(!exp.isNull()) {
      exp = Rewriter::rewrite(exp);
    }
    std::pair< int, Node > p(ret, exp);
    d_delta_cache[r] = p;
  }
  Trace("regexp-delta") << "RegExp-Delta returns : " << ret << std::endl;
  return ret;
}

// 0-unknown, 1-yes, 2-no
int RegExpOpr::derivativeS( Node r, CVC4::String c, Node &retNode ) {
  Assert(c.size() < 2);
  Trace("regexp-derive") << "RegExp-derive starts with /" << mkString( r ) << "/, c=" << c << std::endl;

  int ret = 1;
  retNode = d_emptyRegexp;

  PairNodeStr dv = std::make_pair( r, c );
  if( d_deriv_cache.find( dv ) != d_deriv_cache.end() ) {
    retNode = d_deriv_cache[dv].first;
    ret = d_deriv_cache[dv].second;
  } else if( c.isEmptyString() ) {
    Node expNode;
    ret = delta( r, expNode );
    if(ret == 0) {
      retNode = NodeManager::currentNM()->mkNode(kind::ITE, expNode, r, d_emptyRegexp);
    } else if(ret == 1) {
      retNode = r;
    }
    std::pair< Node, int > p(retNode, ret);
    d_deriv_cache[dv] = p;
  } else {
    switch( r.getKind() ) {
      case kind::REGEXP_EMPTY: {
        ret = 2;
        break;
      }
      case kind::REGEXP_SIGMA: {
        retNode = d_emptySingleton;
        break;
      }
      case kind::REGEXP_RANGE: {
        CVC4::String a = r[0].getConst<String>();
        CVC4::String b = r[1].getConst<String>();
        retNode = (a <= c && c <= b) ? d_emptySingleton : d_emptyRegexp;
        break;
      }
      case kind::STRING_TO_REGEXP: {
        Node tmp = Rewriter::rewrite(r[0]);
        if(tmp.isConst()) {
          if(tmp == d_emptyString) {
            ret = 2;
          } else {
            if (tmp.getConst<CVC4::String>().front() == c.front())
            {
              retNode =  NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP,
                tmp.getConst< CVC4::String >().size() == 1 ? d_emptyString : NodeManager::currentNM()->mkConst( tmp.getConst< CVC4::String >().substr(1) ) );
            } else {
              ret = 2;
            }
          }
        } else {
          ret = 0;
          Node rest;
          if(tmp.getKind() == kind::STRING_CONCAT) {
            Node t2 = tmp[0];
            if(t2.isConst()) {
              if (t2.getConst<CVC4::String>().front() == c.front())
              {
                Node n =  NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP,
                  tmp.getConst< CVC4::String >().size() == 1 ? d_emptyString : NodeManager::currentNM()->mkConst( tmp.getConst< CVC4::String >().substr(1) ) );
                std::vector< Node > vec_nodes;
                vec_nodes.push_back(n);
                for(unsigned i=1; i<tmp.getNumChildren(); i++) {
                  vec_nodes.push_back(tmp[i]);
                }
                retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes);
                ret = 1;
              } else {
                ret = 2;
              }
            } else {
              tmp = tmp[0];
              std::vector< Node > vec_nodes;
              for(unsigned i=1; i<tmp.getNumChildren(); i++) {
                vec_nodes.push_back(tmp[i]);
              }
              rest = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes);
            }
          }
          if(ret == 0) {
            Node sk = NodeManager::currentNM()->mkSkolem( "rsp", NodeManager::currentNM()->stringType(), "Split RegExp" );
            retNode = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, sk);
            if(!rest.isNull()) {
              retNode = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, retNode, rest));
            }
            Node exp = tmp.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT,
                        NodeManager::currentNM()->mkConst(c), sk));
            retNode = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::ITE, exp, retNode, d_emptyRegexp));
          }
        }
        break;
      }
      case kind::REGEXP_CONCAT: {
        std::vector< Node > vec_nodes;
        std::vector< Node > delta_nodes;
        Node dnode = d_true;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node dc;
          Node exp2;
          int rt = derivativeS(r[i], c, dc);
          if(rt != 2) {
            if(rt == 0) {
              ret = 0;
            }
            std::vector< Node > vec_nodes2;
            if(dc != d_emptySingleton) {
              vec_nodes2.push_back( dc );
            }
            for(unsigned j=i+1; j<r.getNumChildren(); ++j) {
              if(r[j] != d_emptySingleton) {
                vec_nodes2.push_back( r[j] );
              }
            }
            Node tmp = vec_nodes2.size()==0 ? d_emptySingleton :
              vec_nodes2.size()==1 ? vec_nodes2[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, vec_nodes2 );
            if(dnode != d_true) {
              tmp = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::ITE, dnode, tmp, d_emptyRegexp));
              ret = 0;
            }
            if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp) == vec_nodes.end()) {
              vec_nodes.push_back( tmp );
            }
          }
          Node exp3;
          int rt2 = delta( r[i], exp3 );
          if( rt2 == 0 ) {
            dnode = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, dnode, exp3));
          } else if( rt2 == 2 ) {
            break;
          }
        }
        retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
              ( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes ) );
        if(retNode == d_emptyRegexp) {
          ret = 2;
        }
        break;
      }
      case kind::REGEXP_UNION: {
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node dc;
          int rt = derivativeS(r[i], c, dc);
          if(rt == 0) {
            ret = 0;
          }
          if(rt != 2) {
            if(std::find(vec_nodes.begin(), vec_nodes.end(), dc) == vec_nodes.end()) {
              vec_nodes.push_back( dc );
            }
          }
          //Trace("regexp-derive") << "RegExp-derive OR R[" << i << "] " << mkString(r[i]) << " returns " << mkString(dc) << std::endl;
        }
        retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
              ( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes ) );
        if(retNode == d_emptyRegexp) {
          ret = 2;
        }
        break;
      }
      case kind::REGEXP_INTER: {
        bool flag = true;
        bool flag_sg = false;
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node dc;
          int rt = derivativeS(r[i], c, dc);
          if(rt == 0) {
            ret = 0;
          } else if(rt == 2) {
            flag = false;
            break;
          }
          if(dc == d_sigma_star) {
            flag_sg = true;
          } else {
            if(std::find(vec_nodes.begin(), vec_nodes.end(), dc) == vec_nodes.end()) {
              vec_nodes.push_back( dc );
            }
          }
        }
        if(flag) {
          if(vec_nodes.size() == 0 && flag_sg) {
            retNode = d_sigma_star;
          } else {
            retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
                  ( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes ) );
            if(retNode == d_emptyRegexp) {
              ret = 2;
            }
          }
        } else {
          retNode = d_emptyRegexp;
          ret = 2;
        }
        break;
      }
      case kind::REGEXP_STAR: {
        Node dc;
        ret = derivativeS(r[0], c, dc);
        retNode = dc==d_emptyRegexp ? dc : (dc==d_emptySingleton ? r : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, dc, r ));
        break;
      }
      case kind::REGEXP_LOOP: {
        if(r[1] == r[2] && r[1] == d_zero) {
          ret = 2;
          //retNode = d_emptyRegexp;
        } else {
          Node dc;
          ret = derivativeS(r[0], c, dc);
          if(dc==d_emptyRegexp) {
            unsigned l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
            unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
            Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], 
              NodeManager::currentNM()->mkConst(CVC4::Rational(l==0? 0 : (l-1))),
              NodeManager::currentNM()->mkConst(CVC4::Rational(u-1)));
            retNode = dc==d_emptySingleton? r2 : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, dc, r2 );
          } else {
            retNode = d_emptyRegexp;
          }
        }
        break;
      }
      case kind::REGEXP_COMPLEMENT:
      {
        // don't know result
        return 0;
        break;
      }
      default: {
        Assert(!isRegExpKind(r.getKind()));
        return 0;
        break;
      }
    }
    if(retNode != d_emptyRegexp) {
      retNode = Rewriter::rewrite( retNode );
    }
    std::pair< Node, int > p(retNode, ret);
    d_deriv_cache[dv] = p;
  }

  Trace("regexp-derive") << "RegExp-derive returns : /" << mkString( retNode ) << "/" << std::endl;
  return ret;
}

Node RegExpOpr::derivativeSingle( Node r, CVC4::String c ) {
  Assert(c.size() < 2);
  Trace("regexp-derive") << "RegExp-derive starts with /" << mkString( r ) << "/, c=" << c << std::endl;
  Node retNode = d_emptyRegexp;
  PairNodeStr dv = std::make_pair( r, c );
  if( d_dv_cache.find( dv ) != d_dv_cache.end() ) {
    retNode = d_dv_cache[dv];
  } else if( c.isEmptyString() ){
    Node exp;
    int tmp = delta( r, exp );
    if(tmp == 0) {
      // TODO variable
      retNode = d_emptyRegexp;
    } else if(tmp == 1) {
      retNode = r;
    } else {
      retNode = d_emptyRegexp;
    }
  } else {
    Kind k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        retNode = d_emptyRegexp;
        break;
      }
      case kind::REGEXP_SIGMA: {
        retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString );
        break;
      }
      case kind::REGEXP_RANGE: {
        CVC4::String a = r[0].getConst<String>();
        CVC4::String b = r[1].getConst<String>();
        retNode = (a <= c && c <= b) ? d_emptySingleton : d_emptyRegexp;
        break;
      }
      case kind::STRING_TO_REGEXP: {
        if(r[0].isConst()) {
          if(r[0] == d_emptyString) {
            retNode = d_emptyRegexp;
          } else {
            if (r[0].getConst<CVC4::String>().front() == c.front())
            {
              retNode =  NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP,
                r[0].getConst< CVC4::String >().size() == 1 ? d_emptyString : NodeManager::currentNM()->mkConst( r[0].getConst< CVC4::String >().substr(1) ) );
            } else {
              retNode = d_emptyRegexp;
            }
          }
        } else {
          // TODO variable
          retNode = d_emptyRegexp;
        }
        break;
      }
      case kind::REGEXP_CONCAT: {
        Node rees = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString );
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node dc = derivativeSingle(r[i], c);
          if(dc != d_emptyRegexp) {
            std::vector< Node > vec_nodes2;
            if(dc != rees) {
              vec_nodes2.push_back( dc );
            }
            for(unsigned j=i+1; j<r.getNumChildren(); ++j) {
              if(r[j] != rees) {
                vec_nodes2.push_back( r[j] );
              }
            }
            Node tmp = vec_nodes2.size()==0 ? rees :
              vec_nodes2.size()==1 ? vec_nodes2[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, vec_nodes2 );
            if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp) == vec_nodes.end()) {
              vec_nodes.push_back( tmp );
            }
          }
          Node exp;
          if( delta( r[i], exp ) != 1 ) {
            break;
          }
        }
        retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
              ( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes ) );
        break;
      }
      case kind::REGEXP_UNION: {
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node dc = derivativeSingle(r[i], c);
          if(dc != d_emptyRegexp) {
            if(std::find(vec_nodes.begin(), vec_nodes.end(), dc) == vec_nodes.end()) {
              vec_nodes.push_back( dc );
            }
          }
          //Trace("regexp-derive") << "RegExp-derive OR R[" << i << "] /" << mkString(r[i]) << "/ returns /" << mkString(dc) << "/" << std::endl;
        }
        retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
              ( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes ) );
        break;
      }
      case kind::REGEXP_INTER: {
        bool flag = true;
        bool flag_sg = false;
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          Node dc = derivativeSingle(r[i], c);
          if(dc != d_emptyRegexp) {
            if(dc == d_sigma_star) {
              flag_sg = true;
            } else {
              if(std::find(vec_nodes.begin(), vec_nodes.end(), dc) == vec_nodes.end()) {
                vec_nodes.push_back( dc );
              }
            }
          } else {
            flag = false;
            break;
          }
        }
        if(flag) {
          if(vec_nodes.size() == 0 && flag_sg) {
            retNode = d_sigma_star;
          } else {
            retNode = vec_nodes.size() == 0 ? d_emptyRegexp :
                  ( vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes ) );
          }
        } else {
          retNode = d_emptyRegexp;
        }
        break;
      }
      case kind::REGEXP_STAR: {
        Node dc = derivativeSingle(r[0], c);
        if(dc != d_emptyRegexp) {
          retNode = dc==d_emptySingleton? r : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, dc, r );
        } else {
          retNode = d_emptyRegexp;
        }
        break;
      }
      case kind::REGEXP_LOOP: {
        if(r[1] == r[2] && r[1] == d_zero) {
          retNode = d_emptyRegexp;
        } else {
          Node dc = derivativeSingle(r[0], c);
          if(dc != d_emptyRegexp) {
            unsigned l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
            unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
            Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], 
              NodeManager::currentNM()->mkConst(CVC4::Rational(l==0? 0 : (l-1))),
              NodeManager::currentNM()->mkConst(CVC4::Rational(u-1)));
            retNode = dc==d_emptySingleton? r2 : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, dc, r2 );
          } else {
            retNode = d_emptyRegexp;
          }
        }
        //Trace("regexp-derive") << "RegExp-derive : REGEXP_LOOP returns /" << mkString(retNode) << "/" << std::endl;
        break;
      }
      case kind::REGEXP_COMPLEMENT:
      default: {
        Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in derivative of RegExp." << std::endl;
        Unreachable();
        break;
      }
    }
    if(retNode != d_emptyRegexp) {
      retNode = Rewriter::rewrite( retNode );
    }
    d_dv_cache[dv] = retNode;
  }
  Trace("regexp-derive") << "RegExp-derive returns : /" << mkString( retNode ) << "/" << std::endl;
  return retNode;
}

void RegExpOpr::firstChars(Node r, std::set<unsigned> &pcset, SetNodes &pvset)
{
  Trace("regexp-fset") << "Start FSET(" << mkString(r) << ")" << std::endl;
  std::map<Node, std::pair<std::set<unsigned>, SetNodes> >::const_iterator itr =
      d_fset_cache.find(r);
  if(itr != d_fset_cache.end()) {
    pcset.insert((itr->second).first.begin(), (itr->second).first.end());
    pvset.insert((itr->second).second.begin(), (itr->second).second.end());
  } else {
    // cset is code points
    std::set<unsigned> cset;
    SetNodes vset;
    Kind k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        break;
      }
      case kind::REGEXP_RANGE: {
        unsigned a = r[0].getConst<String>().front();
        a = String::convertUnsignedIntToCode(a);
        unsigned b = r[1].getConst<String>().front();
        b = String::convertUnsignedIntToCode(b);
        Assert(a < b);
        Assert(b < std::numeric_limits<unsigned>::max());
        for (unsigned c = a; c <= b; c++)
        {
          cset.insert(c);
        }
        break;
      }
      case kind::STRING_TO_REGEXP: {
        Node st = Rewriter::rewrite(r[0]);
        if(st.isConst()) {
          CVC4::String s = st.getConst< CVC4::String >();
          if(s.size() != 0) {
            unsigned sc = s.front();
            sc = String::convertUnsignedIntToCode(sc);
            cset.insert(sc);
          }
        }
        else if (st.getKind() == kind::STRING_CONCAT)
        {
          if(st[0].isConst()) {
            CVC4::String s = st[0].getConst<CVC4::String>();
            unsigned sc = s.front();
            sc = String::convertUnsignedIntToCode(sc);
            cset.insert(sc);
          } else {
            vset.insert( st[0] );
          }
        }
        else
        {
          vset.insert(st);
        }
        break;
      }
      case kind::REGEXP_CONCAT: {
        for(unsigned i=0; i<r.getNumChildren(); i++) {
          firstChars(r[i], cset, vset);
          Node n = r[i];
          Node exp;
          int r = delta( n, exp );
          if(r != 1) {
            break;
          }
        }
        break;
      }
      case kind::REGEXP_UNION: {
        for(unsigned i=0; i<r.getNumChildren(); i++) {
          firstChars(r[i], cset, vset);
        }
        break;
      }
      case kind::REGEXP_INTER: {
        //TODO: Overapproximation for now
        //for(unsigned i=0; i<r.getNumChildren(); i++) {
        // firstChars(r[i], cset, vset);
        //}
        firstChars(r[0], cset, vset);
        break;
      }
      case kind::REGEXP_STAR: {
        firstChars(r[0], cset, vset);
        break;
      }
      case kind::REGEXP_LOOP: {
        firstChars(r[0], cset, vset);
        break;
      }
      case kind::REGEXP_SIGMA:
      case kind::REGEXP_COMPLEMENT:
      default: {
        // we do not expect to call this function on regular expressions that
        // aren't a standard regular expression kind. However, if we do, then
        // the following code is conservative and says that the current
        // regular expression can begin with any character.
        Assert(isRegExpKind(k));
        // can start with any character
        Assert(d_lastchar < std::numeric_limits<unsigned>::max());
        for (unsigned i = 0; i <= d_lastchar; i++)
        {
          cset.insert(i);
        }
        break;
      }
    }
    pcset.insert(cset.begin(), cset.end());
    pvset.insert(vset.begin(), vset.end());
    std::pair<std::set<unsigned>, SetNodes> p(cset, vset);
    d_fset_cache[r] = p;
  }

  if(Trace.isOn("regexp-fset")) {
    Trace("regexp-fset") << "END FSET(" << mkString(r) << ") = {";
    for (std::set<unsigned>::const_iterator itr = pcset.begin();
         itr != pcset.end();
         ++itr)
    {
      if (itr != pcset.begin())
      {
        Trace("regexp-fset") << ",";
      }
      Trace("regexp-fset") << (*itr);
      }
    Trace("regexp-fset") << "}" << std::endl;
  }
}

//simplify
void RegExpOpr::simplify(Node t, std::vector< Node > &new_nodes, bool polarity) {
  Trace("strings-regexp-simpl") << "RegExp-Simpl starts with " << t << ", polarity=" << polarity << std::endl;
  Assert(t.getKind() == kind::STRING_IN_REGEXP);
  Node str = Rewriter::rewrite(t[0]);
  Node re  = Rewriter::rewrite(t[1]);
  if(polarity) {
    simplifyPRegExp( str, re, new_nodes );
  } else {
    simplifyNRegExp( str, re, new_nodes );
  }
  Trace("strings-regexp-simpl") << "RegExp-Simpl  returns (" << new_nodes.size() << "):\n";
  for(unsigned i=0; i<new_nodes.size(); i++) {
    Trace("strings-regexp-simpl") << "\t" << new_nodes[i] << std::endl;
  }
}
void RegExpOpr::simplifyNRegExp( Node s, Node r, std::vector< Node > &new_nodes ) {
  std::pair < Node, Node > p(s, r);
  NodeManager *nm = NodeManager::currentNM();
  std::map < std::pair< Node, Node >, Node >::const_iterator itr = d_simpl_neg_cache.find(p);
  if(itr != d_simpl_neg_cache.end()) {
    new_nodes.push_back( itr->second );
  } else {
    Kind k = r.getKind();
    Node conc;
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        conc = d_true;
        break;
      }
      case kind::REGEXP_SIGMA: {
        conc = d_one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s)).negate();
        break;
      }
      case kind::REGEXP_RANGE: {
        std::vector< Node > vec;
        unsigned a = r[0].getConst<String>().front();
        a = String::convertUnsignedIntToCode(a);
        unsigned b = r[1].getConst<String>().front();
        b = String::convertUnsignedIntToCode(b);
        for (unsigned c = a; c <= b; c++)
        {
          std::vector<unsigned> tmpVec;
          tmpVec.push_back(String::convertCodeToUnsignedInt(c));
          Node tmp = s.eqNode(nm->mkConst(String(tmpVec))).negate();
          vec.push_back( tmp );
        }
        conc = vec.size()==1? vec[0] : NodeManager::currentNM()->mkNode(kind::AND, vec);
        break;
      }
      case kind::STRING_TO_REGEXP: {
        conc = s.eqNode(r[0]).negate();
        break;
      }
      case kind::REGEXP_CONCAT: {
        // The following simplification states that
        //    ~( s in R1 ++ R2 )
        // is equivalent to
        //    forall x.
        //      0 <= x <= len(s) =>
        //        ~( substr(s,0,x) in R1 ) OR ~( substr(s,x,len(s)-x) in R2)
        Node lens = nm->mkNode(STRING_LENGTH, s);
        // the index we are removing from the RE concatenation
        unsigned indexRm = 0;
        Node b1;
        Node b1v;
        // As an optimization to the above reduction, if we can determine that
        // all strings in the language of R1 have the same length, say n,
        // then the conclusion of the reduction is quantifier-free:
        //    ~( substr(s,0,n) in R1 ) OR ~( substr(s,n,len(s)-n) in R2)
        Node reLength = TheoryStringsRewriter::getFixedLengthForRegexp(r[0]);
        if (reLength.isNull())
        {
          // try from the opposite end
          unsigned indexE = r.getNumChildren() - 1;
          reLength = TheoryStringsRewriter::getFixedLengthForRegexp(r[indexE]);
          if (!reLength.isNull())
          {
            indexRm = indexE;
          }
        }
        Node guard;
        if (reLength.isNull())
        {
          b1 = nm->mkBoundVar(nm->integerType());
          b1v = nm->mkNode(BOUND_VAR_LIST, b1);
          guard = nm->mkNode(AND,
                             nm->mkNode(GEQ, b1, d_zero),
                             nm->mkNode(GEQ, nm->mkNode(STRING_LENGTH, s), b1));
        }
        else
        {
          b1 = reLength;
        }
        Node s1;
        Node s2;
        if (indexRm == 0)
        {
          s1 = nm->mkNode(STRING_SUBSTR, s, d_zero, b1);
          s2 = nm->mkNode(STRING_SUBSTR, s, b1, nm->mkNode(MINUS, lens, b1));
        }
        else
        {
          s1 = nm->mkNode(STRING_SUBSTR, s, nm->mkNode(MINUS, lens, b1), b1);
          s2 =
              nm->mkNode(STRING_SUBSTR, s, d_zero, nm->mkNode(MINUS, lens, b1));
        }
        Node s1r1 = nm->mkNode(STRING_IN_REGEXP, s1, r[indexRm]).negate();
        std::vector<Node> nvec;
        for (unsigned i = 0, nchild = r.getNumChildren(); i < nchild; i++)
        {
          if (i != indexRm)
          {
            nvec.push_back( r[i] );
          }
        }
        Node r2 = nvec.size() == 1 ? nvec[0] : nm->mkNode(REGEXP_CONCAT, nvec);
        r2 = Rewriter::rewrite(r2);
        Node s2r2 = nm->mkNode(STRING_IN_REGEXP, s2, r2).negate();
        conc = nm->mkNode(OR, s1r1, s2r2);
        if (!b1v.isNull())
        {
          conc = nm->mkNode(OR, guard.negate(), conc);
          conc = nm->mkNode(FORALL, b1v, conc);
        }
        break;
      }
      case kind::REGEXP_UNION: {
        std::vector< Node > c_and;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(r[i].getKind() == kind::STRING_TO_REGEXP) {
            c_and.push_back( r[i][0].eqNode(s).negate() );
          } else if(r[i].getKind() == kind::REGEXP_EMPTY) {
            continue;
          } else {
            c_and.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]).negate());
          }
        }
        conc = c_and.size() == 0 ? d_true :
            c_and.size() == 1 ? c_and[0] : NodeManager::currentNM()->mkNode(kind::AND, c_and);
        break;
      }
      case kind::REGEXP_INTER: {
        bool emptyflag = false;
        std::vector< Node > c_or;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(r[i].getKind() == kind::STRING_TO_REGEXP) {
            c_or.push_back( r[i][0].eqNode(s).negate() );
          } else if(r[i].getKind() == kind::REGEXP_EMPTY) {
            emptyflag = true;
            break;
          } else {
            c_or.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]).negate());
          }
        }
        if(emptyflag) {
          conc = d_true;
        } else {
          conc = c_or.size() == 1 ? c_or[0] : NodeManager::currentNM()->mkNode(kind::OR, c_or);
        }
        break;
      }
      case kind::REGEXP_STAR: {
        if(s == d_emptyString) {
          conc = d_false;
        } else if(r[0].getKind() == kind::REGEXP_EMPTY) {
          conc = s.eqNode(d_emptyString).negate();
        } else if(r[0].getKind() == kind::REGEXP_SIGMA) {
          conc = d_false;
        } else {
          Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s);
          Node sne = s.eqNode(d_emptyString).negate();
          Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
          Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
          Node g1 = NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode(kind::GEQ, b1, d_one),
                NodeManager::currentNM()->mkNode( kind::GEQ, lens, b1 ) );
          //internal
          Node s1 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, s, d_zero, b1);
          Node s2 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, s, b1, NodeManager::currentNM()->mkNode(kind::MINUS, lens, b1));
          Node s1r1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s1, r[0]).negate();
          Node s2r2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s2, r).negate();

          conc = NodeManager::currentNM()->mkNode(kind::OR, s1r1, s2r2);
          conc = NodeManager::currentNM()->mkNode(kind::IMPLIES, g1, conc);
          conc = NodeManager::currentNM()->mkNode(kind::FORALL, b1v, conc);
          conc = NodeManager::currentNM()->mkNode(kind::AND, sne, conc);
        }
        break;
      }
      case kind::REGEXP_LOOP: {
        Assert(r.getNumChildren() == 3);
        if(r[1] == r[2]) {
          if(r[1] == d_zero) {
            conc = s.eqNode(d_emptyString).negate();
          } else if(r[1] == d_one) {
            conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[0]).negate();
          } else {
            //unroll for now
            unsigned l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
            std::vector<Node> vec;
            for(unsigned i=0; i<l; i++) {
              vec.push_back(r[0]);
            }
            Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec);
            conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r2).negate();
          }
        } else {
          Assert(r[1] == d_zero);
          //unroll for now
          unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
          std::vector<Node> vec;
          vec.push_back(d_emptySingleton);
          std::vector<Node> vec2;
          for(unsigned i=1; i<=u; i++) {
            vec2.push_back(r[0]);
            Node r2 = i==1? r[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec);
            vec.push_back(r2);
          }
          Node r3 = NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec);
          conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r3).negate();
        }
        break;
      }
      case kind::REGEXP_COMPLEMENT:
      {
        // ~( s in complement(R) ) ---> s in R
        conc = nm->mkNode(STRING_IN_REGEXP, s, r[0]);
        break;
      }
      default: {
        Assert(!isRegExpKind(k));
        break;
      }
    }
    if (!conc.isNull())
    {
      conc = Rewriter::rewrite(conc);
      new_nodes.push_back(conc);
      d_simpl_neg_cache[p] = conc;
    }
  }
}
void RegExpOpr::simplifyPRegExp( Node s, Node r, std::vector< Node > &new_nodes ) {
  std::pair < Node, Node > p(s, r);
  NodeManager *nm = NodeManager::currentNM();
  std::map < std::pair< Node, Node >, Node >::const_iterator itr = d_simpl_cache.find(p);
  if(itr != d_simpl_cache.end()) {
    new_nodes.push_back( itr->second );
  } else {
    Kind k = r.getKind();
    Node conc;
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        conc = d_false;
        break;
      }
      case kind::REGEXP_SIGMA: {
        conc = d_one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s));
        break;
      }
      case kind::REGEXP_RANGE: {
        conc = s.eqNode( r[0] );
        if(r[0] != r[1]) {
          unsigned a = r[0].getConst<String>().front();
          unsigned b = r[1].getConst<String>().front();
          a += 1;
          std::vector<unsigned> anvec;
          anvec.push_back(a);
          Node an = nm->mkConst(String(anvec));
          Node tmp = a != b
                         ? nm->mkNode(kind::STRING_IN_REGEXP,
                                      s,
                                      nm->mkNode(kind::REGEXP_RANGE, an, r[1]))
                         : s.eqNode(r[1]);
          conc = NodeManager::currentNM()->mkNode(kind::OR, conc, tmp);
        }
        break;
      }
      case kind::STRING_TO_REGEXP: {
        conc = s.eqNode(r[0]);
        break;
      }
      case kind::REGEXP_CONCAT: {
        std::vector< Node > nvec;
        std::vector< Node > cc;
        bool emptyflag = false;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(r[i].getKind() == kind::STRING_TO_REGEXP) {
            cc.push_back( r[i][0] );
          } else if(r[i].getKind() == kind::REGEXP_EMPTY) {
            emptyflag = true;
            break;
          } else {
            Node sk = NodeManager::currentNM()->mkSkolem( "rc", s.getType(), "created for regular expression concat" );
            Node lem = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk, r[i]);
            nvec.push_back(lem);
            cc.push_back(sk);
          }
        }
        if(emptyflag) {
          conc = d_false;
        } else {
          Node lem = s.eqNode( NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, cc) );
          nvec.push_back(lem);
          conc = nvec.size() == 1 ? nvec[0] : NodeManager::currentNM()->mkNode(kind::AND, nvec);
        }
        break;
      }
      case kind::REGEXP_UNION: {
        std::vector< Node > c_or;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(r[i].getKind() == kind::STRING_TO_REGEXP) {
            c_or.push_back( r[i][0].eqNode(s) );
          } else if(r[i].getKind() == kind::REGEXP_EMPTY) {
            continue;
          } else {
            c_or.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]));
          }
        }
        conc = c_or.size() == 0 ? d_false :
            c_or.size() == 1 ? c_or[0] : NodeManager::currentNM()->mkNode(kind::OR, c_or);
        break;
      }
      case kind::REGEXP_INTER: {
        std::vector< Node > c_and;
        bool emptyflag = false;
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(r[i].getKind() == kind::STRING_TO_REGEXP) {
            c_and.push_back( r[i][0].eqNode(s) );
          } else if(r[i].getKind() == kind::REGEXP_EMPTY) {
            emptyflag = true;
            break;
          } else {
            c_and.push_back(NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[i]));
          }
        }
        if(emptyflag) {
          conc = d_false;
        } else {
          conc = c_and.size() == 1 ? c_and[0] : NodeManager::currentNM()->mkNode(kind::AND, c_and);
        }
        break;
      }
      case kind::REGEXP_STAR: {
        if(s == d_emptyString) {
          conc = d_true;
        } else if(r[0].getKind() == kind::REGEXP_EMPTY) {
          conc = s.eqNode(d_emptyString);
        } else if(r[0].getKind() == kind::REGEXP_SIGMA) {
          conc = d_true;
        } else {
          NodeManager* nm = NodeManager::currentNM();
          Node se = s.eqNode(d_emptyString);
          Node sinr = nm->mkNode(kind::STRING_IN_REGEXP, s, r[0]);
          Node sk1 = nm->mkSkolem(
              "rs", s.getType(), "created for regular expression star");
          Node sk2 = nm->mkSkolem(
              "rs", s.getType(), "created for regular expression star");
          Node sk3 = nm->mkSkolem(
              "rs", s.getType(), "created for regular expression star");

          NodeBuilder<> nb(kind::AND);
          nb << sk1.eqNode(d_emptyString).negate();
          nb << sk3.eqNode(d_emptyString).negate();
          nb << nm->mkNode(kind::STRING_IN_REGEXP, sk1, r[0]);
          nb << nm->mkNode(kind::STRING_IN_REGEXP, sk2, r);
          nb << nm->mkNode(kind::STRING_IN_REGEXP, sk3, r[0]);
          nb << s.eqNode(nm->mkNode(kind::STRING_CONCAT, sk1, sk2, sk3));
          conc = nb;

          // We unfold `x in R*` by considering three cases: `x` is empty, `x`
          // is matched by `R`, or `x` is matched by two or more `R`s. For the
          // last case, we break `x` into three pieces, making the beginning
          // and the end each match `R` and the middle match `R*`. Matching the
          // beginning and the end with `R` allows us to reason about the
          // beginning and the end of `x` simultaneously.
          //
          // x in R* ---> (x = "") v (x in R) v
          //              (x = x1 ++ x2 ++ x3 ^ x1 != "" ^ x3 != "" ^
          //               x1 in R ^ x2 in R* ^ x3 in R)
          conc = nm->mkNode(kind::OR, se, sinr, conc);
        }
        break;
      }
      case kind::REGEXP_LOOP: {
        Assert(r.getNumChildren() == 3);
        if(r[1] == d_zero) {
          if(r[2] == d_zero) {
            conc = s.eqNode( d_emptyString );
          } else {
            //R{0,n}
            if(s != d_emptyString) {
              Node sk1 = NodeManager::currentNM()->mkSkolem( "lps", s.getType(), "created for regular expression loop" );
              Node sk2 = NodeManager::currentNM()->mkSkolem( "lps", s.getType(), "created for regular expression loop" );
              Node seq12 = s.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, sk1, sk2));
              Node sk1ne = sk1.eqNode(d_emptyString).negate();
              Node sk1inr = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk1, r[0]);
              unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
              Node u1 = NodeManager::currentNM()->mkConst(CVC4::Rational(u - 1));
              Node sk2inru = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk2,
                NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], d_zero, u1));
              conc = NodeManager::currentNM()->mkNode(kind::AND, seq12, sk1ne, sk1inr, sk2inru);
              conc = NodeManager::currentNM()->mkNode(kind::OR,
                s.eqNode(d_emptyString), conc);
            } else {
              conc = d_true;
            }
          }
        } else {
          //R^n
          Node sk1 = NodeManager::currentNM()->mkSkolem( "lps", s.getType(), "created for regular expression loop" );
          Node sk2 = NodeManager::currentNM()->mkSkolem( "lps", s.getType(), "created for regular expression loop" );
          Node seq12 = s.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, sk1, sk2));
          Node sk1ne = sk1.eqNode(d_emptyString).negate();
          Node sk1inr = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk1, r[0]);
          unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
          Node u1 = NodeManager::currentNM()->mkConst(CVC4::Rational(u - 1));
          Node sk2inru = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk2,
            NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], u1, u1));
          conc = NodeManager::currentNM()->mkNode(kind::AND, seq12, sk1ne, sk1inr, sk2inru);
        }
        break;
      }
      case kind::REGEXP_COMPLEMENT:
      {
        // s in complement(R) ---> ~( s in R )
        conc = nm->mkNode(STRING_IN_REGEXP, s, r[0]).negate();
        break;
      }
      default: {
        Assert(!isRegExpKind(k));
        break;
      }
    }
    if (!conc.isNull())
    {
      conc = Rewriter::rewrite(conc);
      new_nodes.push_back(conc);
      d_simpl_cache[p] = conc;
    }
  }
}

bool RegExpOpr::isPairNodesInSet(std::set< PairNodes > &s, Node n1, Node n2) {
  for(std::set< PairNodes >::const_iterator itr = s.begin();
      itr != s.end(); ++itr) {
    if((itr->first == n1 && itr->second == n2) ||
       (itr->first == n2 && itr->second == n1)) {
      return true;
    }
  }
  return false;
}

bool RegExpOpr::containC2(unsigned cnt, Node n) {
  if(n.getKind() == kind::REGEXP_RV) {
    Assert(n[0].getConst<Rational>() <= Rational(String::maxSize()))
        << "Exceeded UINT32_MAX in RegExpOpr::containC2";
    unsigned y = n[0].getConst<Rational>().getNumerator().toUnsignedInt();
    return cnt == y;
  } else if(n.getKind() == kind::REGEXP_CONCAT) {
    for( unsigned i=0; i<n.getNumChildren(); i++ ) {
      if(containC2(cnt, n[i])) {
        return true;
      }
    }
  } else if(n.getKind() == kind::REGEXP_STAR) {
    return containC2(cnt, n[0]);
  } else if(n.getKind() == kind::REGEXP_LOOP) {
    return containC2(cnt, n[0]);
  } else if(n.getKind() == kind::REGEXP_UNION) {
    for( unsigned i=0; i<n.getNumChildren(); i++ ) {
      if(containC2(cnt, n[i])) {
        return true;
      }
    }
  }
  return false;
}
Node RegExpOpr::convert1(unsigned cnt, Node n) {
  Trace("regexp-debug") << "Converting " << n << " at " << cnt << "... " << std::endl;
  Node r1, r2;
  convert2(cnt, n, r1, r2);
  Trace("regexp-debug") << "... getting r1=" << r1 << ", and r2=" << r2 << std::endl;
  Node ret = r1==d_emptySingleton ? r2 : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, 
     NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, r1), r2);
  ret = Rewriter::rewrite( ret );
  Trace("regexp-debug") << "... done convert at " << cnt << ", with return " << ret << std::endl;
  return ret;
}
void RegExpOpr::convert2(unsigned cnt, Node n, Node &r1, Node &r2) {
  if(n == d_emptyRegexp) {
    r1 = d_emptyRegexp;
    r2 = d_emptyRegexp;
    return;
  } else if(n == d_emptySingleton) {
    r1 = d_emptySingleton;
    r2 = d_emptySingleton;
  }
  Kind nk = n.getKind();
  if (nk == REGEXP_RV)
  {
    Assert(n[0].getConst<Rational>() <= Rational(String::maxSize()))
        << "Exceeded UINT32_MAX in RegExpOpr::convert2";
    unsigned y = n[0].getConst<Rational>().getNumerator().toUnsignedInt();
    r1 = d_emptySingleton;
    if(cnt == y) {
      r2 = d_emptyRegexp;
    } else {
      r2 = n;
    }
  }
  else if (nk == REGEXP_CONCAT)
  {
    bool flag = true;
    std::vector<Node> vr1, vr2;
    for( unsigned i=0; i<n.getNumChildren(); i++ ) {
      if(containC2(cnt, n[i])) {
        Node t1, t2;
        convert2(cnt, n[i], t1, t2);
        vr1.push_back(t1);
        r1 = vr1.size()==0 ? d_emptyRegexp : vr1.size()==1 ? vr1[0] :
             NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vr1);
        vr2.push_back(t2);
        for( unsigned j=i+1; j<n.getNumChildren(); j++ ) {
          vr2.push_back(n[j]);
        }
        r2 = vr2.size()==0 ? d_emptyRegexp : vr2.size()==1 ? vr2[0] :
             NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vr2);
        flag = false;
        break;
      } else {
        vr1.push_back(n[i]);
      }
    }
    if(flag) {
      r1 = d_emptySingleton;
      r2 = n;
    }
  }
  else if (nk == REGEXP_UNION)
  {
    std::vector<Node> vr1, vr2;
    for( unsigned i=0; i<n.getNumChildren(); i++ ) {
      Node t1, t2;
      convert2(cnt, n[i], t1, t2);
      vr1.push_back(t1);
      vr2.push_back(t2);
    }
    r1 = NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vr1);
    r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vr2);
  }
  else if (nk == STRING_TO_REGEXP || nk == REGEXP_SIGMA || nk == REGEXP_RANGE
           || nk == REGEXP_COMPLEMENT || nk == REGEXP_LOOP)
  {
    // this leaves n unchanged
    r1 = d_emptySingleton;
    r2 = n;
  }
  else
  {
    //is it possible?
    Unreachable();
  }
}

bool RegExpOpr::testNoRV(Node r) {
  std::map< Node, bool >::const_iterator itr = d_norv_cache.find(r);
  if(itr != d_norv_cache.end()) {
    return itr->second;
  } else {
    if(r.getKind() == kind::REGEXP_RV) {
      return false;
    } else if(r.getNumChildren() > 1) {
      for(unsigned int i=0; i<r.getNumChildren(); i++) {
        if(!testNoRV(r[i])) {
          return false;
        }
      }
    }
    return true;
  }
}

Node RegExpOpr::intersectInternal( Node r1, Node r2, std::map< PairNodes, Node > cache, unsigned cnt ) {
  //Assert(checkConstRegExp(r1) && checkConstRegExp(r2));
  if(r1 > r2) {
    TNode tmpNode = r1;
    r1 = r2;
    r2 = tmpNode;
  }
  Trace("regexp-int") << "Starting INTERSECT(" << cnt << "):\n  "<< mkString(r1) << ",\n  " << mkString(r2) << std::endl;
  //if(Trace.isOn("regexp-debug")) {
  //  Trace("regexp-debug") << "... with cache:\n";
  //  for(std::map< PairNodes, Node >::const_iterator itr=cache.begin();
  //      itr!=cache.end();itr++) {
  //        Trace("regexp-debug") << "(" << itr->first.first << "," << itr->first.second << ")->" << itr->second << std::endl;
  //      }
  //}
  std::pair < Node, Node > p(r1, r2);
  std::map < PairNodes, Node >::const_iterator itr = d_inter_cache.find(p);
  Node rNode;
  if(itr != d_inter_cache.end()) {
    rNode = itr->second;
  } else {
    Trace("regexp-int-debug") << " ... not in cache" << std::endl;
    if(r1 == d_emptyRegexp || r2 == d_emptyRegexp) {
      Trace("regexp-int-debug") << " ... one is empty set" << std::endl;
      rNode = d_emptyRegexp;
    } else if(r1 == d_emptySingleton || r2 == d_emptySingleton) {
      Trace("regexp-int-debug") << " ... one is empty singleton" << std::endl;
      Node exp;
      int r = delta((r1 == d_emptySingleton ? r2 : r1), exp);
      if(r == 0) {
        //TODO: variable
        Unreachable();
      } else if(r == 1) {
        rNode = d_emptySingleton;
      } else {
        rNode = d_emptyRegexp;
      }
    } else if(r1 == r2) {
      Trace("regexp-int-debug") << " ... equal" << std::endl;
      rNode = r1; //convert1(cnt, r1);
    } else {
      Trace("regexp-int-debug") << " ... normal checking" << std::endl;
      std::map< PairNodes, Node >::const_iterator itrcache = cache.find(p);
      if(itrcache != cache.end()) {
        rNode = itrcache->second;
      } else {
        Trace("regexp-int-debug") << " ... normal without cache" << std::endl;
        std::vector<unsigned> cset;
        std::set<unsigned> cset1, cset2;
        std::set< Node > vset1, vset2;
        firstChars(r1, cset1, vset1);
        firstChars(r2, cset2, vset2);
        Trace("regexp-int-debug") << " ... got fset" << std::endl;
        std::set_intersection(cset1.begin(), cset1.end(), cset2.begin(), cset2.end(),
             std::inserter(cset, cset.begin()));
        std::vector< Node > vec_nodes;
        Node delta_exp;
        Trace("regexp-int-debug") << " ... try delta" << std::endl;
        int flag = delta(r1, delta_exp);
        int flag2 = delta(r2, delta_exp);
        Trace("regexp-int-debug") << " ... delta1=" << flag << ", delta2=" << flag2 << std::endl;
        if(flag != 2 && flag2 != 2) {
          if(flag == 1 && flag2 == 1) {
            vec_nodes.push_back(d_emptySingleton);
          } else {
            //TODO: variable
            Unreachable();
          }
        }
        if(Trace.isOn("regexp-int-debug")) {
          Trace("regexp-int-debug") << "Try CSET(" << cset.size() << ") = {";
          for (std::vector<unsigned>::const_iterator itr = cset.begin();
               itr != cset.end();
               ++itr)
          {
            if(itr != cset.begin()) {
              Trace("regexp-int-debug") << ", ";
            }
            Trace("regexp-int-debug") << ( *itr );
          }
          Trace("regexp-int-debug") << std::endl;
        }
        std::map< PairNodes, Node > cacheX;
        for (std::vector<unsigned>::const_iterator itr = cset.begin();
             itr != cset.end();
             ++itr)
        {
          std::vector<unsigned> cvec;
          cvec.push_back(String::convertCodeToUnsignedInt(*itr));
          String c(cvec);
          Trace("regexp-int-debug") << "Try character " << c << " ... " << std::endl;
          Node r1l = derivativeSingle(r1, c);
          Node r2l = derivativeSingle(r2, c);
          Trace("regexp-int-debug") << "  ... got partial(r1,c) = " << mkString(r1l) << std::endl;
          Trace("regexp-int-debug") << "  ... got partial(r2,c) = " << mkString(r2l) << std::endl;
          Node rt;
          
          if(r1l > r2l) {
            Node tnode = r1l;
            r1l = r2l; r2l = tnode;
          }
          PairNodes pp(r1l, r2l);
          std::map< PairNodes, Node >::const_iterator itr2 = cacheX.find(pp);
          if(itr2 != cacheX.end()) {
            rt = itr2->second;
          } else {
            std::map< PairNodes, Node > cache2(cache);
            cache2[ p ] = NodeManager::currentNM()->mkNode(kind::REGEXP_RV, NodeManager::currentNM()->mkConst(CVC4::Rational(cnt)));
            rt = intersectInternal(r1l, r2l, cache2, cnt+1);
            cacheX[ pp ] = rt;
          }

          rt = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
            NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(c)), rt) );

          Trace("regexp-int-debug") << "  ... got p(r1,c) && p(r2,c) = " << mkString(rt) << std::endl;
          vec_nodes.push_back(rt);
        }
        rNode = Rewriter::rewrite( vec_nodes.size()==0 ? d_emptyRegexp : vec_nodes.size()==1 ? vec_nodes[0] :
            NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec_nodes) );
        rNode = convert1(cnt, rNode);
        rNode = Rewriter::rewrite( rNode );
      }
    }
    Trace("regexp-int-debug") << "  ... try testing no RV of " << mkString(rNode) << std::endl;
    if(testNoRV(rNode)) {
      d_inter_cache[p] = rNode;
    }
  }
  Trace("regexp-int") << "End(" << cnt << ") of INTERSECT( " << mkString(r1) << ", " << mkString(r2) << " ) = " << mkString(rNode) << std::endl;
  return rNode;
}

Node RegExpOpr::removeIntersection(Node r) {
  Assert(checkConstRegExp(r));
  std::map < Node, Node >::const_iterator itr = d_rm_inter_cache.find(r);
  if(itr != d_rm_inter_cache.end()) {
    return itr->second;
  }
  Node retNode;
  Kind rk = r.getKind();
  switch (rk)
  {
    case REGEXP_EMPTY:
    case REGEXP_SIGMA:
    case REGEXP_RANGE:
    case STRING_TO_REGEXP:
    {
      retNode = r;
      break;
    }
    case REGEXP_CONCAT:
    case REGEXP_UNION:
    case REGEXP_STAR:
    case REGEXP_COMPLEMENT:
    {
      NodeBuilder<> nb(rk);
      for (const Node& rc : r)
      {
        nb << removeIntersection(rc);
      }
      retNode = Rewriter::rewrite(nb.constructNode());
      break;
    }

    case REGEXP_INTER:
    {
      retNode = removeIntersection(r[0]);
      for (size_t i = 1, nchild = r.getNumChildren(); i < nchild; i++)
      {
        bool spflag = false;
        Node tmpNode = removeIntersection(r[i]);
        retNode = intersect(retNode, tmpNode, spflag);
      }
      break;
    }
    case REGEXP_LOOP:
    {
      retNode = removeIntersection(r[0]);
      retNode = Rewriter::rewrite(
          NodeManager::currentNM()->mkNode(REGEXP_LOOP, retNode, r[1], r[2]));
      break;
    }
    default:
    {
      Unreachable();
    }
  }
  d_rm_inter_cache[r] = retNode;
  Trace("regexp-intersect") << "Remove INTERSECTION( " << mkString(r) << " ) = " << mkString(retNode) << std::endl;
  return retNode;
}

Node RegExpOpr::intersect(Node r1, Node r2, bool &spflag) {
  if(checkConstRegExp(r1) && checkConstRegExp(r2)) {
    Node rr1 = removeIntersection(r1);
    Node rr2 = removeIntersection(r2);
    std::map< PairNodes, Node > cache;
    Trace("regexp-intersect-node") << "Intersect (1): " << rr1 << std::endl;
    Trace("regexp-intersect-node") << "Intersect (2): " << rr2 << std::endl;
    Trace("regexp-intersect") << "Start INTERSECTION(\n\t" << mkString(r1) << ",\n\t"<< mkString(r2) << ")" << std::endl;
    Node retNode = intersectInternal(rr1, rr2, cache, 1);
    Trace("regexp-intersect") << "End INTERSECTION(\n\t" << mkString(r1) << ",\n\t"<< mkString(r2) << ") =\n\t" << mkString(retNode) << std::endl;
    Trace("regexp-intersect-node") << "Intersect finished." << std::endl;
    return retNode;
  } else {
    spflag = true;
    return Node::null();
  }
}

//printing
std::string RegExpOpr::niceChar(Node r) {
  if(r.isConst()) {
    std::string s = r.getConst<CVC4::String>().toString() ;
    return s == "." ? "\\." : s;
  } else {
    std::string ss = "$" + r.toString();
    return ss;
  }
}
std::string RegExpOpr::mkString( Node r ) {
  std::string retStr;
  if(r.isNull()) {
    retStr = "\\E";
  } else {
    int k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        retStr += "\\E";
        break;
      }
      case kind::REGEXP_SIGMA: {
        retStr += ".";
        break;
      }
      case kind::STRING_TO_REGEXP: {
        std::string tmp( niceChar( r[0] ) );
        retStr += tmp.size()==1? tmp : "(" + tmp + ")";
        break;
      }
      case kind::REGEXP_CONCAT: {
        retStr += "(";
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          //if(i != 0) retStr += ".";
          retStr += mkString( r[i] );
        }
        retStr += ")";
        break;
      }
      case kind::REGEXP_UNION: {
        retStr += "(";
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(i != 0) retStr += "|";
          retStr += mkString( r[i] );
        }
        retStr += ")";
        break;
      }
      case kind::REGEXP_INTER: {
        retStr += "(";
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(i != 0) retStr += "&";
          retStr += mkString( r[i] );
        }
        retStr += ")";
        break;
      }
      case kind::REGEXP_STAR: {
        retStr += mkString( r[0] );
        retStr += "*";
        break;
      }
      case kind::REGEXP_PLUS: {
        retStr += mkString( r[0] );
        retStr += "+";
        break;
      }
      case kind::REGEXP_OPT: {
        retStr += mkString( r[0] );
        retStr += "?";
        break;
      }
      case kind::REGEXP_RANGE: {
        retStr += "[";
        retStr += niceChar( r[0] );
        retStr += "-";
        retStr += niceChar( r[1] );
        retStr += "]";
        break;
      }
      case kind::REGEXP_LOOP: {
        retStr += "(";
        retStr += mkString(r[0]);
        retStr += ")";
        retStr += "{";
        retStr += r[1].getConst<Rational>().toString();
        retStr += ",";
        if(r.getNumChildren() == 3) {
          retStr += r[2].getConst<Rational>().toString();
        }
        retStr += "}";
        break;
      }
      case kind::REGEXP_RV: {
        retStr += "<";
        retStr += r[0].getConst<Rational>().getNumerator().toString();
        retStr += ">";
        break;
      }
      case REGEXP_COMPLEMENT:
      {
        retStr += "^(";
        retStr += mkString(r[0]);
        retStr += ")";
        break;
      }
      default:
      {
        std::stringstream ss;
        ss << r;
        retStr = ss.str();
        Assert(!isRegExpKind(r.getKind()));
        break;
      }
    }
  }

  return retStr;
}

bool RegExpOpr::regExpIncludes(Node r1, Node r2)
{
  Assert(Rewriter::rewrite(r1) == r1);
  Assert(Rewriter::rewrite(r2) == r2);

  if (r1 == r2)
  {
    return true;
  }

  // This method only works on a fragment of regular expressions
  if (!utils::isSimpleRegExp(r1) || !utils::isSimpleRegExp(r2))
  {
    return false;
  }

  const auto& it = d_inclusionCache.find(std::make_pair(r1, r2));
  if (it != d_inclusionCache.end())
  {
    return (*it).second;
  }

  std::vector<Node> v1, v2;
  utils::getRegexpComponents(r1, v1);
  utils::getRegexpComponents(r2, v2);

  // In the following, we iterate over `r2` (the "includee") and try to
  // match it with `r1`. `idxs`/`newIdxs` keep track of all the possible
  // positions in `r1` that we could currently be at.
  std::unordered_set<size_t> newIdxs = {0};
  std::unordered_set<size_t> idxs;
  for (const Node& n2 : v2)
  {
    // Transfer elements from `newIdxs` to `idxs`. Out-of-bound indices are
    // removed and for (re.* re.allchar), we additionally include the option of
    // skipping it. Indices must be smaller than the size of `v1`.
    idxs.clear();
    for (size_t idx : newIdxs)
    {
      if (idx < v1.size())
      {
        idxs.insert(idx);
        if (idx + 1 < v1.size() && v1[idx] == d_sigma_star)
        {
          Assert(idx + 1 == v1.size() || v1[idx + 1] != d_sigma_star);
          idxs.insert(idx + 1);
        }
      }
    }
    newIdxs.clear();

    if (n2.getKind() == STRING_TO_REGEXP || n2 == d_sigma)
    {
      Assert(n2 == d_sigma
             || (n2[0].isConst() && n2[0].getConst<String>().size() == 1));
      for (size_t idx : idxs)
      {
        if (v1[idx] == d_sigma || v1[idx] == n2)
        {
          // Given a character or an re.allchar in `r2`, we can either
          // match it with a corresponding character in `r1` or an
          // re.allchar
          newIdxs.insert(idx + 1);
        }
      }
    }

    for (size_t idx : idxs)
    {
      if (v1[idx] == d_sigma_star)
      {
        // (re.* re.allchar) can match an arbitrary amount of `r2`
        newIdxs.insert(idx);
      }
      else if (utils::isUnboundedWildcard(v1, idx))
      {
        // If a series of re.allchar is followed by (re.* re.allchar), we
        // can decide not to "waste" the re.allchar because the order of
        // the two wildcards is not observable (i.e. it does not change
        // the sequences matched by the regular expression)
        newIdxs.insert(idx);
      }
    }

    if (newIdxs.empty())
    {
      // If there are no candidates, we can't match the remainder of r2
      d_inclusionCache[std::make_pair(r1, r2)] = false;
      return false;
    }
  }

  // We have processed all of `r2`. We are now looking if there was also a
  // path to the end in `r1`. This makes sure that we don't have leftover
  // bits in `r1` that don't match anything in `r2`.
  bool result = false;
  for (size_t idx : newIdxs)
  {
    if (idx == v1.size() || (idx == v1.size() - 1 && v1[idx] == d_sigma_star))
    {
      result = true;
      break;
    }
  }

  d_inclusionCache[std::make_pair(r1, r2)] = result;
  return result;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
