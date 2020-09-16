/*********************                                                        */
/*! \file regexp_operation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symbolic Regular Expresion Operations
 **
 ** Symbolic Regular Expresion Operations
 **/

#include "theory/strings/regexp_operation.h"

#include "expr/node_algorithm.h"
#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

RegExpOpr::RegExpOpr(SkolemCache* sc)
    : d_true(NodeManager::currentNM()->mkConst(true)),
      d_false(NodeManager::currentNM()->mkConst(false)),
      d_emptyRegexp(NodeManager::currentNM()->mkNode(kind::REGEXP_EMPTY,
                                                     std::vector<Node>{})),
      d_zero(NodeManager::currentNM()->mkConst(::CVC4::Rational(0))),
      d_one(NodeManager::currentNM()->mkConst(::CVC4::Rational(1))),
      d_sigma(NodeManager::currentNM()->mkNode(kind::REGEXP_SIGMA,
                                               std::vector<Node>{})),
      d_sigma_star(
          NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, d_sigma)),
      d_sc(sc)
{
  d_emptyString = Word::mkEmptyWord(NodeManager::currentNM()->stringType());

  d_emptySingleton =
      NodeManager::currentNM()->mkNode(STRING_TO_REGEXP, d_emptyString);
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
      else if (!utils::isRegExpKind(ck))
      {
        // non-regular expression applications, e.g. function applications
        // with regular expression return type are treated as variables.
        d_constCache[cur] = RE_C_VARIABLE;
      }
      else
      {
        d_constCache[cur] = RE_C_UNKNOWN;
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
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

// 0-unknown, 1-yes, 2-no
int RegExpOpr::delta( Node r, Node &exp ) {
  std::map<Node, std::pair<int, Node> >::const_iterator itd =
      d_delta_cache.find(r);
  if (itd != d_delta_cache.end())
  {
    // already computed
    exp = itd->second.second;
    return itd->second.first;
  }
  Trace("regexp-delta") << "RegExpOpr::delta: " << r << std::endl;
  int ret = 0;
  NodeManager* nm = NodeManager::currentNM();
  Kind k = r.getKind();
  switch (k)
  {
    case REGEXP_EMPTY:
    case REGEXP_SIGMA:
    case REGEXP_RANGE:
    {
      // does not contain empty string
      ret = 2;
      break;
    }
    case STRING_TO_REGEXP:
    {
      Node tmp = Rewriter::rewrite(r[0]);
      if (tmp.isConst())
      {
        if (tmp == d_emptyString)
        {
          ret = 1;
        } else {
          ret = 2;
        }
      }
      else
      {
        ret = 0;
        if (tmp.getKind() == STRING_CONCAT)
        {
          for (const Node& tmpc : tmp)
          {
            if (tmpc.isConst())
            {
              ret = 2;
              break;
            }
          }
        }
        if (ret == 0)
        {
          exp = r[0].eqNode(d_emptyString);
        }
      }
      break;
    }
    case REGEXP_CONCAT:
    case REGEXP_UNION:
    case REGEXP_INTER:
    {
      // has there been an unknown child?
      bool hasUnknownChild = false;
      std::vector<Node> vec;
      int checkTmp = k == REGEXP_UNION ? 1 : 2;
      int retTmp = k == REGEXP_UNION ? 2 : 1;
      for (const Node& rc : r)
      {
        Node exp2;
        int tmp = delta(rc, exp2);
        if (tmp == checkTmp)
        {
          // return is implied by the child's return value
          ret = checkTmp;
          break;
        }
        else if (tmp == 0)
        {
          // unknown if child contains empty string
          Assert(!exp2.isNull());
          vec.push_back(exp2);
          hasUnknownChild = true;
        }
      }
      if (ret != checkTmp)
      {
        if (!hasUnknownChild)
        {
          ret = retTmp;
        } else {
          Kind kr = k == REGEXP_UNION ? OR : AND;
          exp = vec.size() == 1 ? vec[0] : nm->mkNode(kr, vec);
        }
      }
      break;
    }
    case REGEXP_STAR:
    case REGEXP_OPT:
    {
      // contains empty string
      ret = 1;
      break;
    }
    case REGEXP_PLUS:
    {
      ret = delta(r[0], exp);
      break;
    }
    case REGEXP_LOOP:
    {
      uint32_t lo = utils::getLoopMinOccurrences(r);
      if (lo == 0)
      {
        ret = 1;
      }
      else
      {
        ret = delta(r[0], exp);
      }
      break;
    }
    case REGEXP_COMPLEMENT:
    {
      int tmp = delta(r[0], exp);
      // flip the result if known
      ret = tmp == 0 ? 0 : (3 - tmp);
      exp = exp.isNull() ? exp : exp.negate();
      break;
    }
    default:
    {
      Assert(!utils::isRegExpKind(k));
      break;
    }
  }
  if (!exp.isNull())
  {
    exp = Rewriter::rewrite(exp);
  }
  std::pair<int, Node> p(ret, exp);
  d_delta_cache[r] = p;
  Trace("regexp-delta") << "RegExpOpr::delta returns " << ret << " for " << r
                        << ", expr = " << exp << std::endl;
  return ret;
}

// 0-unknown, 1-yes, 2-no
int RegExpOpr::derivativeS( Node r, CVC4::String c, Node &retNode ) {
  Assert(c.size() < 2);
  Trace("regexp-derive") << "RegExp-derive starts with /" << mkString( r ) << "/, c=" << c << std::endl;

  int ret = 1;
  retNode = d_emptyRegexp;
  NodeManager* nm = NodeManager::currentNM();

  PairNodeStr dv = std::make_pair( r, c );
  if( d_deriv_cache.find( dv ) != d_deriv_cache.end() ) {
    retNode = d_deriv_cache[dv].first;
    ret = d_deriv_cache[dv].second;
  }
  else if (c.empty())
  {
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
            if (tmp.getConst<String>().front() == c.front())
            {
              retNode =
                  nm->mkNode(STRING_TO_REGEXP,
                             Word::getLength(tmp) == 1 ? d_emptyString
                                                       : Word::substr(tmp, 1));
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
              if (t2.getConst<String>().front() == c.front())
              {
                Node n = nm->mkNode(STRING_TO_REGEXP,
                                    Word::getLength(tmp) == 1
                                        ? d_emptyString
                                        : Word::substr(tmp, 1));
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
        uint32_t l = utils::getLoopMinOccurrences(r);
        uint32_t u = utils::getLoopMaxOccurrences(r);
        if (l == u && l == 0)
        {
          ret = 2;
          //retNode = d_emptyRegexp;
        } else {
          Node dc;
          ret = derivativeS(r[0], c, dc);
          if(dc==d_emptyRegexp) {
            Node lop = nm->mkConst(RegExpLoop(l == 0 ? 0 : (l - 1), u - 1));
            Node r2 = nm->mkNode(REGEXP_LOOP, lop, r[0]);
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
        Assert(!utils::isRegExpKind(r.getKind()));
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
  NodeManager* nm = NodeManager::currentNM();
  if( d_dv_cache.find( dv ) != d_dv_cache.end() ) {
    retNode = d_dv_cache[dv];
  }
  else if (c.empty())
  {
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
            if (r[0].getConst<String>().front() == c.front())
            {
              retNode = nm->mkNode(STRING_TO_REGEXP,
                                   Word::getLength(r[0]) == 1
                                       ? d_emptyString
                                       : Word::substr(r[0], 1));
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
        uint32_t l = utils::getLoopMinOccurrences(r);
        uint32_t u = utils::getLoopMaxOccurrences(r);
        if (l == u || l == 0)
        {
          retNode = d_emptyRegexp;
        } else {
          Node dc = derivativeSingle(r[0], c);
          if(dc != d_emptyRegexp) {
            Node lop = nm->mkConst(RegExpLoop(l == 0 ? 0 : (l - 1), u - 1));
            Node r2 = nm->mkNode(REGEXP_LOOP, lop, r[0]);
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
        unsigned b = r[1].getConst<String>().front();
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
          String s = st.getConst<String>();
          if(s.size() != 0) {
            unsigned sc = s.front();
            cset.insert(sc);
          }
        }
        else if (st.getKind() == kind::STRING_CONCAT)
        {
          if(st[0].isConst()) {
            String s = st[0].getConst<String>();
            unsigned sc = s.front();
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
          if (delta(n, exp) != 1)
          {
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
        Assert(utils::isRegExpKind(k));
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
    for (std::set<unsigned>::const_iterator it = pcset.begin();
         it != pcset.end();
         ++it)
    {
      if (it != pcset.begin())
      {
        Trace("regexp-fset") << ",";
      }
      Trace("regexp-fset") << (*it);
      }
    Trace("regexp-fset") << "}" << std::endl;
  }
}

Node RegExpOpr::simplify(Node t, bool polarity)
{
  Trace("strings-regexp-simpl")
      << "RegExpOpr::simplify: " << t << ", polarity=" << polarity << std::endl;
  Assert(t.getKind() == kind::STRING_IN_REGEXP);
  Node tlit = polarity ? t : t.notNode();
  Node conc;
  std::map<Node, Node>::const_iterator itr = d_simpCache.find(tlit);
  if (itr != d_simpCache.end())
  {
    return itr->second;
  }
  if (polarity)
  {
    std::vector<Node> newSkolems;
    conc = reduceRegExpPos(tlit, d_sc, newSkolems);
  }
  else
  {
    // see if we can use an optimized version of the reduction for re.++.
    Node r = t[1];
    if (r.getKind() == REGEXP_CONCAT)
    {
      // the index we are removing from the RE concatenation
      size_t index = 0;
      // As an optimization to the reduction, if we can determine that
      // all strings in the language of R1 have the same length, say n,
      // then the conclusion of the reduction is quantifier-free:
      //    ~( substr(s,0,n) in R1 ) OR ~( substr(s,n,len(s)-n) in R2)
      Node reLen = getRegExpConcatFixed(r, index);
      if (!reLen.isNull())
      {
        conc = reduceRegExpNegConcatFixed(tlit, reLen, index);
      }
    }
    if (conc.isNull())
    {
      conc = reduceRegExpNeg(tlit);
    }
  }
  d_simpCache[tlit] = conc;
  Trace("strings-regexp-simpl")
      << "RegExpOpr::simplify: returns " << conc << std::endl;
  return conc;
}

Node RegExpOpr::getRegExpConcatFixed(Node r, size_t& index)
{
  Assert(r.getKind() == REGEXP_CONCAT);
  index = 0;
  Node reLen = RegExpEntail::getFixedLengthForRegexp(r[0]);
  if (!reLen.isNull())
  {
    return reLen;
  }
  // try from the opposite end
  size_t indexE = r.getNumChildren() - 1;
  reLen = RegExpEntail::getFixedLengthForRegexp(r[indexE]);
  if (!reLen.isNull())
  {
    index = indexE;
    return reLen;
  }
  return Node::null();
}

Node RegExpOpr::reduceRegExpNeg(Node mem)
{
  Assert(mem.getKind() == NOT && mem[0].getKind() == STRING_IN_REGEXP);
  Node s = mem[0][0];
  Node r = mem[0][1];
  NodeManager* nm = NodeManager::currentNM();
  Kind k = r.getKind();
  Node zero = nm->mkConst(Rational(0));
  Node conc;
  if (k == REGEXP_CONCAT)
  {
    // do not use length entailment, call regular expression concat
    Node reLen;
    size_t i = 0;
    conc = reduceRegExpNegConcatFixed(mem, reLen, i);
  }
  else if (k == REGEXP_STAR)
  {
    Node emp = Word::mkEmptyWord(s.getType());
    Node lens = nm->mkNode(STRING_LENGTH, s);
    Node sne = s.eqNode(emp).negate();
    Node b1 = nm->mkBoundVar(nm->integerType());
    Node b1v = nm->mkNode(BOUND_VAR_LIST, b1);
    Node g1 =
        nm->mkNode(AND, nm->mkNode(GT, b1, zero), nm->mkNode(GEQ, lens, b1));
    // internal
    Node s1 = nm->mkNode(STRING_SUBSTR, s, zero, b1);
    Node s2 = nm->mkNode(STRING_SUBSTR, s, b1, nm->mkNode(MINUS, lens, b1));
    Node s1r1 = nm->mkNode(STRING_IN_REGEXP, s1, r[0]).negate();
    Node s2r2 = nm->mkNode(STRING_IN_REGEXP, s2, r).negate();

    conc = nm->mkNode(OR, s1r1, s2r2);
    conc = nm->mkNode(IMPLIES, g1, conc);
    conc = nm->mkNode(FORALL, b1v, conc);
    conc = nm->mkNode(AND, sne, conc);
  }
  else
  {
    Assert(!utils::isRegExpKind(k));
  }
  return conc;
}

Node RegExpOpr::reduceRegExpNegConcatFixed(Node mem, Node reLen, size_t index)
{
  Assert(mem.getKind() == NOT && mem[0].getKind() == STRING_IN_REGEXP);
  Node s = mem[0][0];
  Node r = mem[0][1];
  NodeManager* nm = NodeManager::currentNM();
  Assert(r.getKind() == REGEXP_CONCAT);
  Node zero = nm->mkConst(Rational(0));
  // The following simplification states that
  //    ~( s in R1 ++ R2 ++... ++ Rn )
  // is equivalent to
  //    forall x.
  //      0 <= x <= len(s) =>
  //        ~(substr(s,0,x) in R1) OR ~(substr(s,x,len(s)-x) in R2 ++ ... ++ Rn)
  // Index is the child index of r that we are stripping off, which is either
  // from the beginning or the end.
  Assert(index == 0 || index == r.getNumChildren() - 1);
  Node lens = nm->mkNode(STRING_LENGTH, s);
  Node b1;
  Node b1v;
  Node guard;
  if (reLen.isNull())
  {
    b1 = SkolemCache::mkIndexVar(mem);
    b1v = nm->mkNode(BOUND_VAR_LIST, b1);
    guard = nm->mkNode(AND,
                       nm->mkNode(GEQ, b1, zero),
                       nm->mkNode(GEQ, nm->mkNode(STRING_LENGTH, s), b1));
  }
  else
  {
    b1 = reLen;
  }
  Node s1;
  Node s2;
  if (index == 0)
  {
    s1 = nm->mkNode(STRING_SUBSTR, s, zero, b1);
    s2 = nm->mkNode(STRING_SUBSTR, s, b1, nm->mkNode(MINUS, lens, b1));
  }
  else
  {
    s1 = nm->mkNode(STRING_SUBSTR, s, nm->mkNode(MINUS, lens, b1), b1);
    s2 = nm->mkNode(STRING_SUBSTR, s, zero, nm->mkNode(MINUS, lens, b1));
  }
  Node s1r1 = nm->mkNode(STRING_IN_REGEXP, s1, r[index]).negate();
  std::vector<Node> nvec;
  for (unsigned i = 0, nchild = r.getNumChildren(); i < nchild; i++)
  {
    if (i != index)
    {
      nvec.push_back(r[i]);
    }
  }
  Node r2 = nvec.size() == 1 ? nvec[0] : nm->mkNode(REGEXP_CONCAT, nvec);
  r2 = Rewriter::rewrite(r2);
  Node s2r2 = nm->mkNode(STRING_IN_REGEXP, s2, r2).negate();
  Node conc = nm->mkNode(OR, s1r1, s2r2);
  if (!b1v.isNull())
  {
    conc = nm->mkNode(OR, guard.negate(), conc);
    conc = nm->mkNode(FORALL, b1v, conc);
  }
  return conc;
}

Node RegExpOpr::reduceRegExpPos(Node mem,
                                SkolemCache* sc,
                                std::vector<Node>& newSkolems)
{
  Assert(mem.getKind() == STRING_IN_REGEXP);
  Node s = mem[0];
  Node r = mem[1];
  NodeManager* nm = NodeManager::currentNM();
  Kind k = r.getKind();
  Node conc;
  if (k == REGEXP_CONCAT)
  {
    std::vector<Node> nvec;
    std::vector<Node> cc;
    // get the (valid) existential for this membership
    Node eform = getExistsForRegExpConcatMem(mem);
    SkolemManager* sm = nm->getSkolemManager();
    // Notice that this rule does not introduce witness terms, instead it
    // uses skolems in the conclusion of the proof rule directly. Thus,
    // the existential eform does not need to be explicitly justified by a
    // proof here, since it is only being used as an intermediate formula in
    // this inference. Hence we do not pass a proof generator to mkSkolemize.
    sm->mkSkolemize(eform, newSkolems, "rc", "regexp concat skolem");
    Assert(newSkolems.size() == r.getNumChildren());
    // Look up skolems for each of the components. If sc has optimizations
    // enabled, this will return arguments of str.to_re.
    for (unsigned i = 0, nchild = r.getNumChildren(); i < nchild; ++i)
    {
      if (r[i].getKind() == STRING_TO_REGEXP)
      {
        // optimization, just take the body
        newSkolems[i] = r[i][0];
      }
      else
      {
        nvec.push_back(nm->mkNode(STRING_IN_REGEXP, newSkolems[i], r[i]));
      }
    }
    // (str.in_re x (re.++ R1 .... Rn)) =>
    // (and (str.in_re k1 R1) ... (str.in_re kn Rn) (= x (str.++ k1 ... kn)))
    Node lem = s.eqNode(nm->mkNode(STRING_CONCAT, newSkolems));
    nvec.push_back(lem);
    conc = nvec.size() == 1 ? nvec[0] : nm->mkNode(AND, nvec);
  }
  else if (k == REGEXP_STAR)
  {
    Node emp = Word::mkEmptyWord(s.getType());
    Node se = s.eqNode(emp);
    Node sinr = nm->mkNode(STRING_IN_REGEXP, s, r[0]);
    Node reExpand = nm->mkNode(REGEXP_CONCAT, r[0], r, r[0]);
    Node sinRExp = nm->mkNode(STRING_IN_REGEXP, s, reExpand);
    // We unfold `x in R*` by considering three cases: `x` is empty, `x`
    // is matched by `R`, or `x` is matched by two or more `R`s. For the
    // last case, `x` will break into three pieces, making the beginning
    // and the end each match `R` and the middle match `R*`. Matching the
    // beginning and the end with `R` allows us to reason about the
    // beginning and the end of `x` simultaneously.
    //
    // x in R* ---> (x = "") v (x in R) v (x in (re.++ R (re.* R) R))

    // We also immediately unfold the last disjunct for re.*. The advantage
    // of doing this is that we use the same scheme for skolems above.
    std::vector<Node> newSkolemsC;
    sinRExp = reduceRegExpPos(sinRExp, sc, newSkolemsC);
    Assert(newSkolemsC.size() == 3);
    // make the return lemma
    // can also assume the component match the first and last R are non-empty.
    // This means that the overall conclusion is:
    //   (x = "") v (x in R) v (x = (str.++ k1 k2 k3) ^
    //                          k1 in R ^ k2 in (re.* R) ^ k3 in R ^
    //                          k1 != ""  ^ k3 != "")
    conc = nm->mkNode(OR,
                      se,
                      sinr,
                      nm->mkNode(AND,
                                 sinRExp,
                                 newSkolemsC[0].eqNode(emp).negate(),
                                 newSkolemsC[2].eqNode(emp).negate()));
  }
  else
  {
    Assert(!utils::isRegExpKind(k));
  }
  return conc;
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

Node RegExpOpr::intersectInternal( Node r1, Node r2, std::map< PairNodes, Node > cache, unsigned cnt ) {
  //Assert(checkConstRegExp(r1) && checkConstRegExp(r2));
  if(r1 > r2) {
    TNode tmpNode = r1;
    r1 = r2;
    r2 = tmpNode;
  }
  Trace("regexp-int") << "Starting INTERSECT(" << cnt << "):\n  "<< mkString(r1) << ",\n  " << mkString(r2) << std::endl;
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
          for (std::vector<unsigned>::const_iterator it = cset.begin();
               it != cset.end();
               ++it)
          {
            if (it != cset.begin())
            {
              Trace("regexp-int-debug") << ", ";
            }
            Trace("regexp-int-debug") << (*it);
          }
          Trace("regexp-int-debug") << std::endl;
        }
        std::map< PairNodes, Node > cacheX;
        for (std::vector<unsigned>::const_iterator it = cset.begin();
             it != cset.end();
             ++it)
        {
          std::vector<unsigned> cvec;
          cvec.push_back(*it);
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
    if (!expr::hasSubtermKind(REGEXP_RV, rNode))
    {
      d_inter_cache[p] = rNode;
    }
  }
  Trace("regexp-int") << "End(" << cnt << ") of INTERSECT( " << mkString(r1) << ", " << mkString(r2) << " ) = " << mkString(rNode) << std::endl;
  return rNode;
}

Node RegExpOpr::removeIntersection(Node r) {
  Assert(checkConstRegExp(r));
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(r);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      Kind ck = cur.getKind();
      Node ret;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        if (ck == REGEXP_INTER)
        {
          if (ret.isNull())
          {
            ret = it->second;
          }
          else
          {
            ret = intersect(ret, it->second);
          }
        }
        else
        {
          // will construct below
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
      }
      if (ck != REGEXP_INTER)
      {
        if (childChanged)
        {
          ret = nm->mkNode(cur.getKind(), children);
        }
        else
        {
          ret = cur;
        }
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(r) != visited.end());
  Assert(!visited.find(r)->second.isNull());
  if (Trace.isOn("regexp-intersect"))
  {
    Trace("regexp-intersect") << "Remove INTERSECTION( " << mkString(r)
                              << " ) = " << mkString(visited[r]) << std::endl;
  }
  return visited[r];
}

Node RegExpOpr::intersect(Node r1, Node r2)
{
  if (!checkConstRegExp(r1) || !checkConstRegExp(r2))
  {
    return Node::null();
  }
  Node rr1 = removeIntersection(r1);
  Node rr2 = removeIntersection(r2);
  std::map<PairNodes, Node> cache;
  Trace("regexp-intersect-node") << "Intersect (1): " << rr1 << std::endl;
  Trace("regexp-intersect-node") << "Intersect (2): " << rr2 << std::endl;
  Trace("regexp-intersect") << "Start INTERSECTION(\n\t" << mkString(r1)
                            << ",\n\t" << mkString(r2) << ")" << std::endl;
  Node retNode = intersectInternal(rr1, rr2, cache, 1);
  Trace("regexp-intersect")
      << "End INTERSECTION(\n\t" << mkString(r1) << ",\n\t" << mkString(r2)
      << ") =\n\t" << mkString(retNode) << std::endl;
  Trace("regexp-intersect-node") << "Intersect finished." << std::endl;
  return retNode;
}

//printing
std::string RegExpOpr::niceChar(Node r) {
  if(r.isConst()) {
    std::string s = r.getConst<String>().toString();
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
        uint32_t l = utils::getLoopMinOccurrences(r);
        std::stringstream ss;
        ss << "(" << mkString(r[0]) << "){" << l << ",";
        if(r.getNumChildren() == 3) {
          uint32_t u = utils::getLoopMaxOccurrences(r);
          ss << u;
        }
        ss << "}";
        retStr += ss.str();
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
        Assert(!utils::isRegExpKind(r.getKind()));
        break;
      }
    }
  }

  return retStr;
}

bool RegExpOpr::regExpIncludes(Node r1, Node r2)
{
  const auto& it = d_inclusionCache.find(std::make_pair(r1, r2));
  if (it != d_inclusionCache.end())
  {
    return (*it).second;
  }
  bool result = RegExpEntail::regExpIncludes(r1, r2);
  d_inclusionCache[std::make_pair(r1, r2)] = result;
  return result;
}

/**
 * Associating formulas with their "exists form", or an existentially
 * quantified formula that is equivalent to it. This is currently used
 * for regular expression memberships in the method below.
 */
struct ExistsFormAttributeId
{
};
typedef expr::Attribute<ExistsFormAttributeId, Node> ExistsFormAttribute;

Node RegExpOpr::getExistsForRegExpConcatMem(Node mem)
{
  // get or make the exists form of the membership
  ExistsFormAttribute efa;
  if (mem.hasAttribute(efa))
  {
    // already computed
    return mem.getAttribute(efa);
  }
  Assert(mem.getKind() == STRING_IN_REGEXP);
  Node x = mem[0];
  Node r = mem[1];
  Assert(r.getKind() == REGEXP_CONCAT);
  NodeManager* nm = NodeManager::currentNM();
  TypeNode xtn = x.getType();
  std::vector<Node> vars;
  std::vector<Node> mems;
  for (const Node& rc : r)
  {
    Node v = nm->mkBoundVar(xtn);
    vars.push_back(v);
    mems.push_back(nm->mkNode(STRING_IN_REGEXP, v, rc));
  }
  Node sconcat = nm->mkNode(STRING_CONCAT, vars);
  Node eq = x.eqNode(sconcat);
  mems.insert(mems.begin(), eq);
  Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  Node ebody = nm->mkNode(AND, mems);
  Node eform = nm->mkNode(EXISTS, bvl, ebody);
  mem.setAttribute(efa, eform);
  Trace("regexp-opr") << "Exists form " << mem << " : " << eform << std::endl;
  return eform;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
