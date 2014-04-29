/*********************                                                        */

/*! \file regexp_operation.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Symbolic Regular Expresion Operations
 **
 ** Symbolic Regular Expresion Operations
 **/

#include "theory/strings/regexp_operation.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace strings {

RegExpOpr::RegExpOpr() {
  d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  d_zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
  d_one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
  d_emptySingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString );
  std::vector< Node > nvec;
  d_emptyRegexp = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
  d_sigma = NodeManager::currentNM()->mkNode( kind::REGEXP_SIGMA, nvec );
  d_sigma_star = NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, d_sigma );
  d_card = 256;
}

int RegExpOpr::gcd ( int a, int b ) {
  int c;
  while ( a != 0 ) {
     c = a; a = b%a;  b = c;
  }
  return b;
}

bool RegExpOpr::checkConstRegExp( Node r ) {
  Trace("strings-regexp-cstre") << "RegExp-CheckConstRegExp starts with " << mkString( r ) << std::endl;
  bool ret = true;
  if( d_cstre_cache.find( r ) != d_cstre_cache.end() ) {
    ret = d_cstre_cache[r];
  } else {
    if(r.getKind() == kind::STRING_TO_REGEXP) {
      Node tmp = Rewriter::rewrite( r[0] );
      ret = tmp.isConst();
    } else {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(!checkConstRegExp(r[i])) {
          ret = false; break;
        }
      }
    }
    d_cstre_cache[r] = ret;
  }
  return ret;
}

// 0-unknown, 1-yes, 2-no
int RegExpOpr::delta( Node r, Node &exp ) {
  Trace("regexp-delta") << "RegExp-Delta starts with " << mkString( r ) << std::endl;
  int ret = 0;
  if( d_delta_cache.find( r ) != d_delta_cache.end() ) {
    ret = d_delta_cache[r].first;
    exp = d_delta_cache[r].second;
  } else {
    int k = r.getKind();
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
      default: {
        Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in delta of RegExp." << std::endl;
        Assert( false );
        //return Node::null();
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
  Assert( c.size() < 2 );
  Trace("regexp-deriv") << "RegExp-deriv starts with R{ " << mkString( r ) << " }, c=" << c << std::endl;

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
      case kind::STRING_TO_REGEXP: {
        Node tmp = Rewriter::rewrite(r[0]);
        if(tmp.isConst()) {
          if(tmp == d_emptyString) {
            ret = 2;
          } else {
            if(tmp.getConst< CVC4::String >().getFirstChar() == c.getFirstChar()) {
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
              if(t2.getConst< CVC4::String >().getFirstChar() == c.getFirstChar()) {
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
          Trace("regexp-deriv") << "RegExp-deriv OR R[" << i << "]{ " << mkString(r[i]) << " returns " << mkString(dc) << std::endl;
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
      default: {
        Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in derivative of RegExp." << std::endl;
        Assert( false, "Unsupported Term" );
      }
    }
    if(retNode != d_emptyRegexp) {
      retNode = Rewriter::rewrite( retNode );
    }
    std::pair< Node, int > p(retNode, ret);
    d_deriv_cache[dv] = p;
  }

  Trace("regexp-deriv") << "RegExp-deriv returns : " << mkString( retNode ) << std::endl;
  return ret;
}

Node RegExpOpr::derivativeSingle( Node r, CVC4::String c ) {
  Assert( c.size() < 2 );
  Trace("regexp-deriv") << "RegExp-deriv starts with R{ " << mkString( r ) << " }, c=" << c << std::endl;
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
    int k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        retNode = d_emptyRegexp;
        break;
      }
      case kind::REGEXP_SIGMA: {
        retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString );
        break;
      }
      case kind::STRING_TO_REGEXP: {
        if(r[0].isConst()) {
          if(r[0] == d_emptyString) {
            retNode = d_emptyRegexp;
          } else {
            if(r[0].getConst< CVC4::String >().getFirstChar() == c.getFirstChar()) {
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
          Trace("regexp-deriv") << "RegExp-deriv OR R[" << i << "]{ " << mkString(r[i]) << " returns " << mkString(dc) << std::endl;
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
          retNode = dc==NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, d_emptyString ) ? r : NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, dc, r );
        } else {
          retNode = d_emptyRegexp;
        }
        break;
      }
      default: {
        //TODO: special sym: sigma, none, all
        Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in derivative of RegExp." << std::endl;
        Assert( false, "Unsupported Term" );
        //return Node::null();
      }
    }
    if(retNode != d_emptyRegexp) {
      retNode = Rewriter::rewrite( retNode );
    }
    d_dv_cache[dv] = retNode;
  }
  Trace("regexp-deriv") << "RegExp-deriv returns : " << mkString( retNode ) << std::endl;
  return retNode;
}

//TODO:
bool RegExpOpr::guessLength( Node r, int &co ) {
  int k = r.getKind();
  switch( k ) {
    case kind::STRING_TO_REGEXP:
    {
      if(r[0].isConst()) {
        co += r[0].getConst< CVC4::String >().size();
        return true;
      } else {
        return false;
      }
    }
      break;
    case kind::REGEXP_CONCAT:
    {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(!guessLength( r[i], co)) {
          return false;
        }
      }
      return true;
    }
      break;
    case kind::REGEXP_UNION:
    {
      int g_co;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        int cop = 0;
        if(!guessLength( r[i], cop)) {
          return false;
        }
        if(i == 0) {
          g_co = cop;
        } else {
          g_co = gcd(g_co, cop);
        }
      }
      return true;
    }
      break;
    case kind::REGEXP_INTER:
    {
      int g_co;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        int cop = 0;
        if(!guessLength( r[i], cop)) {
          return false;
        }
        if(i == 0) {
          g_co = cop;
        } else {
          g_co = gcd(g_co, cop);
        }
      }
      return true;
    }
      break;
    case kind::REGEXP_STAR:
    {
      co = 0;
      return true;
    }
      break;
    default:
      Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in membership of RegExp." << std::endl;
      return false;
  }
}

void RegExpOpr::firstChars( Node r, std::set<unsigned> &pcset, SetNodes &pvset ) {
  std::map< Node, std::pair< std::set<unsigned>, SetNodes > >::const_iterator itr = d_fset_cache.find(r);
  if(itr != d_fset_cache.end()) {
    pcset.insert((itr->second).first.begin(), (itr->second).first.end());
    pvset.insert((itr->second).second.begin(), (itr->second).second.end());
  } else {
    std::set<unsigned> cset;
    SetNodes vset;
    int k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        break;
      }
      case kind::REGEXP_SIGMA: {
        for(unsigned i=0; i<d_card; i++) {
          cset.insert(i);
        }
        break;
      }
      case kind::STRING_TO_REGEXP: {
        Node st = Rewriter::rewrite(r[0]);
        if(st.isConst()) {
          CVC4::String s = st.getConst< CVC4::String >();
          if(s.size() != 0) {
            cset.insert(s[0]);
          }
        } else if(st.getKind() == kind::VARIABLE) {
          vset.insert( st );
        } else {
          if(st[0].isConst()) {
            CVC4::String s = st[0].getConst< CVC4::String >();
            cset.insert(s[0]);
          } else {
            vset.insert( st[0] );
          }
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
        for(unsigned i=0; i<r.getNumChildren(); i++) {
          firstChars(r[i], cset, vset);
        }
        break;
      }
      case kind::REGEXP_STAR: {
        firstChars(r[0], cset, vset);
        break;
      }
      default: {
        Trace("strings-regexp") << "Unsupported term: " << r << " in getCharSet." << std::endl;
        Assert( false, "Unsupported Term" );
      }
    }
    pcset.insert(cset.begin(), cset.end());
    pvset.insert(vset.begin(), vset.end());
    std::pair< std::set<unsigned>, SetNodes > p(cset, vset);
    d_fset_cache[r] = p;

    Trace("regexp-fset") << "FSET( " << mkString(r) << " ) = { ";
    for(std::set<unsigned>::const_iterator itr = cset.begin();
      itr != cset.end(); itr++) {
        Trace("regexp-fset") << CVC4::String::convertUnsignedIntToChar(*itr) << ",";
      }
    Trace("regexp-fset") << " }" << std::endl;
  }
}

bool RegExpOpr::follow( Node r, CVC4::String c, std::vector< char > &vec_chars ) {
  int k = r.getKind();
  switch( k ) {
    case kind::STRING_TO_REGEXP:
    {
      if(r[0].isConst()) {
        if(r[0] != d_emptyString) {
          char t1 = r[0].getConst< CVC4::String >().getFirstChar();
          if(c.isEmptyString()) {
            vec_chars.push_back( t1 );
            return true;
          } else {
            char t2 = c.getFirstChar();
            if(t1 != t2) {
              return false;
            } else {
              if(c.size() >= 2) {
                vec_chars.push_back( c.substr(1,1).getFirstChar() );
              } else {
                vec_chars.push_back( '\0' );
              }
              return true;
            }
          }
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
      break;
    case kind::REGEXP_CONCAT:
    {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if( follow(r[i], c, vec_chars) ) {
          if(vec_chars[vec_chars.size() - 1] == '\0') {
            vec_chars.pop_back();
            c = d_emptyString.getConst< CVC4::String >();
          }
        } else {
          return false;
        }
      }
      vec_chars.push_back( '\0' );
      return true;
    }
      break;
    case kind::REGEXP_UNION:
    {
      bool flag = false;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if( follow(r[i], c, vec_chars) ) {
          flag=true;
        }
      }
      return flag;
    }
      break;
    case kind::REGEXP_INTER:
    {
      std::vector< char > vt2;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        std::vector< char > v_tmp;
        if( !follow(r[i], c, v_tmp) ) {
          return false;
        }
        std::vector< char > vt3(vt2);
        vt2.clear();
        std::set_intersection( vt3.begin(), vt3.end(), v_tmp.begin(), v_tmp.end(), vt2.begin() );
        if(vt2.size() == 0) {
          return false;
        }
      }
      vec_chars.insert( vec_chars.end(), vt2.begin(), vt2.end() );
      return true;
    }
      break;
    case kind::REGEXP_STAR:
    {
      if(follow(r[0], c, vec_chars)) {
        if(vec_chars[vec_chars.size() - 1] == '\0') {
          if(c.isEmptyString()) {
            return true;
          } else {
            vec_chars.pop_back();
            c = d_emptyString.getConst< CVC4::String >();
            return follow(r[0], c, vec_chars);
          }
        } else {
          return true;
        }
      } else {
        vec_chars.push_back( '\0' );
        return true;
      }
    }
      break;
    default: {
      Trace("strings-error") << "Unsupported term: " << mkString( r ) << " in delta of RegExp." << std::endl;
      //AlwaysAssert( false );
      //return Node::null();
      return false;
    }
  }
}

Node RegExpOpr::mkAllExceptOne( char exp_c ) {
  std::vector< Node > vec_nodes;
  for(char c=d_char_start; c<=d_char_end; ++c) {
    if(c != exp_c ) {
      Node n = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String( c ) ) );
      vec_nodes.push_back( n );
    }
  }
  return NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
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
  std::map < std::pair< Node, Node >, Node >::const_iterator itr = d_simpl_neg_cache.find(p);
  if(itr != d_simpl_neg_cache.end()) {
    new_nodes.push_back( itr->second );
  } else {
    int k = r.getKind();
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
      case kind::STRING_TO_REGEXP: {
        conc = s.eqNode(r[0]).negate();
        break;
      }
      case kind::REGEXP_CONCAT: {
        //TODO: rewrite empty
        Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s);
        Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
        Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
        Node g1 = NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode(kind::GEQ, b1, d_zero),
              NodeManager::currentNM()->mkNode( kind::GEQ, NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s), b1 ) );
        Node s1 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, s, d_zero, b1));
        Node s2 = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, s, b1, NodeManager::currentNM()->mkNode(kind::MINUS, lens, b1)));
        Node s1r1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s1, r[0]).negate();
        if(r[0].getKind() == kind::STRING_TO_REGEXP) {
          s1r1 = s1.eqNode(r[0][0]).negate();
        } else if(r[0].getKind() == kind::REGEXP_EMPTY) {
          s1r1 = d_true;
        }
        Node r2 = r[1];
        if(r.getNumChildren() > 2) {
          std::vector< Node > nvec;
          for(unsigned i=1; i<r.getNumChildren(); i++) {
            nvec.push_back( r[i] );
          }
          r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, nvec);
        }
        r2 = Rewriter::rewrite(r2);
        Node s2r2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s2, r2).negate();
        if(r2.getKind() == kind::STRING_TO_REGEXP) {
          s2r2 = s2.eqNode(r2[0]).negate();
        } else if(r2.getKind() == kind::REGEXP_EMPTY) {
          s2r2 = d_true;
        }

        conc = NodeManager::currentNM()->mkNode(kind::OR, s1r1, s2r2);
        conc = NodeManager::currentNM()->mkNode(kind::IMPLIES, g1, conc);
        conc = NodeManager::currentNM()->mkNode(kind::FORALL, b1v, conc);
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
          Node s1 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, s, d_zero, b1);
          Node s2 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, s, b1, NodeManager::currentNM()->mkNode(kind::MINUS, lens, b1));
          Node s1r1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s1, r[0]).negate();
          Node s2r2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s2, r).negate();

          conc = NodeManager::currentNM()->mkNode(kind::OR, s1r1, s2r2);
          conc = NodeManager::currentNM()->mkNode(kind::IMPLIES, g1, conc);
          conc = NodeManager::currentNM()->mkNode(kind::FORALL, b1v, conc);
          conc = NodeManager::currentNM()->mkNode(kind::AND, sne, conc);
        }
        break;
      }
      default: {
        Trace("strings-regexp") << "Unsupported term: " << r << " in simplifyNRegExp." << std::endl;
        Assert( false, "Unsupported Term" );
      }
    }
    conc = Rewriter::rewrite( conc );
    new_nodes.push_back( conc );
    d_simpl_neg_cache[p] = conc;
  }
}
void RegExpOpr::simplifyPRegExp( Node s, Node r, std::vector< Node > &new_nodes ) {
  std::pair < Node, Node > p(s, r);
  std::map < std::pair< Node, Node >, Node >::const_iterator itr = d_simpl_cache.find(p);
  if(itr != d_simpl_cache.end()) {
    new_nodes.push_back( itr->second );
  } else {
    int k = r.getKind();
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
          Node se = s.eqNode(d_emptyString);
          Node sinr = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s, r[0]);
          Node sk1 = NodeManager::currentNM()->mkSkolem( "rs", s.getType(), "created for regular expression star" );
          Node sk2 = NodeManager::currentNM()->mkSkolem( "rs", s.getType(), "created for regular expression star" );
          Node s1nz = sk1.eqNode(d_emptyString).negate();
          Node s2nz = sk2.eqNode(d_emptyString).negate();
          Node s1inr = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk1, r[0]);
          Node s2inrs = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, sk2, r);
          Node s12 = s.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, sk1, sk2));

          conc = NodeManager::currentNM()->mkNode(kind::AND, s12, s1nz, s2nz, s1inr, s2inrs);
          conc = NodeManager::currentNM()->mkNode(kind::OR, se, sinr, conc);
        }
        break;
      }
      default: {
        Trace("strings-regexp") << "Unsupported term: " << r << " in simplifyPRegExp." << std::endl;
        Assert( false, "Unsupported Term" );
      }
    }
    conc = Rewriter::rewrite( conc );
    new_nodes.push_back( conc );
    d_simpl_cache[p] = conc;
  }
}

void RegExpOpr::getCharSet( Node r, std::set<unsigned> &pcset, SetNodes &pvset ) {
  std::map< Node, std::pair< std::set<unsigned>, SetNodes > >::const_iterator itr = d_cset_cache.find(r);
  if(itr != d_cset_cache.end()) {
    pcset.insert((itr->second).first.begin(), (itr->second).first.end());
    pvset.insert((itr->second).second.begin(), (itr->second).second.end());
  } else {
    std::set<unsigned> cset;
    SetNodes vset;
    int k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        break;
      }
      case kind::REGEXP_SIGMA: {
        for(unsigned i=0; i<d_card; i++) {
          cset.insert(i);
        }
        break;
      }
      case kind::STRING_TO_REGEXP: {
        Node st = Rewriter::rewrite(r[0]);
        if(st.isConst()) {
          CVC4::String s = st.getConst< CVC4::String >();
          s.getCharSet( cset );
        } else if(st.getKind() == kind::VARIABLE) {
          vset.insert( st );
        } else {
          for(unsigned i=0; i<st.getNumChildren(); i++) {
            if(st[i].isConst()) {
              CVC4::String s = st[i].getConst< CVC4::String >();
              s.getCharSet( cset );
            } else {
              vset.insert( st[i] );
            }
          }
        }
        break;
      }
      case kind::REGEXP_CONCAT: {
        for(unsigned i=0; i<r.getNumChildren(); i++) {
          getCharSet(r[i], cset, vset);
        }
        break;
      }
      case kind::REGEXP_UNION: {
        for(unsigned i=0; i<r.getNumChildren(); i++) {
          getCharSet(r[i], cset, vset);
        }
        break;
      }
      case kind::REGEXP_INTER: {
        //TODO: Overapproximation for now
        for(unsigned i=0; i<r.getNumChildren(); i++) {
          getCharSet(r[i], cset, vset);
        }
        break;
      }
      case kind::REGEXP_STAR: {
        getCharSet(r[0], cset, vset);
        break;
      }
      default: {
        Trace("strings-regexp") << "Unsupported term: " << r << " in getCharSet." << std::endl;
        Assert( false, "Unsupported Term" );
      }
    }
    pcset.insert(cset.begin(), cset.end());
    pvset.insert(vset.begin(), vset.end());
    std::pair< std::set<unsigned>, SetNodes > p(cset, vset);
    d_cset_cache[r] = p;

    Trace("regexp-cset") << "CSET( " << mkString(r) << " ) = { ";
    for(std::set<unsigned>::const_iterator itr = cset.begin();
      itr != cset.end(); itr++) {
        Trace("regexp-cset") << CVC4::String::convertUnsignedIntToChar(*itr) << ",";
      }
    Trace("regexp-cset") << " }" << std::endl;
  }
}


Node RegExpOpr::intersectInternal( Node r1, Node r2, std::map< unsigned, std::set< PairNodes > > cache, bool &spflag ) {
  if(spflag) {
    //TODO: var
    return Node::null();
  }
  std::pair < Node, Node > p(r1, r2);
  std::map < std::pair< Node, Node >, Node >::const_iterator itr = d_inter_cache.find(p);
  Node rNode;
  if(itr != d_inter_cache.end()) {
    rNode = itr->second;
  } else {
    if(r1 == r2) {
      rNode = r1;
    } else if(r1 == d_emptyRegexp || r2 == d_emptyRegexp) {
      rNode = d_emptyRegexp;
    } else if(r1 == d_emptySingleton || r2 == d_emptySingleton) {
      Node exp;
      int r = delta((r1 == d_emptySingleton ? r2 : r1), exp);
      if(r == 0) {
        //TODO: variable
        spflag = true;
      } else if(r == 1) {
        rNode = d_emptySingleton;
      } else {
        rNode = d_emptyRegexp;
      }
    } else {
      std::set< unsigned > cset, cset2;
      std::set< Node > vset, vset2;
      getCharSet(r1, cset, vset);
      getCharSet(r2, cset2, vset2);
      if(vset.empty() && vset2.empty()) {
        cset.clear();
        firstChars(r1, cset, vset);
        std::vector< Node > vec_nodes;
        for(std::set<unsigned>::const_iterator itr = cset.begin();
          itr != cset.end(); itr++) {
          CVC4::String c( CVC4::String::convertUnsignedIntToChar(*itr) );
          std::pair< Node, Node > p(r1, r2);
          if(cache[ *itr ].find(p) == cache[ *itr ].end()) {
            Node r1l = derivativeSingle(r1, c);
            Node r2l = derivativeSingle(r2, c);
            std::map< unsigned, std::set< PairNodes > > cache2(cache);
            PairNodes p(r1l, r2l);
            cache2[ *itr ].insert( p );
            Node rt = intersectInternal(r1l, r2l, cache2, spflag);
            if(spflag) {
              //TODO:
              return Node::null();
            }
            rt = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
              NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(c)), rt) );
            vec_nodes.push_back(rt);
          }
        }
        rNode = vec_nodes.size()==0 ? d_emptyRegexp : vec_nodes.size()==1 ? vec_nodes[0] :
            NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec_nodes);
        rNode = Rewriter::rewrite( rNode );
      } else {
        //TODO: non-empty var set
        spflag = true;
      }
    }
    d_inter_cache[p] = rNode;
  }
  Trace("regexp-intersect") << "INTERSECT( " << mkString(r1) << ", " << mkString(r2) << " ) = " << mkString(rNode) << std::endl;
  return rNode;
}
Node RegExpOpr::intersect(Node r1, Node r2, bool &spflag) {
  std::map< unsigned, std::set< PairNodes > > cache;
  return intersectInternal(r1, r2, cache, spflag);
}

Node RegExpOpr::complement(Node r, int &ret) {
  Node rNode;
  ret = 1;
  if(d_compl_cache.find(r) != d_compl_cache.end()) {
    rNode = d_compl_cache[r].first;
    ret = d_compl_cache[r].second;
  } else {
    if(r == d_emptyRegexp) {
      rNode = d_sigma_star;
    } else if(r == d_emptySingleton) {
      rNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, d_sigma, d_sigma_star);
    } else if(!checkConstRegExp(r)) {
      //TODO: var to be extended
      ret = 0;
    } else {
      std::set<unsigned> cset;
      SetNodes vset;
      firstChars(r, cset, vset);
      std::vector< Node > vec_nodes;
      for(unsigned i=0; i<d_card; i++) {
        CVC4::String c = CVC4::String::convertUnsignedIntToChar(i);
        Node n = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(c));
        Node r2;
        if(cset.find(i) == cset.end()) {
          r2 = d_sigma_star;
        } else {
          int rt;
          derivativeS(r, c, r2);
          if(r2 == r) {
            r2 = d_emptyRegexp;
          } else {
            r2 = complement(r2, rt);
          }
        }
        n = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, n, r2));
        vec_nodes.push_back(n);
      }
      rNode = vec_nodes.size()==0? d_emptyRegexp : vec_nodes.size()==1? vec_nodes[0] :
            NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec_nodes);
    }
    rNode = Rewriter::rewrite(rNode);
    std::pair< Node, int > p(rNode, ret);
    d_compl_cache[r] = p;
  }
  Trace("regexp-compl") << "COMPL( " << mkString(r) << " ) = " << mkString(rNode) << ", ret=" << ret << std::endl;
  return rNode;
}

void RegExpOpr::splitRegExp(Node r, std::vector< PairNodes > &pset) {
  Assert(checkConstRegExp(r));
  if(d_split_cache.find(r) != d_split_cache.end()) {
    pset = d_split_cache[r];
  } else {
    switch( r.getKind() ) {
      case kind::REGEXP_EMPTY: {
        break;
      }
      case kind::REGEXP_OPT: {
        PairNodes tmp(d_emptySingleton, d_emptySingleton);
        pset.push_back(tmp);
      }
      case kind::REGEXP_RANGE:
      case kind::REGEXP_SIGMA: {
        PairNodes tmp1(d_emptySingleton, r);
        PairNodes tmp2(r, d_emptySingleton);
        pset.push_back(tmp1);
        pset.push_back(tmp2);
        break;
      }
      case kind::STRING_TO_REGEXP: {
        Assert(r[0].isConst());
        CVC4::String s = r[0].getConst< CVC4::String >();
        PairNodes tmp1(d_emptySingleton, r);
        pset.push_back(tmp1);
        for(unsigned i=1; i<s.size(); i++) {
          CVC4::String s1 = s.substr(0, i);
          CVC4::String s2 = s.substr(i);
          Node n1 = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(s1));
          Node n2 = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(s2));
          PairNodes tmp3(n1, n2);
          pset.push_back(tmp3);
        }
        PairNodes tmp2(r, d_emptySingleton);
        pset.push_back(tmp2);
        break;
      }
      case kind::REGEXP_CONCAT: {
        for(unsigned i=0; i<r.getNumChildren(); i++) {
          std::vector< PairNodes > tset;
          splitRegExp(r[i], tset);
          std::vector< Node > hvec;
          std::vector< Node > tvec;
          for(unsigned j=0; j<=i; j++) {
            hvec.push_back(r[j]);
          }
          for(unsigned j=i; j<r.getNumChildren(); j++) {
            tvec.push_back(r[j]);
          }
          for(unsigned j=0; j<tset.size(); j++) {
            hvec[i] = tset[j].first;
            tvec[0] = tset[j].second;
            Node r1 = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, hvec) );
            Node r2 = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, tvec) );
            PairNodes tmp2(r1, r2);
            pset.push_back(tmp2);
          }
        }
        break;
      }
      case kind::REGEXP_UNION: {
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          std::vector< PairNodes > tset;
          splitRegExp(r[i], tset);
          pset.insert(pset.end(), tset.begin(), tset.end());
        }
        break;
      }
      case kind::REGEXP_INTER: {
        bool spflag = false;
        Node tmp = r[0];
        for(unsigned i=1; i<r.getNumChildren(); i++) {
          tmp = intersect(tmp, r[i], spflag);
        }
        splitRegExp(tmp, pset);
        break;
      }
      case kind::REGEXP_STAR: {
        std::vector< PairNodes > tset;
        splitRegExp(r[0], tset);
        PairNodes tmp1(d_emptySingleton, d_emptySingleton);
        pset.push_back(tmp1);
        for(unsigned i=0; i<tset.size(); i++) {
          Node r1 = tset[i].first==d_emptySingleton ? r : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, r, tset[i].first);
          Node r2 = tset[i].second==d_emptySingleton ? r : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, tset[i].second, r);
          PairNodes tmp2(r1, r2);
          pset.push_back(tmp2);
        }
        break;
      }
      case kind::REGEXP_PLUS: {
        std::vector< PairNodes > tset;
        splitRegExp(r[0], tset);
        for(unsigned i=0; i<tset.size(); i++) {
          Node r1 = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, r, tset[i].first);
          Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, tset[i].second, r);
          PairNodes tmp2(r1, r2);
          pset.push_back(tmp2);
        }
        break;
      }
      default: {
        Trace("strings-error") << "Unsupported term: " << r << " in splitRegExp." << std::endl;
        Assert( false );
        //return Node::null();
      }
    }
    d_split_cache[r] = pset;
  }
}

//printing
std::string RegExpOpr::niceChar( Node r ) {
  if(r.isConst()) {
    std::string s = r.getConst<CVC4::String>().toString() ;
    return s == "" ? "{E}" : ( s == " " ? "{ }" : s.size()>1? "("+s+")" : s );
  } else {
    std::string ss = "$" + r.toString();
    return ss;
  }
}
std::string RegExpOpr::mkString( Node r ) {
  std::string retStr;
  if(r.isNull()) {
    retStr = "Empty";
  } else {
    int k = r.getKind();
    switch( k ) {
      case kind::REGEXP_EMPTY: {
        retStr += "Empty";
        break;
      }
      case kind::REGEXP_SIGMA: {
        retStr += "{W}";
        break;
      }
      case kind::STRING_TO_REGEXP: {
        retStr += niceChar( r[0] );
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
        if(r == d_sigma) {
          retStr += "{A}";
        } else {
          retStr += "(";
          for(unsigned i=0; i<r.getNumChildren(); ++i) {
            if(i != 0) retStr += "|";
            retStr += mkString( r[i] );
          }
          retStr += ")";
        }
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
      default:
        Trace("strings-error") << "Unsupported term: " << r << " in RegExp." << std::endl;
        //Assert( false );
        //return Node::null();
    }
  }

  return retStr;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
