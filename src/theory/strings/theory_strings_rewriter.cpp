/*********************                                                        */
/*! \file theory_strings_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/

#include "theory/strings/theory_strings_rewriter.h"

#include <stdint.h>

#include "options/strings_options.h"
#include "smt/logic_exception.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

Node TheoryStringsRewriter::simpleRegexpConsume( std::vector< Node >& mchildren, std::vector< Node >& children, int dir ){
  unsigned tmin = dir<0 ? 0 : dir;
  unsigned tmax = dir<0 ? 1 : dir;
  //try to remove off front and back
  for( unsigned t=0; t<2; t++ ){
    if( tmin<=t && t<=tmax ){
      bool do_next = true;
      while( !children.empty() && !mchildren.empty() && do_next ){
        do_next = false;
        Node xc = mchildren[mchildren.size()-1];
        Node rc = children[children.size()-1];
        Assert( rc.getKind()!=kind::REGEXP_CONCAT );
        Assert( xc.getKind()!=kind::STRING_CONCAT );
        if( rc.getKind() == kind::STRING_TO_REGEXP ){
          if( xc==rc[0] ){
            children.pop_back();
            mchildren.pop_back();
            do_next = true;
          }else if( xc.isConst() && rc[0].isConst() ){
            //split the constant
            int index;
            Node s = splitConstant( xc, rc[0], index, t==0 );
            Trace("regexp-ext-rewrite-debug") << "CRE: Regexp const split : " << xc << " " << rc[0] << " -> " << s << " " << index << " " << t << std::endl;
            if( s.isNull() ){
              return NodeManager::currentNM()->mkConst( false );
            }else{
              children.pop_back();
              mchildren.pop_back();
              if( index==0 ){
                mchildren.push_back( s );
              }else{
                children.push_back( s );
              }
            }
            do_next = true;
          }
        }else if( xc.isConst() ){
          //check for constants
          CVC4::String s = xc.getConst<String>();
          Assert( s.size()>0 );
          if( rc.getKind() == kind::REGEXP_RANGE || rc.getKind()==kind::REGEXP_SIGMA ){
            CVC4::String ss( t==0 ? s.getLastChar() : s.getFirstChar() );
            if( testConstStringInRegExp( ss, 0, rc ) ){
              //strip off one character
              mchildren.pop_back();
              if( s.size()>1 ){
                if( t==0 ){
                  mchildren.push_back( NodeManager::currentNM()->mkConst(s.substr( 0, s.size()-1 )) );
                }else{
                  mchildren.push_back( NodeManager::currentNM()->mkConst(s.substr( 1 )) );
                }
              }
              children.pop_back();
              do_next = true;
            }else{
              return NodeManager::currentNM()->mkConst( false );
            }
          }else if( rc.getKind()==kind::REGEXP_INTER || rc.getKind()==kind::REGEXP_UNION ){
            //see if any/each child does not work
            bool result_valid = true;
            Node result;
            Node emp_s = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
            for( unsigned i=0; i<rc.getNumChildren(); i++ ){
              std::vector< Node > mchildren_s;
              std::vector< Node > children_s;
              mchildren_s.push_back( xc );
              getConcat( rc[i], children_s );
              Node ret = simpleRegexpConsume( mchildren_s, children_s, t );
              if( !ret.isNull() ){
                // one conjunct cannot be satisfied, return false
                if( rc.getKind()==kind::REGEXP_INTER ){
                  return ret;
                }
              }else{
                if( children_s.empty() ){
                  //if we were able to fully consume, store the result
                  Assert( mchildren_s.size()<=1 );
                  if( mchildren_s.empty() ){
                    mchildren_s.push_back( emp_s );
                  }
                  if( result.isNull() ){
                    result = mchildren_s[0];
                  }else if( result!=mchildren_s[0] ){
                    result_valid = false;
                  }
                }else{
                  result_valid = false;
                }
              }
            }
            if( result_valid ){
              if( result.isNull() ){
                //all disjuncts cannot be satisfied, return false
                Assert( rc.getKind()==kind::REGEXP_UNION );
                return NodeManager::currentNM()->mkConst( false );
              }else{
                //all branches led to the same result
                children.pop_back();
                mchildren.pop_back();
                if( result!=emp_s ){
                  mchildren.push_back( result );
                }
                do_next = true;
              }
            }
          }else if( rc.getKind()==kind::REGEXP_STAR ){
            //check if there is no way that this star can be unrolled even once
            std::vector< Node > mchildren_s;
            mchildren_s.insert( mchildren_s.end(), mchildren.begin(), mchildren.end() );
            if( t==1 ){
              std::reverse( mchildren_s.begin(), mchildren_s.end() );
            }
            std::vector< Node > children_s;
            getConcat( rc[0], children_s );
            Node ret = simpleRegexpConsume( mchildren_s, children_s, t );
            if( !ret.isNull() ){
              Trace("regexp-ext-rewrite-debug") << "CRE : regexp star infeasable " << xc << " " << rc << std::endl;
              children.pop_back();
              if( children.empty() ){
                return NodeManager::currentNM()->mkConst( false );
              }else{
                do_next = true;
              }
            }else{
              if( children_s.empty() ){
                //check if beyond this, we can't do it or there is nothing left, if so, repeat
                bool can_skip = false;
                if( children.size()>1 ){
                  std::vector< Node > mchildren_ss;
                  mchildren_ss.insert( mchildren_ss.end(), mchildren.begin(), mchildren.end() );
                  std::vector< Node > children_ss;
                  children_ss.insert( children_ss.end(), children.begin(), children.end()-1 );
                  if( t==1 ){
                    std::reverse( mchildren_ss.begin(), mchildren_ss.end() );
                    std::reverse( children_ss.begin(), children_ss.end() );
                  }
                  Node ret = simpleRegexpConsume( mchildren_ss, children_ss, t );
                  if( ret.isNull() ){
                    can_skip = true;
                  }
                }
                if( !can_skip ){
                  //take the result of fully consuming once
                  if( t==1 ){
                    std::reverse( mchildren_s.begin(), mchildren_s.end() );
                  }
                  mchildren.clear();
                  mchildren.insert( mchildren.end(), mchildren_s.begin(), mchildren_s.end() );
                  do_next = true;
                }else{
                  Trace("regexp-ext-rewrite-debug") << "CRE : can skip " << rc << " from " << xc << std::endl;
                }
              }
            }
          }
        }
        if( !do_next ){
          Trace("regexp-ext-rewrite") << "Cannot consume : " << xc << " " << rc << std::endl;
        }
      }
    }
    if( dir!=0 ){
      std::reverse( children.begin(), children.end() );
      std::reverse( mchildren.begin(), mchildren.end() );
    }
  }
  return Node::null();
}

Node TheoryStringsRewriter::rewriteEquality(Node node)
{
  Assert(node.getKind() == kind::EQUAL);
  if (node[0] == node[1])
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  else if (node[0].isConst() && node[1].isConst())
  {
    return NodeManager::currentNM()->mkConst(false);
  }

  // ( ~contains( s, t ) V ~contains( t, s ) ) => ( s == t ---> false )
  for (unsigned r = 0; r < 2; r++)
  {
    Node ctn = NodeManager::currentNM()->mkNode(
        kind::STRING_STRCTN, node[r], node[1 - r]);
    // must call rewrite contains directly to avoid infinite loop
    // we do a fix point since we may rewrite contains terms to simpler
    // contains terms.
    Node prev;
    do
    {
      prev = ctn;
      ctn = rewriteContains(ctn);
    } while (prev != ctn && ctn.getKind() == kind::STRING_STRCTN);
    if (ctn.isConst())
    {
      if (!ctn.getConst<bool>())
      {
        return returnRewrite(node, ctn, "eq-nctn");
      }
      else
      {
        // definitely contains but not syntactically equal
        // We may be able to simplify, e.g.
        //  str.++( x, "a" ) == "a"  ----> x = ""
      }
    }
  }

  // ( len( s ) != len( t ) ) => ( s == t ---> false )
  // This covers cases like str.++( x, x ) == "a" ---> false
  Node len0 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]);
  Node len1 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
  Node len_eq = len0.eqNode(len1);
  len_eq = Rewriter::rewrite(len_eq);
  if (len_eq.isConst() && !len_eq.getConst<bool>())
  {
    return returnRewrite(node, len_eq, "eq-len-deq");
  }

  std::vector<Node> c[2];
  for (unsigned i = 0; i < 2; i++)
  {
    strings::TheoryStringsRewriter::getConcat(node[i], c[i]);
  }

  // check if the prefix, suffix mismatches
  //   For example, str.++( x, "a", y ) == str.++( x, "bc", z ) ---> false
  unsigned minsize = std::min(c[0].size(), c[1].size());
  for (unsigned r = 0; r < 2; r++)
  {
    for (unsigned i = 0; i < minsize; i++)
    {
      unsigned index1 = r == 0 ? i : (c[0].size() - 1) - i;
      unsigned index2 = r == 0 ? i : (c[1].size() - 1) - i;
      if (c[0][index1].isConst() && c[1][index2].isConst())
      {
        CVC4::String s = c[0][index1].getConst<String>();
        CVC4::String t = c[1][index2].getConst<String>();
        unsigned len_short = s.size() <= t.size() ? s.size() : t.size();
        bool isSameFix =
            r == 1 ? s.rstrncmp(t, len_short) : s.strncmp(t, len_short);
        if (!isSameFix)
        {
          Node ret = NodeManager::currentNM()->mkConst(false);
          return returnRewrite(node, ret, "eq-nfix");
        }
      }
      if (c[0][index1] != c[1][index2])
      {
        break;
      }
    }
  }

  // standard ordering
  if (node[0] > node[1])
  {
    return NodeManager::currentNM()->mkNode(kind::EQUAL, node[1], node[0]);
  }
  else
  {
    return node;
  }
}

// TODO (#1180) add rewrite
//  str.++( str.substr( x, n1, n2 ), str.substr( x, n1+n2, n3 ) ) --->
//  str.substr( x, n1, n2+n3 )
Node TheoryStringsRewriter::rewriteConcat(Node node)
{
  Assert(node.getKind() == kind::STRING_CONCAT);
  Trace("strings-prerewrite") << "Strings::rewriteConcat start " << node
                              << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  Node preNode = Node::null();
  for(unsigned int i=0; i<node.getNumChildren(); ++i) {
    Node tmpNode = node[i];
    if(node[i].getKind() == kind::STRING_CONCAT) {
      if(tmpNode.getKind() == kind::STRING_CONCAT) {
        unsigned j=0;
        if(!preNode.isNull()) {
          if(tmpNode[0].isConst()) {
            preNode = NodeManager::currentNM()->mkConst( preNode.getConst<String>().concat( tmpNode[0].getConst<String>() ) );
            node_vec.push_back( preNode );
          } else {
            node_vec.push_back( preNode );
            node_vec.push_back( tmpNode[0] );
          }
          preNode = Node::null();
          ++j;
        }
        for(; j<tmpNode.getNumChildren() - 1; ++j) {
          node_vec.push_back( tmpNode[j] );
        }
        tmpNode = tmpNode[j];
      }
    }
    if(!tmpNode.isConst()) {
      if(!preNode.isNull()) {
        if(preNode.getKind() == kind::CONST_STRING && !preNode.getConst<String>().isEmptyString() ) {
          node_vec.push_back( preNode );
        }
        preNode = Node::null();
      }
      node_vec.push_back( tmpNode );
    }else{
      if( preNode.isNull() ){
        preNode = tmpNode;
      }else{
        preNode = NodeManager::currentNM()->mkConst( preNode.getConst<String>().concat( tmpNode.getConst<String>() ) );
      }
    }
  }
  if( !preNode.isNull() && ( preNode.getKind()!=kind::CONST_STRING || !preNode.getConst<String>().isEmptyString() ) ){
    node_vec.push_back( preNode );
  }
  retNode = mkConcat( kind::STRING_CONCAT, node_vec );
  Trace("strings-prerewrite") << "Strings::rewriteConcat end " << retNode
                              << std::endl;
  return retNode;
}


void TheoryStringsRewriter::mergeInto(std::vector<Node> &t, const std::vector<Node> &s) {
  for(std::vector<Node>::const_iterator itr=s.begin(); itr!=s.end(); itr++) {
    if(std::find(t.begin(), t.end(), (*itr)) == t.end()) {
      t.push_back( *itr );
    }
  }
}

void TheoryStringsRewriter::shrinkConVec(std::vector<Node> &vec) {
  unsigned i = 0;
  Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
  while(i < vec.size()) {
    if( vec[i] == emptysingleton ) {
      vec.erase(vec.begin() + i);
    } else if(vec[i].getKind()==kind::STRING_TO_REGEXP && i<vec.size()-1 && vec[i+1].getKind()==kind::STRING_TO_REGEXP) {
      Node tmp = NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, vec[i][0], vec[i+1][0]);
      tmp = rewriteConcat(tmp);
      vec[i] = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, tmp);
      vec.erase(vec.begin() + i + 1);
    } else {
      i++;
    }
  }
}

Node TheoryStringsRewriter::applyAX( TNode node ) {
  Trace("regexp-ax") << "Regexp::AX start " << node << std::endl;
  Node retNode = node;

  int k = node.getKind();
  switch( k ) {
    case kind::REGEXP_UNION: {
      std::vector<Node> vec_nodes;
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_UNION) {
          for(unsigned j=0; j<tmp.getNumChildren(); j++) {
            if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp[j]) == vec_nodes.end()) {
              vec_nodes.push_back(tmp[j]);
            }
          }
        } else if(tmp.getKind() == kind::REGEXP_EMPTY) {
          // do nothing
        } else {
          if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp) == vec_nodes.end()) {
            vec_nodes.push_back(tmp);
          }
        }
      }
      if(vec_nodes.empty()) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else {
        retNode = vec_nodes.size() == 1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
      }
      break;
    }
    case kind::REGEXP_CONCAT: {
      std::vector< std::vector<Node> > vec_nodes;
      bool emptyflag = false;
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_EMPTY) {
          emptyflag = true;
          break;
        } else if(tmp == emptysingleton) {
          //do nothing
        } else if(vec_nodes.empty()) {
          if(tmp.getKind() == kind::REGEXP_UNION) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              std::vector<Node> vtmp;
              if(tmp[j].getKind() == kind::REGEXP_CONCAT) {
                for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                  vtmp.push_back(tmp[j][j2]);
                }
              } else {
                vtmp.push_back(tmp[j]);
              }
              vec_nodes.push_back(vtmp);
            }
          } else if(tmp.getKind() == kind::REGEXP_CONCAT) {
            std::vector<Node> vtmp;
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              vtmp.push_back(tmp[j]);
            }
            vec_nodes.push_back(vtmp);
          } else {
            std::vector<Node> vtmp;
            vtmp.push_back(tmp);
            vec_nodes.push_back(vtmp);
          }
        } else {
          //non-empty vec
          if(tmp.getKind() == kind::REGEXP_UNION) {
            unsigned cnt = vec_nodes.size();
            for(unsigned i2=0; i2<cnt; i2++) {
              //std::vector<Node> vleft( vec_nodes[i2] );
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                if(tmp[j] == emptysingleton) {
                  vec_nodes.push_back( vec_nodes[i2] );
                } else {
                  std::vector<Node> vt( vec_nodes[i2] );
                  if(tmp[j].getKind() != kind::REGEXP_CONCAT) {
                    vt.push_back( tmp[j] );
                  } else {
                    for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                      vt.push_back(tmp[j][j2]);
                    }
                  }
                  vec_nodes.push_back(vt);
                }
              }
            }
            vec_nodes.erase(vec_nodes.begin(), vec_nodes.begin() + cnt);
          } else if(tmp.getKind() == kind::REGEXP_CONCAT) {
            for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                vec_nodes[i2].push_back(tmp[j]);
              }
            }
          } else {
            for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
              vec_nodes[i2].push_back(tmp);
            }
          }
        }
      }
      if(emptyflag) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else if(vec_nodes.empty()) {
        retNode = emptysingleton;
      } else if(vec_nodes.size() == 1) {
        shrinkConVec(vec_nodes[0]);
        retNode = vec_nodes[0].empty()? emptysingleton
          : vec_nodes[0].size()==1? vec_nodes[0][0]
          : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes[0]);
      } else {
        std::vector<Node> vtmp;
        for(unsigned i=0; i<vec_nodes.size(); i++) {
          shrinkConVec(vec_nodes[i]);
          if(!vec_nodes[i].empty()) {
            Node ntmp = vec_nodes[i].size()==1? vec_nodes[i][0]
              : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes[i]);
            vtmp.push_back(ntmp);
          }
        }
        retNode = vtmp.empty()? emptysingleton
          : vtmp.size()==1? vtmp[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vtmp);
      }
      break;
    }
    case kind::REGEXP_STAR: {
      Node tmp = applyAX(node[0]);
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      if(tmp.getKind() == kind::REGEXP_EMPTY || tmp == emptysingleton) {
        retNode = emptysingleton;
      } else {
        if(tmp.getKind() == kind::REGEXP_UNION) {
          std::vector<Node> vec;
          for(unsigned i=0; i<tmp.getNumChildren(); i++) {
            if(tmp[i] != emptysingleton) {
              vec.push_back(tmp[i]);
            }
          }
          if(vec.size() != tmp.getNumChildren()) {
            tmp = vec.size()==1? vec[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec) ;
          }
        } else if(tmp.getKind() == kind::REGEXP_STAR) {
          tmp = tmp[0];
        }
        if(tmp != node[0]) {
          retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, tmp );
        }
      }
      break;
    }
    case kind::REGEXP_INTER: {
      std::vector< std::vector<Node> > vec_nodes;
      bool emptyflag = false;
      bool epsflag = false;
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_EMPTY) {
          emptyflag = true;
          break;
        } else if(vec_nodes.empty()) {
          if(tmp.getKind() == kind::REGEXP_INTER) {
            std::vector<Node> vtmp;
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              vtmp.push_back(tmp[j]);
            }
            vec_nodes.push_back(vtmp);
          } else if(tmp.getKind() == kind::REGEXP_UNION) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              std::vector<Node> vtmp;
              if(tmp[j].getKind() == kind::REGEXP_INTER) {
                for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                  vtmp.push_back(tmp[j][j2]);
                }
              } else {
                vtmp.push_back(tmp[j]);
              }
              vec_nodes.push_back(vtmp);
            }
          } else {
            if(tmp == emptysingleton) {
              epsflag = true;
            }
            std::vector<Node> vtmp;
            vtmp.push_back(tmp);
            vec_nodes.push_back(vtmp);
          }
        } else {
          //non-empty vec
          if(tmp.getKind() == kind::REGEXP_INTER) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
                if(std::find(vec_nodes[i2].begin(), vec_nodes[i2].end(), tmp[j]) == vec_nodes[i2].end()) {
                  vec_nodes[i2].push_back(tmp[j]);
                }
              }
            }
          } else if(tmp == emptysingleton) {
            if(!epsflag) {
              epsflag = true;
              for(unsigned j=0; j<vec_nodes.size(); j++) {
                vec_nodes[j].insert(vec_nodes[j].begin(), emptysingleton);
              }
            }
          } else if(tmp.getKind() == kind::REGEXP_UNION) {
            unsigned cnt = vec_nodes.size();
            for(unsigned i2=0; i2<cnt; i2++) {
              //std::vector<Node> vleft( vec_nodes[i2] );
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                std::vector<Node> vt(vec_nodes[i2]);
                if(tmp[j].getKind() != kind::REGEXP_INTER) {
                  if(std::find(vt.begin(), vt.end(), tmp[j]) == vt.end()) {
                    vt.push_back(tmp[j]);
                  }
                } else {
                  std::vector<Node> vtmp;
                  for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                    vtmp.push_back(tmp[j][j2]);
                  }
                  mergeInto(vt, vtmp);
                }
                vec_nodes.push_back(vt);
              }
            }
            vec_nodes.erase(vec_nodes.begin(), vec_nodes.begin() + cnt);
          } else {
            for(unsigned j=0; j<vec_nodes.size(); j++) {
              if(std::find(vec_nodes[j].begin(), vec_nodes[j].end(), tmp) == vec_nodes[j].end()) {
                vec_nodes[j].push_back(tmp);
              }
            }
          }
        }
      }
      if(emptyflag) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else if(vec_nodes.empty()) {
        //to check?
        retNode = emptysingleton;
      } else if(vec_nodes.size() == 1) {
        retNode = vec_nodes[0].empty() ? emptysingleton : vec_nodes[0].size() == 1 ? vec_nodes[0][0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes[0] );
      } else {
        std::vector<Node> vtmp;
        for(unsigned i=0; i<vec_nodes.size(); i++) {
          Node tmp = vec_nodes[i].empty()? emptysingleton : vec_nodes[i].size() == 1 ? vec_nodes[i][0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes[i] );
          vtmp.push_back(tmp);
        }
        retNode = vtmp.size() == 1? vtmp[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vtmp );
      }
      break;
    }
/*    case kind::REGEXP_UNION: {
      break;
    }*/
    case kind::REGEXP_SIGMA: {
      break;
    }
    case kind::REGEXP_EMPTY: {
      break;
    }
    //default: {
      //to check?
    //}
  }

  Trace("regexp-ax") << "Regexp::AX end " << node << " to\n               " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteConcatRegExp( TNode node ) {
  Assert( node.getKind() == kind::REGEXP_CONCAT );
  Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  Node preNode = Node::null();
  bool emptyflag = false;
  for(unsigned int i=0; i<node.getNumChildren(); ++i) {
    Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp preNode: " << preNode << std::endl;
    Node tmpNode = node[i];
    if(tmpNode.getKind() == kind::REGEXP_CONCAT) {
      tmpNode = prerewriteConcatRegExp(node[i]);
      if(tmpNode.getKind() == kind::REGEXP_CONCAT) {
        unsigned j=0;
        if(!preNode.isNull()) {
          if(tmpNode[0].getKind() == kind::STRING_TO_REGEXP) {
            preNode = rewriteConcat(NodeManager::currentNM()->mkNode(
                kind::STRING_CONCAT, preNode, tmpNode[0][0]));
            node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
            preNode = Node::null();
          } else {
            node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
            preNode = Node::null();
            node_vec.push_back( tmpNode[0] );
          }
          ++j;
        }
        for(; j<tmpNode.getNumChildren() - 1; ++j) {
          node_vec.push_back( tmpNode[j] );
        }
        tmpNode = tmpNode[j];
      }
    }
    if( tmpNode.getKind() == kind::STRING_TO_REGEXP ) {
      if(preNode.isNull()) {
        preNode = tmpNode[0];
      } else {
        preNode = rewriteConcat(NodeManager::currentNM()->mkNode(
            kind::STRING_CONCAT, preNode, tmpNode[0]));
      }
    } else if( tmpNode.getKind() == kind::REGEXP_EMPTY ) {
      emptyflag = true;
      break;
    } else {
      if(!preNode.isNull()) {
        if(preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().isEmptyString() ) {
          preNode = Node::null();
        } else {
          node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
          preNode = Node::null();
        }
      }
      node_vec.push_back( tmpNode );
    }
  }
  if(emptyflag) {
    std::vector< Node > nvec;
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
  } else {
    if(!preNode.isNull()) {
      bool bflag = (preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().isEmptyString() );
      if(node_vec.empty() || !bflag ) {
        node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
      }
    }
    if(node_vec.size() > 1) {
      retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, node_vec);
    } else {
      retNode = node_vec[0];
    }
  }
  Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp end " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteOrRegExp(TNode node) {
  Assert( node.getKind() == kind::REGEXP_UNION );
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  bool allflag = false;
  for(unsigned i=0; i<node.getNumChildren(); ++i) {
    if(node[i].getKind() == kind::REGEXP_UNION) {
      Node tmpNode = prerewriteOrRegExp( node[i] );
      if(tmpNode.getKind() == kind::REGEXP_UNION) {
        for(unsigned int j=0; j<tmpNode.getNumChildren(); ++j) {
          if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
            if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
              node_vec.push_back( tmpNode[j] );
            }
          }
        }
      } else if(tmpNode.getKind() == kind::REGEXP_EMPTY) {
        //nothing
      } else if(tmpNode.getKind() == kind::REGEXP_STAR && tmpNode[0].getKind() == kind::REGEXP_SIGMA) {
        allflag = true;
        retNode = tmpNode;
        break;
      } else {
        if(std::find(node_vec.begin(), node_vec.end(), tmpNode) == node_vec.end()) {
          node_vec.push_back( tmpNode );
        }
      }
    } else if(node[i].getKind() == kind::REGEXP_EMPTY) {
      //nothing
    } else if(node[i].getKind() == kind::REGEXP_STAR && node[i][0].getKind() == kind::REGEXP_SIGMA) {
      allflag = true;
      retNode = node[i];
      break;
    } else {
      if(std::find(node_vec.begin(), node_vec.end(), node[i]) == node_vec.end()) {
        node_vec.push_back( node[i] );
      }
    }
  }
  if(!allflag) {
    std::vector< Node > nvec;
    retNode = node_vec.size() == 0 ? NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec ) :
          node_vec.size() == 1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, node_vec);
  }
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp end " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteAndRegExp(TNode node) {
  Assert( node.getKind() == kind::REGEXP_INTER );
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  //Node allNode = Node::null();
  for(unsigned i=0; i<node.getNumChildren(); ++i) {
    if(node[i].getKind() == kind::REGEXP_INTER) {
      Node tmpNode = prerewriteAndRegExp( node[i] );
      if(tmpNode.getKind() == kind::REGEXP_INTER) {
        for(unsigned int j=0; j<tmpNode.getNumChildren(); ++j) {
          if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
            node_vec.push_back( tmpNode[j] );
          }
        }
      } else if(tmpNode.getKind() == kind::REGEXP_EMPTY) {
        retNode = tmpNode;
        break;
      } else if(tmpNode.getKind() == kind::REGEXP_STAR && tmpNode[0].getKind() == kind::REGEXP_SIGMA) {
        //allNode = tmpNode;
      } else {
        if(std::find(node_vec.begin(), node_vec.end(), tmpNode) == node_vec.end()) {
          node_vec.push_back( tmpNode );
        }
      }
    } else if(node[i].getKind() == kind::REGEXP_EMPTY) {
      retNode = node[i];
      break;
    } else if(node[i].getKind() == kind::REGEXP_STAR && node[i][0].getKind() == kind::REGEXP_SIGMA) {
      //allNode = node[i];
    } else {
      if(std::find(node_vec.begin(), node_vec.end(), node[i]) == node_vec.end()) {
        node_vec.push_back( node[i] );
      }
    }
  }
  if( retNode==node ){
    std::vector< Node > nvec;
    retNode = node_vec.size() == 0 ?
          NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, NodeManager::currentNM()->mkNode(kind::REGEXP_SIGMA, nvec)) :
          node_vec.size() == 1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_INTER, node_vec);
  }
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp end " << retNode << std::endl;
  return retNode;
}

bool TheoryStringsRewriter::isConstRegExp( TNode t ) {
  if( t.getKind()==kind::STRING_TO_REGEXP ) {
    return t[0].isConst();
  }else{
    for( unsigned i = 0; i<t.getNumChildren(); ++i ) {
      if( !isConstRegExp(t[i]) ){
        return false;
      }
    }
    return true;
  }
}

bool TheoryStringsRewriter::testConstStringInRegExp( CVC4::String &s, unsigned int index_start, TNode r ) {
  Assert( index_start <= s.size() );
  Trace("regexp-debug") << "Checking " << s << " in " << r << ", starting at " << index_start << std::endl;
  int k = r.getKind();
  switch( k ) {
    case kind::STRING_TO_REGEXP: {
      CVC4::String s2 = s.substr( index_start, s.size() - index_start );
      if(r[0].getKind() == kind::CONST_STRING) {
        return ( s2 == r[0].getConst<String>() );
      } else {
        Assert( false, "RegExp contains variables" );
        return false;
      }
    }
    case kind::REGEXP_CONCAT: {
      if( s.size() != index_start ) {
        std::vector<int> vec_k( r.getNumChildren(), -1 );
        int start = 0;
        int left = (int) s.size() - index_start;
        int i=0;
        while( i<(int) r.getNumChildren() ) {
          bool flag = true;
          if( i == (int) r.getNumChildren() - 1 ) {
            if( testConstStringInRegExp( s, index_start + start, r[i] ) ) {
              return true;
            }
          } else if( i == -1 ) {
            return false;
          } else {
            for(vec_k[i] = vec_k[i] + 1; vec_k[i] <= left; ++vec_k[i]) {
              CVC4::String t = s.substr(index_start + start, vec_k[i]);
              if( testConstStringInRegExp( t, 0, r[i] ) ) {
                start += vec_k[i]; left -= vec_k[i]; flag = false;
                ++i; vec_k[i] = -1;
                break;
              }
            }
          }

          if(flag) {
            --i;
            if(i >= 0) {
              start -= vec_k[i]; left += vec_k[i];
            }
          }
        }
        return false;
      } else {
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(!testConstStringInRegExp( s, index_start, r[i] )) return false;
        }
        return true;
      }
    }
    case kind::REGEXP_UNION: {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(testConstStringInRegExp( s, index_start, r[i] )) return true;
      }
      return false;
    }
    case kind::REGEXP_INTER: {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(!testConstStringInRegExp( s, index_start, r[i] )) return false;
      }
      return true;
    }
    case kind::REGEXP_STAR: {
      if( s.size() != index_start ) {
        for(unsigned k=s.size() - index_start; k>0; --k) {
          CVC4::String t = s.substr(index_start, k);
          if( testConstStringInRegExp( t, 0, r[0] ) ) {
            if( index_start + k == s.size() || testConstStringInRegExp( s, index_start + k, r ) ) {
              return true;
            }
          }
        }
        return false;
      } else {
        return true;
      }
    }
    case kind::REGEXP_EMPTY: {
      return false;
    }
    case kind::REGEXP_SIGMA: {
      if(s.size() == index_start + 1) {
        return true;
      } else {
        return false;
      }
    }
    case kind::REGEXP_RANGE: {
      if(s.size() == index_start + 1) {
        unsigned char a = r[0].getConst<String>().getFirstChar();
        unsigned char b = r[1].getConst<String>().getFirstChar();
        unsigned char c = s.getLastChar();
        return (a <= c && c <= b);
      } else {
        return false;
      }
    }
    case kind::REGEXP_LOOP: {
      unsigned l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
      if(s.size() == index_start) {
        return l==0? true : testConstStringInRegExp(s, index_start, r[0]);
      } else if(l==0 && r[1]==r[2]) {
        return false;
      } else {
        Assert(r.getNumChildren() == 3, "String rewriter error: LOOP has 2 children");
        if(l==0) {
          //R{0,u}
          unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
          for(unsigned len=s.size() - index_start; len>=1; len--) {
            CVC4::String t = s.substr(index_start, len);
            if(testConstStringInRegExp(t, 0, r[0])) {
              if(len + index_start == s.size()) {
                return true;
              } else {
                Node num2 = NodeManager::currentNM()->mkConst( CVC4::Rational(u - 1) );
                Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], r[1], num2);
                if(testConstStringInRegExp(s, index_start+len, r2)) {
                  return true;
                }
              }
            }
          }
          return false;
        } else {
          //R{l,l}
          Assert(r[1]==r[2], "String rewriter error: LOOP nums are not equal");
          if(l>s.size() - index_start) {
            if(testConstStringInRegExp(s, s.size(), r[0])) {
              l = s.size() - index_start;
            } else {
              return false;
            }
          }
          for(unsigned len=1; len<=s.size() - index_start; len++) {
            CVC4::String t = s.substr(index_start, len);
            if(testConstStringInRegExp(t, 0, r[0])) {
              Node num2 = NodeManager::currentNM()->mkConst( CVC4::Rational(l - 1) );
              Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], num2, num2);
              if(testConstStringInRegExp(s, index_start+len, r2)) {
                return true;
              }
            }
          }
          return false;
        }
      }
    }
    default: {
      Trace("strings-error") << "Unsupported term: " << r << " in testConstStringInRegExp." << std::endl;
      Unreachable();
      return false;
    }
  }
}

Node TheoryStringsRewriter::rewriteMembership(TNode node) {
  Node retNode = node;
  Node x = node[0];
  Node r = node[1];//applyAX(node[1]);

  if(r.getKind() == kind::REGEXP_EMPTY) {
    retNode = NodeManager::currentNM()->mkConst( false );
  } else if(x.getKind()==kind::CONST_STRING && isConstRegExp(r)) {
    //test whether x in node[1]
    CVC4::String s = x.getConst<String>();
    retNode = NodeManager::currentNM()->mkConst( testConstStringInRegExp( s, 0, r ) );
  } else if(r.getKind() == kind::REGEXP_SIGMA) {
    Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
    retNode = one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x));
  } else if( r.getKind() == kind::REGEXP_STAR ) {
    if( r[0].getKind() == kind::REGEXP_SIGMA ){
      retNode = NodeManager::currentNM()->mkConst( true );
    }
  }else if( r.getKind() == kind::REGEXP_CONCAT ){
    bool allSigma = true;
    bool allString = true;
    std::vector< Node > cc;
    for(unsigned i=0; i<r.getNumChildren(); i++) {
      Assert( r[i].getKind() != kind::REGEXP_EMPTY );
      if( r[i].getKind() != kind::REGEXP_SIGMA ){
        allSigma = false;
      }
      if( r[i].getKind() != kind::STRING_TO_REGEXP ){
        allString = false;
      }else{
        cc.push_back( r[i] );
      }
    }
    if( allSigma ){
      Node num = NodeManager::currentNM()->mkConst( ::CVC4::Rational( r.getNumChildren() ) );
      retNode = num.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x));
    }else if( allString ){
      retNode = x.eqNode( mkConcat( kind::STRING_CONCAT, cc ) );
    }
  }else if( r.getKind()==kind::REGEXP_INTER || r.getKind()==kind::REGEXP_UNION ){
    std::vector< Node > mvec;
    for( unsigned i=0; i<r.getNumChildren(); i++ ){
      mvec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r[i] ) );
    }
    retNode = NodeManager::currentNM()->mkNode( r.getKind()==kind::REGEXP_INTER ? kind::AND : kind::OR, mvec );
  }else if(r.getKind() == kind::STRING_TO_REGEXP) {
    retNode = x.eqNode(r[0]);
  }else if(x != node[0] || r != node[1]) {
    retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r );
  }

  //do simple consumes
  if( retNode==node ){
    if( r.getKind()==kind::REGEXP_STAR ){
      for( unsigned dir=0; dir<=1; dir++ ){
        std::vector< Node > mchildren;
        getConcat( x, mchildren );
        bool success = true;
        while( success ){
          success = false;
          std::vector< Node > children;
          getConcat( r[0], children );
          Node scn = simpleRegexpConsume( mchildren, children, dir );
          if( !scn.isNull() ){
            Trace("regexp-ext-rewrite") << "Regexp star : const conflict : " << node << std::endl;
            return scn;
          }else if( children.empty() ){
            //fully consumed one copy of the STAR
            if( mchildren.empty() ){
              Trace("regexp-ext-rewrite") << "Regexp star : full consume : " << node << std::endl;
              return NodeManager::currentNM()->mkConst( true );
            }else{
              retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, mkConcat( kind::STRING_CONCAT, mchildren ), r );
              success = true;
            }
          }
        }
        if( retNode!=node ){
          Trace("regexp-ext-rewrite") << "Regexp star : rewrite " << node << " -> " << retNode << std::endl;
          break;
        }
      }
    }else{
      std::vector< Node > children;
      getConcat( r, children );
      std::vector< Node > mchildren;
      getConcat( x, mchildren );
      unsigned prevSize = children.size() + mchildren.size();
      Node scn = simpleRegexpConsume( mchildren, children );
      if( !scn.isNull() ){
        Trace("regexp-ext-rewrite") << "Regexp : const conflict : " << node << std::endl;
        return scn;
      }else{
        if( (children.size() + mchildren.size())!=prevSize ){
          if( children.empty() ){
            retNode = NodeManager::currentNM()->mkConst( mchildren.empty() );
          }else{
            retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, mkConcat( kind::STRING_CONCAT, mchildren ), mkConcat( kind::REGEXP_CONCAT, children ) );
          }
          Trace("regexp-ext-rewrite") << "Regexp : rewrite : " << node << " -> " << retNode << std::endl;
        }
      }
    }
  }
  return retNode;
}

RewriteResponse TheoryStringsRewriter::postRewrite(TNode node) {
  Trace("strings-postrewrite") << "Strings::postRewrite start " << node << std::endl;
  Node retNode = node;
  Node orig = retNode;

  if(node.getKind() == kind::STRING_CONCAT) {
    retNode = rewriteConcat(node);
  } else if(node.getKind() == kind::EQUAL) {
    retNode = rewriteEquality(node);
  } else if(node.getKind() == kind::STRING_LENGTH) {
    if( node[0].isConst() ){
      retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( node[0].getConst<String>().size() ) );
    }else if( node[0].getKind() == kind::STRING_CONCAT ){
      Node tmpNode = node[0];
      if(tmpNode.isConst()) {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode.getConst<String>().size() ) );
      //} else if(tmpNode.getKind() == kind::STRING_SUBSTR) {
        //retNode = tmpNode[2];
      }else if( tmpNode.getKind()==kind::STRING_CONCAT ){
        // it has to be string concat
        std::vector<Node> node_vec;
        for(unsigned int i=0; i<tmpNode.getNumChildren(); ++i) {
          if(tmpNode[i].isConst()) {
            node_vec.push_back( NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode[i].getConst<String>().size() ) ) );
          //} else if(tmpNode[i].getKind() == kind::STRING_SUBSTR) {
          //  node_vec.push_back( tmpNode[i][2] );
          } else {
            node_vec.push_back( NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, tmpNode[i]) );
          }
        }
        retNode = NodeManager::currentNM()->mkNode(kind::PLUS, node_vec);
      }
    }else if( node[0].getKind()==kind::STRING_STRREPL ){
      if( node[0][1].isConst() && node[0][2].isConst() ){
        // TODO (#1180) length entailment here
        if( node[0][1].getConst<String>().size()==node[0][2].getConst<String>().size() ){
          retNode = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, node[0][0] );
        }
      }
    }
  }else if( node.getKind() == kind::STRING_CHARAT ){
    Node one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
    retNode = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, node[0], node[1], one);
  }else if( node.getKind() == kind::STRING_SUBSTR ){
    retNode = rewriteSubstr(node);
  }else if( node.getKind() == kind::STRING_STRCTN ){
    retNode = rewriteContains( node );
  }else if( node.getKind()==kind::STRING_STRIDOF ){
    retNode = rewriteIndexof( node );
  }else if( node.getKind() == kind::STRING_STRREPL ){
    retNode = rewriteReplace( node );
  }
  else if (node.getKind() == kind::STRING_PREFIX
           || node.getKind() == kind::STRING_SUFFIX)
  {
    retNode = rewritePrefixSuffix(node);
  }else if(node.getKind() == kind::STRING_ITOS) {
    if(node[0].isConst()) {
      if( node[0].getConst<Rational>().sgn()==-1 ){
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
      }else{
        std::string stmp = node[0].getConst<Rational>().getNumerator().toString();
        Assert(stmp[0] != '-');
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String(stmp) );
      }
    }
  }else if(node.getKind() == kind::STRING_STOI) {
    if(node[0].isConst()) {
      CVC4::String s = node[0].getConst<String>();
      if(s.isNumber()) {
        std::string stmp = s.toString();
        //TODO: leading zeros : when smt2 standard for strings is set, uncomment this if applicable
        //if(stmp[0] == '0' && stmp.size() != 1) {
          //retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
        //} else {
          CVC4::Rational r2(stmp.c_str());
          retNode = NodeManager::currentNM()->mkConst( r2 );
        //}
      } else {
        retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
      }
    } else if(node[0].getKind() == kind::STRING_CONCAT) {
      for(unsigned i=0; i<node[0].getNumChildren(); ++i) {
        if(node[0][i].isConst()) {
          CVC4::String t = node[0][i].getConst<String>();
          if(!t.isNumber()) {
            retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
            break;
          }
        }
      }
    }
  } else if(node.getKind() == kind::STRING_IN_REGEXP) {
    retNode = rewriteMembership(node);
  }

  Trace("strings-postrewrite") << "Strings::postRewrite returning " << retNode << std::endl;
  if( orig!=retNode ){
    Trace("strings-rewrite-debug") << "Strings: post-rewrite " << orig << " to " << retNode << std::endl;
  }
  return RewriteResponse(orig==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}

bool TheoryStringsRewriter::hasEpsilonNode(TNode node) {
  for(unsigned int i=0; i<node.getNumChildren(); i++) {
    if(node[i].getKind() == kind::STRING_TO_REGEXP && node[i][0].getKind() == kind::CONST_STRING && node[i][0].getConst<String>().isEmptyString()) {
      return true;
    }
  }
  return false;
}

RewriteResponse TheoryStringsRewriter::preRewrite(TNode node) {
  Node retNode = node;
  Node orig = retNode;
  Trace("strings-prerewrite") << "Strings::preRewrite start " << node << std::endl;

  if (node.getKind() == kind::REGEXP_CONCAT)
  {
    retNode = prerewriteConcatRegExp(node);
  } else if(node.getKind() == kind::REGEXP_UNION) {
    retNode = prerewriteOrRegExp(node);
  } else if(node.getKind() == kind::REGEXP_INTER) {
    retNode = prerewriteAndRegExp(node);
  }
  else if(node.getKind() == kind::REGEXP_STAR) {
    if(node[0].getKind() == kind::REGEXP_STAR) {
      retNode = node[0];
    } else if(node[0].getKind() == kind::STRING_TO_REGEXP && node[0][0].getKind() == kind::CONST_STRING && node[0][0].getConst<String>().isEmptyString()) {
      retNode = node[0];
    } else if(node[0].getKind() == kind::REGEXP_EMPTY) {
      retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
    } else if(node[0].getKind() == kind::REGEXP_UNION) {
      Node tmpNode = prerewriteOrRegExp(node[0]);
      if(tmpNode.getKind() == kind::REGEXP_UNION) {
        if(hasEpsilonNode(node[0])) {
          std::vector< Node > node_vec;
          for(unsigned int i=0; i<node[0].getNumChildren(); i++) {
            if(node[0][i].getKind() == kind::STRING_TO_REGEXP && node[0][i][0].getKind() == kind::CONST_STRING && node[0][i][0].getConst<String>().isEmptyString()) {
              //return true;
            } else {
              node_vec.push_back(node[0][i]);
            }
          }
          retNode = node_vec.size()==1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, node_vec);
          retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, retNode);
        }
      } else if(tmpNode.getKind() == kind::STRING_TO_REGEXP && tmpNode[0].getKind() == kind::CONST_STRING && tmpNode[0].getConst<String>().isEmptyString()) {
        retNode = tmpNode;
      } else {
        retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, tmpNode);
      }
    }
  } else if(node.getKind() == kind::REGEXP_PLUS) {
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, node[0], NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, node[0]));
  } else if(node.getKind() == kind::REGEXP_OPT) {
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION,
          NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) ),
          node[0]);
  } else if(node.getKind() == kind::REGEXP_RANGE) {
    if(node[0] == node[1]) {
      retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, node[0] );
    }
    /*std::vector< Node > vec_nodes;
    unsigned char c = node[0].getConst<String>().getFirstChar();
    unsigned char end = node[1].getConst<String>().getFirstChar();
    for(; c<=end; ++c) {
      Node n = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String( c ) ) );
      vec_nodes.push_back( n );
    }
    if(vec_nodes.size() == 1) {
      retNode = vec_nodes[0];
    } else {
      retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
    }*/
  } else if(node.getKind() == kind::REGEXP_LOOP) {
    Node r = node[0];
    if(r.getKind() == kind::REGEXP_STAR) {
      retNode = r;
    } else {
      /* //lazy
      Node n1 = Rewriter::rewrite( node[1] );
      if(!n1.isConst()) {
        throw LogicException("re.loop contains non-constant integer (1).");
      }
      CVC4::Rational rz(0);
      CVC4::Rational RMAXINT(LONG_MAX);
      AlwaysAssert(rz <= n1.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (1)");
      Assert(n1.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (1)");
      unsigned l = n1.getConst<Rational>().getNumerator().toUnsignedInt();
      if(node.getNumChildren() == 3) {
        Node n2 = Rewriter::rewrite( node[2] );
        if(!n2.isConst()) {
          throw LogicException("re.loop contains non-constant integer (2).");
        }
        if(n1 == n2) {
          if(l == 0) {
            retNode = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP,
              NodeManager::currentNM()->mkConst(CVC4::String("")));
          } else if(l == 1) {
            retNode = node[0];
          }
        } else {
          AlwaysAssert(rz <= n2.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (2)");
          Assert(n2.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (2)");
          unsigned u = n2.getConst<Rational>().getNumerator().toUnsignedInt();
          AlwaysAssert(l <= u, "REGEXP_LOOP (1) > REGEXP_LOOP (2)");
          if(l != 0) {
            Node zero = NodeManager::currentNM()->mkConst( CVC4::Rational(0) );
            Node num = NodeManager::currentNM()->mkConst( CVC4::Rational(u - l) );
            Node t1 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], n1, n1);
            Node t2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], zero, num);
            retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, t1, t2);
          }
        }
      } else {
        retNode = l==0? NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, node[0]) :
          NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
            NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], n1, n1),
            NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, node[0]));
      }
    }*/ //lazy
    /*else {*/
      // eager
      TNode n1 = Rewriter::rewrite( node[1] );
      //
      if(!n1.isConst()) {
        throw LogicException("re.loop contains non-constant integer (1).");
      }
      CVC4::Rational rz(0);
      CVC4::Rational RMAXINT(LONG_MAX);
      AlwaysAssert(rz <= n1.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (1)");
      Assert(n1.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (1)");
      //
      unsigned l = n1.getConst<Rational>().getNumerator().toUnsignedInt();
      std::vector< Node > vec_nodes;
      for(unsigned i=0; i<l; i++) {
        vec_nodes.push_back(r);
      }
      if(node.getNumChildren() == 3) {
        TNode n2 = Rewriter::rewrite( node[2] );
        //if(!n2.isConst()) {
        //  throw LogicException("re.loop contains non-constant integer (2).");
        //}
        Node n = vec_nodes.size()==0 ? NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(CVC4::String("")))
          : vec_nodes.size()==1 ? r : prerewriteConcatRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes));
        //Assert(n2.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (2)");
        unsigned u = n2.getConst<Rational>().getNumerator().toUnsignedInt();
        if(u <= l) {
          retNode = n;
        } else {
          std::vector< Node > vec2;
          vec2.push_back(n);
          for(unsigned j=l; j<u; j++) {
            vec_nodes.push_back(r);
            n = vec_nodes.size()==1? r : prerewriteConcatRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes));
            vec2.push_back(n);
          }
          retNode = prerewriteOrRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec2));
        }
      } else {
        Node rest = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, r);
        retNode = vec_nodes.size()==0? rest : prerewriteConcatRegExp( vec_nodes.size()==1?
                 NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, r, rest)
                :NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
                  NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes), rest) );
      }
    }
    Trace("strings-lp") << "Strings::lp " << node << " => " << retNode << std::endl;
  }

  Trace("strings-prerewrite") << "Strings::preRewrite returning " << retNode << std::endl;
  if( orig!=retNode ){
    Trace("strings-rewrite-debug") << "Strings: pre-rewrite " << orig << " to " << retNode << std::endl;
  }
  return RewriteResponse(orig==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}

Node TheoryStringsRewriter::rewriteSubstr(Node node)
{
  Assert(node.getKind() == kind::STRING_SUBSTR);
  if (node[0].isConst())
  {
    if (node[0].getConst<String>().size() == 0)
    {
      Node ret = node[0];
      return returnRewrite(node, ret, "ss-emptystr");
    }
    // rewriting for constant arguments
    if (node[1].isConst() && node[2].isConst())
    {
      CVC4::String s = node[0].getConst<String>();
      CVC4::Rational RMAXINT(LONG_MAX);
      unsigned start;
      if (node[1].getConst<Rational>() > RMAXINT)
      {
        // start beyond the maximum size of strings
        // thus, it must be beyond the end point of this string
        Node ret = NodeManager::currentNM()->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-const-start-max-oob");
      }
      else if (node[1].getConst<Rational>().sgn() < 0)
      {
        // start before the beginning of the string
        Node ret = NodeManager::currentNM()->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-const-start-neg");
      }
      else
      {
        start = node[1].getConst<Rational>().getNumerator().toUnsignedInt();
        if (start >= s.size())
        {
          // start beyond the end of the string
          Node ret = NodeManager::currentNM()->mkConst(::CVC4::String(""));
          return returnRewrite(node, ret, "ss-const-start-oob");
        }
      }
      if (node[2].getConst<Rational>() > RMAXINT)
      {
        // take up to the end of the string
        Node ret = NodeManager::currentNM()->mkConst(
            ::CVC4::String(s.suffix(s.size() - start)));
        return returnRewrite(node, ret, "ss-const-len-max-oob");
      }
      else if (node[2].getConst<Rational>().sgn() <= 0)
      {
        Node ret = NodeManager::currentNM()->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-const-len-non-pos");
      }
      else
      {
        unsigned len =
            node[2].getConst<Rational>().getNumerator().toUnsignedInt();
        if (start + len > s.size())
        {
          // take up to the end of the string
          Node ret = NodeManager::currentNM()->mkConst(
              ::CVC4::String(s.suffix(s.size() - start)));
          return returnRewrite(node, ret, "ss-const-end-oob");
        }
        else
        {
          // compute the substr using the constant string
          Node ret = NodeManager::currentNM()->mkConst(
              ::CVC4::String(s.substr(start, len)));
          return returnRewrite(node, ret, "ss-const-ss");
        }
      }
    }
  }
  Node zero = NodeManager::currentNM()->mkConst(CVC4::Rational(0));

  // if entailed non-positive length or negative start point
  if (checkEntailArith(zero, node[1], true))
  {
    Node ret = NodeManager::currentNM()->mkConst(::CVC4::String(""));
    return returnRewrite(node, ret, "ss-start-neg");
  }
  else if (checkEntailArith(zero, node[2]))
  {
    Node ret = NodeManager::currentNM()->mkConst(::CVC4::String(""));
    return returnRewrite(node, ret, "ss-len-non-pos");
  }

  std::vector<Node> n1;
  getConcat(node[0], n1);

  // definite inclusion
  if (node[1] == zero)
  {
    Node curr = node[2];
    std::vector<Node> childrenr;
    if (stripSymbolicLength(n1, childrenr, 1, curr))
    {
      if (curr != zero && !n1.empty())
      {
        childrenr.push_back(
            NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR,
                                             mkConcat(kind::STRING_CONCAT, n1),
                                             node[1],
                                             curr));
      }
      Node ret = mkConcat(kind::STRING_CONCAT, childrenr);
      return returnRewrite(node, ret, "ss-len-include");
    }
  }

  // symbolic length analysis
  for (unsigned r = 0; r < 2; r++)
  {
    // the amount of characters we can strip
    Node curr;
    if (r == 0)
    {
      if (node[1] != zero)
      {
        // strip up to start point off the start of the string
        curr = node[1];
      }
    }
    else if (r == 1)
    {
      Node tot_len = Rewriter::rewrite(
          NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]));
      Node end_pt = Rewriter::rewrite(
          NodeManager::currentNM()->mkNode(kind::PLUS, node[1], node[2]));
      if (node[2] != tot_len)
      {
        if (checkEntailArith(node[2], tot_len))
        {
          // end point beyond end point of string, map to tot_len
          Node ret = NodeManager::currentNM()->mkNode(
              kind::STRING_SUBSTR, node[0], node[1], tot_len);
          return returnRewrite(node, ret, "ss-end-pt-norm");
        }
        else
        {
          // strip up to ( str.len(node[0]) - end_pt ) off the end of the string
          curr = Rewriter::rewrite(
              NodeManager::currentNM()->mkNode(kind::MINUS, tot_len, end_pt));
        }
      }
    }
    if (!curr.isNull())
    {
      // strip off components while quantity is entailed positive
      int dir = r == 0 ? 1 : -1;
      std::vector<Node> childrenr;
      if (stripSymbolicLength(n1, childrenr, dir, curr))
      {
        if (r == 0)
        {
          Node ret = NodeManager::currentNM()->mkNode(
              kind::STRING_SUBSTR,
              mkConcat(kind::STRING_CONCAT, n1),
              curr,
              node[2]);
          return returnRewrite(node, ret, "ss-strip-start-pt");
        }
        else
        {
          Node ret = NodeManager::currentNM()->mkNode(
              kind::STRING_SUBSTR,
              mkConcat(kind::STRING_CONCAT, n1),
              node[1],
              node[2]);
          return returnRewrite(node, ret, "ss-strip-end-pt");
        }
      }
    }
  }
  // combine substr
  if (node[0].getKind() == kind::STRING_SUBSTR)
  {
    Node start_inner = node[0][1];
    Node start_outer = node[1];
    if (checkEntailArith(start_outer) && checkEntailArith(start_inner))
    {
      // both are positive
      // thus, start point is definitely start_inner+start_outer.
      // We can rewrite if it for certain what the length is

      // the length of a string from the inner substr subtracts the start point
      // of the outer substr
      Node len_from_inner = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
          kind::MINUS, node[0][2], start_outer));
      Node len_from_outer = node[2];
      Node new_len;
      // take quantity that is for sure smaller than the other
      if (len_from_inner == len_from_outer)
      {
        new_len = len_from_inner;
      }
      else if (checkEntailArith(len_from_inner, len_from_outer))
      {
        new_len = len_from_outer;
      }
      else if (checkEntailArith(len_from_outer, len_from_inner))
      {
        new_len = len_from_inner;
      }
      if (!new_len.isNull())
      {
        Node new_start = NodeManager::currentNM()->mkNode(
            kind::PLUS, start_inner, start_outer);
        Node ret = NodeManager::currentNM()->mkNode(
            kind::STRING_SUBSTR, node[0][0], new_start, new_len);
        return returnRewrite(node, ret, "ss-combine");
      }
    }
  }
  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return node;
}

Node TheoryStringsRewriter::rewriteContains( Node node ) {
  Assert(node.getKind() == kind::STRING_STRCTN);
  if( node[0] == node[1] ){
    Node ret = NodeManager::currentNM()->mkConst(true);
    return returnRewrite(node, ret, "ctn-eq");
  }
  if (node[0].isConst())
  {
    CVC4::String s = node[0].getConst<String>();
    if (node[1].isConst())
    {
      CVC4::String t = node[1].getConst<String>();
      Node ret =
          NodeManager::currentNM()->mkConst(s.find(t) != std::string::npos);
      return returnRewrite(node, ret, "ctn-const");
    }else{
      if (s.size() == 0)
      {
        Node len1 =
            NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
        if (checkEntailArith(len1, true))
        {
          // we handle the false case here since the rewrite for equality
          // uses this function, hence we want to conclude false if possible.
          // len(x)>0 => contains( "", x ) ---> false
          Node ret = NodeManager::currentNM()->mkConst(false);
          return returnRewrite(node, ret, "ctn-lhs-emptystr");
        }
        // contains( "", x ) ---> ( "" = x )
        Node ret = node[0].eqNode(node[1]);
        return returnRewrite(node, ret, "ctn-lhs-emptystr-eq");
      }
      else if (node[1].getKind() == kind::STRING_CONCAT)
      {
        int firstc, lastc;
        if (!canConstantContainConcat(node[0], node[1], firstc, lastc))
        {
          Node ret = NodeManager::currentNM()->mkConst(false);
          return returnRewrite(node, ret, "ctn-nconst-ctn-concat");
        }
      }
    }
  }
  if (node[1].isConst())
  {
    CVC4::String t = node[1].getConst<String>();
    if (t.size() == 0)
    {
      // contains( x, "" ) ---> true
      Node ret = NodeManager::currentNM()->mkConst(true);
      return returnRewrite(node, ret, "ctn-rhs-emptystr");
    }
  }
  std::vector<Node> nc1;
  getConcat(node[0], nc1);
  std::vector<Node> nc2;
  getConcat(node[1], nc2);

  // component-wise containment
  std::vector<Node> nc1rb;
  std::vector<Node> nc1re;
  if (componentContains(nc1, nc2, nc1rb, nc1re) != -1)
  {
    Node ret = NodeManager::currentNM()->mkConst(true);
    return returnRewrite(node, ret, "ctn-component");
  }

  // strip endpoints
  std::vector<Node> nb;
  std::vector<Node> ne;
  if (stripConstantEndpoints(nc1, nc2, nb, ne))
  {
    Node ret = NodeManager::currentNM()->mkNode(
        kind::STRING_STRCTN, mkConcat(kind::STRING_CONCAT, nc1), node[1]);
    return returnRewrite(node, ret, "ctn-strip-endpt");
  }

  // length entailment
  Node len_n1 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]);
  Node len_n2 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
  if (checkEntailArith(len_n2, len_n1, true))
  {
    // len( n2 ) > len( n1 ) => contains( n1, n2 ) ---> false
    Node ret = NodeManager::currentNM()->mkConst(false);
    return returnRewrite(node, ret, "ctn-len-ineq");
  }

  // multi-set reasoning
  //   For example, contains( str.++( x, "b" ), str.++( "a", x ) ) ---> false
  //   since the number of a's in the second argument is greater than the number
  //   of a's in the first argument
  std::map<Node, unsigned> num_nconst[2];
  std::map<Node, unsigned> num_const[2];
  for (unsigned j = 0; j < 2; j++)
  {
    std::vector<Node>& ncj = j == 0 ? nc1 : nc2;
    for (const Node& cc : ncj)
    {
      if (cc.isConst())
      {
        num_const[j][cc]++;
      }
      else
      {
        num_nconst[j][cc]++;
      }
    }
  }
  bool ms_success = true;
  for (std::pair<const Node, unsigned>& nncp : num_nconst[0])
  {
    if (nncp.second > num_nconst[1][nncp.first])
    {
      ms_success = false;
      break;
    }
  }
  if (ms_success)
  {
    // count the number of constant characters in the first argument
    std::map<Node, unsigned> count_const[2];
    std::vector<Node> chars;
    for (unsigned j = 0; j < 2; j++)
    {
      for (std::pair<const Node, unsigned>& ncp : num_const[j])
      {
        Node cn = ncp.first;
        Assert(cn.isConst());
        std::vector<unsigned> cc_vec;
        const std::vector<unsigned>& cvec = cn.getConst<String>().getVec();
        for (unsigned i = 0, size = cvec.size(); i < size; i++)
        {
          // make the character
          cc_vec.clear();
          cc_vec.insert(cc_vec.end(), cvec.begin() + i, cvec.begin() + i + 1);
          Node ch = NodeManager::currentNM()->mkConst(String(cc_vec));
          count_const[j][ch] += ncp.second;
          if (std::find(chars.begin(), chars.end(), ch) == chars.end())
          {
            chars.push_back(ch);
          }
        }
      }
    }
    Trace("strings-rewrite-multiset") << "For " << node << " : " << std::endl;
    for (const Node& ch : chars)
    {
      Trace("strings-rewrite-multiset") << "  # occurrences of substring ";
      Trace("strings-rewrite-multiset") << ch << " in arguments is ";
      Trace("strings-rewrite-multiset") << count_const[0][ch] << " / "
                                        << count_const[1][ch] << std::endl;
      if (count_const[0][ch] < count_const[1][ch])
      {
        Node ret = NodeManager::currentNM()->mkConst(false);
        return returnRewrite(node, ret, "ctn-mset-nss");
      }
    }
    // TODO (#1180): count the number of 2,3,4,.. character substrings
    // for example:
    // str.contains( str.++( x, "cbabc" ), str.++( "cabbc", x ) ) ---> false
    // since the second argument contains more occurrences of "bb".
    // note this is orthogonal reasoning to inductive reasoning
    // via regular membership reduction in Liang et al CAV 2015.
  }
  // TODO (#1180): abstract interpretation with multi-set domain
  // to show first argument is a strict subset of second argument

  if (checkEntailArithEq(len_n1, len_n2))
  {
    // len( n2 ) = len( n1 ) => contains( n1, n2 ) ---> n1 = n2
    Node ret = node[0].eqNode(node[1]);
    return returnRewrite(node, ret, "ctn-len-eq");
  }

  // splitting
  if (node[0].getKind() == kind::STRING_CONCAT)
  {
    if( node[1].isConst() ){
      CVC4::String t = node[1].getConst<String>();
      // Below, we are looking for a constant component of node[0]
      // has no overlap with node[1], which means we can split.
      // Notice that if the first or last components had no
      // overlap, these would have been removed by strip
      // constant endpoints above.
      // Hence, we consider only the inner children.
      for (unsigned i = 1; i < (node[0].getNumChildren() - 1); i++)
      {
        //constant contains
        if( node[0][i].isConst() ){
          CVC4::String s = node[0][i].getConst<String>();
          // if no overlap, we can split into disjunction
          if (t.find(s) == std::string::npos && s.overlap(t) == 0
              && t.overlap(s) == 0)
          {
            std::vector<Node> nc0;
            getConcat(node[0], nc0);
            std::vector<Node> spl[2];
            spl[0].insert(spl[0].end(), nc0.begin(), nc0.begin() + i);
            Assert(i < nc0.size() - 1);
            spl[1].insert(spl[1].end(), nc0.begin() + i + 1, nc0.end());
            Node ret = NodeManager::currentNM()->mkNode(
                kind::OR,
                NodeManager::currentNM()->mkNode(
                    kind::STRING_STRCTN,
                    mkConcat(kind::STRING_CONCAT, spl[0]),
                    node[1]),
                NodeManager::currentNM()->mkNode(
                    kind::STRING_STRCTN,
                    mkConcat(kind::STRING_CONCAT, spl[1]),
                    node[1]));
            return returnRewrite(node, ret, "ctn-split");
          }
        }
      }
    }
  }

  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return node;
}

Node TheoryStringsRewriter::rewriteIndexof( Node node ) {
  Assert(node.getKind() == kind::STRING_STRIDOF);
  NodeManager* nm = NodeManager::currentNM();

  if (node[2].isConst() && node[2].getConst<Rational>().sgn() < 0)
  {
    // z<0  implies  str.indexof( x, y, z ) --> -1
    Node negone = nm->mkConst(Rational(-1));
    return returnRewrite(node, negone, "idof-neg");
  }

  // evaluation and simple cases
  std::vector<Node> children0;
  getConcat(node[0], children0);
  if (children0[0].isConst() && node[1].isConst() && node[2].isConst())
  {
    CVC4::Rational RMAXINT(CVC4::String::maxSize());
    if (node[2].getConst<Rational>() > RMAXINT)
    {
      // We know that, due to limitations on the size of string constants
      // in our implementation, that accessing a position greater than
      // RMAXINT is guaranteed to be out of bounds.
      Node negone = nm->mkConst(Rational(-1));
      return returnRewrite(node, negone, "idof-max");
    }
    Assert(node[2].getConst<Rational>().sgn() >= 0);
    unsigned start =
        node[2].getConst<Rational>().getNumerator().toUnsignedInt();
    CVC4::String s = children0[0].getConst<String>();
    CVC4::String t = node[1].getConst<String>();
    std::size_t ret = s.find(t, start);
    if (ret != std::string::npos)
    {
      Node retv = nm->mkConst(Rational(static_cast<unsigned>(ret)));
      return returnRewrite(node, retv, "idof-find");
    }
    else if (children0.size() == 1)
    {
      Node negone = nm->mkConst(Rational(-1));
      return returnRewrite(node, negone, "idof-nfind");
    }
  }

  Node len0 = nm->mkNode(kind::STRING_LENGTH, node[0]);
  Node len1 = nm->mkNode(kind::STRING_LENGTH, node[1]);
  Node len0m2 = nm->mkNode(kind::MINUS, len0, node[2]);
  if (checkEntailArith(len1, len0m2, true))
  {
    // len(x)-z < len(y)  implies  indexof( x, y, z ) ----> -1
    Node negone = nm->mkConst(Rational(-1));
    return returnRewrite(node, negone, "idof-len");
  }

  Node fstr = node[0];
  if (!node[2].isConst() || node[2].getConst<Rational>().sgn() != 0)
  {
    fstr = nm->mkNode(kind::STRING_SUBSTR, node[0], node[2], len0);
    fstr = Rewriter::rewrite(fstr);
  }

  Node cmp_con = nm->mkNode(kind::STRING_STRCTN, fstr, node[1]);
  Node cmp_conr = Rewriter::rewrite(cmp_con);
  if (cmp_conr.isConst())
  {
    if (cmp_conr.getConst<bool>())
    {
      if (node[2].isConst() && node[2].getConst<Rational>().sgn() == 0)
      {
        // past the first position in node[0] that contains node[1], we can drop
        std::vector<Node> children1;
        getConcat(node[1], children1);
        std::vector<Node> nb;
        std::vector<Node> ne;
        int cc = componentContains(children0, children1, nb, ne, true, 1);
        if (cc != -1 && !ne.empty())
        {
          // For example:
          // str.indexof(str.++(x,y,z),y,0) ---> str.indexof(str.++(x,y),y,0)
          Node nn = mkConcat(kind::STRING_CONCAT, children0);
          Node ret = nm->mkNode(kind::STRING_STRIDOF, nn, node[1], node[2]);
          return returnRewrite(node, ret, "idof-def-ctn");
        }
      }

      // these rewrites are only possible if we will not return -1
      Node l1 = nm->mkNode(kind::STRING_LENGTH, node[1]);
      Node zero = NodeManager::currentNM()->mkConst(CVC4::Rational(0));
      bool is_non_empty = checkEntailArith(l1, zero, true);

      if (is_non_empty)
      {
        // strip symbolic length
        Node new_len = node[2];
        std::vector<Node> nr;
        if (stripSymbolicLength(children0, nr, 1, new_len))
        {
          // For example:
          // z>str.len( x1 ) and str.len( y )>0 and str.contains( x2, y )-->true
          // implies
          // str.indexof( str.++( x1, x2 ), y, z ) --->
          // str.len( x1 ) + str.indexof( x2, y, z-str.len(x1) )
          Node nn = mkConcat(kind::STRING_CONCAT, children0);
          Node ret = nm->mkNode(
              kind::PLUS,
              nm->mkNode(kind::MINUS, node[2], new_len),
              nm->mkNode(kind::STRING_STRIDOF, nn, node[1], new_len));
          return returnRewrite(node, ret, "idof-strip-sym-len");
        }
      }
    }
    else
    {
      // str.contains( x, y ) --> false  implies  str.indexof(x,y,z) --> -1
      Node negone = nm->mkConst(Rational(-1));
      return returnRewrite(node, negone, "idof-nctn");
    }
  }

  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return node;
}

Node TheoryStringsRewriter::rewriteReplace( Node node ) {
  Assert(node.getKind() == kind::STRING_STRREPL);
  NodeManager* nm = NodeManager::currentNM();

  if (node[1] == node[2])
  {
    return returnRewrite(node, node[0], "rpl-id");
  }

  if (node[0] == node[1])
  {
    return returnRewrite(node, node[2], "rpl-replace");
  }

  if (node[1].isConst() && node[1].getConst<String>().isEmptyString())
  {
    Node ret = nm->mkNode(STRING_CONCAT, node[2], node[0]);
    return returnRewrite(node, ret, "rpl-rpl-empty");
  }

  std::vector<Node> children0;
  getConcat(node[0], children0);

  if (node[1].isConst() && children0[0].isConst())
  {
    CVC4::String s = children0[0].getConst<String>();
    CVC4::String t = node[1].getConst<String>();
    std::size_t p = s.find(t);
    if (p == std::string::npos)
    {
      if (children0.size() == 1)
      {
        return returnRewrite(node, node[0], "rpl-const-nfind");
      }
      // if no overlap, we can pull the first child
      if (s.overlap(t) == 0)
      {
        std::vector<Node> spl(children0.begin() + 1, children0.end());
        Node ret = NodeManager::currentNM()->mkNode(
            kind::STRING_CONCAT,
            children0[0],
            NodeManager::currentNM()->mkNode(kind::STRING_STRREPL,
                                             mkConcat(kind::STRING_CONCAT, spl),
                                             node[1],
                                             node[2]));
        return returnRewrite(node, ret, "rpl-prefix-nfind");
      }
    }
    else
    {
      CVC4::String s1 = s.substr(0, (int)p);
      CVC4::String s3 = s.substr((int)p + (int)t.size());
      Node ns1 = NodeManager::currentNM()->mkConst(::CVC4::String(s1));
      Node ns3 = NodeManager::currentNM()->mkConst(::CVC4::String(s3));
      std::vector<Node> children;
      children.push_back(ns1);
      children.push_back(node[2]);
      children.push_back(ns3);
      children.insert(children.end(), children0.begin() + 1, children0.end());
      Node ret = mkConcat(kind::STRING_CONCAT, children);
      return returnRewrite(node, ret, "rpl-const-find");
    }
  }

  if (node[0] == node[2])
  {
    // ( len( y )>=len(x) ) => str.replace( x, y, x ) ---> x
    Node l0 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]);
    Node l1 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
    if (checkEntailArith(l1, l0))
    {
      return returnRewrite(node, node[0], "rpl-rpl-len-id");
    }
  }

  std::vector<Node> children1;
  getConcat(node[1], children1);

  // check if contains definitely does (or does not) hold
  Node cmp_con =
      NodeManager::currentNM()->mkNode(kind::STRING_STRCTN, node[0], node[1]);
  Node cmp_conr = Rewriter::rewrite(cmp_con);
  if (cmp_conr.isConst())
  {
    if (cmp_conr.getConst<bool>())
    {
      // component-wise containment
      std::vector<Node> cb;
      std::vector<Node> ce;
      int cc = componentContains(children0, children1, cb, ce, true, 1);
      if (cc != -1)
      {
        if (cc == 0 && children0[0] == children1[0])
        {
          // definitely a prefix, can do the replace
          // for example,
          //   str.replace( str.++( x, "ab" ), str.++( x, "a" ), y )  --->
          //   str.++( y, "b" )
          std::vector<Node> cres;
          cres.push_back(node[2]);
          cres.insert(cres.end(), ce.begin(), ce.end());
          Node ret = mkConcat(kind::STRING_CONCAT, cres);
          return returnRewrite(node, ret, "rpl-cctn-rpl");
        }
        else if (!ce.empty())
        {
          // we can pull remainder past first definite containment
          // for example,
          //   str.replace( str.++( x, "ab" ), "a", y ) --->
          //   str.++( str.replace( str.++( x, "a" ), "a", y ), "b" )
          // this is independent of whether the second argument may be empty
          std::vector<Node> cc;
          cc.push_back(NodeManager::currentNM()->mkNode(
              kind::STRING_STRREPL,
              mkConcat(kind::STRING_CONCAT, children0),
              node[1],
              node[2]));
          cc.insert(cc.end(), ce.begin(), ce.end());
          Node ret = mkConcat(kind::STRING_CONCAT, cc);
          return returnRewrite(node, ret, "rpl-cctn");
        }
      }
    }
    else
    {
      // ~contains( t, s ) => ( replace( t, s, r ) ----> t )
      return returnRewrite(node, node[0], "rpl-nctn");
    }
  }

  if (cmp_conr != cmp_con)
  {
    if (checkEntailNonEmpty(node[1]))
    {
      // pull endpoints that can be stripped
      // for example,
      //   str.replace( str.++( "b", x, "b" ), "a", y ) --->
      //   str.++( "b", str.replace( x, "a", y ), "b" )
      std::vector<Node> cb;
      std::vector<Node> ce;
      if (stripConstantEndpoints(children0, children1, cb, ce))
      {
        std::vector<Node> cc;
        cc.insert(cc.end(), cb.begin(), cb.end());
        cc.push_back(NodeManager::currentNM()->mkNode(
            kind::STRING_STRREPL,
            mkConcat(kind::STRING_CONCAT, children0),
            node[1],
            node[2]));
        cc.insert(cc.end(), ce.begin(), ce.end());
        Node ret = mkConcat(kind::STRING_CONCAT, cc);
        return returnRewrite(node, ret, "rpl-pull-endpt");
      }
    }
  }

  // TODO (#1180) incorporate these?
  // contains( t, s ) =>
  //   replace( replace( x, t, s ), s, r ) ----> replace( x, t, r )
  // contains( t, s ) =>
  //   contains( replace( t, s, r ), r ) ----> true

  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return node;
}

Node TheoryStringsRewriter::rewritePrefixSuffix(Node n)
{
  Assert(n.getKind() == kind::STRING_PREFIX
         || n.getKind() == kind::STRING_SUFFIX);
  bool isPrefix = n.getKind() == kind::STRING_PREFIX;
  if (n[0] == n[1])
  {
    Node ret = NodeManager::currentNM()->mkConst(true);
    return returnRewrite(n, ret, "suf/prefix-eq");
  }
  if (n[0].isConst())
  {
    CVC4::String t = n[0].getConst<String>();
    if (t.isEmptyString())
    {
      Node ret = NodeManager::currentNM()->mkConst(true);
      return returnRewrite(n, ret, "suf/prefix-empty-const");
    }
  }
  if (n[1].isConst())
  {
    CVC4::String s = n[1].getConst<String>();
    if (n[0].isConst())
    {
      Node ret = NodeManager::currentNM()->mkConst(false);
      CVC4::String t = n[0].getConst<String>();
      if (s.size() >= t.size())
      {
        if ((isPrefix && t == s.prefix(t.size()))
            || (!isPrefix && t == s.suffix(t.size())))
        {
          ret = NodeManager::currentNM()->mkConst(true);
        }
      }
      return returnRewrite(n, ret, "suf/prefix-const");
    }
    else if (s.isEmptyString())
    {
      Node ret = n[0].eqNode(n[1]);
      return returnRewrite(n, ret, "suf/prefix-empty");
    }
    else if (s.size() == 1)
    {
      // (str.prefix x "A") and (str.suffix x "A") are equivalent to
      // (str.contains "A" x )
      Node ret =
          NodeManager::currentNM()->mkNode(kind::STRING_STRCTN, n[1], n[0]);
      return returnRewrite(n, ret, "suf/prefix-ctn");
    }
  }
  Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[0]);
  Node lent = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n[1]);
  Node val;
  if (isPrefix)
  {
    val = NodeManager::currentNM()->mkConst(::CVC4::Rational(0));
  }
  else
  {
    val = NodeManager::currentNM()->mkNode(kind::MINUS, lent, lens);
  }
  // general reduction to equality + substr
  Node retNode = n[0].eqNode(
      NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, n[1], val, lens));
  // add length constraint if it cannot be shown by simple entailment check
  if (!checkEntailArith(lent, lens))
  {
    retNode = NodeManager::currentNM()->mkNode(
        kind::AND,
        retNode,
        NodeManager::currentNM()->mkNode(kind::GEQ, lent, lens));
  }
  return retNode;
}

void TheoryStringsRewriter::getConcat( Node n, std::vector< Node >& c ) {
  if( n.getKind()==kind::STRING_CONCAT || n.getKind()==kind::REGEXP_CONCAT ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      c.push_back( n[i] );
    }
  }else{
    c.push_back( n );
  }
}

Node TheoryStringsRewriter::mkConcat( Kind k, std::vector< Node >& c ){
  Assert( !c.empty() || k==kind::STRING_CONCAT );
  return c.size()>1 ? NodeManager::currentNM()->mkNode( k, c ) : ( c.size()==1 ? c[0] : NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
}

Node TheoryStringsRewriter::splitConstant( Node a, Node b, int& index, bool isRev ) {
  Assert( a.isConst() && b.isConst() );
  index = a.getConst<String>().size() <= b.getConst<String>().size() ? 1 : 0;
  unsigned len_short = index==1 ? a.getConst<String>().size() : b.getConst<String>().size();
  bool cmp = isRev ? a.getConst<String>().rstrncmp(b.getConst<String>(), len_short): a.getConst<String>().strncmp(b.getConst<String>(), len_short);
  if( cmp ) {
    Node l = index==0 ? a : b;
    if( isRev ){
      int new_len = l.getConst<String>().size() - len_short;
      return NodeManager::currentNM()->mkConst(l.getConst<String>().substr( 0, new_len ));
    }else{
      return NodeManager::currentNM()->mkConst(l.getConst<String>().substr( len_short ));
    }
  }else{
    //not the same prefix/suffix
    return Node::null();
  }
}

bool TheoryStringsRewriter::canConstantContainConcat( Node c, Node n, int& firstc, int& lastc ) {
  Assert( c.isConst() );
  CVC4::String t = c.getConst<String>();
  const std::vector<unsigned>& tvec = t.getVec();
  Assert( n.getKind()==kind::STRING_CONCAT );
  //must find constant components in order
  size_t pos = 0;
  firstc = -1;
  lastc = -1;
  for(unsigned i=0; i<n.getNumChildren(); i++) {
    if( n[i].isConst() ){
      firstc = firstc==-1 ? i : firstc;
      lastc = i;
      CVC4::String s = n[i].getConst<String>();
      size_t new_pos = t.find(s,pos);
      if( new_pos==std::string::npos ) {
        return false;
      }else{
        pos = new_pos + s.size();
      }
    }
    else if (n[i].getKind() == kind::STRING_ITOS)
    {
      // find the first occurrence of a digit starting at pos
      while (pos < tvec.size() && !String::isDigit(tvec[pos]))
      {
        pos++;
      }
      if (pos == tvec.size())
      {
        return false;
      }
      // must consume at least one digit here
      pos++;
    }
  }
  return true;
}

bool TheoryStringsRewriter::canConstantContainList( Node c, std::vector< Node >& l, int& firstc, int& lastc ) {
  Assert( c.isConst() );
  CVC4::String t = c.getConst<String>();
  //must find constant components in order
  size_t pos = 0;
  firstc = -1;
  lastc = -1;
  for(unsigned i=0; i<l.size(); i++) {
    if( l[i].isConst() ){
      firstc = firstc==-1 ? i : firstc;
      lastc = i;
      CVC4::String s = l[i].getConst<String>();
      size_t new_pos = t.find(s,pos);
      if( new_pos==std::string::npos ) {
        return false;
      }else{
        pos = new_pos + s.size();
      }
    }
  }
  return true;
}

Node TheoryStringsRewriter::getNextConstantAt( std::vector< Node >& vec, unsigned& start_index, unsigned& end_index, bool isRev ) {
  while( vec.size()>start_index && !vec[ start_index ].isConst() ){
    //return Node::null();
    start_index++;
  }
  if( start_index<vec.size() ){    
    end_index = start_index;
    return collectConstantStringAt( vec, end_index, isRev );
  }else{
    return Node::null();
  }
}

Node TheoryStringsRewriter::collectConstantStringAt( std::vector< Node >& vec, unsigned& end_index, bool isRev ) {
  std::vector< Node > c;
  while( vec.size()>end_index && vec[ end_index ].isConst() ){
    c.push_back( vec[ end_index ] );
    end_index++;
    //break;
  }
  if( !c.empty() ){
    if( isRev ){
      std::reverse( c.begin(), c.end() );
    }
    Node cc = Rewriter::rewrite( mkConcat( kind::STRING_CONCAT, c ) );
    Assert( cc.isConst() );
    return cc;
  }else{
    return Node::null();
  }
}

bool TheoryStringsRewriter::stripSymbolicLength(std::vector<Node>& n1,
                                                std::vector<Node>& nr,
                                                int dir,
                                                Node& curr)
{
  Assert(dir == 1 || dir == -1);
  Assert(nr.empty());
  Node zero = NodeManager::currentNM()->mkConst(CVC4::Rational(0));
  bool ret = false;
  bool success;
  unsigned sindex = 0;
  do
  {
    Assert(!curr.isNull());
    success = false;
    if (curr != zero && sindex < n1.size())
    {
      unsigned sindex_use = dir == 1 ? sindex : ((n1.size() - 1) - sindex);
      if (n1[sindex_use].isConst())
      {
        // could strip part of a constant
        Node lowerBound = getConstantArithBound(curr);
        if (!lowerBound.isNull())
        {
          Assert(lowerBound.isConst());
          Rational lbr = lowerBound.getConst<Rational>();
          if (lbr.sgn() > 0)
          {
            Assert(checkEntailArith(curr, true));
            CVC4::String s = n1[sindex_use].getConst<String>();
            Node ncl =
                NodeManager::currentNM()->mkConst(CVC4::Rational(s.size()));
            Node next_s =
                NodeManager::currentNM()->mkNode(kind::MINUS, lowerBound, ncl);
            next_s = Rewriter::rewrite(next_s);
            Assert(next_s.isConst());
            // we can remove the entire constant
            if (next_s.getConst<Rational>().sgn() >= 0)
            {
              curr = Rewriter::rewrite(
                  NodeManager::currentNM()->mkNode(kind::MINUS, curr, ncl));
              success = true;
              sindex++;
            }
            else
            {
              // we can remove part of the constant
              // lower bound minus the length of a concrete string is negative,
              // hence lowerBound cannot be larger than long max
              Assert(lbr < Rational(LONG_MAX));
              curr = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
                  kind::MINUS, curr, lowerBound));
              unsigned lbsize = lbr.getNumerator().toUnsignedInt();
              Assert(lbsize < s.size());
              if (dir == 1)
              {
                // strip partially from the front
                nr.push_back(
                    NodeManager::currentNM()->mkConst(s.prefix(lbsize)));
                n1[sindex_use] = NodeManager::currentNM()->mkConst(
                    s.suffix(s.size() - lbsize));
              }
              else
              {
                // strip partially from the back
                nr.push_back(
                    NodeManager::currentNM()->mkConst(s.suffix(lbsize)));
                n1[sindex_use] = NodeManager::currentNM()->mkConst(
                    s.prefix(s.size() - lbsize));
              }
              ret = true;
            }
            Assert(checkEntailArith(curr));
          }
          else
          {
            // we cannot remove the constant
          }
        }
      }
      else
      {
        Node next_s = NodeManager::currentNM()->mkNode(
            kind::MINUS,
            curr,
            NodeManager::currentNM()->mkNode(kind::STRING_LENGTH,
                                             n1[sindex_use]));
        next_s = Rewriter::rewrite(next_s);
        if (checkEntailArith(next_s))
        {
          success = true;
          curr = next_s;
          sindex++;
        }
      }
    }
  } while (success);
  if (sindex > 0)
  {
    if (dir == 1)
    {
      nr.insert(nr.begin(), n1.begin(), n1.begin() + sindex);
      n1.erase(n1.begin(), n1.begin() + sindex);
    }
    else
    {
      nr.insert(nr.end(), n1.end() - sindex, n1.end());
      n1.erase(n1.end() - sindex, n1.end());
    }
    ret = true;
  }
  return ret;
}

int TheoryStringsRewriter::componentContains(std::vector<Node>& n1,
                                             std::vector<Node>& n2,
                                             std::vector<Node>& nb,
                                             std::vector<Node>& ne,
                                             bool computeRemainder,
                                             int remainderDir)
{
  Assert(nb.empty());
  Assert(ne.empty());
  // if n2 is a singleton, we can do optimized version here
  if (n2.size() == 1)
  {
    for (unsigned i = 0; i < n1.size(); i++)
    {
      Node n1rb;
      Node n1re;
      if (componentContainsBase(n1[i], n2[0], n1rb, n1re, 0, computeRemainder))
      {
        if (computeRemainder)
        {
          n1[i] = n2[0];
          if (remainderDir != -1)
          {
            if (!n1re.isNull())
            {
              ne.push_back(n1re);
            }
            ne.insert(ne.end(), n1.begin() + i + 1, n1.end());
            n1.erase(n1.begin() + i + 1, n1.end());
          }
          else if (!n1re.isNull())
          {
            n1[i] = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
                kind::STRING_CONCAT, n1[i], n1re));
          }
          if (remainderDir != 1)
          {
            nb.insert(nb.end(), n1.begin(), n1.begin() + i);
            n1.erase(n1.begin(), n1.begin() + i);
            if (!n1rb.isNull())
            {
              nb.push_back(n1rb);
            }
          }
          else if (!n1rb.isNull())
          {
            n1[i] = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
                kind::STRING_CONCAT, n1rb, n1[i]));
          }
        }
        return i;
      }
    }
  }
  else if (n1.size() >= n2.size())
  {
    unsigned diff = n1.size() - n2.size();
    for (unsigned i = 0; i <= diff; i++)
    {
      Node n1rb_first;
      Node n1re_first;
      // first component of n2 must be a suffix
      if (componentContainsBase(n1[i],
                                n2[0],
                                n1rb_first,
                                n1re_first,
                                1,
                                computeRemainder && remainderDir != 1))
      {
        Assert(n1re_first.isNull());
        for (unsigned j = 1; j < n2.size(); j++)
        {
          // are we in the last component?
          if (j + 1 == n2.size())
          {
            Node n1rb_last;
            Node n1re_last;
            // last component of n2 must be a prefix
            if (componentContainsBase(n1[i + j],
                                      n2[j],
                                      n1rb_last,
                                      n1re_last,
                                      -1,
                                      computeRemainder && remainderDir != -1))
            {
              Assert(n1rb_last.isNull());
              if (computeRemainder)
              {
                if (remainderDir != -1)
                {
                  if (!n1re_last.isNull())
                  {
                    ne.push_back(n1re_last);
                  }
                  ne.insert(ne.end(), n1.begin() + i + j + 1, n1.end());
                  n1.erase(n1.begin() + i + j + 1, n1.end());
                  n1[i + j] = n2[j];
                }
                if (remainderDir != 1)
                {
                  n1[i] = n2[0];
                  nb.insert(nb.end(), n1.begin(), n1.begin() + i);
                  n1.erase(n1.begin(), n1.begin() + i);
                  if (!n1rb_first.isNull())
                  {
                    nb.push_back(n1rb_first);
                  }
                }
              }
              return i;
            }
            else
            {
              break;
            }
          }
          else if (n1[i + j] != n2[j])
          {
            break;
          }
        }
      }
    }
  }
  return -1;
}

bool TheoryStringsRewriter::componentContainsBase(
    Node n1, Node n2, Node& n1rb, Node& n1re, int dir, bool computeRemainder)
{
  Assert(n1rb.isNull());
  Assert(n1re.isNull());
  if (n1 == n2)
  {
    return true;
  }
  else
  {
    if (n1.isConst() && n2.isConst())
    {
      CVC4::String s = n1.getConst<String>();
      CVC4::String t = n2.getConst<String>();
      if (t.size() < s.size())
      {
        if (dir == 1)
        {
          if (s.suffix(t.size()) == t)
          {
            if (computeRemainder)
            {
              n1rb = NodeManager::currentNM()->mkConst(
                  ::CVC4::String(s.prefix(s.size() - t.size())));
            }
            return true;
          }
        }
        else if (dir == -1)
        {
          if (s.prefix(t.size()) == t)
          {
            if (computeRemainder)
            {
              n1re = NodeManager::currentNM()->mkConst(
                  ::CVC4::String(s.suffix(s.size() - t.size())));
            }
            return true;
          }
        }
        else
        {
          size_t f = s.find(t);
          if (f != std::string::npos)
          {
            if (computeRemainder)
            {
              if (f > 0)
              {
                n1rb = NodeManager::currentNM()->mkConst(
                    ::CVC4::String(s.prefix(f)));
              }
              if (s.size() > f + t.size())
              {
                n1re = NodeManager::currentNM()->mkConst(
                    ::CVC4::String(s.suffix(s.size() - (f + t.size()))));
              }
            }
            return true;
          }
        }
      }
    }
    else
    {
      // cases for:
      //   n1 = x   containing   n2 = substr( x, n2[1], n2[2] )
      if (n2.getKind() == kind::STRING_SUBSTR)
      {
        if (n2[0] == n1)
        {
          bool success = true;
          Node start_pos = n2[1];
          Node end_pos =
              NodeManager::currentNM()->mkNode(kind::PLUS, n2[1], n2[2]);
          Node len_n2s =
              NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n2[0]);
          if (dir == 1)
          {
            // To be a suffix, start + length must be greater than
            // or equal to the length of the string.
            success = checkEntailArith(end_pos, len_n2s);
          }
          else if (dir == -1)
          {
            // To be a prefix, must literally start at 0, since
            //   if we knew it started at <0, it should be rewritten to "",
            //   if we knew it started at 0, then n2[1] should be rewritten to
            //   0.
            success = start_pos.isConst()
                      && start_pos.getConst<Rational>().sgn() == 0;
          }
          if (success)
          {
            if (computeRemainder)
            {
              // we can only compute the remainder if start_pos and end_pos
              // are known to be non-negative.
              if (!checkEntailArith(start_pos) || !checkEntailArith(end_pos))
              {
                return false;
              }
              if (dir != 1)
              {
                n1rb = NodeManager::currentNM()->mkNode(
                    kind::STRING_SUBSTR,
                    n2[0],
                    NodeManager::currentNM()->mkConst(Rational(0)),
                    start_pos);
              }
              if (dir != -1)
              {
                n1re = NodeManager::currentNM()->mkNode(
                    kind::STRING_SUBSTR, n2[0], end_pos, len_n2s);
              }
            }
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool TheoryStringsRewriter::stripConstantEndpoints(std::vector<Node>& n1,
                                                   std::vector<Node>& n2,
                                                   std::vector<Node>& nb,
                                                   std::vector<Node>& ne,
                                                   int dir)
{
  Assert(nb.empty());
  Assert(ne.empty());
  bool changed = false;
  // for ( forwards, backwards ) direction
  for (unsigned r = 0; r < 2; r++)
  {
    if (dir == 0 || (r == 0 && dir == -1) || (r == 1 && dir == 1))
    {
      unsigned index0 = r == 0 ? 0 : n1.size() - 1;
      unsigned index1 = r == 0 ? 0 : n2.size() - 1;
      bool removeComponent = false;
      Trace("strings-rewrite-debug2") << "stripConstantEndpoints : Compare "
                                      << n1[index0] << " " << n2[index1]
                                      << ", dir = " << dir << std::endl;
      if (n1[index0].isConst())
      {
        CVC4::String s = n1[index0].getConst<String>();
        // overlap is an overapproximation of the number of characters
        // n2[index1] can match in s
        unsigned overlap = s.size();
        if (n2[index1].isConst())
        {
          CVC4::String t = n2[index1].getConst<String>();
          std::size_t ret = r == 0 ? s.find(t) : s.rfind(t);
          if (ret == std::string::npos)
          {
            if (n1.size() == 1)
            {
              // can remove everything
              //   e.g. str.contains( "abc", str.++( "ba", x ) ) -->
              //   str.contains( "", str.++( "ba", x ) )
              removeComponent = true;
            }
            else
            {
              // check how much overlap there is
              // This is used to partially strip off the endpoint
              // e.g. str.contains( str.++( "abc", x ), str.++( "cd", y ) ) -->
              // str.contains( str.++( "c", x ), str.++( "cd", y ) )
              overlap = r == 0 ? s.overlap(t) : t.overlap(s);
            }
          }
          else
          {
            Assert(ret < s.size());
            // can strip off up to the find position, e.g.
            // str.contains( str.++( "abc", x ), str.++( "b", y ) ) -->
            // str.contains( str.++( "bc", x ), str.++( "b", y ) ),
            // and
            // str.contains( str.++( x, "abbd" ), str.++( y, "b" ) ) -->
            // str.contains( str.++( x, "abb" ), str.++( y, "b" ) )
            overlap = s.size() - ret;
          }
        }
        else if (n2[index1].getKind() == kind::STRING_ITOS)
        {
          const std::vector<unsigned>& svec = s.getVec();
          // can remove up to the first occurrence of a digit
          for (unsigned i = 0; i < svec.size(); i++)
          {
            unsigned sindex = r == 0 ? i : svec.size() - i;
            if (String::isDigit(svec[sindex]))
            {
              break;
            }
            else
            {
              // e.g. str.contains( str.++( "a", x ), int.to.str(y) ) -->
              // str.contains( x, int.to.str(y) )
              overlap--;
            }
          }
        }
        else
        {
          // inconclusive
        }
        // process the overlap
        if (overlap < s.size())
        {
          changed = true;
          if (overlap == 0)
          {
            removeComponent = true;
          }
          else
          {
            // can drop the prefix (resp. suffix) from the first (resp. last)
            // component
            if (r == 0)
            {
              nb.push_back(
                  NodeManager::currentNM()->mkConst(s.prefix(overlap)));
              n1[index0] = NodeManager::currentNM()->mkConst(s.suffix(overlap));
            }
            else
            {
              ne.push_back(
                  NodeManager::currentNM()->mkConst(s.suffix(overlap)));
              n1[index0] = NodeManager::currentNM()->mkConst(s.prefix(overlap));
            }
          }
        }
      }
      else if (n1[index0].getKind() == kind::STRING_ITOS)
      {
        if (n2[index1].isConst())
        {
          CVC4::String t = n2[index1].getConst<String>();

          if (n1.size() == 1)
          {
            // if n1.size()==1, then if n2[index1] is not a number, we can drop
            // the entire component
            //    e.g. str.contains( int.to.str(x), "123a45") --> false
            if (!t.isNumber())
            {
              removeComponent = true;
            }
          }
          else
          {
            const std::vector<unsigned>& tvec = t.getVec();
            Assert(tvec.size() > 0);

            // if n1.size()>1, then if the first (resp. last) character of
            // n2[index1]
            //  is not a digit, we can drop the entire component, e.g.:
            //    str.contains( str.++( int.to.str(x), y ), "a12") -->
            //    str.contains( y, "a12" )
            //    str.contains( str.++( y, int.to.str(x) ), "a0b") -->
            //    str.contains( y, "a0b" )
            unsigned i = r == 0 ? 0 : (tvec.size() - 1);
            if (!String::isDigit(tvec[i]))
            {
              removeComponent = true;
            }
          }
        }
      }
      if (removeComponent)
      {
        // can drop entire first (resp. last) component
        if (r == 0)
        {
          nb.push_back(n1[index0]);
          n1.erase(n1.begin(), n1.begin() + 1);
        }
        else
        {
          ne.push_back(n1[index0]);
          n1.pop_back();
        }
        if (n1.empty())
        {
          // if we've removed everything, just return (we will rewrite to false)
          return true;
        }
        else
        {
          changed = true;
        }
      }
    }
  }
  // TODO (#1180) : computing the maximal overlap in this function may be
  // important.
  // str.contains( str.++( str.to.int(x), str.substr(y,0,3) ), "2aaaa" ) --->
  // false
  //   ...since str.to.int(x) can contain at most 1 character from "2aaaa",
  //   leaving 4 characters
  //      which is larger that the upper bound for length of str.substr(y,0,3),
  //      which is 3.
  return changed;
}

bool TheoryStringsRewriter::checkEntailNonEmpty(Node a)
{
  Node len = NodeManager::currentNM()->mkNode(STRING_LENGTH, a);
  len = Rewriter::rewrite(len);
  return checkEntailArith(len, true);
}

bool TheoryStringsRewriter::checkEntailArithEq(Node a, Node b)
{
  if (a == b)
  {
    return true;
  }
  else
  {
    Node ar = Rewriter::rewrite(a);
    Node br = Rewriter::rewrite(b);
    return ar == br;
  }
}

bool TheoryStringsRewriter::checkEntailArith(Node a, Node b, bool strict)
{
  if (a == b)
  {
    return !strict;
  }
  else
  {
    Node diff = NodeManager::currentNM()->mkNode(kind::MINUS, a, b);
    return checkEntailArith(diff, strict);
  }
}

bool TheoryStringsRewriter::checkEntailArith(Node a, bool strict)
{
  if (a.isConst())
  {
    return a.getConst<Rational>().sgn() >= (strict ? 1 : 0);
  }
  else
  {
    Node ar = strict
                  ? NodeManager::currentNM()->mkNode(
                        kind::MINUS,
                        a,
                        NodeManager::currentNM()->mkConst(Rational(1)))
                  : a;
    ar = Rewriter::rewrite(ar);
    if (checkEntailArithInternal(ar))
    {
      return true;
    }
    // TODO (#1180) : abstract interpretation goes here

    // over approximation O/U

    // O( x + y ) -> O( x ) + O( y )
    // O( c * x ) -> O( x ) if c > 0, U( x ) if c < 0
    // O( len( x ) ) -> len( x )
    // O( len( int.to.str( x ) ) ) -> len( int.to.str( x ) )
    // O( len( str.substr( x, n1, n2 ) ) ) -> O( n2 ) | O( len( x ) )
    // O( len( str.replace( x, y, z ) ) ) ->
    //   O( len( x ) ) + O( len( z ) ) - U( len( y ) )
    // O( indexof( x, y, n ) ) -> O( len( x ) ) - U( len( y ) )
    // O( str.to.int( x ) ) -> str.to.int( x )

    // U( x + y ) -> U( x ) + U( y )
    // U( c * x ) -> U( x ) if c > 0, O( x ) if c < 0
    // U( len( x ) ) -> len( x )
    // U( len( int.to.str( x ) ) ) -> 1
    // U( len( str.substr( x, n1, n2 ) ) ) ->
    //   min( U( len( x ) ) - O( n1 ), U( n2 ) )
    // U( len( str.replace( x, y, z ) ) ) ->
    //   U( len( x ) ) + U( len( z ) ) - O( len( y ) ) | 0
    // U( indexof( x, y, n ) ) -> -1    ?
    // U( str.to.int( x ) ) -> -1

    return false;
  }
}

Node TheoryStringsRewriter::getConstantArithBound(Node a, bool isLower)
{
  Assert(Rewriter::rewrite(a) == a);
  Node ret;
  if (a.isConst())
  {
    ret = a;
  }
  else if (a.getKind() == kind::STRING_LENGTH)
  {
    if (isLower)
    {
      ret = NodeManager::currentNM()->mkConst(Rational(0));
    }
  }
  else if (a.getKind() == kind::PLUS || a.getKind() == kind::MULT)
  {
    std::vector<Node> children;
    bool success = true;
    for (unsigned i = 0; i < a.getNumChildren(); i++)
    {
      Node ac = getConstantArithBound(a[i], isLower);
      if (ac.isNull())
      {
        ret = ac;
        success = false;
        break;
      }
      else
      {
        if (ac.getConst<Rational>().sgn() == 0)
        {
          if (a.getKind() == kind::MULT)
          {
            ret = ac;
            success = false;
            break;
          }
        }
        else
        {
          if (a.getKind() == kind::MULT)
          {
            if ((ac.getConst<Rational>().sgn() > 0) != isLower)
            {
              ret = Node::null();
              success = false;
              break;
            }
          }
          children.push_back(ac);
        }
      }
    }
    if (success)
    {
      if (children.empty())
      {
        ret = NodeManager::currentNM()->mkConst(Rational(0));
      }
      else if (children.size() == 1)
      {
        ret = children[0];
      }
      else
      {
        ret = NodeManager::currentNM()->mkNode(a.getKind(), children);
        ret = Rewriter::rewrite(ret);
      }
    }
  }
  Trace("strings-rewrite-cbound")
      << "Constant " << (isLower ? "lower" : "upper") << " bound for " << a
      << " is " << ret << std::endl;
  Assert(ret.isNull() || ret.isConst());
  Assert(!isLower
         || (ret.isNull() || ret.getConst<Rational>().sgn() < 0)
                != checkEntailArith(a, false));
  Assert(!isLower
         || (ret.isNull() || ret.getConst<Rational>().sgn() <= 0)
                != checkEntailArith(a, true));
  return ret;
}

bool TheoryStringsRewriter::checkEntailArithInternal(Node a)
{
  Assert(Rewriter::rewrite(a) == a);
  // check whether a >= 0
  if (a.isConst())
  {
    return a.getConst<Rational>().sgn() >= 0;
  }
  else if (a.getKind() == kind::STRING_LENGTH)
  {
    // str.len( t ) >= 0
    return true;
  }
  else if (a.getKind() == kind::PLUS || a.getKind() == kind::MULT)
  {
    for (unsigned i = 0; i < a.getNumChildren(); i++)
    {
      if (!checkEntailArithInternal(a[i]))
      {
        return false;
      }
    }
    // t1 >= 0 ^ ... ^ tn >= 0 => t1 op ... op tn >= 0
    return true;
  }

  return false;
}

Node TheoryStringsRewriter::returnRewrite(Node node, Node ret, const char* c)
{
  Trace("strings-rewrite") << "Rewrite " << node << " to " << ret << " by " << c
                           << "." << std::endl;
  return ret;
}
