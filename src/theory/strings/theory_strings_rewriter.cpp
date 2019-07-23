/*********************                                                        */
/*! \file theory_strings_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include <algorithm>

#include "expr/node_builder.h"
#include "options/strings_options.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_msum.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/theory.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

Node TheoryStringsRewriter::simpleRegexpConsume( std::vector< Node >& mchildren, std::vector< Node >& children, int dir ){
  Trace("regexp-ext-rewrite-debug")
      << "Simple reg exp consume, dir=" << dir << ":" << std::endl;
  Trace("regexp-ext-rewrite-debug")
      << "  mchildren : " << mchildren << std::endl;
  Trace("regexp-ext-rewrite-debug") << "  children : " << children << std::endl;
  NodeManager* nm = NodeManager::currentNM();
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
            Trace("regexp-ext-rewrite-debug") << "...strip equal" << std::endl;
          }else if( xc.isConst() && rc[0].isConst() ){
            //split the constant
            int index;
            Node s = splitConstant( xc, rc[0], index, t==0 );
            Trace("regexp-ext-rewrite-debug") << "CRE: Regexp const split : " << xc << " " << rc[0] << " -> " << s << " " << index << " " << t << std::endl;
            if( s.isNull() ){
              Trace("regexp-ext-rewrite-debug")
                  << "...return false" << std::endl;
              return NodeManager::currentNM()->mkConst( false );
            }else{
              Trace("regexp-ext-rewrite-debug")
                  << "...strip equal const" << std::endl;
              children.pop_back();
              mchildren.pop_back();
              if( index==0 ){
                mchildren.push_back( s );
              }else{
                children.push_back(nm->mkNode(STRING_TO_REGEXP, s));
              }
            }
            do_next = true;
          }
        }else if( xc.isConst() ){
          //check for constants
          CVC4::String s = xc.getConst<String>();
          if (s.size() == 0)
          {
            Trace("regexp-ext-rewrite-debug") << "...ignore empty" << std::endl;
            // ignore and continue
            mchildren.pop_back();
            do_next = true;
          }
          else if (rc.getKind() == kind::REGEXP_RANGE
                   || rc.getKind() == kind::REGEXP_SIGMA)
          {
            std::vector<unsigned> ssVec;
            ssVec.push_back(t == 0 ? s.back() : s.front());
            CVC4::String ss(ssVec);
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
              utils::getConcat(rc[i], children_s);
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
            utils::getConcat(rc[0], children_s);
            Trace("regexp-ext-rewrite-debug")
                << "...recursive call on body of star" << std::endl;
            Node ret = simpleRegexpConsume( mchildren_s, children_s, t );
            if( !ret.isNull() ){
              Trace("regexp-ext-rewrite-debug") << "CRE : regexp star infeasable " << xc << " " << rc << std::endl;
              children.pop_back();
              if (!children.empty())
              {
                Trace("regexp-ext-rewrite-debug") << "...continue" << std::endl;
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
                  Trace("regexp-ext-rewrite-debug")
                      << "...can't skip" << std::endl;
                  //take the result of fully consuming once
                  if( t==1 ){
                    std::reverse( mchildren_s.begin(), mchildren_s.end() );
                  }
                  mchildren.clear();
                  mchildren.insert( mchildren.end(), mchildren_s.begin(), mchildren_s.end() );
                  do_next = true;
                }else{
                  Trace("regexp-ext-rewrite-debug")
                      << "...can skip " << rc << " from " << xc << std::endl;
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

unsigned TheoryStringsRewriter::getAlphabetCardinality()
{
  if (options::stdPrintASCII())
  {
    Assert(128 <= String::num_codes());
    return 128;
  }
  Assert(256 <= String::num_codes());
  return 256;
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
    // must call rewrite contains directly to avoid infinite loop
    // we do a fix point since we may rewrite contains terms to simpler
    // contains terms.
    Node ctn = checkEntailContains(node[r], node[1 - r], false);
    if (!ctn.isNull())
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
    utils::getConcat(node[i], c[i]);
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
  return node;
}

Node TheoryStringsRewriter::rewriteEqualityExt(Node node)
{
  Assert(node.getKind() == EQUAL);
  if (node[0].getType().isInteger())
  {
    return rewriteArithEqualityExt(node);
  }
  if (node[0].getType().isString())
  {
    return rewriteStrEqualityExt(node);
  }
  return node;
}

Node TheoryStringsRewriter::rewriteStrEqualityExt(Node node)
{
  Assert(node.getKind() == EQUAL && node[0].getType().isString());

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> c[2];
  Node new_ret;
  for (unsigned i = 0; i < 2; i++)
  {
    utils::getConcat(node[i], c[i]);
  }
  // ------- equality unification
  bool changed = false;
  for (unsigned i = 0; i < 2; i++)
  {
    while (!c[0].empty() && !c[1].empty() && c[0].back() == c[1].back())
    {
      c[0].pop_back();
      c[1].pop_back();
      changed = true;
    }
    // splice constants
    if (!c[0].empty() && !c[1].empty() && c[0].back().isConst()
        && c[1].back().isConst())
    {
      String cs[2];
      for (unsigned j = 0; j < 2; j++)
      {
        cs[j] = c[j].back().getConst<String>();
      }
      unsigned larger = cs[0].size() > cs[1].size() ? 0 : 1;
      unsigned smallerSize = cs[1 - larger].size();
      if (cs[1 - larger]
          == (i == 0 ? cs[larger].suffix(smallerSize)
                     : cs[larger].prefix(smallerSize)))
      {
        unsigned sizeDiff = cs[larger].size() - smallerSize;
        c[larger][c[larger].size() - 1] = nm->mkConst(
            i == 0 ? cs[larger].prefix(sizeDiff) : cs[larger].suffix(sizeDiff));
        c[1 - larger].pop_back();
        changed = true;
      }
    }
    for (unsigned j = 0; j < 2; j++)
    {
      std::reverse(c[j].begin(), c[j].end());
    }
  }
  if (changed)
  {
    // e.g. x++y = x++z ---> y = z, "AB" ++ x = "A" ++ y --> "B" ++ x = y
    Node s1 = utils::mkConcat(STRING_CONCAT, c[0]);
    Node s2 = utils::mkConcat(STRING_CONCAT, c[1]);
    new_ret = s1.eqNode(s2);
    node = returnRewrite(node, new_ret, "str-eq-unify");
  }

  // ------- homogeneous constants
  for (unsigned i = 0; i < 2; i++)
  {
    Node cn = checkEntailHomogeneousString(node[i]);
    if (!cn.isNull() && cn.getConst<String>().size() > 0)
    {
      Assert(cn.isConst());
      Assert(cn.getConst<String>().size() == 1);
      unsigned hchar = cn.getConst<String>().front();

      // The operands of the concat on each side of the equality without
      // constant strings
      std::vector<Node> trimmed[2];
      // Counts the number of `hchar`s on each side
      size_t numHChars[2] = {0, 0};
      for (size_t j = 0; j < 2; j++)
      {
        // Sort the operands of the concats on both sides of the equality
        // (since both sides may only contain one char, the order does not
        // matter)
        std::sort(c[j].begin(), c[j].end());
        for (const Node& cc : c[j])
        {
          if (cc.getKind() == CONST_STRING)
          {
            // Count the number of `hchar`s in the string constant and make
            // sure that all chars are `hchar`s
            std::vector<unsigned> veccc = cc.getConst<String>().getVec();
            for (size_t k = 0, size = veccc.size(); k < size; k++)
            {
              if (veccc[k] != hchar)
              {
                // This conflict case should mostly should be taken care of by
                // multiset reasoning in the strings rewriter, but we recognize
                // this conflict just in case.
                new_ret = nm->mkConst(false);
                return returnRewrite(
                    node, new_ret, "string-eq-const-conflict-non-homog");
              }
              numHChars[j]++;
            }
          }
          else
          {
            trimmed[j].push_back(cc);
          }
        }
      }

      // We have to remove the same number of `hchar`s from both sides, so the
      // side with less `hchar`s determines how many we can remove
      size_t trimmedConst = std::min(numHChars[0], numHChars[1]);
      for (size_t j = 0; j < 2; j++)
      {
        size_t diff = numHChars[j] - trimmedConst;
        if (diff != 0)
        {
          // Add a constant string to the side with more `hchar`s to restore
          // the difference in number of `hchar`s
          std::vector<unsigned> vec(diff, hchar);
          trimmed[j].push_back(nm->mkConst(String(vec)));
        }
      }

      Node lhs = utils::mkConcat(STRING_CONCAT, trimmed[i]);
      Node ss = utils::mkConcat(STRING_CONCAT, trimmed[1 - i]);
      if (lhs != node[i] || ss != node[1 - i])
      {
        // e.g.
        //  "AA" = y ++ x ---> "AA" = x ++ y if x < y
        //  "AAA" = y ++ "A" ++ z ---> "AA" = y ++ z
        new_ret = lhs.eqNode(ss);
        node = returnRewrite(node, new_ret, "str-eq-homog-const");
      }
    }
  }

  // ------- rewrites for (= "" _)
  Node empty = nm->mkConst(::CVC4::String(""));
  for (size_t i = 0; i < 2; i++)
  {
    if (node[i] == empty)
    {
      Node ne = node[1 - i];
      if (ne.getKind() == STRING_STRREPL)
      {
        // (= "" (str.replace x y x)) ---> (= x "")
        if (ne[0] == ne[2])
        {
          Node ret = nm->mkNode(EQUAL, ne[0], empty);
          return returnRewrite(node, ret, "str-emp-repl-x-y-x");
        }

        // (= "" (str.replace x y "A")) ---> (and (= x "") (not (= y "")))
        if (checkEntailNonEmpty(ne[2]))
        {
          Node ret =
              nm->mkNode(AND,
                         nm->mkNode(EQUAL, ne[0], empty),
                         nm->mkNode(NOT, nm->mkNode(EQUAL, ne[1], empty)));
          return returnRewrite(node, ret, "str-emp-repl-emp");
        }

        // (= "" (str.replace x "A" "")) ---> (str.prefix x "A")
        if (checkEntailLengthOne(ne[1]) && ne[2] == empty)
        {
          Node ret = nm->mkNode(STRING_PREFIX, ne[0], ne[1]);
          return returnRewrite(node, ret, "str-emp-repl-emp");
        }
      }
      else if (ne.getKind() == STRING_SUBSTR)
      {
        Node zero = nm->mkConst(Rational(0));

        if (checkEntailArith(ne[1], false) && checkEntailArith(ne[2], true))
        {
          // (= "" (str.substr x 0 m)) ---> (= "" x) if m > 0
          if (ne[1] == zero)
          {
            Node ret = nm->mkNode(EQUAL, ne[0], empty);
            return returnRewrite(node, ret, "str-emp-substr-leq-len");
          }

          // (= "" (str.substr x n m)) ---> (<= (str.len x) n)
          // if n >= 0 and m > 0
          Node ret = nm->mkNode(LEQ, nm->mkNode(STRING_LENGTH, ne[0]), ne[1]);
          return returnRewrite(node, ret, "str-emp-substr-leq-len");
        }

        // (= "" (str.substr "A" 0 z)) ---> (<= z 0)
        if (checkEntailNonEmpty(ne[0]) && ne[1] == zero)
        {
          Node ret = nm->mkNode(LEQ, ne[2], zero);
          return returnRewrite(node, ret, "str-emp-substr-leq-z");
        }
      }
    }
  }

  // ------- rewrites for (= (str.replace _ _ _) _)
  for (size_t i = 0; i < 2; i++)
  {
    if (node[i].getKind() == STRING_STRREPL)
    {
      Node repl = node[i];
      Node x = node[1 - i];

      // (= "A" (str.replace "" x y)) ---> (= "" (str.replace "A" y x))
      if (checkEntailNonEmpty(x) && repl[0] == empty)
      {
        Node ret = nm->mkNode(
            EQUAL, empty, nm->mkNode(STRING_STRREPL, x, repl[2], repl[1]));
        return returnRewrite(node, ret, "str-eq-repl-emp");
      }

      // (= x (str.replace y x y)) ---> (= x y)
      if (repl[0] == repl[2] && x == repl[1])
      {
        Node ret = nm->mkNode(EQUAL, x, repl[0]);
        return returnRewrite(node, ret, "str-eq-repl-to-eq");
      }

      // (= x (str.replace x "A" "B")) ---> (not (str.contains x "A"))
      if (x == repl[0])
      {
        Node eq = Rewriter::rewrite(nm->mkNode(EQUAL, repl[1], repl[2]));
        if (eq.isConst() && !eq.getConst<bool>())
        {
          Node ret = nm->mkNode(NOT, nm->mkNode(STRING_STRCTN, x, repl[1]));
          return returnRewrite(node, ret, "str-eq-repl-not-ctn");
        }
      }

      // (= (str.replace x y z) z) --> (or (= x y) (= x z))
      // if (str.len y) = (str.len z)
      if (repl[2] == x)
      {
        Node lenY = nm->mkNode(STRING_LENGTH, repl[1]);
        Node lenZ = nm->mkNode(STRING_LENGTH, repl[2]);
        if (checkEntailArithEq(lenY, lenZ))
        {
          Node ret = nm->mkNode(OR,
                                nm->mkNode(EQUAL, repl[0], repl[1]),
                                nm->mkNode(EQUAL, repl[0], repl[2]));
          return returnRewrite(node, ret, "str-eq-repl-to-dis");
        }
      }
    }
  }

  // Try to rewrite (= x y) into a conjunction of equalities based on length
  // entailment.
  //
  // (<= (str.len x) (str.++ y1 ... yn)) AND (= x (str.++ y1 ... yn)) --->
  //  (and (= x (str.++ y1' ... ym')) (= y1'' "") ... (= yk'' ""))
  //
  // where yi' and yi'' correspond to some yj and
  //   (<= (str.len x) (str.++ y1' ... ym'))
  for (unsigned i = 0; i < 2; i++)
  {
    if (node[1 - i].getKind() == STRING_CONCAT)
    {
      new_ret = inferEqsFromContains(node[i], node[1 - i]);
      if (!new_ret.isNull())
      {
        return returnRewrite(node, new_ret, "str-eq-conj-len-entail");
      }
    }
  }

  return node;
}

Node TheoryStringsRewriter::rewriteArithEqualityExt(Node node)
{
  Assert(node.getKind() == EQUAL && node[0].getType().isInteger());

  // cases where we can solve the equality

  // notice we cannot rewrite str.to.int(x)=n to x="n" due to leading zeroes.

  return node;
}

// TODO (#1180) add rewrite
//  str.++( str.substr( x, n1, n2 ), str.substr( x, n1+n2, n3 ) ) --->
//  str.substr( x, n1, n2+n3 )
Node TheoryStringsRewriter::rewriteConcat(Node node)
{
  Assert(node.getKind() == kind::STRING_CONCAT);
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcat start " << node << std::endl;
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

  // Sort adjacent operands in str.++ that all result in the same string or the
  // empty string.
  //
  // E.g.: (str.++ ... (str.replace "A" x "") "A" (str.substr "A" 0 z) ...) -->
  // (str.++ ... [sort those 3 arguments] ... )
  size_t lastIdx = 0;
  Node lastX;
  for (size_t i = 0; i < node_vec.size(); i++)
  {
    Node s = getStringOrEmpty(node_vec[i]);
    bool nextX = false;
    if (s != lastX)
    {
      nextX = true;
    }

    if (nextX)
    {
      std::sort(node_vec.begin() + lastIdx, node_vec.begin() + i);
      lastX = s;
      lastIdx = i;
    }
  }
  std::sort(node_vec.begin() + lastIdx, node_vec.end());

  retNode = utils::mkConcat(STRING_CONCAT, node_vec);
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcat end " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::rewriteConcatRegExp(TNode node)
{
  Assert( node.getKind() == kind::REGEXP_CONCAT );
  NodeManager* nm = NodeManager::currentNM();
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcatRegExp flatten " << node << std::endl;
  Node retNode = node;
  std::vector<Node> vec;
  bool changed = false;
  Node emptyRe;
  for (const Node& c : node)
  {
    if (c.getKind() == REGEXP_CONCAT)
    {
      changed = true;
      for (const Node& cc : c)
      {
        vec.push_back(cc);
      }
    }
    else if (c.getKind() == STRING_TO_REGEXP && c[0].isConst()
             && c[0].getConst<String>().isEmptyString())
    {
      changed = true;
      emptyRe = c;
    }
    else if (c.getKind() == REGEXP_EMPTY)
    {
      // re.++( ..., empty, ... ) ---> empty
      std::vector<Node> nvec;
      return nm->mkNode(REGEXP_EMPTY, nvec);
    }
    else
    {
      vec.push_back(c);
    }
  }
  if (changed)
  {
    // flatten
    // this handles nested re.++ and elimination or str.to.re(""), e.g.:
    // re.++( re.++( R1, R2 ), str.to.re(""), R3 ) ---> re.++( R1, R2, R3 )
    if (vec.empty())
    {
      Assert(!emptyRe.isNull());
      retNode = emptyRe;
    }
    else
    {
      retNode = vec.size() == 1 ? vec[0] : nm->mkNode(REGEXP_CONCAT, vec);
    }
    return returnRewrite(node, retNode, "re.concat-flatten");
  }
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcatRegExp start " << node << std::endl;
  std::vector<Node> cvec;
  std::vector<Node> preReStr;
  for (unsigned i = 0, size = vec.size(); i <= size; i++)
  {
    Node curr;
    if (i < size)
    {
      curr = vec[i];
      Assert(curr.getKind() != REGEXP_CONCAT);
      if (!cvec.empty() && preReStr.empty())
      {
        Node cvecLast = cvec.back();
        if (cvecLast.getKind() == REGEXP_STAR && cvecLast[0] == curr)
        {
          // by convention, flip the order (a*)++a ---> a++(a*)
          cvec[cvec.size() - 1] = curr;
          cvec.push_back(cvecLast);
          curr = Node::null();
        }
      }
    }
    // update preReStr
    if (!curr.isNull() && curr.getKind() == STRING_TO_REGEXP)
    {
      preReStr.push_back(curr[0]);
      curr = Node::null();
    }
    else if (!preReStr.empty())
    {
      // this groups consecutive strings a++b ---> ab
      Node acc = nm->mkNode(STRING_TO_REGEXP,
                            utils::mkConcat(STRING_CONCAT, preReStr));
      cvec.push_back(acc);
      preReStr.clear();
    }
    if (!curr.isNull() && curr.getKind() == REGEXP_STAR)
    {
      // we can group stars (a*)++(a*) ---> a*
      if (!cvec.empty() && cvec.back() == curr)
      {
        curr = Node::null();
      }
    }
    if (!curr.isNull())
    {
      cvec.push_back(curr);
    }
  }
  Assert(!cvec.empty());
  retNode = utils::mkConcat(REGEXP_CONCAT, cvec);
  if (retNode != node)
  {
    // handles all cases where consecutive re constants are combined, and cases
    // where arguments are swapped, as described in the loop above.
    return returnRewrite(node, retNode, "re.concat");
  }
  return node;
}

Node TheoryStringsRewriter::rewriteStarRegExp(TNode node)
{
  Assert(node.getKind() == REGEXP_STAR);
  NodeManager* nm = NodeManager::currentNM();
  Node retNode = node;
  if (node[0].getKind() == REGEXP_STAR)
  {
    // ((R)*)* ---> R*
    return returnRewrite(node, node[0], "re-star-nested-star");
  }
  else if (node[0].getKind() == STRING_TO_REGEXP
           && node[0][0].getKind() == CONST_STRING
           && node[0][0].getConst<String>().isEmptyString())
  {
    // ("")* ---> ""
    return returnRewrite(node, node[0], "re-star-empty-string");
  }
  else if (node[0].getKind() == REGEXP_EMPTY)
  {
    // (empty)* ---> ""
    retNode = nm->mkNode(STRING_TO_REGEXP, nm->mkConst(String("")));
    return returnRewrite(node, retNode, "re-star-empty");
  }
  else if (node[0].getKind() == REGEXP_UNION)
  {
    // simplification of unions under star
    if (hasEpsilonNode(node[0]))
    {
      bool changed = false;
      std::vector<Node> node_vec;
      for (const Node& nc : node[0])
      {
        if (nc.getKind() == STRING_TO_REGEXP && nc[0].getKind() == CONST_STRING
            && nc[0].getConst<String>().isEmptyString())
        {
          // can be removed
          changed = true;
        }
        else
        {
          node_vec.push_back(nc);
        }
      }
      if (changed)
      {
        retNode = node_vec.size() == 1 ? node_vec[0]
                                       : nm->mkNode(REGEXP_UNION, node_vec);
        retNode = nm->mkNode(REGEXP_STAR, retNode);
        // simplification of union beneath star based on loop above
        // for example, ( "" | "a" )* ---> ("a")*
        return returnRewrite(node, retNode, "re-star-union");
      }
    }
  }
  return node;
}

Node TheoryStringsRewriter::rewriteAndOrRegExp(TNode node)
{
  Kind nk = node.getKind();
  Assert(nk == REGEXP_UNION || nk == REGEXP_INTER);
  Trace("strings-rewrite-debug")
      << "Strings::rewriteAndOrRegExp start " << node << std::endl;
  std::vector<Node> node_vec;
  for (const Node& ni : node)
  {
    if (ni.getKind() == nk)
    {
      for (const Node& nic : ni)
      {
        if (std::find(node_vec.begin(), node_vec.end(), nic) == node_vec.end())
        {
          node_vec.push_back(nic);
        }
      }
    }
    else if (ni.getKind() == REGEXP_EMPTY)
    {
      if (nk == REGEXP_INTER)
      {
        return returnRewrite(node, ni, "re.and-empty");
      }
      // otherwise, can ignore
    }
    else if (ni.getKind() == REGEXP_STAR && ni[0].getKind() == REGEXP_SIGMA)
    {
      if (nk == REGEXP_UNION)
      {
        return returnRewrite(node, ni, "re.or-all");
      }
      // otherwise, can ignore
    }
    else if (std::find(node_vec.begin(), node_vec.end(), ni) == node_vec.end())
    {
      node_vec.push_back(ni);
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> nvec;
  Node retNode;
  if (node_vec.empty())
  {
    if (nk == REGEXP_INTER)
    {
      retNode = nm->mkNode(REGEXP_STAR, nm->mkNode(REGEXP_SIGMA, nvec));
    }
    else
    {
      retNode = nm->mkNode(kind::REGEXP_EMPTY, nvec);
    }
  }
  else
  {
    retNode = node_vec.size() == 1 ? node_vec[0] : nm->mkNode(nk, node_vec);
  }
  if (retNode != node)
  {
    // flattening and removing children, based on loop above
    return returnRewrite(node, retNode, "re.andor-flatten");
  }
  return node;
}

Node TheoryStringsRewriter::rewriteLoopRegExp(TNode node)
{
  Assert(node.getKind() == REGEXP_LOOP);
  Node retNode = node;
  Node r = node[0];
  if (r.getKind() == REGEXP_STAR)
  {
    return returnRewrite(node, r, "re.loop-star");
  }
  TNode n1 = node[1];
  NodeManager* nm = NodeManager::currentNM();
  CVC4::Rational rMaxInt(String::maxSize());
  AlwaysAssert(n1.isConst(), "re.loop contains non-constant integer (1).");
  AlwaysAssert(n1.getConst<Rational>().sgn() >= 0,
               "Negative integer in string REGEXP_LOOP (1)");
  Assert(n1.getConst<Rational>() <= rMaxInt,
         "Exceeded UINT32_MAX in string REGEXP_LOOP (1)");
  uint32_t l = n1.getConst<Rational>().getNumerator().toUnsignedInt();
  std::vector<Node> vec_nodes;
  for (unsigned i = 0; i < l; i++)
  {
    vec_nodes.push_back(r);
  }
  if (node.getNumChildren() == 3)
  {
    TNode n2 = Rewriter::rewrite(node[2]);
    Node n =
        vec_nodes.size() == 0
            ? nm->mkNode(STRING_TO_REGEXP, nm->mkConst(String("")))
            : vec_nodes.size() == 1 ? r : nm->mkNode(REGEXP_CONCAT, vec_nodes);
    AlwaysAssert(n2.isConst(), "re.loop contains non-constant integer (2).");
    AlwaysAssert(n2.getConst<Rational>().sgn() >= 0,
                 "Negative integer in string REGEXP_LOOP (2)");
    Assert(n2.getConst<Rational>() <= rMaxInt,
           "Exceeded UINT32_MAX in string REGEXP_LOOP (2)");
    uint32_t u = n2.getConst<Rational>().getNumerator().toUnsignedInt();
    if (u <= l)
    {
      retNode = n;
    }
    else
    {
      std::vector<Node> vec2;
      vec2.push_back(n);
      for (unsigned j = l; j < u; j++)
      {
        vec_nodes.push_back(r);
        n = utils::mkConcat(REGEXP_CONCAT, vec_nodes);
        vec2.push_back(n);
      }
      retNode = nm->mkNode(REGEXP_UNION, vec2);
    }
  }
  else
  {
    Node rest = nm->mkNode(REGEXP_STAR, r);
    retNode = vec_nodes.size() == 0
                  ? rest
                  : vec_nodes.size() == 1
                        ? nm->mkNode(REGEXP_CONCAT, r, rest)
                        : nm->mkNode(REGEXP_CONCAT,
                                     nm->mkNode(REGEXP_CONCAT, vec_nodes),
                                     rest);
  }
  Trace("strings-lp") << "Strings::lp " << node << " => " << retNode
                      << std::endl;
  if (retNode != node)
  {
    return returnRewrite(node, retNode, "re.loop");
  }
  return node;
}

bool TheoryStringsRewriter::isConstRegExp( TNode t ) {
  if( t.getKind()==kind::STRING_TO_REGEXP ) {
    return t[0].isConst();
  }
  else if (t.isVar())
  {
    return false;
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
  Assert(!r.isVar());
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
        unsigned a = r[0].getConst<String>().front();
        a = String::convertUnsignedIntToCode(a);
        unsigned b = r[1].getConst<String>().front();
        b = String::convertUnsignedIntToCode(b);
        unsigned c = s.back();
        c = String::convertUnsignedIntToCode(c);
        return (a <= c && c <= b);
      } else {
        return false;
      }
    }
    case kind::REGEXP_LOOP: {
      uint32_t l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
      if(s.size() == index_start) {
        return l==0? true : testConstStringInRegExp(s, index_start, r[0]);
      } else if(l==0 && r[1]==r[2]) {
        return false;
      } else {
        Assert(r.getNumChildren() == 3, "String rewriter error: LOOP has 2 children");
        if(l==0) {
          //R{0,u}
          uint32_t u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
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
  NodeManager* nm = NodeManager::currentNM();
  Node retNode = node;
  Node x = node[0];
  Node r = node[1];

  if(r.getKind() == kind::REGEXP_EMPTY) {
    retNode = NodeManager::currentNM()->mkConst( false );
  } else if(x.getKind()==kind::CONST_STRING && isConstRegExp(r)) {
    //test whether x in node[1]
    CVC4::String s = x.getConst<String>();
    retNode = NodeManager::currentNM()->mkConst( testConstStringInRegExp( s, 0, r ) );
  } else if(r.getKind() == kind::REGEXP_SIGMA) {
    Node one = nm->mkConst(Rational(1));
    retNode = one.eqNode(nm->mkNode(STRING_LENGTH, x));
  } else if( r.getKind() == kind::REGEXP_STAR ) {
    if (x.isConst())
    {
      String s = x.getConst<String>();
      if (s.size() == 0)
      {
        retNode = nm->mkConst(true);
        // e.g. (str.in.re "" (re.* (str.to.re x))) ----> true
        return returnRewrite(node, retNode, "re-empty-in-str-star");
      }
      else if (s.size() == 1)
      {
        if (r[0].getKind() == STRING_TO_REGEXP)
        {
          retNode = r[0][0].eqNode(x);
          // e.g. (str.in.re "A" (re.* (str.to.re x))) ----> "A" = x
          return returnRewrite(node, retNode, "re-char-in-str-star");
        }
      }
    }
    else if (x.getKind() == STRING_CONCAT)
    {
      // (str.in.re (str.++ x1 ... xn) (re.* R)) -->
      //   (str.in.re x1 (re.* R)) AND ... AND (str.in.re xn (re.* R))
      //     if the length of all strings in R is one.
      Node flr = getFixedLengthForRegexp(r[0]);
      if (!flr.isNull())
      {
        Node one = nm->mkConst(Rational(1));
        if (flr == one)
        {
          NodeBuilder<> nb(AND);
          for (const Node& xc : x)
          {
            nb << nm->mkNode(STRING_IN_REGEXP, xc, r);
          }
          Node retNode = nb.constructNode();
          return returnRewrite(node, retNode, "re-in-dist-char-star");
        }
      }
    }
    if (r[0].getKind() == kind::REGEXP_SIGMA)
    {
      retNode = NodeManager::currentNM()->mkConst( true );
      return returnRewrite(node, retNode, "re-in-sigma-star");
    }
  }else if( r.getKind() == kind::REGEXP_CONCAT ){
    bool allSigma = true;
    bool allSigmaStrict = true;
    unsigned allSigmaMinSize = 0;
    Node constStr;
    size_t constIdx = 0;
    size_t nchildren = r.getNumChildren();
    for (size_t i = 0; i < nchildren; i++)
    {
      Node rc = r[i];
      Assert(rc.getKind() != kind::REGEXP_EMPTY);
      if (rc.getKind() == kind::REGEXP_SIGMA)
      {
        allSigmaMinSize++;
      }
      else if (rc.getKind() == REGEXP_STAR && rc[0].getKind() == REGEXP_SIGMA)
      {
        allSigmaStrict = false;
      }
      else if (rc.getKind() == STRING_TO_REGEXP)
      {
        if (constStr.isNull())
        {
          constStr = rc[0];
          constIdx = i;
        }
        else
        {
          allSigma = false;
          break;
        }
      }
      else
      {
        allSigma = false;
        break;
      }
    }
    if (allSigma)
    {
      if (constStr.isNull())
      {
        // x in re.++(_*, _, _) ---> str.len(x) >= 2
        Node num = nm->mkConst(Rational(allSigmaMinSize));
        Node lenx = nm->mkNode(STRING_LENGTH, x);
        retNode = nm->mkNode(allSigmaStrict ? EQUAL : GEQ, lenx, num);
        return returnRewrite(node, retNode, "re-concat-pure-allchar");
      }
      else if (allSigmaMinSize == 0 && nchildren >= 3 && constIdx != 0
               && constIdx != nchildren - 1)
      {
        // x in re.++(_*, "abc", _*) ---> str.contains(x, "abc")
        retNode = nm->mkNode(STRING_STRCTN, x, constStr);
        return returnRewrite(node, retNode, "re-concat-to-contains");
      }
    }
  }else if( r.getKind()==kind::REGEXP_INTER || r.getKind()==kind::REGEXP_UNION ){
    std::vector< Node > mvec;
    for( unsigned i=0; i<r.getNumChildren(); i++ ){
      mvec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r[i] ) );
    }
    retNode = NodeManager::currentNM()->mkNode( r.getKind()==kind::REGEXP_INTER ? kind::AND : kind::OR, mvec );
  }else if(r.getKind() == kind::STRING_TO_REGEXP) {
    retNode = x.eqNode(r[0]);
  }
  else if (r.getKind() == REGEXP_RANGE)
  {
    // x in re.range( char_i, char_j ) ---> i <= str.code(x) <= j
    Node xcode = nm->mkNode(STRING_CODE, x);
    retNode = nm->mkNode(AND,
                         nm->mkNode(LEQ, nm->mkNode(STRING_CODE, r[0]), xcode),
                         nm->mkNode(LEQ, xcode, nm->mkNode(STRING_CODE, r[1])));
  }else if(x != node[0] || r != node[1]) {
    retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r );
  }

  //do simple consumes
  if( retNode==node ){
    if( r.getKind()==kind::REGEXP_STAR ){
      for( unsigned dir=0; dir<=1; dir++ ){
        std::vector< Node > mchildren;
        utils::getConcat(x, mchildren);
        bool success = true;
        while( success ){
          success = false;
          std::vector< Node > children;
          utils::getConcat(r[0], children);
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
              retNode = nm->mkNode(STRING_IN_REGEXP,
                                   utils::mkConcat(STRING_CONCAT, mchildren),
                                   r);
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
      utils::getConcat(r, children);
      std::vector< Node > mchildren;
      utils::getConcat(x, mchildren);
      unsigned prevSize = children.size() + mchildren.size();
      Node scn = simpleRegexpConsume( mchildren, children );
      if( !scn.isNull() ){
        Trace("regexp-ext-rewrite") << "Regexp : const conflict : " << node << std::endl;
        return scn;
      }else{
        if( (children.size() + mchildren.size())!=prevSize ){
          // Given a membership (str.++ x1 ... xn) in (re.++ r1 ... rm),
          // above, we strip components to construct an equivalent membership:
          // (str.++ xi .. xj) in (re.++ rk ... rl).
          Node xn = utils::mkConcat(STRING_CONCAT, mchildren);
          Node emptyStr = nm->mkConst(String(""));
          if( children.empty() ){
            // If we stripped all components on the right, then the left is
            // equal to the empty string.
            // e.g. (str.++ "a" x) in (re.++ (str.to.re "a")) ---> (= x "")
            retNode = xn.eqNode(emptyStr);
          }else{
            // otherwise, construct the updated regular expression
            retNode = nm->mkNode(
                STRING_IN_REGEXP, xn, utils::mkConcat(REGEXP_CONCAT, children));
          }
          Trace("regexp-ext-rewrite") << "Regexp : rewrite : " << node << " -> " << retNode << std::endl;
          return returnRewrite(node, retNode, "re-simple-consume");
        }
      }
    }
  }
  return retNode;
}

RewriteResponse TheoryStringsRewriter::postRewrite(TNode node) {
  Trace("strings-postrewrite") << "Strings::postRewrite start " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node retNode = node;
  Node orig = retNode;
  Kind nk = node.getKind();
  if (nk == kind::STRING_CONCAT)
  {
    retNode = rewriteConcat(node);
  }
  else if (nk == kind::EQUAL)
  {
    retNode = rewriteEquality(node);
  }
  else if (nk == kind::STRING_LENGTH)
  {
    Kind nk0 = node[0].getKind();
    if( node[0].isConst() ){
      retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( node[0].getConst<String>().size() ) );
    }
    else if (nk0 == kind::STRING_CONCAT)
    {
      Node tmpNode = node[0];
      if(tmpNode.isConst()) {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode.getConst<String>().size() ) );
      }else if( tmpNode.getKind()==kind::STRING_CONCAT ){
        std::vector<Node> node_vec;
        for(unsigned int i=0; i<tmpNode.getNumChildren(); ++i) {
          if(tmpNode[i].isConst()) {
            node_vec.push_back( NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode[i].getConst<String>().size() ) ) );
          } else {
            node_vec.push_back( NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, tmpNode[i]) );
          }
        }
        retNode = NodeManager::currentNM()->mkNode(kind::PLUS, node_vec);
      }
    }
    else if (nk0 == STRING_STRREPL || nk0 == STRING_STRREPLALL)
    {
      Node len1 = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, node[0][1]));
      Node len2 = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, node[0][2]));
      if (len1 == len2)
      {
        // len( y ) == len( z ) => len( str.replace( x, y, z ) ) ---> len( x )
        retNode = nm->mkNode(STRING_LENGTH, node[0][0]);
      }
    }
  }
  else if (nk == kind::STRING_CHARAT)
  {
    Node one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
    retNode = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, node[0], node[1], one);
  }
  else if (nk == kind::STRING_SUBSTR)
  {
    retNode = rewriteSubstr(node);
  }
  else if (nk == kind::STRING_STRCTN)
  {
    retNode = rewriteContains( node );
  }
  else if (nk == kind::STRING_LT)
  {
    // eliminate s < t ---> s != t AND s <= t
    retNode = nm->mkNode(AND,
                         node[0].eqNode(node[1]).negate(),
                         nm->mkNode(STRING_LEQ, node[0], node[1]));
  }
  else if (nk == kind::STRING_LEQ)
  {
    retNode = rewriteStringLeq(node);
  }
  else if (nk == kind::STRING_STRIDOF)
  {
    retNode = rewriteIndexof( node );
  }
  else if (nk == kind::STRING_STRREPL)
  {
    retNode = rewriteReplace( node );
  }
  else if (nk == kind::STRING_STRREPLALL)
  {
    retNode = rewriteReplaceAll(node);
  }
  else if (nk == STRING_TOLOWER || nk == STRING_TOUPPER)
  {
    retNode = rewriteStrConvert(node);
  }
  else if (nk == kind::STRING_PREFIX || nk == kind::STRING_SUFFIX)
  {
    retNode = rewritePrefixSuffix(node);
  }
  else if (nk == kind::STRING_ITOS)
  {
    if(node[0].isConst()) {
      if( node[0].getConst<Rational>().sgn()==-1 ){
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
      }else{
        std::string stmp = node[0].getConst<Rational>().getNumerator().toString();
        Assert(stmp[0] != '-');
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String(stmp) );
      }
    }
  }
  else if (nk == kind::STRING_STOI)
  {
    if(node[0].isConst()) {
      CVC4::String s = node[0].getConst<String>();
      if(s.isNumber()) {
        retNode = nm->mkConst(s.toNumber());
      } else {
        retNode = nm->mkConst(Rational(-1));
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
  }
  else if (nk == kind::STRING_IN_REGEXP)
  {
    retNode = rewriteMembership(node);
  }
  else if (nk == STRING_CODE)
  {
    retNode = rewriteStringCode(node);
  }
  else if (nk == REGEXP_CONCAT)
  {
    retNode = rewriteConcatRegExp(node);
  }
  else if (nk == REGEXP_UNION || nk == REGEXP_INTER)
  {
    retNode = rewriteAndOrRegExp(node);
  }
  else if (nk == REGEXP_STAR)
  {
    retNode = rewriteStarRegExp(node);
  }
  else if (nk == REGEXP_PLUS)
  {
    retNode =
        nm->mkNode(REGEXP_CONCAT, node[0], nm->mkNode(REGEXP_STAR, node[0]));
  }
  else if (nk == REGEXP_OPT)
  {
    retNode = nm->mkNode(REGEXP_UNION,
                         nm->mkNode(STRING_TO_REGEXP, nm->mkConst(String(""))),
                         node[0]);
  }
  else if (nk == REGEXP_RANGE)
  {
    if (node[0] == node[1])
    {
      retNode = nm->mkNode(STRING_TO_REGEXP, node[0]);
    }
  }
  else if (nk == REGEXP_LOOP)
  {
    retNode = rewriteLoopRegExp(node);
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
  return RewriteResponse(REWRITE_DONE, node);
}

Node TheoryStringsRewriter::rewriteSubstr(Node node)
{
  Assert(node.getKind() == kind::STRING_SUBSTR);

  NodeManager* nm = NodeManager::currentNM();
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
      CVC4::Rational rMaxInt(String::maxSize());
      uint32_t start;
      if (node[1].getConst<Rational>() > rMaxInt)
      {
        // start beyond the maximum size of strings
        // thus, it must be beyond the end point of this string
        Node ret = nm->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-const-start-max-oob");
      }
      else if (node[1].getConst<Rational>().sgn() < 0)
      {
        // start before the beginning of the string
        Node ret = nm->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-const-start-neg");
      }
      else
      {
        start = node[1].getConst<Rational>().getNumerator().toUnsignedInt();
        if (start >= s.size())
        {
          // start beyond the end of the string
          Node ret = nm->mkConst(::CVC4::String(""));
          return returnRewrite(node, ret, "ss-const-start-oob");
        }
      }
      if (node[2].getConst<Rational>() > rMaxInt)
      {
        // take up to the end of the string
        Node ret = nm->mkConst(::CVC4::String(s.suffix(s.size() - start)));
        return returnRewrite(node, ret, "ss-const-len-max-oob");
      }
      else if (node[2].getConst<Rational>().sgn() <= 0)
      {
        Node ret = nm->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-const-len-non-pos");
      }
      else
      {
        uint32_t len =
            node[2].getConst<Rational>().getNumerator().toUnsignedInt();
        if (start + len > s.size())
        {
          // take up to the end of the string
          Node ret = nm->mkConst(::CVC4::String(s.suffix(s.size() - start)));
          return returnRewrite(node, ret, "ss-const-end-oob");
        }
        else
        {
          // compute the substr using the constant string
          Node ret = nm->mkConst(::CVC4::String(s.substr(start, len)));
          return returnRewrite(node, ret, "ss-const-ss");
        }
      }
    }
  }
  Node zero = nm->mkConst(CVC4::Rational(0));

  // if entailed non-positive length or negative start point
  if (checkEntailArith(zero, node[1], true))
  {
    Node ret = nm->mkConst(::CVC4::String(""));
    return returnRewrite(node, ret, "ss-start-neg");
  }
  else if (checkEntailArith(zero, node[2]))
  {
    Node ret = nm->mkConst(::CVC4::String(""));
    return returnRewrite(node, ret, "ss-len-non-pos");
  }

  if (node[0].getKind() == STRING_SUBSTR)
  {
    // (str.substr (str.substr x a b) c d) ---> "" if c >= b
    //
    // Note that this rewrite can be generalized to:
    //
    // (str.substr x a b) ---> "" if a >= (str.len x)
    //
    // This can be done when we generalize our entailment methods to
    // accept an optional context. Then we could conjecture that
    // (str.substr x a b) rewrites to "" and do a case analysis:
    //
    // - a < 0 or b < 0 (the result is trivially empty in these cases)
    // - a >= (str.len x) assuming that { a >= 0, b >= 0 }
    //
    // For example, for (str.substr (str.substr x a a) a a), we could
    // then deduce that under those assumptions, "a" is an
    // over-approximation of the length of (str.substr x a a), which
    // then allows us to reason that the result of the whole term must
    // be empty.
    if (checkEntailArith(node[1], node[0][2]))
    {
      Node ret = nm->mkConst(::CVC4::String(""));
      return returnRewrite(node, ret, "ss-start-geq-len");
    }
  }
  else if (node[0].getKind() == STRING_STRREPL)
  {
    // (str.substr (str.replace x y z) 0 n)
    // 	 ---> (str.replace (str.substr x 0 n) y z)
    // if (str.len y) = 1 and (str.len z) = 1
    if (node[1] == zero)
    {
      if (checkEntailLengthOne(node[0][1], true)
          && checkEntailLengthOne(node[0][2], true))
      {
        Node ret = nm->mkNode(
            kind::STRING_STRREPL,
            nm->mkNode(kind::STRING_SUBSTR, node[0][0], node[1], node[2]),
            node[0][1],
            node[0][2]);
        return returnRewrite(node, ret, "substr-repl-swap");
      }
    }
  }

  std::vector<Node> n1;
  utils::getConcat(node[0], n1);

  // definite inclusion
  if (node[1] == zero)
  {
    Node curr = node[2];
    std::vector<Node> childrenr;
    if (stripSymbolicLength(n1, childrenr, 1, curr))
    {
      if (curr != zero && !n1.empty())
      {
        childrenr.push_back(nm->mkNode(kind::STRING_SUBSTR,
                                       utils::mkConcat(STRING_CONCAT, n1),
                                       node[1],
                                       curr));
      }
      Node ret = utils::mkConcat(STRING_CONCAT, childrenr);
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
      Node tot_len =
          Rewriter::rewrite(nm->mkNode(kind::STRING_LENGTH, node[0]));
      Node end_pt = Rewriter::rewrite(nm->mkNode(kind::PLUS, node[1], node[2]));
      if (node[2] != tot_len)
      {
        if (checkEntailArith(node[2], tot_len))
        {
          // end point beyond end point of string, map to tot_len
          Node ret = nm->mkNode(kind::STRING_SUBSTR, node[0], node[1], tot_len);
          return returnRewrite(node, ret, "ss-end-pt-norm");
        }
        else
        {
          // strip up to ( str.len(node[0]) - end_pt ) off the end of the string
          curr = Rewriter::rewrite(nm->mkNode(kind::MINUS, tot_len, end_pt));
        }
      }

      // (str.substr s x y) --> "" if x < len(s) |= 0 >= y
      Node n1_lt_tot_len =
          Rewriter::rewrite(nm->mkNode(kind::LT, node[1], tot_len));
      if (checkEntailArithWithAssumption(n1_lt_tot_len, zero, node[2], false))
      {
        Node ret = nm->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-start-entails-zero-len");
      }

      // (str.substr s x y) --> "" if 0 < y |= x >= str.len(s)
      Node non_zero_len =
          Rewriter::rewrite(nm->mkNode(kind::LT, zero, node[2]));
      if (checkEntailArithWithAssumption(non_zero_len, node[1], tot_len, false))
      {
        Node ret = nm->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-non-zero-len-entails-oob");
      }

      // (str.substr s x y) --> "" if x >= 0 |= 0 >= str.len(s)
      Node geq_zero_start =
          Rewriter::rewrite(nm->mkNode(kind::GEQ, node[1], zero));
      if (checkEntailArithWithAssumption(geq_zero_start, zero, tot_len, false))
      {
        Node ret = nm->mkConst(String(""));
        return returnRewrite(node, ret, "ss-geq-zero-start-entails-emp-s");
      }

      // (str.substr s x x) ---> "" if (str.len s) <= 1
      if (node[1] == node[2] && checkEntailLengthOne(node[0]))
      {
        Node ret = nm->mkConst(::CVC4::String(""));
        return returnRewrite(node, ret, "ss-len-one-z-z");
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
          Node ret = nm->mkNode(kind::STRING_SUBSTR,
                                utils::mkConcat(STRING_CONCAT, n1),
                                curr,
                                node[2]);
          return returnRewrite(node, ret, "ss-strip-start-pt");
        }
        else
        {
          Node ret = nm->mkNode(kind::STRING_SUBSTR,
                                utils::mkConcat(STRING_CONCAT, n1),
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
      Node len_from_inner =
          Rewriter::rewrite(nm->mkNode(kind::MINUS, node[0][2], start_outer));
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
        Node new_start = nm->mkNode(kind::PLUS, start_inner, start_outer);
        Node ret =
            nm->mkNode(kind::STRING_SUBSTR, node[0][0], new_start, new_len);
        return returnRewrite(node, ret, "ss-combine");
      }
    }
  }
  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return node;
}

Node TheoryStringsRewriter::rewriteContains( Node node ) {
  Assert(node.getKind() == kind::STRING_STRCTN);
  NodeManager* nm = NodeManager::currentNM();

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
    else if (t.size() == 1)
    {
      // The following rewrites are specific to a single character second
      // argument of contains, where we can reason that this character is
      // not split over multiple components in the first argument.
      if (node[0].getKind() == STRING_CONCAT)
      {
        std::vector<Node> nc1;
        utils::getConcat(node[0], nc1);
        NodeBuilder<> nb(OR);
        for (const Node& ncc : nc1)
        {
          nb << nm->mkNode(STRING_STRCTN, ncc, node[1]);
        }
        Node ret = nb.constructNode();
        // str.contains( x ++ y, "A" ) --->
        //   str.contains( x, "A" ) OR str.contains( y, "A" )
        return returnRewrite(node, ret, "ctn-concat-char");
      }
      else if (node[0].getKind() == STRING_STRREPL)
      {
        Node rplDomain = checkEntailContains(node[0][1], node[1]);
        if (!rplDomain.isNull() && !rplDomain.getConst<bool>())
        {
          Node d1 = nm->mkNode(STRING_STRCTN, node[0][0], node[1]);
          Node d2 =
              nm->mkNode(AND,
                         nm->mkNode(STRING_STRCTN, node[0][0], node[0][1]),
                         nm->mkNode(STRING_STRCTN, node[0][2], node[1]));
          Node ret = nm->mkNode(OR, d1, d2);
          // If str.contains( y, "A" ) ---> false, then:
          // str.contains( str.replace( x, y, z ), "A" ) --->
          //   str.contains( x, "A" ) OR
          //   ( str.contains( x, y ) AND str.contains( z, "A" ) )
          return returnRewrite(node, ret, "ctn-repl-char");
        }
      }
    }
  }
  std::vector<Node> nc1;
  utils::getConcat(node[0], nc1);
  std::vector<Node> nc2;
  utils::getConcat(node[1], nc2);

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
        kind::STRING_STRCTN, utils::mkConcat(STRING_CONCAT, nc1), node[1]);
    return returnRewrite(node, ret, "ctn-strip-endpt");
  }

  for (const Node& n : nc2)
  {
    if (n.getKind() == kind::STRING_STRREPL)
    {
      // (str.contains x (str.replace y z w)) --> false
      // if (str.contains x y) = false and (str.contains x w) = false
      //
      // Reasoning: (str.contains x y) checks that x does not contain y if the
      // replacement does not change y. (str.contains x w) checks that if the
      // replacement changes anything in y, the w makes it impossible for it to
      // occur in x.
      Node ctnConst = checkEntailContains(node[0], n[0]);
      if (!ctnConst.isNull() && !ctnConst.getConst<bool>())
      {
        Node ctnConst2 = checkEntailContains(node[0], n[2]);
        if (!ctnConst2.isNull() && !ctnConst2.getConst<bool>())
        {
          Node res = nm->mkConst(false);
          return returnRewrite(node, res, "ctn-rpl-non-ctn");
        }
      }

      // (str.contains x (str.++ w (str.replace x y x) z)) --->
      //   (and (= w "") (= x (str.replace x y x)) (= z ""))
      //
      // TODO: Remove with under-/over-approximation
      if (node[0] == n[0] && node[0] == n[2])
      {
        Node ret;
        if (nc2.size() > 1)
        {
          Node emp = nm->mkConst(CVC4::String(""));
          NodeBuilder<> nb(kind::AND);
          for (const Node& n2 : nc2)
          {
            if (n2 == n)
            {
              nb << nm->mkNode(kind::EQUAL, node[0], node[1]);
            }
            else
            {
              nb << nm->mkNode(kind::EQUAL, emp, n2);
            }
          }
          ret = nb.constructNode();
        }
        else
        {
          ret = nm->mkNode(kind::EQUAL, node[0], node[1]);
        }
        return returnRewrite(node, ret, "ctn-repl-self");
      }
    }
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
  if (checkEntailMultisetSubset(node[0], node[1]))
  {
    Node ret = nm->mkConst(false);
    return returnRewrite(node, ret, "ctn-mset-nss");
  }

  if (checkEntailArith(len_n2, len_n1, false))
  {
    // len( n2 ) >= len( n1 ) => contains( n1, n2 ) ---> n1 = n2
    Node ret = node[0].eqNode(node[1]);
    return returnRewrite(node, ret, "ctn-len-ineq-nstrict");
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
          if (s.noOverlapWith(t))
          {
            std::vector<Node> nc0;
            utils::getConcat(node[0], nc0);
            std::vector<Node> spl[2];
            spl[0].insert(spl[0].end(), nc0.begin(), nc0.begin() + i);
            Assert(i < nc0.size() - 1);
            spl[1].insert(spl[1].end(), nc0.begin() + i + 1, nc0.end());
            Node ret = NodeManager::currentNM()->mkNode(
                kind::OR,
                NodeManager::currentNM()->mkNode(
                    kind::STRING_STRCTN,
                    utils::mkConcat(STRING_CONCAT, spl[0]),
                    node[1]),
                NodeManager::currentNM()->mkNode(
                    kind::STRING_STRCTN,
                    utils::mkConcat(STRING_CONCAT, spl[1]),
                    node[1]));
            return returnRewrite(node, ret, "ctn-split");
          }
        }
      }
    }
  }
  else if (node[0].getKind() == kind::STRING_SUBSTR)
  {
    // (str.contains (str.substr x n (str.len y)) y) --->
    //   (= (str.substr x n (str.len y)) y)
    //
    // TODO: Remove with under-/over-approximation
    if (node[0][2] == nm->mkNode(kind::STRING_LENGTH, node[1]))
    {
      Node ret = nm->mkNode(kind::EQUAL, node[0], node[1]);
      return returnRewrite(node, ret, "ctn-substr");
    }
  }
  else if (node[0].getKind() == kind::STRING_STRREPL)
  {
    if (node[1].isConst() && node[0][1].isConst() && node[0][2].isConst())
    {
      String c = node[1].getConst<String>();
      if (c.noOverlapWith(node[0][1].getConst<String>())
          && c.noOverlapWith(node[0][2].getConst<String>()))
      {
        // (str.contains (str.replace x c1 c2) c3) ---> (str.contains x c3)
        // if there is no overlap between c1 and c3 and none between c2 and c3
        Node ret = nm->mkNode(STRING_STRCTN, node[0][0], node[1]);
        return returnRewrite(node, ret, "ctn-repl-cnsts-to-ctn");
      }
    }

    if (node[0][0] == node[0][2])
    {
      // (str.contains (str.replace x y x) y) ---> (str.contains x y)
      if (node[0][1] == node[1])
      {
        Node ret = nm->mkNode(kind::STRING_STRCTN, node[0][0], node[1]);
        return returnRewrite(node, ret, "ctn-repl-to-ctn");
      }

      // (str.contains (str.replace x y x) z) ---> (str.contains x z)
      // if (str.len z) <= 1
      if (checkEntailLengthOne(node[1]))
      {
        Node ret = nm->mkNode(kind::STRING_STRCTN, node[0][0], node[1]);
        return returnRewrite(node, ret, "ctn-repl-len-one-to-ctn");
      }
    }

    // (str.contains (str.replace x y z) z) --->
    //   (or (str.contains x y) (str.contains x z))
    if (node[0][2] == node[1])
    {
      Node ret = nm->mkNode(OR,
                            nm->mkNode(STRING_STRCTN, node[0][0], node[0][1]),
                            nm->mkNode(STRING_STRCTN, node[0][0], node[0][2]));
      return returnRewrite(node, ret, "ctn-repl-to-ctn-disj");
    }

    // (str.contains (str.replace x y z) w) --->
    //   (str.contains (str.replace x y "") w)
    // if (str.contains z w) ---> false and (str.len w) = 1
    if (checkEntailLengthOne(node[1]))
    {
      Node ctn = checkEntailContains(node[1], node[0][2]);
      if (!ctn.isNull() && !ctn.getConst<bool>())
      {
        Node empty = nm->mkConst(String(""));
        Node ret = nm->mkNode(
            kind::STRING_STRCTN,
            nm->mkNode(kind::STRING_STRREPL, node[0][0], node[0][1], empty),
            node[1]);
        return returnRewrite(node, ret, "ctn-repl-simp-repl");
      }
    }
  }

  if (node[1].getKind() == kind::STRING_STRREPL)
  {
    // (str.contains x (str.replace y x y)) --->
    //   (str.contains x y)
    if (node[0] == node[1][1] && node[1][0] == node[1][2])
    {
      Node ret = nm->mkNode(kind::STRING_STRCTN, node[0], node[1][0]);
      return returnRewrite(node, ret, "ctn-repl");
    }

    // (str.contains x (str.replace "" x y)) --->
    //   (= "" (str.replace "" x y))
    //
    // Note: Length-based reasoning is not sufficient to get this rewrite. We
    // can neither show that str.len(str.replace("", x, y)) - str.len(x) >= 0
    // nor str.len(x) - str.len(str.replace("", x, y)) >= 0
    Node emp = nm->mkConst(CVC4::String(""));
    if (node[0] == node[1][1] && node[1][0] == emp)
    {
      Node ret = nm->mkNode(kind::EQUAL, emp, node[1]);
      return returnRewrite(node, ret, "ctn-repl-empty");
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
  utils::getConcat(node[0], children0);
  if (children0[0].isConst() && node[1].isConst() && node[2].isConst())
  {
    CVC4::Rational rMaxInt(CVC4::String::maxSize());
    if (node[2].getConst<Rational>() > rMaxInt)
    {
      // We know that, due to limitations on the size of string constants
      // in our implementation, that accessing a position greater than
      // rMaxInt is guaranteed to be out of bounds.
      Node negone = nm->mkConst(Rational(-1));
      return returnRewrite(node, negone, "idof-max");
    }
    Assert(node[2].getConst<Rational>().sgn() >= 0);
    uint32_t start =
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

  if (node[0] == node[1])
  {
    if (node[2].isConst())
    {
      if (node[2].getConst<Rational>().sgn() == 0)
      {
        // indexof( x, x, 0 ) --> 0
        Node zero = nm->mkConst(Rational(0));
        return returnRewrite(node, zero, "idof-eq-cst-start");
      }
    }
    if (checkEntailArith(node[2], true))
    {
      // y>0  implies  indexof( x, x, y ) --> -1
      Node negone = nm->mkConst(Rational(-1));
      return returnRewrite(node, negone, "idof-eq-nstart");
    }
    Node emp = nm->mkConst(CVC4::String(""));
    if (node[0] != emp)
    {
      // indexof( x, x, z ) ---> indexof( "", "", z )
      Node ret = nm->mkNode(STRING_STRIDOF, emp, emp, node[2]);
      return returnRewrite(node, ret, "idof-eq-norm");
    }
  }

  Node len0 = nm->mkNode(STRING_LENGTH, node[0]);
  Node len1 = nm->mkNode(STRING_LENGTH, node[1]);
  Node len0m2 = nm->mkNode(MINUS, len0, node[2]);

  if (node[1].isConst())
  {
    CVC4::String t = node[1].getConst<String>();
    if (t.size() == 0)
    {
      if (checkEntailArith(len0, node[2]) && checkEntailArith(node[2]))
      {
        // len(x)>=z ^ z >=0 implies indexof( x, "", z ) ---> z
        return returnRewrite(node, node[2], "idof-emp-idof");
      }
    }
  }

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

  Node cmp_conr = checkEntailContains(fstr, node[1]);
  Trace("strings-rewrite-debug") << "For " << node << ", check contains("
                                 << fstr << ", " << node[1] << ")" << std::endl;
  Trace("strings-rewrite-debug") << "...got " << cmp_conr << std::endl;
  std::vector<Node> children1;
  utils::getConcat(node[1], children1);
  if (!cmp_conr.isNull())
  {
    if (cmp_conr.getConst<bool>())
    {
      if (node[2].isConst() && node[2].getConst<Rational>().sgn() == 0)
      {
        // past the first position in node[0] that contains node[1], we can drop
        std::vector<Node> nb;
        std::vector<Node> ne;
        int cc = componentContains(children0, children1, nb, ne, true, 1);
        if (cc != -1 && !ne.empty())
        {
          // For example:
          // str.indexof(str.++(x,y,z),y,0) ---> str.indexof(str.++(x,y),y,0)
          Node nn = utils::mkConcat(STRING_CONCAT, children0);
          Node ret = nm->mkNode(kind::STRING_STRIDOF, nn, node[1], node[2]);
          return returnRewrite(node, ret, "idof-def-ctn");
        }

        // Strip components from the beginning that are guaranteed not to match
        if (stripConstantEndpoints(children0, children1, nb, ne, 1))
        {
          // str.indexof(str.++("AB", x, "C"), "C", 0) --->
          // 2 + str.indexof(str.++(x, "C"), "C", 0)
          Node ret =
              nm->mkNode(kind::PLUS,
                         nm->mkNode(kind::STRING_LENGTH,
                                    utils::mkConcat(STRING_CONCAT, nb)),
                         nm->mkNode(kind::STRING_STRIDOF,
                                    utils::mkConcat(STRING_CONCAT, children0),
                                    node[1],
                                    node[2]));
          return returnRewrite(node, ret, "idof-strip-cnst-endpts");
        }
      }

      // strip symbolic length
      Node new_len = node[2];
      std::vector<Node> nr;
      if (stripSymbolicLength(children0, nr, 1, new_len))
      {
        // For example:
        // z>str.len( x1 ) and str.contains( x2, y )-->true
        // implies
        // str.indexof( str.++( x1, x2 ), y, z ) --->
        // str.len( x1 ) + str.indexof( x2, y, z-str.len(x1) )
        Node nn = utils::mkConcat(STRING_CONCAT, children0);
        Node ret =
            nm->mkNode(kind::PLUS,
                       nm->mkNode(kind::MINUS, node[2], new_len),
                       nm->mkNode(kind::STRING_STRIDOF, nn, node[1], new_len));
        return returnRewrite(node, ret, "idof-strip-sym-len");
      }
    }
    else
    {
      // str.contains( x, y ) --> false  implies  str.indexof(x,y,z) --> -1
      Node negone = nm->mkConst(Rational(-1));
      return returnRewrite(node, negone, "idof-nctn");
    }
  }
  else
  {
    Node new_len = node[2];
    std::vector<Node> nr;
    if (stripSymbolicLength(children0, nr, 1, new_len))
    {
      // Normalize the string before the start index.
      //
      // For example:
      // str.indexof(str.++("ABCD", x), y, 3) --->
      // str.indexof(str.++("AAAD", x), y, 3)
      Node nodeNr = utils::mkConcat(STRING_CONCAT, nr);
      Node normNr = lengthPreserveRewrite(nodeNr);
      if (normNr != nodeNr)
      {
        std::vector<Node> normNrChildren;
        utils::getConcat(normNr, normNrChildren);
        std::vector<Node> children(normNrChildren);
        children.insert(children.end(), children0.begin(), children0.end());
        Node nn = utils::mkConcat(STRING_CONCAT, children);
        Node res = nm->mkNode(kind::STRING_STRIDOF, nn, node[1], node[2]);
        return returnRewrite(node, res, "idof-norm-prefix");
      }
    }
  }

  if (node[2].isConst() && node[2].getConst<Rational>().sgn()==0)
  {
    std::vector<Node> cb;
    std::vector<Node> ce;
    if (stripConstantEndpoints(children0, children1, cb, ce, -1))
    {
      Node ret = utils::mkConcat(STRING_CONCAT, children0);
      ret = nm->mkNode(STRING_STRIDOF, ret, node[1], node[2]);
      // For example:
      // str.indexof( str.++( x, "A" ), "B", 0 ) ---> str.indexof( x, "B", 0 )
      return returnRewrite(node, ret, "rpl-pull-endpt");
    }
  }

  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return node;
}

Node TheoryStringsRewriter::rewriteReplace( Node node ) {
  Assert(node.getKind() == kind::STRING_STRREPL);
  NodeManager* nm = NodeManager::currentNM();

  if (node[1].isConst() && node[1].getConst<String>().isEmptyString())
  {
    Node ret = nm->mkNode(STRING_CONCAT, node[2], node[0]);
    return returnRewrite(node, ret, "rpl-rpl-empty");
  }

  std::vector<Node> children0;
  utils::getConcat(node[0], children0);

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
      Node ret = utils::mkConcat(STRING_CONCAT, children);
      return returnRewrite(node, ret, "rpl-const-find");
    }
  }

  // rewrites that apply to both replace and replaceall
  Node rri = rewriteReplaceInternal(node);
  if (!rri.isNull())
  {
    // printing of the rewrite managed by the call above
    return rri;
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

    // (str.replace x y x) ---> (str.replace x (str.++ y1 ... yn) x)
    // if 1 >= (str.len x) and (= y "") ---> (= y1 "") ... (= yn "")
    if (checkEntailLengthOne(node[0]))
    {
      Node empty = nm->mkConst(String(""));
      Node rn1 = Rewriter::rewrite(
          rewriteEqualityExt(nm->mkNode(EQUAL, node[1], empty)));
      if (rn1 != node[1])
      {
        std::vector<Node> emptyNodes;
        bool allEmptyEqs;
        std::tie(allEmptyEqs, emptyNodes) = collectEmptyEqs(rn1);

        if (allEmptyEqs)
        {
          Node nn1 = utils::mkConcat(STRING_CONCAT, emptyNodes);
          if (node[1] != nn1)
          {
            Node ret = nm->mkNode(STRING_STRREPL, node[0], nn1, node[2]);
            return returnRewrite(node, ret, "rpl-x-y-x-simp");
          }
        }
      }
    }
  }

  std::vector<Node> children1;
  utils::getConcat(node[1], children1);

  // check if contains definitely does (or does not) hold
  Node cmp_con = nm->mkNode(kind::STRING_STRCTN, node[0], node[1]);
  Node cmp_conr = Rewriter::rewrite(cmp_con);
  if (!checkEntailContains(node[0], node[1]).isNull())
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
          Node ret = utils::mkConcat(STRING_CONCAT, cres);
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
              utils::mkConcat(STRING_CONCAT, children0),
              node[1],
              node[2]));
          cc.insert(cc.end(), ce.begin(), ce.end());
          Node ret = utils::mkConcat(STRING_CONCAT, cc);
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
  else if (cmp_conr.getKind() == kind::EQUAL || cmp_conr.getKind() == kind::AND)
  {
    // Rewriting the str.contains may return equalities of the form (= x "").
    // In that case, we can substitute the variables appearing in those
    // equalities with the empty string in the third argument of the
    // str.replace. For example:
    //
    // (str.replace x (str.++ x y) y) --> (str.replace x (str.++ x y) "")
    //
    // This can be done because str.replace changes x iff (str.++ x y) is in x
    // but that means that y must be empty in that case. Thus, we can
    // substitute y with "" in the third argument. Note that the third argument
    // does not matter when the str.replace does not apply.
    //
    Node empty = nm->mkConst(::CVC4::String(""));

    std::vector<Node> emptyNodes;
    bool allEmptyEqs;
    std::tie(allEmptyEqs, emptyNodes) = collectEmptyEqs(cmp_conr);

    if (emptyNodes.size() > 0)
    {
      // Perform the substitutions
      std::vector<TNode> substs(emptyNodes.size(), TNode(empty));
      Node nn2 = node[2].substitute(
          emptyNodes.begin(), emptyNodes.end(), substs.begin(), substs.end());

      // If the contains rewrites to a conjunction of empty-string equalities
      // and we are doing the replacement in an empty string, we can rewrite
      // the string-to-replace with a concatenation of all the terms that must
      // be empty:
      //
      // (str.replace "" y z) ---> (str.replace "" (str.++ y1 ... yn)  z)
      // if (str.contains "" y) ---> (and (= y1 "") ... (= yn ""))
      if (node[0] == empty && allEmptyEqs)
      {
        std::vector<Node> emptyNodesList(emptyNodes.begin(), emptyNodes.end());
        Node nn1 = utils::mkConcat(STRING_CONCAT, emptyNodesList);
        if (nn1 != node[1] || nn2 != node[2])
        {
          Node res = nm->mkNode(kind::STRING_STRREPL, node[0], nn1, nn2);
          return returnRewrite(node, res, "rpl-emp-cnts-substs");
        }
      }

      if (nn2 != node[2])
      {
        Node res = nm->mkNode(kind::STRING_STRREPL, node[0], node[1], nn2);
        return returnRewrite(node, res, "rpl-cnts-substs");
      }
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
            utils::mkConcat(STRING_CONCAT, children0),
            node[1],
            node[2]));
        cc.insert(cc.end(), ce.begin(), ce.end());
        Node ret = utils::mkConcat(STRING_CONCAT, cc);
        return returnRewrite(node, ret, "rpl-pull-endpt");
      }
    }
  }

  children1.clear();
  utils::getConcat(node[1], children1);
  Node lastChild1 = children1[children1.size() - 1];
  if (lastChild1.getKind() == kind::STRING_SUBSTR)
  {
    // (str.replace x (str.++ t (str.substr y i j)) z) --->
    // (str.replace x (str.++ t
    //                  (str.substr y i (+ (str.len x) 1 (- (str.len t))))) z)
    // if j > len(x)
    //
    // Reasoning: If the string to be replaced is longer than x, then it does
    // not matter how much longer it is, the result is always x. Thus, it is
    // fine to only look at the prefix of length len(x) + 1 - len(t).

    children1.pop_back();
    // Length of the non-substr components in the second argument
    Node partLen1 = nm->mkNode(kind::STRING_LENGTH,
                               utils::mkConcat(STRING_CONCAT, children1));
    Node maxLen1 = nm->mkNode(kind::PLUS, partLen1, lastChild1[2]);

    Node zero = nm->mkConst(Rational(0));
    Node one = nm->mkConst(Rational(1));
    Node len0 = nm->mkNode(kind::STRING_LENGTH, node[0]);
    Node len0_1 = nm->mkNode(kind::PLUS, len0, one);
    // Check len(t) + j > len(x) + 1
    if (checkEntailArith(maxLen1, len0_1, true))
    {
      children1.push_back(nm->mkNode(
          kind::STRING_SUBSTR,
          lastChild1[0],
          lastChild1[1],
          nm->mkNode(
              kind::PLUS, len0, one, nm->mkNode(kind::UMINUS, partLen1))));
      Node res = nm->mkNode(kind::STRING_STRREPL,
                            node[0],
                            utils::mkConcat(STRING_CONCAT, children1),
                            node[2]);
      return returnRewrite(node, res, "repl-subst-idx");
    }
  }

  if (node[0].getKind() == STRING_STRREPL)
  {
    Node x = node[0];
    Node y = node[1];
    Node z = node[2];
    if (x[0] == x[2] && x[0] == y)
    {
      // (str.replace (str.replace y w y) y z) -->
      //   (str.replace (str.replace y w z) y z)
      // if (str.len w) >= (str.len z) and w != z
      //
      // Reasoning: There are two cases: (1) w does not appear in y and (2) w
      // does appear in y.
      //
      // Case (1): In this case, the reasoning is trivial. The
      // inner replace does not do anything, so we can just replace its third
      // argument with any string.
      //
      // Case (2): After the inner replace, we are guaranteed to have a string
      // that contains y at the index of w in the original string y. The outer
      // replace then replaces that y with z, so we can short-circuit that
      // replace by directly replacing w with z in the inner replace. We can
      // only do that if the result of the new inner replace does not contain
      // y, otherwise we end up doing two replaces that are different from the
      // original expression. We enforce that by requiring that the length of w
      // has to be greater or equal to the length of z and that w and z have to
      // be different. This makes sure that an inner replace changes a string
      // to a string that is shorter than y, making it impossible for the outer
      // replace to match.
      Node w = x[1];

      // (str.len w) >= (str.len z)
      Node wlen = nm->mkNode(kind::STRING_LENGTH, w);
      Node zlen = nm->mkNode(kind::STRING_LENGTH, z);
      if (checkEntailArith(wlen, zlen))
      {
        // w != z
        Node wEqZ = Rewriter::rewrite(nm->mkNode(kind::EQUAL, w, z));
        if (wEqZ.isConst() && !wEqZ.getConst<bool>())
        {
          Node ret = nm->mkNode(kind::STRING_STRREPL,
                                nm->mkNode(kind::STRING_STRREPL, y, w, z),
                                y,
                                z);
          return returnRewrite(node, ret, "repl-repl-short-circuit");
        }
      }
    }
  }

  if (node[1].getKind() == STRING_STRREPL)
  {
    if (node[1][0] == node[0])
    {
      if (node[1][0] == node[1][2] && node[1][0] == node[2])
      {
        // str.replace( x, str.replace( x, y, x ), x ) ---> x
        return returnRewrite(node, node[0], "repl-repl2-inv-id");
      }
      bool dualReplIteSuccess = false;
      Node cmp_con = checkEntailContains(node[1][0], node[1][2]);
      if (!cmp_con.isNull() && !cmp_con.getConst<bool>())
      {
        // str.contains( x, z ) ---> false
        //   implies
        // str.replace( x, str.replace( x, y, z ), w ) --->
        // ite( str.contains( x, y ), x, w )
        dualReplIteSuccess = true;
      }
      else
      {
        // str.contains( y, z ) ---> false and str.contains( z, y ) ---> false
        //   implies
        // str.replace( x, str.replace( x, y, z ), w ) --->
        // ite( str.contains( x, y ), x, w )
        cmp_con = checkEntailContains(node[1][1], node[1][2]);
        if (!cmp_con.isNull() && !cmp_con.getConst<bool>())
        {
          cmp_con = checkEntailContains(node[1][2], node[1][1]);
          if (!cmp_con.isNull() && !cmp_con.getConst<bool>())
          {
            dualReplIteSuccess = true;
          }
        }
      }
      if (dualReplIteSuccess)
      {
        Node res = nm->mkNode(ITE,
                              nm->mkNode(STRING_STRCTN, node[0], node[1][1]),
                              node[0],
                              node[2]);
        return returnRewrite(node, res, "repl-dual-repl-ite");
      }
    }

    bool invSuccess = false;
    if (node[1][1] == node[0])
    {
      if (node[1][0] == node[1][2])
      {
        // str.replace(x, str.replace(y, x, y), w) ---> str.replace(x, y, w)
        invSuccess = true;
      }
      else if (node[1][1] == node[2] || node[1][0] == node[2])
      {
        // str.contains(y, z) ----> false and ( y == w or x == w ) implies
        //   implies
        // str.replace(x, str.replace(y, x, z), w) ---> str.replace(x, y, w)
        Node cmp_con = checkEntailContains(node[1][0], node[1][2]);
        invSuccess = !cmp_con.isNull() && !cmp_con.getConst<bool>();
      }
    }
    else
    {
      // str.contains(x, z) ----> false and str.contains(x, w) ----> false
      //   implies
      // str.replace(x, str.replace(y, z, w), u) ---> str.replace(x, y, u)
      Node cmp_con = checkEntailContains(node[0], node[1][1]);
      if (!cmp_con.isNull() && !cmp_con.getConst<bool>())
      {
        cmp_con = checkEntailContains(node[0], node[1][2]);
        invSuccess = !cmp_con.isNull() && !cmp_con.getConst<bool>();
      }
    }
    if (invSuccess)
    {
      Node res = nm->mkNode(kind::STRING_STRREPL, node[0], node[1][0], node[2]);
      return returnRewrite(node, res, "repl-repl2-inv");
    }
  }
  if (node[2].getKind() == STRING_STRREPL)
  {
    if (node[2][1] == node[0])
    {
      // str.contains( z, w ) ----> false implies
      // str.replace( x, w, str.replace( z, x, y ) ) ---> str.replace( x, w, z )
      Node cmp_con = checkEntailContains(node[1], node[2][0]);
      if (!cmp_con.isNull() && !cmp_con.getConst<bool>())
      {
        Node res =
            nm->mkNode(kind::STRING_STRREPL, node[0], node[1], node[2][0]);
        return returnRewrite(node, res, "repl-repl3-inv");
      }
    }
    if (node[2][0] == node[1])
    {
      bool success = false;
      if (node[2][0] == node[2][2] && node[2][1] == node[0])
      {
        // str.replace( x, y, str.replace( y, x, y ) ) ---> x
        success = true;
      }
      else
      {
        // str.contains( x, z ) ----> false implies
        // str.replace( x, y, str.replace( y, z, w ) ) ---> x
        cmp_con = checkEntailContains(node[0], node[2][1]);
        success = !cmp_con.isNull() && !cmp_con.getConst<bool>();
      }
      if (success)
      {
        return returnRewrite(node, node[0], "repl-repl3-inv-id");
      }
    }
  }
  // miniscope based on components that do not contribute to contains
  // for example,
  //   str.replace( x ++ y ++ x ++ y, "A", z ) -->
  //   str.replace( x ++ y, "A", z ) ++ x ++ y
  // since if "A" occurs in x ++ y ++ x ++ y, then it must occur in x ++ y.
  if (checkEntailLengthOne(node[1]))
  {
    Node lastLhs;
    unsigned lastCheckIndex = 0;
    for (unsigned i = 1, iend = children0.size(); i < iend; i++)
    {
      unsigned checkIndex = children0.size() - i;
      std::vector<Node> checkLhs;
      checkLhs.insert(
          checkLhs.end(), children0.begin(), children0.begin() + checkIndex);
      Node lhs = utils::mkConcat(STRING_CONCAT, checkLhs);
      Node rhs = children0[checkIndex];
      Node ctn = checkEntailContains(lhs, rhs);
      if (!ctn.isNull() && ctn.getConst<bool>())
      {
        lastLhs = lhs;
        lastCheckIndex = checkIndex;
      }
      else
      {
        break;
      }
    }
    if (!lastLhs.isNull())
    {
      std::vector<Node> remc(children0.begin() + lastCheckIndex,
                             children0.end());
      Node rem = utils::mkConcat(STRING_CONCAT, remc);
      Node ret =
          nm->mkNode(STRING_CONCAT,
                     nm->mkNode(STRING_STRREPL, lastLhs, node[1], node[2]),
                     rem);
      // for example:
      //   str.replace( x ++ x, "A", y ) ---> str.replace( x, "A", y ) ++ x
      // Since we know that the first occurrence of "A" cannot be in the
      // second occurrence of x. Notice this is specific to single characters
      // due to complications with finds that span multiple components for
      // non-characters.
      return returnRewrite(node, ret, "repl-char-ncontrib-find");
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

Node TheoryStringsRewriter::rewriteReplaceAll(Node node)
{
  Assert(node.getKind() == STRING_STRREPLALL);
  NodeManager* nm = NodeManager::currentNM();

  if (node[0].isConst() && node[1].isConst())
  {
    std::vector<Node> children;
    String s = node[0].getConst<String>();
    String t = node[1].getConst<String>();
    if (s.isEmptyString() || t.isEmptyString())
    {
      return returnRewrite(node, node[0], "replall-empty-find");
    }
    std::size_t index = 0;
    std::size_t curr = 0;
    do
    {
      curr = s.find(t, index);
      if (curr != std::string::npos)
      {
        if (curr > index)
        {
          children.push_back(nm->mkConst(s.substr(index, curr - index)));
        }
        children.push_back(node[2]);
        index = curr + t.size();
      }
      else
      {
        children.push_back(nm->mkConst(s.substr(index, s.size() - index)));
      }
    } while (curr != std::string::npos && curr < s.size());
    // constant evaluation
    Node res = utils::mkConcat(STRING_CONCAT, children);
    return returnRewrite(node, res, "replall-const");
  }

  // rewrites that apply to both replace and replaceall
  Node rri = rewriteReplaceInternal(node);
  if (!rri.isNull())
  {
    // printing of the rewrite managed by the call above
    return rri;
  }

  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return node;
}

Node TheoryStringsRewriter::rewriteReplaceInternal(Node node)
{
  Kind nk = node.getKind();
  Assert(nk == STRING_STRREPL || nk == STRING_STRREPLALL);

  if (node[1] == node[2])
  {
    return returnRewrite(node, node[0], "rpl-id");
  }

  if (node[0] == node[1])
  {
    // only holds for replaceall if non-empty
    if (nk == STRING_STRREPL || checkEntailNonEmpty(node[1]))
    {
      return returnRewrite(node, node[2], "rpl-replace");
    }
  }

  return Node::null();
}

Node TheoryStringsRewriter::rewriteStrConvert(Node node)
{
  Kind nk = node.getKind();
  Assert(nk == STRING_TOLOWER || nk == STRING_TOUPPER);
  NodeManager* nm = NodeManager::currentNM();
  if (node[0].isConst())
  {
    std::vector<unsigned> nvec = node[0].getConst<String>().getVec();
    for (unsigned i = 0, nvsize = nvec.size(); i < nvsize; i++)
    {
      unsigned newChar = CVC4::String::convertUnsignedIntToCode(nvec[i]);
      // transform it
      // upper 65 ... 90
      // lower 97 ... 122
      if (nk == STRING_TOUPPER)
      {
        if (newChar >= 97 && newChar <= 122)
        {
          newChar = newChar - 32;
        }
      }
      else if (nk == STRING_TOLOWER)
      {
        if (newChar >= 65 && newChar <= 90)
        {
          newChar = newChar + 32;
        }
      }
      newChar = CVC4::String::convertCodeToUnsignedInt(newChar);
      nvec[i] = newChar;
    }
    Node retNode = nm->mkConst(String(nvec));
    return returnRewrite(node, retNode, "str-conv-const");
  }
  else if (node[0].getKind() == STRING_CONCAT)
  {
    NodeBuilder<> concatBuilder(STRING_CONCAT);
    for (const Node& nc : node[0])
    {
      concatBuilder << nm->mkNode(nk, nc);
    }
    // tolower( x1 ++ x2 ) --> tolower( x1 ) ++ tolower( x2 )
    Node retNode = concatBuilder.constructNode();
    return returnRewrite(node, retNode, "str-conv-minscope-concat");
  }
  else if (node[0].getKind() == STRING_TOLOWER
           || node[0].getKind() == STRING_TOUPPER)
  {
    // tolower( tolower( x ) ) --> tolower( x )
    // tolower( toupper( x ) ) --> tolower( x )
    Node retNode = nm->mkNode(nk, node[0][0]);
    return returnRewrite(node, retNode, "str-conv-idem");
  }
  else if (node[0].getKind() == STRING_ITOS)
  {
    // tolower( str.from.int( x ) ) --> str.from.int( x )
    return returnRewrite(node, node[0], "str-conv-itos");
  }
  return node;
}

Node TheoryStringsRewriter::rewriteStringLeq(Node n)
{
  Assert(n.getKind() == kind::STRING_LEQ);
  NodeManager* nm = NodeManager::currentNM();
  if (n[0] == n[1])
  {
    Node ret = nm->mkConst(true);
    return returnRewrite(n, ret, "str-leq-id");
  }
  if (n[0].isConst() && n[1].isConst())
  {
    String s = n[0].getConst<String>();
    String t = n[1].getConst<String>();
    Node ret = nm->mkConst(s.isLeq(t));
    return returnRewrite(n, ret, "str-leq-eval");
  }
  // empty strings
  for (unsigned i = 0; i < 2; i++)
  {
    if (n[i].isConst() && n[i].getConst<String>().isEmptyString())
    {
      Node ret = i == 0 ? nm->mkConst(true) : n[0].eqNode(n[1]);
      return returnRewrite(n, ret, "str-leq-empty");
    }
  }

  std::vector<Node> n1;
  utils::getConcat(n[0], n1);
  std::vector<Node> n2;
  utils::getConcat(n[1], n2);
  Assert(!n1.empty() && !n2.empty());

  // constant prefixes
  if (n1[0].isConst() && n2[0].isConst() && n1[0] != n2[0])
  {
    String s = n1[0].getConst<String>();
    String t = n2[0].getConst<String>();
    // only need to truncate if s is longer
    if (s.size() > t.size())
    {
      s = s.prefix(t.size());
    }
    // if prefix is not leq, then entire string is not leq
    if (!s.isLeq(t))
    {
      Node ret = nm->mkConst(false);
      return returnRewrite(n, ret, "str-leq-cprefix");
    }
  }

  Trace("strings-rewrite-nf") << "No rewrites for : " << n << std::endl;
  return n;
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

  // Check if we can turn the prefix/suffix into equalities by showing that the
  // prefix/suffix is at least as long as the string
  Node eqs = inferEqsFromContains(n[1], n[0]);
  if (!eqs.isNull())
  {
    return returnRewrite(n, eqs, "suf/prefix-to-eqs");
  }

  // general reduction to equality + substr
  Node retNode = n[0].eqNode(
      NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR, n[1], val, lens));

  return retNode;
}

Node TheoryStringsRewriter::rewriteStringCode(Node n)
{
  Assert(n.getKind() == kind::STRING_CODE);
  if (n[0].isConst())
  {
    CVC4::String s = n[0].getConst<String>();
    Node ret;
    if (s.size() == 1)
    {
      std::vector<unsigned> vec = s.getVec();
      Assert(vec.size() == 1);
      ret = NodeManager::currentNM()->mkConst(
          Rational(CVC4::String::convertUnsignedIntToCode(vec[0])));
    }
    else
    {
      ret = NodeManager::currentNM()->mkConst(Rational(-1));
    }
    return returnRewrite(n, ret, "code-eval");
  }

  return n;
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
    else if (n[i].getKind() == kind::STRING_ITOS && checkEntailArith(n[i][0]))
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
    Node cc = Rewriter::rewrite(utils::mkConcat(STRING_CONCAT, c));
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
        Node lowerBound = getConstantArithBound(Rewriter::rewrite(curr));
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
              Assert(lbr < Rational(String::maxSize()));
              curr = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
                  kind::MINUS, curr, lowerBound));
              uint32_t lbsize = lbr.getNumerator().toUnsignedInt();
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

  NodeManager* nm = NodeManager::currentNM();

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
              n1rb = nm->mkConst(::CVC4::String(s.prefix(s.size() - t.size())));
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
              n1re = nm->mkConst(::CVC4::String(s.suffix(s.size() - t.size())));
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
                n1rb = nm->mkConst(::CVC4::String(s.prefix(f)));
              }
              if (s.size() > f + t.size())
              {
                n1re = nm->mkConst(
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
          Node end_pos = nm->mkNode(kind::PLUS, n2[1], n2[2]);
          Node len_n2s = nm->mkNode(kind::STRING_LENGTH, n2[0]);
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
                n1rb = nm->mkNode(kind::STRING_SUBSTR,
                                  n2[0],
                                  nm->mkConst(Rational(0)),
                                  start_pos);
              }
              if (dir != -1)
              {
                n1re = nm->mkNode(kind::STRING_SUBSTR, n2[0], end_pos, len_n2s);
              }
            }
            return true;
          }
        }
      }

      if (!computeRemainder && dir == 0)
      {
        if (n1.getKind() == STRING_STRREPL)
        {
          // (str.contains (str.replace x y z) w) ---> true
          // if (str.contains x w) --> true and (str.contains z w) ---> true
          Node xCtnW = checkEntailContains(n1[0], n2);
          if (!xCtnW.isNull() && xCtnW.getConst<bool>())
          {
            Node zCtnW = checkEntailContains(n1[2], n2);
            if (!zCtnW.isNull() && zCtnW.getConst<bool>())
            {
              return true;
            }
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

  NodeManager* nm = NodeManager::currentNM();
  bool changed = false;
  // for ( forwards, backwards ) direction
  for (unsigned r = 0; r < 2; r++)
  {
    if (dir == 0 || (r == 0 && dir == 1) || (r == 1 && dir == -1))
    {
      unsigned index0 = r == 0 ? 0 : n1.size() - 1;
      unsigned index1 = r == 0 ? 0 : n2.size() - 1;
      bool removeComponent = false;
      Node n1cmp = n1[index0];

      if (n1cmp.isConst() && n1cmp.getConst<String>().size() == 0)
      {
        return false;
      }

      std::vector<Node> sss;
      std::vector<Node> sls;
      n1cmp = decomposeSubstrChain(n1cmp, sss, sls);
      Trace("strings-rewrite-debug2")
          << "stripConstantEndpoints : Compare " << n1cmp << " " << n2[index1]
          << ", dir = " << dir << std::endl;
      if (n1cmp.isConst())
      {
        CVC4::String s = n1cmp.getConst<String>();
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
            else if (sss.empty())  // only if not substr
            {
              // check how much overlap there is
              // This is used to partially strip off the endpoint
              // e.g. str.contains( str.++( "abc", x ), str.++( "cd", y ) ) -->
              // str.contains( str.++( "c", x ), str.++( "cd", y ) )
              overlap = r == 0 ? s.overlap(t) : t.overlap(s);
            }
            else
            {
              // if we are looking at a substring, we can remove the component
              // if there is no overlap
              //   e.g. str.contains( str.++( str.substr( "c", i, j ), x), "a" )
              //        --> str.contains( x, "a" )
              removeComponent = ((r == 0 ? s.overlap(t) : t.overlap(s)) == 0);
            }
          }
          else if (sss.empty())  // only if not substr
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
              nb.push_back(nm->mkConst(s.prefix(s.size() - overlap)));
              n1[index0] = nm->mkConst(s.suffix(overlap));
            }
            else
            {
              ne.push_back(nm->mkConst(s.suffix(s.size() - overlap)));
              n1[index0] = nm->mkConst(s.prefix(overlap));
            }
          }
        }
      }
      else if (n1cmp.getKind() == kind::STRING_ITOS)
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

Node TheoryStringsRewriter::canonicalStrForSymbolicLength(Node len)
{
  NodeManager* nm = NodeManager::currentNM();

  Node res;
  if (len.getKind() == kind::CONST_RATIONAL)
  {
    // c -> "A" repeated c times
    Rational ratLen = len.getConst<Rational>();
    Assert(ratLen.getDenominator() == 1);
    Integer intLen = ratLen.getNumerator();
    res = nm->mkConst(String(std::string(intLen.getUnsignedInt(), 'A')));
  }
  else if (len.getKind() == kind::PLUS)
  {
    // x + y -> norm(x) + norm(y)
    NodeBuilder<> concatBuilder(kind::STRING_CONCAT);
    for (const auto& n : len)
    {
      Node sn = canonicalStrForSymbolicLength(n);
      if (sn.isNull())
      {
        return Node::null();
      }
      std::vector<Node> snChildren;
      utils::getConcat(sn, snChildren);
      concatBuilder.append(snChildren);
    }
    res = concatBuilder.constructNode();
  }
  else if (len.getKind() == kind::MULT && len.getNumChildren() == 2
           && len[0].isConst())
  {
    // c * x -> norm(x) repeated c times
    Rational ratReps = len[0].getConst<Rational>();
    Assert(ratReps.getDenominator() == 1);
    Integer intReps = ratReps.getNumerator();

    Node nRep = canonicalStrForSymbolicLength(len[1]);
    std::vector<Node> nRepChildren;
    utils::getConcat(nRep, nRepChildren);
    NodeBuilder<> concatBuilder(kind::STRING_CONCAT);
    for (size_t i = 0, reps = intReps.getUnsignedInt(); i < reps; i++)
    {
      concatBuilder.append(nRepChildren);
    }
    res = concatBuilder.constructNode();
  }
  else if (len.getKind() == kind::STRING_LENGTH)
  {
    // len(x) -> x
    res = len[0];
  }
  return res;
}

Node TheoryStringsRewriter::lengthPreserveRewrite(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node len = Rewriter::rewrite(nm->mkNode(kind::STRING_LENGTH, n));
  Node res = canonicalStrForSymbolicLength(len);
  return res.isNull() ? n : res;
}

Node TheoryStringsRewriter::checkEntailContains(Node a,
                                                Node b,
                                                bool fullRewriter)
{
  NodeManager* nm = NodeManager::currentNM();
  Node ctn = nm->mkNode(kind::STRING_STRCTN, a, b);

  if (fullRewriter)
  {
    ctn = Rewriter::rewrite(ctn);
  }
  else
  {
    Node prev;
    do
    {
      prev = ctn;
      ctn = rewriteContains(ctn);
    } while (prev != ctn && ctn.getKind() == kind::STRING_STRCTN);
  }

  Assert(ctn.getType().isBoolean());
  return ctn.isConst() ? ctn : Node::null();
}

bool TheoryStringsRewriter::checkEntailNonEmpty(Node a)
{
  Node len = NodeManager::currentNM()->mkNode(STRING_LENGTH, a);
  len = Rewriter::rewrite(len);
  return checkEntailArith(len, true);
}

bool TheoryStringsRewriter::checkEntailLengthOne(Node s, bool strict)
{
  NodeManager* nm = NodeManager::currentNM();
  Node one = nm->mkConst(Rational(1));
  Node len = nm->mkNode(STRING_LENGTH, s);
  len = Rewriter::rewrite(len);
  return checkEntailArith(one, len) && (!strict || checkEntailArith(len, true));
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

struct StrCheckEntailArithTag
{
};
struct StrCheckEntailArithComputedTag
{
};
/** Attribute true for expressions for which checkEntailArith returned true */
typedef expr::Attribute<StrCheckEntailArithTag, bool> StrCheckEntailArithAttr;
typedef expr::Attribute<StrCheckEntailArithComputedTag, bool>
    StrCheckEntailArithComputedAttr;

bool TheoryStringsRewriter::checkEntailArith(Node a, bool strict)
{
  if (a.isConst())
  {
    return a.getConst<Rational>().sgn() >= (strict ? 1 : 0);
  }

  Node ar =
      strict
          ? NodeManager::currentNM()->mkNode(
                kind::MINUS, a, NodeManager::currentNM()->mkConst(Rational(1)))
          : a;
  ar = Rewriter::rewrite(ar);

  if (ar.getAttribute(StrCheckEntailArithComputedAttr()))
  {
    return ar.getAttribute(StrCheckEntailArithAttr());
  }

  bool ret = checkEntailArithInternal(ar);
  if (!ret)
  {
    // try with approximations
    ret = checkEntailArithApprox(ar);
  }
  // cache the result
  ar.setAttribute(StrCheckEntailArithAttr(), ret);
  ar.setAttribute(StrCheckEntailArithComputedAttr(), true);
  return ret;
}

bool TheoryStringsRewriter::checkEntailArithApprox(Node ar)
{
  Assert(Rewriter::rewrite(ar) == ar);
  NodeManager* nm = NodeManager::currentNM();
  std::map<Node, Node> msum;
  Trace("strings-ent-approx-debug")
      << "Setup arithmetic approximations for " << ar << std::endl;
  if (!ArithMSum::getMonomialSum(ar, msum))
  {
    Trace("strings-ent-approx-debug")
        << "...failed to get monomial sum!" << std::endl;
    return false;
  }
  // for each monomial v*c, mApprox[v] a list of
  // possibilities for how the term can be soundly approximated, that is,
  // if mApprox[v] contains av, then v*c > av*c. Notice that if c
  // is positive, then v > av, otherwise if c is negative, then v < av.
  // In other words, av is an under-approximation if c is positive, and an
  // over-approximation if c is negative.
  bool changed = false;
  std::map<Node, std::vector<Node> > mApprox;
  // map from approximations to their monomial sums
  std::map<Node, std::map<Node, Node> > approxMsums;
  // aarSum stores each monomial that does not have multiple approximations
  std::vector<Node> aarSum;
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    Node c = m.second;
    Trace("strings-ent-approx-debug")
        << "Get approximations " << v << "..." << std::endl;
    if (v.isNull())
    {
      Node mn = c.isNull() ? nm->mkConst(Rational(1)) : c;
      aarSum.push_back(mn);
    }
    else
    {
      // c.isNull() means c = 1
      bool isOverApprox = !c.isNull() && c.getConst<Rational>().sgn() == -1;
      std::vector<Node>& approx = mApprox[v];
      std::unordered_set<Node, NodeHashFunction> visited;
      std::vector<Node> toProcess;
      toProcess.push_back(v);
      do
      {
        Node curr = toProcess.back();
        Trace("strings-ent-approx-debug") << "  process " << curr << std::endl;
        curr = Rewriter::rewrite(curr);
        toProcess.pop_back();
        if (visited.find(curr) == visited.end())
        {
          visited.insert(curr);
          std::vector<Node> currApprox;
          getArithApproximations(curr, currApprox, isOverApprox);
          if (currApprox.empty())
          {
            Trace("strings-ent-approx-debug")
                << "...approximation: " << curr << std::endl;
            // no approximations, thus curr is a possibility
            approx.push_back(curr);
          }
          else
          {
            toProcess.insert(
                toProcess.end(), currApprox.begin(), currApprox.end());
          }
        }
      } while (!toProcess.empty());
      Assert(!approx.empty());
      // if we have only one approximation, move it to final
      if (approx.size() == 1)
      {
        changed = v != approx[0];
        Node mn = ArithMSum::mkCoeffTerm(c, approx[0]);
        aarSum.push_back(mn);
        mApprox.erase(v);
      }
      else
      {
        // compute monomial sum form for each approximation, used below
        for (const Node& aa : approx)
        {
          if (approxMsums.find(aa) == approxMsums.end())
          {
            CVC4_UNUSED bool ret =
                ArithMSum::getMonomialSum(aa, approxMsums[aa]);
            Assert(ret);
          }
        }
        changed = true;
      }
    }
  }
  if (!changed)
  {
    // approximations had no effect, return
    Trace("strings-ent-approx-debug") << "...no approximations" << std::endl;
    return false;
  }
  // get the current "fixed" sum for the abstraction of ar
  Node aar = aarSum.empty()
                 ? nm->mkConst(Rational(0))
                 : (aarSum.size() == 1 ? aarSum[0] : nm->mkNode(PLUS, aarSum));
  aar = Rewriter::rewrite(aar);
  Trace("strings-ent-approx-debug")
      << "...processed fixed sum " << aar << " with " << mApprox.size()
      << " approximated monomials." << std::endl;
  // if we have a choice of how to approximate
  if (!mApprox.empty())
  {
    // convert aar back to monomial sum
    std::map<Node, Node> msumAar;
    if (!ArithMSum::getMonomialSum(aar, msumAar))
    {
      return false;
    }
    if (Trace.isOn("strings-ent-approx"))
    {
      Trace("strings-ent-approx")
          << "---- Check arithmetic entailment by under-approximation " << ar
          << " >= 0" << std::endl;
      Trace("strings-ent-approx") << "FIXED:" << std::endl;
      ArithMSum::debugPrintMonomialSum(msumAar, "strings-ent-approx");
      Trace("strings-ent-approx") << "APPROX:" << std::endl;
      for (std::pair<const Node, std::vector<Node> >& a : mApprox)
      {
        Node c = msum[a.first];
        Trace("strings-ent-approx") << "  ";
        if (!c.isNull())
        {
          Trace("strings-ent-approx") << c << " * ";
        }
        Trace("strings-ent-approx")
            << a.second << " ...from " << a.first << std::endl;
      }
      Trace("strings-ent-approx") << std::endl;
    }
    Rational one(1);
    // incorporate monomials one at a time that have a choice of approximations
    while (!mApprox.empty())
    {
      Node v;
      Node vapprox;
      int maxScore = -1;
      // Look at each approximation, take the one with the best score.
      // Notice that we are in the process of trying to prove
      // ( c1*t1 + .. + cn*tn ) + ( approx_1 | ... | approx_m ) >= 0,
      // where c1*t1 + .. + cn*tn is the "fixed" component of our sum (aar)
      // and approx_1 ... approx_m are possible approximations. The
      // intution here is that we want coefficients c1...cn to be positive.
      // This is because arithmetic string terms t1...tn (which may be
      // applications of len, indexof, str.to.int) are never entailed to be
      // negative. Hence, we add the approx_i that contributes the "most"
      // towards making all constants c1...cn positive and cancelling negative
      // monomials in approx_i itself.
      for (std::pair<const Node, std::vector<Node> >& nam : mApprox)
      {
        Node cr = msum[nam.first];
        for (const Node& aa : nam.second)
        {
          unsigned helpsCancelCount = 0;
          unsigned addsObligationCount = 0;
          std::map<Node, Node>::iterator it;
          // we are processing an approximation cr*( c1*t1 + ... + cn*tn )
          for (std::pair<const Node, Node>& aam : approxMsums[aa])
          {
            // Say aar is of the form t + c*ti, and aam is the monomial ci*ti
            // where ci != 0. We say aam:
            // (1) helps cancel if c != 0 and c>0 != ci>0
            // (2) adds obligation if c>=0 and c+ci<0
            Node ti = aam.first;
            Node ci = aam.second;
            if (!cr.isNull())
            {
              ci = ci.isNull() ? cr
                               : Rewriter::rewrite(nm->mkNode(MULT, ci, cr));
            }
            Trace("strings-ent-approx-debug") << ci << "*" << ti << " ";
            int ciSgn = ci.isNull() ? 1 : ci.getConst<Rational>().sgn();
            it = msumAar.find(ti);
            if (it != msumAar.end())
            {
              Node c = it->second;
              int cSgn = c.isNull() ? 1 : c.getConst<Rational>().sgn();
              if (cSgn == 0)
              {
                addsObligationCount += (ciSgn == -1 ? 1 : 0);
              }
              else if (cSgn != ciSgn)
              {
                helpsCancelCount++;
                Rational r1 = c.isNull() ? one : c.getConst<Rational>();
                Rational r2 = ci.isNull() ? one : ci.getConst<Rational>();
                Rational r12 = r1 + r2;
                if (r12.sgn() == -1)
                {
                  addsObligationCount++;
                }
              }
            }
            else
            {
              addsObligationCount += (ciSgn == -1 ? 1 : 0);
            }
          }
          Trace("strings-ent-approx-debug")
              << "counts=" << helpsCancelCount << "," << addsObligationCount
              << " for " << aa << " into " << aar << std::endl;
          int score = (addsObligationCount > 0 ? 0 : 2)
                      + (helpsCancelCount > 0 ? 1 : 0);
          // if its the best, update v and vapprox
          if (v.isNull() || score > maxScore)
          {
            v = nam.first;
            vapprox = aa;
            maxScore = score;
          }
        }
        if (!v.isNull())
        {
          break;
        }
      }
      Trace("strings-ent-approx")
          << "- Decide " << v << " = " << vapprox << std::endl;
      // we incorporate v approximated by vapprox into the overall approximation
      // for ar
      Assert(!v.isNull() && !vapprox.isNull());
      Assert(msum.find(v) != msum.end());
      Node mn = ArithMSum::mkCoeffTerm(msum[v], vapprox);
      aar = nm->mkNode(PLUS, aar, mn);
      // update the msumAar map
      aar = Rewriter::rewrite(aar);
      msumAar.clear();
      if (!ArithMSum::getMonomialSum(aar, msumAar))
      {
        Assert(false);
        Trace("strings-ent-approx")
            << "...failed to get monomial sum!" << std::endl;
        return false;
      }
      // we have processed the approximation for v
      mApprox.erase(v);
    }
    Trace("strings-ent-approx") << "-----------------" << std::endl;
  }
  if (aar == ar)
  {
    Trace("strings-ent-approx-debug")
        << "...approximation had no effect" << std::endl;
    // this should never happen, but we avoid the infinite loop for sanity here
    Assert(false);
    return false;
  }
  // Check entailment on the approximation of ar.
  // Notice that this may trigger further reasoning by approximation. For
  // example, len( replace( x ++ y, substr( x, 0, n ), z ) ) may be
  // under-approximated as len( x ) + len( y ) - len( substr( x, 0, n ) ) on
  // this call, where in the recursive call we may over-approximate
  // len( substr( x, 0, n ) ) as len( x ). In this example, we can infer
  // that len( replace( x ++ y, substr( x, 0, n ), z ) ) >= len( y ) in two
  // steps.
  if (checkEntailArith(aar))
  {
    Trace("strings-ent-approx")
        << "*** StrArithApprox: showed " << ar
        << " >= 0 using under-approximation!" << std::endl;
    Trace("strings-ent-approx")
        << "*** StrArithApprox: under-approximation was " << aar << std::endl;
    return true;
  }
  return false;
}

void TheoryStringsRewriter::getArithApproximations(Node a,
                                                   std::vector<Node>& approx,
                                                   bool isOverApprox)
{
  NodeManager* nm = NodeManager::currentNM();
  // We do not handle PLUS here since this leads to exponential behavior.
  // Instead, this is managed, e.g. during checkEntailArithApprox, where
  // PLUS terms are expanded "on-demand" during the reasoning.
  Trace("strings-ent-approx-debug")
      << "Get arith approximations " << a << std::endl;
  Kind ak = a.getKind();
  if (ak == MULT)
  {
    Node c;
    Node v;
    if (ArithMSum::getMonomial(a, c, v))
    {
      bool isNeg = c.getConst<Rational>().sgn() == -1;
      getArithApproximations(v, approx, isNeg ? !isOverApprox : isOverApprox);
      for (unsigned i = 0, size = approx.size(); i < size; i++)
      {
        approx[i] = nm->mkNode(MULT, c, approx[i]);
      }
    }
  }
  else if (ak == STRING_LENGTH)
  {
    Kind aak = a[0].getKind();
    if (aak == STRING_SUBSTR)
    {
      // over,under-approximations for len( substr( x, n, m ) )
      Node lenx = nm->mkNode(STRING_LENGTH, a[0][0]);
      if (isOverApprox)
      {
        // m >= 0 implies
        //  m >= len( substr( x, n, m ) )
        if (checkEntailArith(a[0][2]))
        {
          approx.push_back(a[0][2]);
        }
        if (checkEntailArith(lenx, a[0][1]))
        {
          // n <= len( x ) implies
          //   len( x ) - n >= len( substr( x, n, m ) )
          approx.push_back(nm->mkNode(MINUS, lenx, a[0][1]));
        }
        else
        {
          // len( x ) >= len( substr( x, n, m ) )
          approx.push_back(lenx);
        }
      }
      else
      {
        // 0 <= n and n+m <= len( x ) implies
        //   m <= len( substr( x, n, m ) )
        Node npm = nm->mkNode(PLUS, a[0][1], a[0][2]);
        if (checkEntailArith(a[0][1]) && checkEntailArith(lenx, npm))
        {
          approx.push_back(a[0][2]);
        }
        // 0 <= n and n+m >= len( x ) implies
        //   len(x)-n <= len( substr( x, n, m ) )
        if (checkEntailArith(a[0][1]) && checkEntailArith(npm, lenx))
        {
          approx.push_back(nm->mkNode(MINUS, lenx, a[0][1]));
        }
      }
    }
    else if (aak == STRING_STRREPL)
    {
      // over,under-approximations for len( replace( x, y, z ) )
      // notice this is either len( x ) or ( len( x ) + len( z ) - len( y ) )
      Node lenx = nm->mkNode(STRING_LENGTH, a[0][0]);
      Node leny = nm->mkNode(STRING_LENGTH, a[0][1]);
      Node lenz = nm->mkNode(STRING_LENGTH, a[0][2]);
      if (isOverApprox)
      {
        if (checkEntailArith(leny, lenz))
        {
          // len( y ) >= len( z ) implies
          //   len( x ) >= len( replace( x, y, z ) )
          approx.push_back(lenx);
        }
        else
        {
          // len( x ) + len( z ) >= len( replace( x, y, z ) )
          approx.push_back(nm->mkNode(PLUS, lenx, lenz));
        }
      }
      else
      {
        if (checkEntailArith(lenz, leny) || checkEntailArith(lenz, lenx))
        {
          // len( y ) <= len( z ) or len( x ) <= len( z ) implies
          //   len( x ) <= len( replace( x, y, z ) )
          approx.push_back(lenx);
        }
        else
        {
          // len( x ) - len( y ) <= len( replace( x, y, z ) )
          approx.push_back(nm->mkNode(MINUS, lenx, leny));
        }
      }
    }
    else if (aak == STRING_ITOS)
    {
      // over,under-approximations for len( int.to.str( x ) )
      if (isOverApprox)
      {
        if (checkEntailArith(a[0][0], false))
        {
          if (checkEntailArith(a[0][0], true))
          {
            // x > 0 implies
            //   x >= len( int.to.str( x ) )
            approx.push_back(a[0][0]);
          }
          else
          {
            // x >= 0 implies
            //   x+1 >= len( int.to.str( x ) )
            approx.push_back(
                nm->mkNode(PLUS, nm->mkConst(Rational(1)), a[0][0]));
          }
        }
      }
      else
      {
        if (checkEntailArith(a[0][0]))
        {
          // x >= 0 implies
          //   len( int.to.str( x ) ) >= 1
          approx.push_back(nm->mkConst(Rational(1)));
        }
        // other crazy things are possible here, e.g.
        // len( int.to.str( len( y ) + 10 ) ) >= 2
      }
    }
  }
  else if (ak == STRING_STRIDOF)
  {
    // over,under-approximations for indexof( x, y, n )
    if (isOverApprox)
    {
      Node lenx = nm->mkNode(STRING_LENGTH, a[0]);
      Node leny = nm->mkNode(STRING_LENGTH, a[1]);
      if (checkEntailArith(lenx, leny))
      {
        // len( x ) >= len( y ) implies
        //   len( x ) - len( y ) >= indexof( x, y, n )
        approx.push_back(nm->mkNode(MINUS, lenx, leny));
      }
      else
      {
        // len( x ) >= indexof( x, y, n )
        approx.push_back(lenx);
      }
    }
    else
    {
      // TODO?:
      // contains( substr( x, n, len( x ) ), y ) implies
      //   n <= indexof( x, y, n )
      // ...hard to test, runs risk of non-termination

      // -1 <= indexof( x, y, n )
      approx.push_back(nm->mkConst(Rational(-1)));
    }
  }
  else if (ak == STRING_STOI)
  {
    // over,under-approximations for str.to.int( x )
    if (isOverApprox)
    {
      // TODO?:
      // y >= 0 implies
      //   y >= str.to.int( int.to.str( y ) )
    }
    else
    {
      // -1 <= str.to.int( x )
      approx.push_back(nm->mkConst(Rational(-1)));
    }
  }
  Trace("strings-ent-approx-debug") << "Return " << approx.size() << std::endl;
}

bool TheoryStringsRewriter::checkEntailMultisetSubset(Node a, Node b)
{
  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> avec;
  utils::getConcat(getMultisetApproximation(a), avec);
  std::vector<Node> bvec;
  utils::getConcat(b, bvec);

  std::map<Node, unsigned> num_nconst[2];
  std::map<Node, unsigned> num_const[2];
  for (unsigned j = 0; j < 2; j++)
  {
    std::vector<Node>& jvec = j == 0 ? avec : bvec;
    for (const Node& cc : jvec)
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
          Node ch = nm->mkConst(String(cc_vec));
          count_const[j][ch] += ncp.second;
          if (std::find(chars.begin(), chars.end(), ch) == chars.end())
          {
            chars.push_back(ch);
          }
        }
      }
    }
    Trace("strings-entail-ms-ss")
        << "For " << a << " and " << b << " : " << std::endl;
    for (const Node& ch : chars)
    {
      Trace("strings-entail-ms-ss") << "  # occurrences of substring ";
      Trace("strings-entail-ms-ss") << ch << " in arguments is ";
      Trace("strings-entail-ms-ss")
          << count_const[0][ch] << " / " << count_const[1][ch] << std::endl;
      if (count_const[0][ch] < count_const[1][ch])
      {
        return true;
      }
    }

    // TODO (#1180): count the number of 2,3,4,.. character substrings
    // for example:
    // str.contains( str.++( x, "cbabc" ), str.++( "cabbc", x ) ) ---> false
    // since the second argument contains more occurrences of "bb".
    // note this is orthogonal reasoning to inductive reasoning
    // via regular membership reduction in Liang et al CAV 2015.
  }
  return false;
}

Node TheoryStringsRewriter::checkEntailHomogeneousString(Node a)
{
  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> avec;
  utils::getConcat(getMultisetApproximation(a), avec);

  bool cValid = false;
  unsigned c = 0;
  for (const Node& ac : avec)
  {
    if (ac.getKind() == CONST_STRING)
    {
      std::vector<unsigned> acv = ac.getConst<String>().getVec();
      for (unsigned cc : acv)
      {
        if (!cValid)
        {
          cValid = true;
          c = cc;
        }
        else if (c != cc)
        {
          // Found a different character
          return Node::null();
        }
      }
    }
    else
    {
      // Could produce a different character
      return Node::null();
    }
  }

  if (!cValid)
  {
    return nm->mkConst(String(""));
  }

  std::vector<unsigned> cv = {c};
  return nm->mkConst(String(cv));
}

Node TheoryStringsRewriter::getMultisetApproximation(Node a)
{
  NodeManager* nm = NodeManager::currentNM();
  if (a.getKind() == STRING_SUBSTR)
  {
    return a[0];
  }
  else if (a.getKind() == STRING_STRREPL)
  {
    return getMultisetApproximation(nm->mkNode(STRING_CONCAT, a[0], a[2]));
  }
  else if (a.getKind() == STRING_CONCAT)
  {
    NodeBuilder<> nb(STRING_CONCAT);
    for (const Node& ac : a)
    {
      nb << getMultisetApproximation(ac);
    }
    return nb.constructNode();
  }
  else
  {
    return a;
  }
}

bool TheoryStringsRewriter::checkEntailArithWithEqAssumption(Node assumption,
                                                             Node a,
                                                             bool strict)
{
  Assert(assumption.getKind() == kind::EQUAL);
  Assert(Rewriter::rewrite(assumption) == assumption);

  // Find candidates variables to compute substitutions for
  std::unordered_set<Node, NodeHashFunction> candVars;
  std::vector<Node> toVisit = {assumption};
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    if (curr.getKind() == kind::PLUS || curr.getKind() == kind::MULT
        || curr.getKind() == kind::MINUS || curr.getKind() == kind::EQUAL)
    {
      for (const auto& currChild : curr)
      {
        toVisit.push_back(currChild);
      }
    }
    else if (curr.isVar() && Theory::theoryOf(curr) == THEORY_ARITH)
    {
      candVars.insert(curr);
    }
    else if (curr.getKind() == kind::STRING_LENGTH)
    {
      candVars.insert(curr);
    }
  }

  // Check if any of the candidate variables are in n
  Node v;
  Assert(toVisit.empty());
  toVisit.push_back(a);
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    for (const auto& currChild : curr)
    {
      toVisit.push_back(currChild);
    }

    if (candVars.find(curr) != candVars.end())
    {
      v = curr;
      break;
    }
  }

  if (v.isNull())
  {
    // No suitable candidate found
    return false;
  }

  Node solution = ArithMSum::solveEqualityFor(assumption, v);
  if (solution.isNull())
  {
    // Could not solve for v
    return false;
  }

  a = a.substitute(TNode(v), TNode(solution));
  return checkEntailArith(a, strict);
}

bool TheoryStringsRewriter::checkEntailArithWithAssumption(Node assumption,
                                                           Node a,
                                                           Node b,
                                                           bool strict)
{
  Assert(Rewriter::rewrite(assumption) == assumption);

  NodeManager* nm = NodeManager::currentNM();

  if (!assumption.isConst() && assumption.getKind() != kind::EQUAL)
  {
    // We rewrite inequality assumptions from x <= y to x + (str.len s) = y
    // where s is some fresh string variable. We use (str.len s) because
    // (str.len s) must be non-negative for the equation to hold.
    Node x, y;
    if (assumption.getKind() == kind::GEQ)
    {
      x = assumption[0];
      y = assumption[1];
    }
    else
    {
      // (not (>= s t)) --> (>= (t - 1) s)
      Assert(assumption.getKind() == kind::NOT
             && assumption[0].getKind() == kind::GEQ);
      x = nm->mkNode(kind::MINUS, assumption[0][1], nm->mkConst(Rational(1)));
      y = assumption[0][0];
    }

    Node s = nm->mkBoundVar("slackVal", nm->stringType());
    Node slen = nm->mkNode(kind::STRING_LENGTH, s);
    assumption = Rewriter::rewrite(
        nm->mkNode(kind::EQUAL, x, nm->mkNode(kind::PLUS, y, slen)));
  }

  Node diff = nm->mkNode(kind::MINUS, a, b);
  bool res = false;
  if (assumption.isConst())
  {
    bool assumptionBool = assumption.getConst<bool>();
    if (assumptionBool)
    {
      res = checkEntailArith(diff, strict);
    }
    else
    {
      res = true;
    }
  }
  else
  {
    res = checkEntailArithWithEqAssumption(assumption, diff, strict);
  }
  return res;
}

bool TheoryStringsRewriter::checkEntailArithWithAssumptions(
    std::vector<Node> assumptions, Node a, Node b, bool strict)
{
  // TODO: We currently try to show the entailment with each assumption
  // independently. In the future, we should make better use of multiple
  // assumptions.
  bool res = false;
  for (const auto& assumption : assumptions)
  {
    Assert(Rewriter::rewrite(assumption) == assumption);

    if (checkEntailArithWithAssumption(assumption, a, b, strict))
    {
      res = true;
      break;
    }
  }
  return res;
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
  // entailment check should be at least as powerful as computing a lower bound
  Assert(!isLower || ret.isNull() || ret.getConst<Rational>().sgn() < 0
         || checkEntailArith(a, false));
  Assert(!isLower || ret.isNull() || ret.getConst<Rational>().sgn() <= 0
         || checkEntailArith(a, true));
  return ret;
}

Node TheoryStringsRewriter::getFixedLengthForRegexp(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == STRING_TO_REGEXP)
  {
    Node ret = nm->mkNode(STRING_LENGTH, n[0]);
    ret = Rewriter::rewrite(ret);
    if (ret.isConst())
    {
      return ret;
    }
  }
  else if (n.getKind() == REGEXP_SIGMA || n.getKind() == REGEXP_RANGE)
  {
    return nm->mkConst(Rational(1));
  }
  else if (n.getKind() == REGEXP_UNION || n.getKind() == REGEXP_INTER)
  {
    Node ret;
    for (const Node& nc : n)
    {
      Node flc = getFixedLengthForRegexp(nc);
      if (flc.isNull() || (!ret.isNull() && ret != flc))
      {
        return Node::null();
      }
      else if (ret.isNull())
      {
        // first time
        ret = flc;
      }
    }
    return ret;
  }
  else if (n.getKind() == REGEXP_CONCAT)
  {
    NodeBuilder<> nb(PLUS);
    for (const Node& nc : n)
    {
      Node flc = getFixedLengthForRegexp(nc);
      if (flc.isNull())
      {
        return flc;
      }
      nb << flc;
    }
    Node ret = nb.constructNode();
    ret = Rewriter::rewrite(ret);
    return ret;
  }
  return Node::null();
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

Node TheoryStringsRewriter::decomposeSubstrChain(Node s,
                                                 std::vector<Node>& ss,
                                                 std::vector<Node>& ls)
{
  Assert( ss.empty() );
  Assert( ls.empty() );
  while (s.getKind() == STRING_SUBSTR)
  {
    ss.push_back(s[1]);
    ls.push_back(s[2]);
    s = s[0];
  }
  std::reverse(ss.begin(), ss.end());
  std::reverse(ls.begin(), ls.end());
  return s;
}

Node TheoryStringsRewriter::mkSubstrChain(Node base,
                                          const std::vector<Node>& ss,
                                          const std::vector<Node>& ls)
{
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = ss.size(); i < size; i++)
  {
    base = nm->mkNode(STRING_SUBSTR, base, ss[i], ls[i]);
  }
  return base;
}

Node TheoryStringsRewriter::getStringOrEmpty(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node res;
  while (res.isNull())
  {
    switch (n.getKind())
    {
      case kind::STRING_STRREPL:
      {
        Node empty = nm->mkConst(::CVC4::String(""));
        if (n[0] == empty)
        {
          // (str.replace "" x y) --> y
          n = n[2];
          break;
        }

        if (checkEntailLengthOne(n[0]) && n[2] == empty)
        {
          // (str.replace "A" x "") --> "A"
          res = n[0];
          break;
        }

        res = n;
        break;
      }
      case kind::STRING_SUBSTR:
      {
        if (checkEntailLengthOne(n[0]))
        {
          // (str.substr "A" x y) --> "A"
          res = n[0];
          break;
        }
        res = n;
          break;
      }
      default:
      {
        res = n;
        break;
      }
    }
  }
  return res;
}

bool TheoryStringsRewriter::inferZerosInSumGeq(Node x,
                                               std::vector<Node>& ys,
                                               std::vector<Node>& zeroYs)
{
  Assert(zeroYs.empty());

  NodeManager* nm = NodeManager::currentNM();

  // Check if we can show that y1 + ... + yn >= x
  Node sum = (ys.size() > 1) ? nm->mkNode(PLUS, ys) : ys[0];
  if (!checkEntailArith(sum, x))
  {
    return false;
  }

  // Try to remove yi one-by-one and check if we can still show:
  //
  // y1 + ... + yi-1 +  yi+1 + ... + yn >= x
  //
  // If that's the case, we know that yi can be zero and the inequality still
  // holds.
  size_t i = 0;
  while (i < ys.size())
  {
    Node yi = ys[i];
    std::vector<Node>::iterator pos = ys.erase(ys.begin() + i);
    if (ys.size() > 1)
    {
      sum = nm->mkNode(PLUS, ys);
    }
    else
    {
      sum = ys.size() == 1 ? ys[0] : nm->mkConst(Rational(0));
    }

    if (checkEntailArith(sum, x))
    {
      zeroYs.push_back(yi);
    }
    else
    {
      ys.insert(pos, yi);
      i++;
    }
  }
  return true;
}

Node TheoryStringsRewriter::inferEqsFromContains(Node x, Node y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node emp = nm->mkConst(String(""));

  Node xLen = nm->mkNode(STRING_LENGTH, x);
  std::vector<Node> yLens;
  if (y.getKind() != STRING_CONCAT)
  {
    yLens.push_back(nm->mkNode(STRING_LENGTH, y));
  }
  else
  {
    for (const Node& yi : y)
    {
      yLens.push_back(nm->mkNode(STRING_LENGTH, yi));
    }
  }

  std::vector<Node> zeroLens;
  if (x == emp)
  {
    // If x is the empty string, then all ys must be empty, too, and we can
    // skip the expensive checks. Note that this is just a performance
    // optimization.
    zeroLens.swap(yLens);
  }
  else
  {
    // Check if we can infer that str.len(x) <= str.len(y). If that is the
    // case, try to minimize the sum in str.len(x) <= str.len(y1) + ... +
    // str.len(yn) (where y = y1 ++ ... ++ yn) while keeping the inequality
    // true. The terms that can have length zero without making the inequality
    // false must be all be empty if (str.contains x y) is true.
    if (!inferZerosInSumGeq(xLen, yLens, zeroLens))
    {
      // We could not prove that the inequality holds
      return Node::null();
    }
    else if (yLens.size() == y.getNumChildren())
    {
      // We could only prove that the inequality holds but not that any of the
      // ys must be empty
      return nm->mkNode(EQUAL, x, y);
    }
  }

  if (y.getKind() != STRING_CONCAT)
  {
    if (zeroLens.size() == 1)
    {
      // y is not a concatenation and we found that it must be empty, so just
      // return (= y "")
      Assert(zeroLens[0][0] == y);
      return nm->mkNode(EQUAL, y, emp);
    }
    else
    {
      Assert(yLens.size() == 1 && yLens[0][0] == y);
      return nm->mkNode(EQUAL, x, y);
    }
  }

  std::vector<Node> cs;
  for (const Node& yiLen : yLens)
  {
    Assert(std::find(y.begin(), y.end(), yiLen[0]) != y.end());
    cs.push_back(yiLen[0]);
  }

  NodeBuilder<> nb(AND);
  // (= x (str.++ y1' ... ym'))
  if (!cs.empty())
  {
    nb << nm->mkNode(EQUAL, x, utils::mkConcat(STRING_CONCAT, cs));
  }
  // (= y1'' "") ... (= yk'' "")
  for (const Node& zeroLen : zeroLens)
  {
    Assert(std::find(y.begin(), y.end(), zeroLen[0]) != y.end());
    nb << nm->mkNode(EQUAL, zeroLen[0], emp);
  }

  // (and (= x (str.++ y1' ... ym')) (= y1'' "") ... (= yk'' ""))
  return nb.constructNode();
}

std::pair<bool, std::vector<Node> > TheoryStringsRewriter::collectEmptyEqs(
    Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node empty = nm->mkConst(::CVC4::String(""));

  // Collect the equalities of the form (= x "") (sorted)
  std::set<TNode> emptyNodes;
  bool allEmptyEqs = true;
  if (x.getKind() == kind::EQUAL)
  {
    if (x[0] == empty)
    {
      emptyNodes.insert(x[1]);
    }
    else if (x[1] == empty)
    {
      emptyNodes.insert(x[0]);
    }
    else
    {
      allEmptyEqs = false;
    }
  }
  else if (x.getKind() == kind::AND)
  {
    for (const Node& c : x)
    {
      if (c.getKind() == kind::EQUAL)
      {
        if (c[0] == empty)
        {
          emptyNodes.insert(c[1]);
        }
        else if (c[1] == empty)
        {
          emptyNodes.insert(c[0]);
        }
      }
      else
      {
        allEmptyEqs = false;
      }
    }
  }

  if (emptyNodes.size() == 0)
  {
    allEmptyEqs = false;
  }

  return std::make_pair(
      allEmptyEqs, std::vector<Node>(emptyNodes.begin(), emptyNodes.end()));
}

Node TheoryStringsRewriter::returnRewrite(Node node, Node ret, const char* c)
{
  Trace("strings-rewrite") << "Rewrite " << node << " to " << ret << " by " << c
                           << "." << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  // standard post-processing
  // We rewrite (string) equalities immediately here. This allows us to forego
  // the standard invariant on equality rewrites (that s=t must rewrite to one
  // of { s=t, t=s, true, false } ).
  Kind retk = ret.getKind();
  if (retk == OR || retk == AND)
  {
    std::vector<Node> children;
    bool childChanged = false;
    for (const Node& cret : ret)
    {
      Node creter = cret;
      if (cret.getKind() == EQUAL)
      {
        creter = rewriteEqualityExt(cret);
      }
      else if (cret.getKind() == NOT && cret[0].getKind() == EQUAL)
      {
        creter = nm->mkNode(NOT, rewriteEqualityExt(cret[0]));
      }
      childChanged = childChanged || cret != creter;
      children.push_back(creter);
    }
    if (childChanged)
    {
      ret = nm->mkNode(retk, children);
    }
  }
  else if (retk == NOT && ret[0].getKind() == EQUAL)
  {
    ret = nm->mkNode(NOT, rewriteEqualityExt(ret[0]));
  }
  else if (retk == EQUAL && node.getKind() != EQUAL)
  {
    Trace("strings-rewrite")
        << "Apply extended equality rewrite on " << ret << std::endl;
    ret = rewriteEqualityExt(ret);
  }
  return ret;
}
