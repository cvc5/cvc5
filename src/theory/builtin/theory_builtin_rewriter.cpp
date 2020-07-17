/*********************                                                        */
/*! \file theory_builtin_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/builtin/theory_builtin_rewriter.h"

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "theory/rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

Node TheoryBuiltinRewriter::blastDistinct(TNode in) {
  Assert(in.getKind() == kind::DISTINCT);

  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 != pair will be generated so the
    // AND is not required
    Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, in[0], in[1]);
    Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
    return neq;
  }

  // assume that in.getNumChildren() > 2 => diseqs.size() > 1
  vector<Node> diseqs;
  for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
    TNode::iterator j = i;
    while(++j != in.end()) {
      Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, *i, *j);
      Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
      diseqs.push_back(neq);
    }
  }
  Node out = NodeManager::currentNM()->mkNode(kind::AND, diseqs);
  return out;
}

RewriteResponse TheoryBuiltinRewriter::postRewrite(TNode node) {
  if( node.getKind()==kind::LAMBDA ){
    // The following code ensures that if node is equivalent to a constant
    // lambda, then we return the canonical representation for the lambda, which
    // in turn ensures that two constant lambdas are equivalent if and only
    // if they are the same node.
    // We canonicalize lambdas by turning them into array constants, applying
    // normalization on array constants, and then converting the array constant
    // back to a lambda.
    Trace("builtin-rewrite") << "Rewriting lambda " << node << "..." << std::endl;
    Node anode = getArrayRepresentationForLambda( node );
    // Only rewrite constant array nodes, since these are the only cases
    // where we require canonicalization of lambdas. Moreover, applying the
    // below code is not correct if the arguments to the lambda occur
    // in return values. For example, lambda x. ite( x=1, f(x), c ) would
    // be converted to (store (storeall ... c) 1 f(x)), and then converted
    // to lambda y. ite( y=1, f(x), c), losing the relation between x and y.
    if (!anode.isNull() && anode.isConst())
    {
      Assert(anode.getType().isArray());
      //must get the standard bound variable list
      Node varList = NodeManager::currentNM()->getBoundVarListForFunctionType( node.getType() );
      Node retNode = getLambdaForArrayRepresentation( anode, varList );
      if( !retNode.isNull() && retNode!=node ){
        Trace("builtin-rewrite") << "Rewrote lambda : " << std::endl;
        Trace("builtin-rewrite") << "     input  : " << node << std::endl;
        Trace("builtin-rewrite") << "     output : " << retNode << ", constant = " << retNode.isConst() << std::endl;
        Trace("builtin-rewrite") << "  array rep : " << anode << ", constant = " << anode.isConst() << std::endl;
        Assert(anode.isConst() == retNode.isConst());
        Assert(retNode.getType() == node.getType());
        Assert(expr::hasFreeVar(node) == expr::hasFreeVar(retNode));
        return RewriteResponse(REWRITE_DONE, retNode);
      }
    }
    else
    {
      Trace("builtin-rewrite-debug") << "...failed to get array representation." << std::endl;
    }
    return RewriteResponse(REWRITE_DONE, node);
  }
  else if (node.getKind() == kind::WITNESS)
  {
    if (node[1].getKind() == kind::EQUAL)
    {
      for (unsigned i = 0; i < 2; i++)
      {
        // (witness ((x T)) (= x t)) ---> t
        if (node[1][i] == node[0][0])
        {
          Trace("builtin-rewrite") << "Witness rewrite: " << node << " --> "
                                   << node[1][1 - i] << std::endl;
          // also must be a legal elimination: the other side of the equality
          // cannot contain the variable, and it must be a subtype of the
          // variable
          if (!expr::hasSubterm(node[1][1 - i], node[0][0]) &&
              node[1][i].getType().isSubtypeOf(node[0][0].getType()))
          {
            return RewriteResponse(REWRITE_DONE, node[1][1 - i]);
          }
        }
      }
    }
    else if (node[1] == node[0][0])
    {
      // (witness ((x Bool)) x) ---> true
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(true));
    }
    else if (node[1].getKind() == kind::NOT && node[1][0] == node[0][0])
    {
      // (witness ((x Bool)) (not x)) ---> false
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(false));
    }
    return RewriteResponse(REWRITE_DONE, node);
  }else{ 
    return doRewrite(node);
  }
}

TypeNode TheoryBuiltinRewriter::getFunctionTypeForArrayType(TypeNode atn,
                                                            Node bvl)
{
  std::vector<TypeNode> children;
  for (unsigned i = 0; i < bvl.getNumChildren(); i++)
  {
    Assert(atn.isArray());
    Assert(bvl[i].getType() == atn.getArrayIndexType());
    children.push_back(atn.getArrayIndexType());
    atn = atn.getArrayConstituentType();
  }
  children.push_back(atn);
  return NodeManager::currentNM()->mkFunctionType(children);
}

TypeNode TheoryBuiltinRewriter::getArrayTypeForFunctionType(TypeNode ftn)
{
  Assert(ftn.isFunction());
  // construct the curried array type
  unsigned nchildren = ftn.getNumChildren();
  TypeNode ret = ftn[nchildren - 1];
  for (int i = (static_cast<int>(nchildren) - 2); i >= 0; i--)
  {
    ret = NodeManager::currentNM()->mkArrayType(ftn[i], ret);
  }
  return ret;
}

Node TheoryBuiltinRewriter::getLambdaForArrayRepresentationRec( TNode a, TNode bvl, unsigned bvlIndex, 
                                                                std::unordered_map< TNode, Node, TNodeHashFunction >& visited ){
  std::unordered_map< TNode, Node, TNodeHashFunction >::iterator it = visited.find( a );
  if( it==visited.end() ){
    Node ret;
    if( bvlIndex<bvl.getNumChildren() ){
      Assert(a.getType().isArray());
      if( a.getKind()==kind::STORE ){
        // convert the array recursively
        Node body = getLambdaForArrayRepresentationRec( a[0], bvl, bvlIndex, visited );
        if( !body.isNull() ){
          // convert the value recursively (bounded by the number of arguments in bvl)
          Node val = getLambdaForArrayRepresentationRec( a[2], bvl, bvlIndex+1, visited );
          if( !val.isNull() ){
            Assert(!TypeNode::leastCommonTypeNode(a[1].getType(),
                                                  bvl[bvlIndex].getType())
                        .isNull());
            Assert(!TypeNode::leastCommonTypeNode(val.getType(), body.getType())
                        .isNull());
            Node cond = bvl[bvlIndex].eqNode( a[1] );
            ret = NodeManager::currentNM()->mkNode( kind::ITE, cond, val, body );
          }
        }
      }else if( a.getKind()==kind::STORE_ALL ){
        ArrayStoreAll storeAll = a.getConst<ArrayStoreAll>();
        Node sa = storeAll.getValue();
        // convert the default value recursively (bounded by the number of arguments in bvl)
        ret = getLambdaForArrayRepresentationRec( sa, bvl, bvlIndex+1, visited );
      }
    }else{
      ret = a;
    }
    visited[a] = ret;
    return ret;
  }else{
    return it->second;
  }
}

Node TheoryBuiltinRewriter::getLambdaForArrayRepresentation( TNode a, TNode bvl ){
  Assert(a.getType().isArray());
  std::unordered_map< TNode, Node, TNodeHashFunction > visited;
  Trace("builtin-rewrite-debug") << "Get lambda for : " << a << ", with variables " << bvl << std::endl;
  Node body = getLambdaForArrayRepresentationRec( a, bvl, 0, visited );
  if( !body.isNull() ){
    body = Rewriter::rewrite( body );
    Trace("builtin-rewrite-debug") << "...got lambda body " << body << std::endl;
    return NodeManager::currentNM()->mkNode( kind::LAMBDA, bvl, body );
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get lambda body" << std::endl;
    return Node::null();
  }
}

Node TheoryBuiltinRewriter::getArrayRepresentationForLambdaRec(TNode n,
                                                               TypeNode retType)
{
  Assert(n.getKind() == kind::LAMBDA);
  NodeManager* nm = NodeManager::currentNM();
  Trace("builtin-rewrite-debug") << "Get array representation for : " << n << std::endl;

  Node first_arg = n[0][0];
  Node rec_bvl;
  unsigned size = n[0].getNumChildren();
  if (size > 1)
  {
    std::vector< Node > args;
    for (unsigned i = 1; i < size; i++)
    {
      args.push_back( n[0][i] );
    }
    rec_bvl = nm->mkNode(kind::BOUND_VAR_LIST, args);
  }

  Trace("builtin-rewrite-debug2") << "  process body..." << std::endl;
  std::vector< Node > conds;
  std::vector< Node > vals;
  Node curr = n[1];
  Kind ck = curr.getKind();
  while (ck == kind::ITE || ck == kind::OR || ck == kind::AND
         || ck == kind::EQUAL || ck == kind::NOT || ck == kind::BOUND_VARIABLE)
  {
    Node index_eq;
    Node curr_val;
    Node next;
    // Each iteration of this loop infers an entry in the function, e.g. it
    // has a value under some condition.

    // [1] We infer that the entry has value "curr_val" under condition
    // "index_eq". We set "next" to the node that is the remainder of the
    // function to process.
    if (ck == kind::ITE)
    {
      Trace("builtin-rewrite-debug2")
          << "  process condition : " << curr[0] << std::endl;
      index_eq = curr[0];
      curr_val = curr[1];
      next = curr[2];
    }
    else if (ck == kind::OR || ck == kind::AND)
    {
      Trace("builtin-rewrite-debug2")
          << "  process base : " << curr << std::endl;
      // curr = Rewriter::rewrite(curr);
      // Trace("builtin-rewrite-debug2")
      //     << "  rewriten base : " << curr << std::endl;
      // Complex Boolean return cases, in which
      //  (1) lambda x. (= x v1) v ... becomes
      //      lambda x. (ite (= x v1) true [...])
      //
      //  (2) lambda x. (not (= x v1)) ^ ... becomes
      //      lambda x. (ite (= x v1) false [...])
      //
      // Note the negated cases of the lhs of the OR/AND operators above are
      // handled by pushing the recursion to the then-branch, with the
      // else-branch being the constant value. For example, the negated (1)
      // would be
      //  (1') lambda x. (not (= x v1)) v ... becomes
      //       lambda x. (ite (= x v1) [...] true)
      // thus requiring the rest of the disjunction to be further processed in
      // the then-branch as the current value.
      bool pol = curr[0].getKind() != kind::NOT;
      bool inverted = (pol && ck == kind::AND) || (!pol && ck == kind::OR);
      index_eq = pol ? curr[0] : curr[0][0];
      // processed : the value that is determined by the first child of curr
      // remainder : the remaining children of curr
      Node processed, remainder;
      // the value is the polarity of the first child or its inverse if we are
      // in the inverted case
      processed = nm->mkConst(!inverted? pol : !pol);
      // build an OR/AND with the remaining components
      if (curr.getNumChildren() == 2)
      {
        remainder = curr[1];
      }
      else
      {
        std::vector<Node> remainderNodes{curr.begin() + 1, curr.end()};
        remainder = nm->mkNode(ck, remainderNodes);
      }
      if (inverted)
      {
        curr_val = remainder;
        next = processed;
        // If the lambda contains more variables than the one being currently
        // processed, the current value can be non-constant, since it'll be
        // processed recursively below. Otherwise we fail.
        if (rec_bvl.isNull() && !curr_val.isConst())
        {
          Trace("builtin-rewrite-debug2")
              << "...non-const curr_val " << curr_val << "\n";
          return Node::null();
        }
      }
      else
      {
        curr_val = processed;
        next = remainder;
      }
      Trace("builtin-rewrite-debug2") << "  index_eq : " << index_eq << "\n";
      Trace("builtin-rewrite-debug2") << "  curr_val : " << curr_val << "\n";
      Trace("builtin-rewrite-debug2") << "  next : " << next << std::endl;
    }
    else
    {
      Trace("builtin-rewrite-debug2")
          << "  process base : " << curr << std::endl;
      // Simple Boolean return cases, in which
      //  (1) lambda x. (= x v) becomes lambda x. (ite (= x v) true false)
      //  (2) lambda x. v becomes lambda x. (ite (= x v) true false)
      // Note the negateg cases of the bodies above are also handled.
      bool pol = ck != kind::NOT;
      index_eq = pol ? curr : curr[0];
      curr_val = nm->mkConst(pol);
      next = nm->mkConst(!pol);
    }

    // [2] We ensure that "index_eq" is an equality, if possible.
    if (index_eq.getKind() != kind::EQUAL)
    {
      bool pol = index_eq.getKind() != kind::NOT;
      Node indexEqAtom = pol ? index_eq : index_eq[0];
      if (indexEqAtom.getKind() == kind::BOUND_VARIABLE)
      {
        if (!indexEqAtom.getType().isBoolean())
        {
          // Catches default case of non-Boolean variable, e.g.
          // lambda x : Int. x. In this case, it is not canonical and we fail.
          Trace("builtin-rewrite-debug2")
              << "  ...non-Boolean variable." << std::endl;
          return Node::null();
        }
        // Boolean argument case, e.g. lambda x. ite( x, t, s ) is processed as
        // lambda x. (ite (= x true) t s)
        index_eq = indexEqAtom.eqNode(nm->mkConst(pol));
      }
      else
      {
        // non-equality condition
        Trace("builtin-rewrite-debug2")
            << "  ...non-equality condition." << std::endl;
        return Node::null();
      }
    }
    else if (Rewriter::rewrite(index_eq) != index_eq)
    {
      // equality must be oriented correctly based on rewriter
      Trace("builtin-rewrite-debug2") << "  ...equality not oriented properly." << std::endl;
      return Node::null();
    }

    // [3] We ensure that "index_eq" is an equality that is equivalent to
    // "first_arg" = "curr_index", where curr_index is a constant, and
    // "first_arg" is the current argument we are processing, if possible.
    Node curr_index;
    for( unsigned r=0; r<2; r++ ){
      Node arg = index_eq[r];
      Node val = index_eq[1-r];
      if( arg==first_arg ){
        if (!val.isConst())
        {
          // non-constant value
          Trace("builtin-rewrite-debug2")
              << "  ...non-constant value for argument\n.";
          return Node::null();
        }else{
          curr_index = val;
          Trace("builtin-rewrite-debug2")
              << "  arg " << arg << " -> " << val << std::endl;
          break;
        }
      }
    }
    if (curr_index.isNull())
    {
      Trace("builtin-rewrite-debug2")
          << "  ...could not infer index value." << std::endl;
      return Node::null();
    }

    // [4] Recurse to ensure that "curr_val" has been normalized w.r.t. the
    // remaining arguments (rec_bvl).
    if (!rec_bvl.isNull())
    {
      curr_val = nm->mkNode(kind::LAMBDA, rec_bvl, curr_val);
      Trace("builtin-rewrite-debug") << push;
      Trace("builtin-rewrite-debug2") << push;
      curr_val = getArrayRepresentationForLambdaRec(curr_val, retType);
      Trace("builtin-rewrite-debug") << pop;
      Trace("builtin-rewrite-debug2") << pop;
      if (curr_val.isNull())
      {
        Trace("builtin-rewrite-debug2")
            << "  ...failed to recursively find value." << std::endl;
        return Node::null();
      }
    }
    Trace("builtin-rewrite-debug2")
        << "  ...condition is index " << curr_val << std::endl;

    // [5] Add the entry
    conds.push_back( curr_index );
    vals.push_back( curr_val );

    // we will now process the remainder
    curr = next;
    ck = curr.getKind();
    Trace("builtin-rewrite-debug2")
        << "  process remainder : " << curr << std::endl;
  }
  if( !rec_bvl.isNull() ){
    curr = nm->mkNode(kind::LAMBDA, rec_bvl, curr);
    Trace("builtin-rewrite-debug") << push;
    Trace("builtin-rewrite-debug2") << push;
    curr = getArrayRepresentationForLambdaRec(curr, retType);
    Trace("builtin-rewrite-debug") << pop;
    Trace("builtin-rewrite-debug2") << pop;
  }
  if( !curr.isNull() && curr.isConst() ){
    // compute the return type
    TypeNode array_type = retType;
    for (unsigned i = 0; i < size; i++)
    {
      unsigned index = (size - 1) - i;
      array_type = nm->mkArrayType(n[0][index].getType(), array_type);
    }
    Trace("builtin-rewrite-debug2") << "  make array store all " << curr.getType() << " annotated : " << array_type << std::endl;
    Assert(curr.getType().isSubtypeOf(array_type.getArrayConstituentType()));
    curr = nm->mkConst(ArrayStoreAll(array_type, curr));
    Trace("builtin-rewrite-debug2") << "  build array..." << std::endl;
    // can only build if default value is constant (since array store all must be constant)
    Trace("builtin-rewrite-debug2") << "  got constant base " << curr << std::endl;
    Trace("builtin-rewrite-debug2") << "  conditions " << conds << std::endl;
    Trace("builtin-rewrite-debug2") << "  values " << vals << std::endl;
    // construct store chain
    for (int i = static_cast<int>(conds.size()) - 1; i >= 0; i--)
    {
      Assert(conds[i].getType().isSubtypeOf(first_arg.getType()));
      curr = nm->mkNode(kind::STORE, curr, conds[i], vals[i]);
    }
    Trace("builtin-rewrite-debug") << "...got array " << curr << " for " << n << std::endl;
    return curr;
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get array (cannot get constant default value)" << std::endl;
    return Node::null();    
  }
}

Node TheoryBuiltinRewriter::getArrayRepresentationForLambda(TNode n)
{
  Assert(n.getKind() == kind::LAMBDA);
  // must carry the overall return type to deal with cases like (lambda ((x Int)
  // (y Int)) (ite (= x _) 0.5 0.0)), where the inner construction for the else
  // case above should be (arraystoreall (Array Int Real) 0.0)
  Node anode = getArrayRepresentationForLambdaRec(n, n[1].getType());
  if (anode.isNull())
  {
    return anode;
  }
  // must rewrite it to make canonical
  return Rewriter::rewrite(anode);
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
