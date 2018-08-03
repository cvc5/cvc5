/*********************                                                        */
/*! \file term_database_sygus.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term database sygus class
 **/

#include "theory/quantifiers/sygus/term_database_sygus.h"

#include "base/cvc4_check.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/arith/arith_msum.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TermDbSygus::TermDbSygus(context::Context* c, QuantifiersEngine* qe)
    : d_quantEngine(qe),
      d_syexp(new SygusExplain(this)),
      d_ext_rw(new ExtendedRewriter(true)),
      d_eval(new Evaluator),
      d_eval_unfold(new SygusEvalUnfold(this))
{
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

bool TermDbSygus::reset( Theory::Effort e ) { 
  return true;  
}

TNode TermDbSygus::getFreeVar( TypeNode tn, int i, bool useSygusType ) {
  unsigned sindex = 0;
  TypeNode vtn = tn;
  if( useSygusType ){
    if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      if( !dt.getSygusType().isNull() ){
        vtn = TypeNode::fromType( dt.getSygusType() );
        sindex = 1;
      } 
    }
  }
  while( i>=(int)d_fv[sindex][tn].size() ){
    std::stringstream ss;
    if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      ss << "fv_" << dt.getName() << "_" << i;
    }else{
      ss << "fv_" << tn << "_" << i;
    }
    Assert( !vtn.isNull() );
    Node v = NodeManager::currentNM()->mkSkolem( ss.str(), vtn, "for sygus normal form testing" );
    d_fv_stype[v] = tn;
    d_fv_num[v] = i;
    d_fv[sindex][tn].push_back( v );
  }
  return d_fv[sindex][tn][i];
}

TNode TermDbSygus::getFreeVarInc( TypeNode tn, std::map< TypeNode, int >& var_count, bool useSygusType ) {
  std::map< TypeNode, int >::iterator it = var_count.find( tn );
  if( it==var_count.end() ){
    var_count[tn] = 1;
    return getFreeVar( tn, 0, useSygusType );
  }else{
    int index = it->second;
    var_count[tn]++;
    return getFreeVar( tn, index, useSygusType );
  }
}

bool TermDbSygus::hasFreeVar( Node n, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( isFreeVar( n ) ){
      return true;    
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( hasFreeVar( n[i], visited ) ){
        return true;
      }
    }
  }
  return false;
}

bool TermDbSygus::hasFreeVar( Node n ) {
  std::map< Node, bool > visited;
  return hasFreeVar( n, visited );
}

Node TermDbSygus::getProxyVariable(TypeNode tn, Node c)
{
  Assert(tn.isDatatype());
  Assert(static_cast<DatatypeType>(tn.toType()).getDatatype().isSygus());
  Assert(
      TypeNode::fromType(
          static_cast<DatatypeType>(tn.toType()).getDatatype().getSygusType())
          .isComparableTo(c.getType()));

  std::map<Node, Node>::iterator it = d_proxy_vars[tn].find(c);
  if (it == d_proxy_vars[tn].end())
  {
    int anyC = getAnyConstantConsNum(tn);
    Node k;
    if (anyC == -1)
    {
      k = NodeManager::currentNM()->mkSkolem("sy", tn, "sygus proxy");
      SygusPrintProxyAttribute spa;
      k.setAttribute(spa, c);
    }
    else
    {
      const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
      k = NodeManager::currentNM()->mkNode(
          APPLY_CONSTRUCTOR, Node::fromExpr(dt[anyC].getConstructor()), c);
    }
    d_proxy_vars[tn][c] = k;
    return k;
  }
  return it->second;
}

TypeNode TermDbSygus::getSygusTypeForVar( Node v ) {
  Assert( d_fv_stype.find( v )!=d_fv_stype.end() );
  return d_fv_stype[v];
}

Node TermDbSygus::mkGeneric(const Datatype& dt,
                            unsigned c,
                            std::map<TypeNode, int>& var_count,
                            std::map<int, Node>& pre)
{
  Assert(c < dt.getNumConstructors());
  Assert( dt.isSygus() );
  Assert( !dt[c].getSygusOp().isNull() );
  std::vector< Node > children;
  Trace("sygus-db-debug") << "mkGeneric " << dt.getName() << " " << c << "..."
                          << std::endl;
  for (unsigned i = 0, nargs = dt[c].getNumArgs(); i < nargs; i++)
  {
    Node a;
    std::map< int, Node >::iterator it = pre.find( i );
    if( it!=pre.end() ){
      a = it->second;
    }else{
      TypeNode tna = TypeNode::fromType(dt[c].getArgType(i));
      a = getFreeVarInc( tna, var_count, true );
    }
    Trace("sygus-db-debug")
        << "  child " << i << " : " << a << " : " << a.getType() << std::endl;
    Assert( !a.isNull() );
    children.push_back( a );
  }
  return datatypes::DatatypesRewriter::mkSygusTerm(dt, c, children);
}

Node TermDbSygus::mkGeneric(const Datatype& dt, int c, std::map<int, Node>& pre)
{
  std::map<TypeNode, int> var_count;
  return mkGeneric(dt, c, var_count, pre);
}

Node TermDbSygus::mkGeneric(const Datatype& dt, int c)
{
  std::map<int, Node> pre;
  return mkGeneric(dt, c, pre);
}

struct CanonizeBuiltinAttributeId
{
};
using CanonizeBuiltinAttribute =
    expr::Attribute<CanonizeBuiltinAttributeId, Node>;

Node TermDbSygus::canonizeBuiltin(Node n)
{
  std::map<TypeNode, int> var_count;
  return canonizeBuiltin(n, var_count);
}

Node TermDbSygus::canonizeBuiltin(Node n, std::map<TypeNode, int>& var_count)
{
  // has it already been computed?
  if (var_count.empty() && n.hasAttribute(CanonizeBuiltinAttribute()))
  {
    Node ret = n.getAttribute(CanonizeBuiltinAttribute());
    Trace("sygus-db-canon") << "cached " << n << " : " << ret << "\n";
    return ret;
  }
  Trace("sygus-db-canon") << "  CanonizeBuiltin : compute for " << n << "\n";
  Node ret = n;
  // it is symbolic if it represents "any constant"
  if (n.getKind() == APPLY_SELECTOR_TOTAL)
  {
    ret = getFreeVarInc(n[0].getType(), var_count, true);
  }
  else if (n.getKind() != APPLY_CONSTRUCTOR)
  {
    ret = n;
  }
  else
  {
    Assert(n.getKind() == APPLY_CONSTRUCTOR);
    bool childChanged = false;
    std::vector<Node> children;
    children.push_back(n.getOperator());
    for (unsigned j = 0, size = n.getNumChildren(); j < size; ++j)
    {
      Node child = canonizeBuiltin(n[j], var_count);
      children.push_back(child);
      childChanged = childChanged || child != n[j];
    }
    if (childChanged)
    {
      ret = NodeManager::currentNM()->mkNode(APPLY_CONSTRUCTOR, children);
    }
  }
  // cache if we had a fresh variable count
  if (var_count.empty())
  {
    n.setAttribute(CanonizeBuiltinAttribute(), ret);
  }
  Trace("sygus-db-canon") << "  ...normalized " << n << " --> " << ret
                          << std::endl;
  Assert(ret.getType().isComparableTo(n.getType()));
  return ret;
}

struct SygusToBuiltinAttributeId
{
};
typedef expr::Attribute<SygusToBuiltinAttributeId, Node>
    SygusToBuiltinAttribute;

Node TermDbSygus::sygusToBuiltin(Node n, TypeNode tn)
{
  Assert(n.getType().isComparableTo(tn));
  if (!tn.isDatatype())
  {
    return n;
  }
  // has it already been computed?
  if (n.hasAttribute(SygusToBuiltinAttribute()))
  {
    return n.getAttribute(SygusToBuiltinAttribute());
  }
  Trace("sygus-db-debug") << "SygusToBuiltin : compute for " << n
                          << ", type = " << tn << std::endl;
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  if (!dt.isSygus())
  {
    return n;
  }
  if (n.getKind() == APPLY_CONSTRUCTOR)
  {
    unsigned i = datatypes::DatatypesRewriter::indexOf(n.getOperator());
    Assert(n.getNumChildren() == dt[i].getNumArgs());
    std::map<int, Node> pre;
    for (unsigned j = 0, size = n.getNumChildren(); j < size; j++)
    {
      pre[j] = sygusToBuiltin(n[j], TypeNode::fromType(dt[i].getArgType(j)));
    }
    Node ret = mkGeneric(dt, i, pre);
    Trace("sygus-db-debug")
        << "SygusToBuiltin : Generic is " << ret << std::endl;
    // cache
    n.setAttribute(SygusToBuiltinAttribute(), ret);
    return ret;
  }
  if (n.hasAttribute(SygusPrintProxyAttribute()))
  {
    // this variable was associated by an attribute to a builtin node
    return n.getAttribute(SygusPrintProxyAttribute());
  }
  Assert(isFreeVar(n));
  // map to builtin variable type
  int fv_num = getVarNum(n);
  Assert(!dt.getSygusType().isNull());
  TypeNode vtn = TypeNode::fromType(dt.getSygusType());
  Node ret = getFreeVar(vtn, fv_num);
  return ret;
}

Node TermDbSygus::sygusSubstituted( TypeNode tn, Node n, std::vector< Node >& args ) {
  Assert( d_var_list[tn].size()==args.size() );
  return n.substitute( d_var_list[tn].begin(), d_var_list[tn].end(), args.begin(), args.end() );
}

unsigned TermDbSygus::getSygusTermSize( Node n ){
  if (n.getKind() != APPLY_CONSTRUCTOR)
  {
    return 0;
  }
  unsigned sum = 0;
  for (unsigned i = 0; i < n.getNumChildren(); i++)
  {
    sum += getSygusTermSize(n[i]);
  }
  const Datatype& dt = Datatype::datatypeOf(n.getOperator().toExpr());
  int cindex = datatypes::DatatypesRewriter::indexOf(n.getOperator());
  Assert(cindex >= 0 && cindex < (int)dt.getNumConstructors());
  unsigned weight = dt[cindex].getWeight();
  return weight + sum;
}

class ReqTrie {
public:
  ReqTrie() : d_req_kind( UNDEFINED_KIND ){}
  std::map< unsigned, ReqTrie > d_children;
  Kind d_req_kind;
  TypeNode d_req_type;
  Node d_req_const;
  void print( const char * c, int indent = 0 ){
    if( d_req_kind!=UNDEFINED_KIND ){
      Trace(c) << d_req_kind << " ";
    }else if( !d_req_type.isNull() ){
      Trace(c) << d_req_type;
    }else if( !d_req_const.isNull() ){
      Trace(c) << d_req_const;
    }else{
      Trace(c) << "_";
    }
    Trace(c) << std::endl;
    for( std::map< unsigned, ReqTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
      for( int i=0; i<=indent; i++ ) { Trace(c) << "  "; }
      Trace(c) << it->first << " : ";
      it->second.print( c, indent+1 );
    }
  }
  bool satisfiedBy( quantifiers::TermDbSygus * tdb, TypeNode tn ){
    if( !d_req_const.isNull() ){
      if( !tdb->hasConst( tn, d_req_const ) ){
        return false;
      }
    }
    if( !d_req_type.isNull() ){
      Trace("sygus-sb-debug") << "- check if " << tn << " is type "
                              << d_req_type << std::endl;
      if( tn!=d_req_type ){
        return false;
      }
    }
    if( d_req_kind!=UNDEFINED_KIND ){
      Trace("sygus-sb-debug") << "- check if " << tn << " has " << d_req_kind
                              << std::endl;
      std::vector<TypeNode> argts;
      if (tdb->canConstructKind(tn, d_req_kind, argts))
      {
        bool ret = true;
        for( std::map< unsigned, ReqTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
          if (it->first < argts.size())
          {
            TypeNode tnc = argts[it->first];
            if( !it->second.satisfiedBy( tdb, tnc ) ){
              return false;
            }
          }else{
            return false;
          }
        }
        if( !ret ){
          return false;
        }
      }else{
        return false;
      }
    }
    return true;
  }
  bool empty()
  {
    return d_req_kind == UNDEFINED_KIND && d_req_const.isNull()
           && d_req_type.isNull() && d_children.empty();
  }
};

//this function gets all easy redundant cases, before consulting rewriters
bool TermDbSygus::considerArgKind( TypeNode tn, TypeNode tnp, Kind k, Kind pk, int arg ) {
  const Datatype& pdt = ((DatatypeType)(tnp).toType()).getDatatype();
  const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
  Assert( hasKind( tn, k ) );
  Assert( hasKind( tnp, pk ) );
  Trace("sygus-sb-debug") << "Consider sygus arg kind " << k << ", pk = " << pk
                          << ", arg = " << arg << " in " << tnp << "?"
                          << std::endl;
  int c = getKindConsNum( tn, k );
  int pc = getKindConsNum( tnp, pk );
    //check for associativity
  if (k == pk && quantifiers::TermUtil::isAssoc(k))
  {
    // if the operator is associative, then a repeated occurrence should only
    // occur in the leftmost argument position
    int firstArg = getFirstArgOccurrence(pdt[pc], tn);
    Assert(firstArg != -1);
    if (arg == firstArg)
    {
      return true;
    }
    // the argument types of the child must be the parent's type
    for (unsigned i = 0, nargs = dt[c].getNumArgs(); i < nargs; i++)
    {
      TypeNode tn = TypeNode::fromType(dt[c].getArgType(i));
      if (tn != tnp)
      {
        return true;
      }
    }
    Trace("sygus-sb-simple")
        << "  sb-simple : do not consider " << k << " at child arg " << arg
        << " of " << k
        << " since it is associative, with first arg = " << firstArg
        << std::endl;
    return false;
  }
  //describes the shape of an alternate term to construct
  //  we check whether this term is in the sygus grammar below
  ReqTrie rt;
  Assert( rt.empty() );
  
  //construct rt by cases
  if( pk==NOT || pk==BITVECTOR_NOT || pk==UMINUS || pk==BITVECTOR_NEG ){
    //negation normal form
    if( pk==k ){
      rt.d_req_type = getArgType( dt[c], 0 );
    }else{
      Kind reqk = UNDEFINED_KIND;       //required kind for all children
      std::map< unsigned, Kind > reqkc; //required kind for some children
      if( pk==NOT ){
        if( k==AND ) {
          rt.d_req_kind = OR;reqk = NOT;
        }else if( k==OR ){
          rt.d_req_kind = AND;reqk = NOT;
        //AJR : eliminate this if we eliminate xor
        }else if( k==EQUAL ) {
          rt.d_req_kind = XOR;
        }else if( k==XOR ) {
          rt.d_req_kind = EQUAL;
        }else if( k==ITE ){
          rt.d_req_kind = ITE;reqkc[1] = NOT;reqkc[2] = NOT;
          rt.d_children[0].d_req_type = getArgType( dt[c], 0 );
        }else if( k==LEQ || k==GT ){
          //  (not (~ x y)) ----->  (~ (+ y 1) x)
          rt.d_req_kind = k;
          rt.d_children[0].d_req_kind = PLUS;
          rt.d_children[0].d_children[0].d_req_type = getArgType( dt[c], 1 );
          rt.d_children[0].d_children[1].d_req_const = NodeManager::currentNM()->mkConst( Rational( 1 ) );
          rt.d_children[1].d_req_type = getArgType( dt[c], 0 );
          //TODO: other possibilities?
        }else if( k==LT || k==GEQ ){
          //  (not (~ x y)) ----->  (~ y (+ x 1))
          rt.d_req_kind = k;
          rt.d_children[0].d_req_type = getArgType( dt[c], 1 );
          rt.d_children[1].d_req_kind = PLUS;
          rt.d_children[1].d_children[0].d_req_type = getArgType( dt[c], 0 );
          rt.d_children[1].d_children[1].d_req_const = NodeManager::currentNM()->mkConst( Rational( 1 ) );
        }
      }else if( pk==BITVECTOR_NOT ){
        if( k==BITVECTOR_AND ) {
          rt.d_req_kind = BITVECTOR_OR;reqk = BITVECTOR_NOT;
        }else if( k==BITVECTOR_OR ){
          rt.d_req_kind = BITVECTOR_AND;reqk = BITVECTOR_NOT;
        }else if( k==BITVECTOR_XNOR ) {
          rt.d_req_kind = BITVECTOR_XOR;
        }else if( k==BITVECTOR_XOR ) {
          rt.d_req_kind = BITVECTOR_XNOR;
        }
      }else if( pk==UMINUS ){
        if( k==PLUS ){
          rt.d_req_kind = PLUS;reqk = UMINUS;
        }
      }else if( pk==BITVECTOR_NEG ){
        if( k==PLUS ){
          rt.d_req_kind = PLUS;reqk = BITVECTOR_NEG;
        }
      }
      if( !rt.empty() && ( reqk!=UNDEFINED_KIND || !reqkc.empty() ) ){
        int pcr = getKindConsNum( tnp, rt.d_req_kind );
        if( pcr!=-1 ){
          Assert( pcr<(int)pdt.getNumConstructors() );
          //must have same number of arguments
          if( pdt[pcr].getNumArgs()==dt[c].getNumArgs() ){
            for( unsigned i=0; i<pdt[pcr].getNumArgs(); i++ ){
              Kind rk = reqk;
              if( reqk==UNDEFINED_KIND ){
                std::map< unsigned, Kind >::iterator itr = reqkc.find( i );
                if( itr!=reqkc.end() ){
                  rk = itr->second;
                }
              }
              if( rk!=UNDEFINED_KIND ){
                rt.d_children[i].d_req_kind = rk;
                rt.d_children[i].d_children[0].d_req_type = getArgType( dt[c], i );
              }
            }
          }
        }
      }
    }
  }else if( k==MINUS || k==BITVECTOR_SUB ){
    if( pk==EQUAL || 
        pk==MINUS || pk==BITVECTOR_SUB || 
        pk==LEQ || pk==LT || pk==GEQ || pk==GT ){
      int oarg = arg==0 ? 1 : 0;
      //  (~ x (- y z))  ---->  (~ (+ x z) y)
      //  (~ (- y z) x)  ---->  (~ y (+ x z))
      rt.d_req_kind = pk;
      rt.d_children[arg].d_req_type = getArgType( dt[c], 0 );
      rt.d_children[oarg].d_req_kind = k==MINUS ? PLUS : BITVECTOR_PLUS;
      rt.d_children[oarg].d_children[0].d_req_type = getArgType( pdt[pc], oarg );
      rt.d_children[oarg].d_children[1].d_req_type = getArgType( dt[c], 1 );
    }else if( pk==PLUS || pk==BITVECTOR_PLUS ){
      //  (+ x (- y z))  -----> (- (+ x y) z)
      //  (+ (- y z) x)  -----> (- (+ x y) z)
      rt.d_req_kind = pk==PLUS ? MINUS : BITVECTOR_SUB;
      int oarg = arg==0 ? 1 : 0;
      rt.d_children[0].d_req_kind = pk;
      rt.d_children[0].d_children[0].d_req_type = getArgType( pdt[pc], oarg );
      rt.d_children[0].d_children[1].d_req_type = getArgType( dt[c], 0 );
      rt.d_children[1].d_req_type = getArgType( dt[c], 1 );
      // TODO : this is subsumbed by solving for MINUS
    }
  }else if( k==ITE ){
    if( pk!=ITE ){
      //  (o X (ite y z w) X')  -----> (ite y (o X z X') (o X w X'))
      rt.d_req_kind = ITE;
      rt.d_children[0].d_req_type = getArgType( dt[c], 0 );
      unsigned n_args = pdt[pc].getNumArgs();
      for( unsigned r=1; r<=2; r++ ){
        rt.d_children[r].d_req_kind = pk;
        for( unsigned q=0; q<n_args; q++ ){
          if( (int)q==arg ){
            rt.d_children[r].d_children[q].d_req_type = getArgType( dt[c], r );
          }else{
            rt.d_children[r].d_children[q].d_req_type = getArgType( pdt[pc], q );
          }
        }
      }
      //TODO: this increases term size but is probably a good idea
    }
  }else if( k==NOT ){
    if( pk==ITE ){
      //  (ite (not y) z w)  -----> (ite y w z)
      rt.d_req_kind = ITE;
      rt.d_children[0].d_req_type = getArgType( dt[c], 0 );
      rt.d_children[1].d_req_type = getArgType( pdt[pc], 2 );
      rt.d_children[2].d_req_type = getArgType( pdt[pc], 1 );
    }
  }
  Trace("sygus-sb-debug") << "Consider sygus arg kind " << k << ", pk = " << pk << ", arg = " << arg << "?" << std::endl;
  if( !rt.empty() ){
    rt.print("sygus-sb-debug");
    //check if it meets the requirements
    if( rt.satisfiedBy( this, tnp ) ){
      Trace("sygus-sb-debug") << "...success!" << std::endl;
      Trace("sygus-sb-simple") << "  sb-simple : do not consider " << k << " as arg " << arg << " of " << pk << std::endl;
      //do not need to consider the kind in the search since there are ways to construct equivalent terms
      return false;
    }else{
      Trace("sygus-sb-debug") << "...failed." << std::endl;
    }
    Trace("sygus-sb-debug") << std::endl;
  }
  //must consider this kind in the search  
  return true;
}

bool TermDbSygus::considerConst( TypeNode tn, TypeNode tnp, Node c, Kind pk, int arg ) {
  const Datatype& pdt = ((DatatypeType)(tnp).toType()).getDatatype();
  // child grammar-independent
  if( !considerConst( pdt, tnp, c, pk, arg ) ){
    return false;
  }
  // TODO : this can probably be made child grammar independent
  int pc = getKindConsNum( tnp, pk );
  if( pdt[pc].getNumArgs()==2 ){
    Kind ok;
    int offset;
    if (d_quantEngine->getTermUtil()->hasOffsetArg(pk, arg, offset, ok))
    {
      Trace("sygus-sb-simple-debug") << pk << " has offset arg " << ok << " " << offset << std::endl;
      int ok_arg = getKindConsNum( tnp, ok );
      if( ok_arg!=-1 ){
        Trace("sygus-sb-simple-debug") << "...at argument " << ok_arg << std::endl;
        //other operator be the same type
        if( isTypeMatch( pdt[ok_arg], pdt[arg] ) ){
          int status;
          Node co = d_quantEngine->getTermUtil()->getTypeValueOffset(
              c.getType(), c, offset, status);
          Trace("sygus-sb-simple-debug") << c << " with offset " << offset << " is " << co << ", status=" << status << std::endl;
          if( status==0 && !co.isNull() ){
            if( hasConst( tn, co ) ){
              Trace("sygus-sb-simple") << "  sb-simple : by offset reasoning, do not consider const " << c;
              Trace("sygus-sb-simple") << " as arg " << arg << " of " << pk << " since we can use " << co << " under " << ok << " " << std::endl;
              return false;
            }
          }
        }
      }
    }
  }
  return true;
}

bool TermDbSygus::considerConst( const Datatype& pdt, TypeNode tnp, Node c, Kind pk, int arg ) {
  Assert( hasKind( tnp, pk ) );
  int pc = getKindConsNum( tnp, pk );
  bool ret = true;
  Trace("sygus-sb-debug") << "Consider sygus const " << c << ", parent = " << pk << ", arg = " << arg << "?" << std::endl;
  if (d_quantEngine->getTermUtil()->isIdempotentArg(c, pk, arg))
  {
    if( pdt[pc].getNumArgs()==2 ){
      int oarg = arg==0 ? 1 : 0;
      TypeNode otn = TypeNode::fromType( ((SelectorType)pdt[pc][oarg].getType()).getRangeType() );
      if( otn==tnp ){
        Trace("sygus-sb-simple") << "  sb-simple : " << c << " is idempotent arg " << arg << " of " << pk << "..." << std::endl;
        ret = false;
      }
    }
  }else{
    Node sc = d_quantEngine->getTermUtil()->isSingularArg(c, pk, arg);
    if( !sc.isNull() ){
      if( hasConst( tnp, sc ) ){
        Trace("sygus-sb-simple") << "  sb-simple : " << c << " is singular arg " << arg << " of " << pk << ", evaluating to " << sc << "..." << std::endl;
        ret = false;
      }
    }
  }
  if( ret ){
    ReqTrie rt;
    Assert( rt.empty() );
    Node max_c = d_quantEngine->getTermUtil()->getTypeMaxValue(c.getType());
    Node zero_c = d_quantEngine->getTermUtil()->getTypeValue(c.getType(), 0);
    Node one_c = d_quantEngine->getTermUtil()->getTypeValue(c.getType(), 1);
    if( pk==XOR || pk==BITVECTOR_XOR ){
      if( c==max_c ){
        rt.d_req_kind = pk==XOR ? NOT : BITVECTOR_NOT;
      }
    }else if( pk==ITE ){
      if( arg==0 ){
        if( c==max_c ){
          rt.d_children[1].d_req_type = tnp;
        }
        else if (c == zero_c)
        {
          rt.d_children[2].d_req_type = tnp;
        }
      }
    }else if( pk==STRING_SUBSTR ){
      if (c == one_c && arg == 2)
      {
        rt.d_req_kind = STRING_CHARAT;
        rt.d_children[0].d_req_type = getArgType( pdt[pc], 0 );
        rt.d_children[1].d_req_type = getArgType( pdt[pc], 1 );
      }
    }
    if( !rt.empty() ){
      //check if satisfied
      if( rt.satisfiedBy( this, tnp ) ){
        Trace("sygus-sb-simple") << "  sb-simple : do not consider const " << c << " as arg " << arg << " of " << pk;
        Trace("sygus-sb-simple") << " in " << ((DatatypeType)tnp.toType()).getDatatype().getName() << std::endl;
        //do not need to consider the constant in the search since there are ways to construct equivalent terms
        ret = false;
      }
    }
  }
  // TODO : cache?
  return ret;
}

int TermDbSygus::solveForArgument( TypeNode tn, unsigned cindex, unsigned arg ) {
  // FIXME
  return -1;  // TODO : if using, modify considerArgKind above
  Assert( isRegistered( tn ) );
  const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
  Assert( cindex<dt.getNumConstructors() );
  Assert( arg<dt[cindex].getNumArgs() );
  Kind nk = getConsNumKind( tn, cindex );
  TypeNode tnc = getArgType( dt[cindex], arg );
  const Datatype& cdt = ((DatatypeType)(tnc).toType()).getDatatype();

  ReqTrie rt;
  Assert( rt.empty() );
  int solve_ret = -1;
  if( nk==MINUS || nk==BITVECTOR_SUB ){
    if( dt[cindex].getNumArgs()==2 && arg==0 ){
      TypeNode tnco = getArgType( dt[cindex], 1 );
      Node builtin = d_quantEngine->getTermUtil()->getTypeValue(
          sygusToBuiltinType(tnc), 0);
      solve_ret = getConstConsNum( tn, builtin );
      if( solve_ret!=-1 ){
        // t - s    ----->  ( 0 - s ) + t
        rt.d_req_kind = nk == MINUS ? PLUS : BITVECTOR_PLUS;
        rt.d_children[0].d_req_type = tn; // avoid?
        rt.d_children[0].d_req_kind = nk;
        rt.d_children[0].d_children[0].d_req_const = builtin;
        rt.d_children[0].d_children[0].d_req_type = tnco;
        rt.d_children[1].d_req_type = tnc;
        // TODO : this can be made more general for multiple type grammars to remove MINUS entirely 
      }
    }
  }
  
  if( !rt.empty() ){
    Assert( solve_ret>=0 );
    Assert( solve_ret<=(int)cdt.getNumConstructors() );
    //check if satisfied
    if( rt.satisfiedBy( this, tn ) ){
      Trace("sygus-sb-simple") << "  sb-simple : ONLY consider " << cdt[solve_ret].getSygusOp() << " as arg " << arg << " of " << nk;
      Trace("sygus-sb-simple") << " in " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
      return solve_ret;
    }
  }
  
  return -1;
}

void TermDbSygus::registerSygusType( TypeNode tn ) {
  std::map< TypeNode, TypeNode >::iterator itr = d_register.find( tn );
  if( itr==d_register.end() ){
    d_register[tn] = TypeNode::null();
    if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      Trace("sygus-db") << "Register type " << dt.getName() << "..." << std::endl;
      TypeNode btn = TypeNode::fromType( dt.getSygusType() );
      d_register[tn] = btn;
      if( !d_register[tn].isNull() ){
        // get the sygus variable list
        Node var_list = Node::fromExpr( dt.getSygusVarList() );
        if( !var_list.isNull() ){
          for( unsigned j=0; j<var_list.getNumChildren(); j++ ){
            Node sv = var_list[j];
            SygusVarNumAttribute svna;
            sv.setAttribute( svna, j );
            d_var_list[tn].push_back( sv );
          }
        }else{
          // no arguments to synthesis functions
        }
        // register connected types
        for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
        {
          for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
          {
            TypeNode ctn = TypeNode::fromType(dt[i].getArgType(j));
            registerSygusType(ctn);
            // carry type attributes
            if (d_has_subterm_sym_cons.find(ctn)
                != d_has_subterm_sym_cons.end())
            {
              d_has_subterm_sym_cons[tn] = true;
            }
          }
        }
        //iterate over constructors
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          Expr sop = dt[i].getSygusOp();
          Assert( !sop.isNull() );
          Node n = Node::fromExpr( sop );
          Trace("sygus-db") << "  Operator #" << i << " : " << sop;
          if( sop.getKind() == kind::BUILTIN ){
            Kind sk = NodeManager::operatorToKind( n );
            Trace("sygus-db") << ", kind = " << sk;
            d_kinds[tn][sk] = i;
            d_arg_kind[tn][i] = sk;
          }else if( sop.isConst() ){
            Trace("sygus-db") << ", constant";
            d_consts[tn][n] = i;
            d_arg_const[tn][i] = n;
          }
          else if (sop.getKind() == LAMBDA)
          {
            // do type checking
            Assert(sop[0].getNumChildren() == dt[i].getNumArgs());
            for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
            {
              TypeNode ct = TypeNode::fromType(dt[i].getArgType(j));
              TypeNode cbt = sygusToBuiltinType(ct);
              TypeNode lat = TypeNode::fromType(sop[0][j].getType());
              CVC4_CHECK(cbt.isSubtypeOf(lat))
                  << "In sygus datatype " << dt.getName()
                  << ", argument to a lambda constructor is not " << lat
                  << std::endl;
            }
          }
          // symbolic constructors
          if (n.getAttribute(SygusAnyConstAttribute()))
          {
            d_sym_cons_any_constant[tn] = i;
            d_has_subterm_sym_cons[tn] = true;
          }
          // TODO (as part of #1170): we still do not properly catch type
          // errors in sygus grammars for arguments of builtin operators.
          // The challenge is that we easily ask for expected argument types of
          // builtin operators e.g. PLUS. Hence the call to mkGeneric below
          // will throw a type exception.
          d_ops[tn][n] = i;
          d_arg_ops[tn][i] = n;
          Trace("sygus-db") << std::endl;
          // ensure that terms that this constructor encodes are
          // of the type specified in the datatype. This will fail if
          // e.g. bitvector-and is a constructor of an integer grammar.
          Node g = mkGeneric(dt, i);
          TypeNode gtn = g.getType();
          CVC4_CHECK(gtn.isSubtypeOf(btn))
              << "Sygus datatype " << dt.getName()
              << " encodes terms that are not of type " << btn << std::endl;
          Trace("sygus-db") << "...done register Operator #" << i << std::endl;
        }
        // compute min type depth information
        computeMinTypeDepthInternal(tn, tn, 0);
      }
    }
  }
}

void TermDbSygus::registerEnumerator(Node e,
                                     Node f,
                                     CegConjecture* conj,
                                     bool mkActiveGuard,
                                     bool useSymbolicCons)
{
  if (d_enum_to_conjecture.find(e) != d_enum_to_conjecture.end())
  {
    // already registered
    return;
  }
  Trace("sygus-db") << "Register enumerator : " << e << std::endl;
  // register its type
  TypeNode et = e.getType();
  registerSygusType(et);
  d_enum_to_conjecture[e] = conj;
  d_enum_to_synth_fun[e] = f;
  NodeManager* nm = NodeManager::currentNM();
  if( mkActiveGuard ){
    // make the guard
    Node eg = Rewriter::rewrite(nm->mkSkolem("eG", nm->booleanType()));
    eg = d_quantEngine->getValuation().ensureLiteral( eg );
    AlwaysAssert( !eg.isNull() );
    d_quantEngine->getOutputChannel().requirePhase( eg, true );
    //add immediate lemma
    Node lem = nm->mkNode(OR, eg, eg.negate());
    Trace("cegqi-lemma") << "Cegqi::Lemma : enumerator : " << lem << std::endl;
    d_quantEngine->getOutputChannel().lemma( lem );
    d_enum_to_active_guard[e] = eg;
  }

  Trace("sygus-db") << "  registering symmetry breaking clauses..."
                    << std::endl;
  d_enum_to_using_sym_cons[e] = useSymbolicCons;
  // depending on if we are using symbolic constructors, introduce symmetry
  // breaking lemma templates for each relevant subtype of the grammar
  std::vector<TypeNode> sf_types;
  getSubfieldTypes(et, sf_types);
  // for each type of subfield type of this enumerator
  for (unsigned i = 0, ntypes = sf_types.size(); i < ntypes; i++)
  {
    std::vector<unsigned> rm_indices;
    TypeNode stn = sf_types[i];
    Assert(stn.isDatatype());
    const Datatype& dt = static_cast<DatatypeType>(stn.toType()).getDatatype();
    std::map<TypeNode, unsigned>::iterator itsa =
        d_sym_cons_any_constant.find(stn);
    if (itsa != d_sym_cons_any_constant.end())
    {
      if (!useSymbolicCons)
      {
        // do not use the symbolic constructor
        rm_indices.push_back(itsa->second);
      }
      else
      {
        // can remove all other concrete constant constructors
        for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
        {
          if (i != itsa->second)
          {
            Node c_op = getConsNumConst(stn, i);
            if (!c_op.isNull())
            {
              rm_indices.push_back(i);
            }
          }
        }
      }
    }
    for (unsigned& rindex : rm_indices)
    {
      // make the apply-constructor corresponding to an application of the
      // constant or "any constant" constructor
      // we call getInstCons since in the case of any constant constructors, it
      // is necessary to generate a term of the form any_constant( x.0 ) for a
      // fresh variable x.0.
      Node fv = getFreeVar(stn, 0);
      Node exc_val = datatypes::DatatypesRewriter::getInstCons(fv, dt, rindex);
      // should not include the constuctor in any subterm
      Node x = getFreeVar(stn, 0);
      Trace("sygus-db") << "Construct symmetry breaking lemma from " << x
                        << " == " << exc_val << std::endl;
      Node lem = getExplain()->getExplanationForEquality(x, exc_val);
      lem = lem.negate();
      Trace("cegqi-lemma")
          << "Cegqi::Lemma : exclude symbolic cons lemma (template) : " << lem
          << std::endl;
      // the size of the subterm we are blocking is the weight of the
      // constructor (usually zero)
      registerSymBreakLemma(e, lem, stn, dt[rindex].getWeight());
    }
  }
  Trace("sygus-db") << "  ...finished" << std::endl;
}

bool TermDbSygus::isEnumerator(Node e) const
{
  return d_enum_to_conjecture.find(e) != d_enum_to_conjecture.end();
}

CegConjecture* TermDbSygus::getConjectureForEnumerator(Node e) const
{
  std::map<Node, CegConjecture*>::const_iterator itm =
      d_enum_to_conjecture.find(e);
  if (itm != d_enum_to_conjecture.end()) {
    return itm->second;
  }
  return nullptr;
}

Node TermDbSygus::getSynthFunForEnumerator(Node e) const
{
  std::map<Node, Node>::const_iterator itsf = d_enum_to_synth_fun.find(e);
  if (itsf != d_enum_to_synth_fun.end())
  {
    return itsf->second;
  }
  return Node::null();
}

Node TermDbSygus::getActiveGuardForEnumerator(Node e) const
{
  std::map<Node, Node>::const_iterator itag = d_enum_to_active_guard.find(e);
  if (itag != d_enum_to_active_guard.end()) {
    return itag->second;
  }
  return Node::null();
}

bool TermDbSygus::usingSymbolicConsForEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_to_using_sym_cons.find(e);
  if (itus != d_enum_to_using_sym_cons.end())
  {
    return itus->second;
  }
  return false;
}

void TermDbSygus::getEnumerators(std::vector<Node>& mts)
{
  for (std::map<Node, CegConjecture*>::iterator itm =
           d_enum_to_conjecture.begin();
       itm != d_enum_to_conjecture.end(); ++itm) {
    mts.push_back( itm->first );
  }
}

void TermDbSygus::registerSymBreakLemma(Node e,
                                        Node lem,
                                        TypeNode tn,
                                        unsigned sz)
{
  d_enum_to_sb_lemmas[e].push_back(lem);
  d_sb_lemma_to_type[lem] = tn;
  d_sb_lemma_to_size[lem] = sz;
}

bool TermDbSygus::hasSymBreakLemmas(std::vector<Node>& enums) const
{
  if (!d_enum_to_sb_lemmas.empty())
  {
    for (std::pair<const Node, std::vector<Node> > sb : d_enum_to_sb_lemmas)
    {
      enums.push_back(sb.first);
    }
    return true;
  }
  return false;
}

void TermDbSygus::getSymBreakLemmas(Node e, std::vector<Node>& lemmas) const
{
  std::map<Node, std::vector<Node> >::const_iterator itsb =
      d_enum_to_sb_lemmas.find(e);
  if (itsb != d_enum_to_sb_lemmas.end())
  {
    lemmas.insert(lemmas.end(), itsb->second.begin(), itsb->second.end());
  }
}

TypeNode TermDbSygus::getTypeForSymBreakLemma(Node lem) const
{
  std::map<Node, TypeNode>::const_iterator it = d_sb_lemma_to_type.find(lem);
  Assert(it != d_sb_lemma_to_type.end());
  return it->second;
}
unsigned TermDbSygus::getSizeForSymBreakLemma(Node lem) const
{
  std::map<Node, unsigned>::const_iterator it = d_sb_lemma_to_size.find(lem);
  Assert(it != d_sb_lemma_to_size.end());
  return it->second;
}

void TermDbSygus::clearSymBreakLemmas(Node e) { d_enum_to_sb_lemmas.erase(e); }

bool TermDbSygus::isRegistered(TypeNode tn) const
{
  return d_register.find( tn )!=d_register.end();
}

TypeNode TermDbSygus::sygusToBuiltinType( TypeNode tn ) {
  Assert( isRegistered( tn ) );
  return d_register[tn];
}

void TermDbSygus::toStreamSygus(const char* c, Node n)
{
  if (Trace.isOn(c))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, n);
    Trace(c) << ss.str();
  }
}

void TermDbSygus::computeMinTypeDepthInternal( TypeNode root_tn, TypeNode tn, unsigned type_depth ) {
  std::map< TypeNode, unsigned >::iterator it = d_min_type_depth[root_tn].find( tn );
  if( it==d_min_type_depth[root_tn].end() || type_depth<it->second ){
    if (!tn.isDatatype())
    {
      // do not recurse to non-datatype types
      return;
    }
    d_min_type_depth[root_tn][tn] = type_depth;
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    //compute for connected types
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      for( unsigned j=0; j<dt[i].getNumArgs(); j++ ){
        computeMinTypeDepthInternal( root_tn, getArgType( dt[i], j ), type_depth+1 );
      }
    }
  }
}
  
unsigned TermDbSygus::getMinTypeDepth( TypeNode root_tn, TypeNode tn ){
  std::map< TypeNode, unsigned >::iterator it = d_min_type_depth[root_tn].find( tn );
  if( it==d_min_type_depth[root_tn].end() ){
    Assert( d_min_type_depth[root_tn].find( tn )!=d_min_type_depth[root_tn].end() );  
    return d_min_type_depth[root_tn][tn];
  }else{
    return it->second;
  }
}

unsigned TermDbSygus::getMinTermSize( TypeNode tn ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, unsigned >::iterator it = d_min_term_size.find( tn );
  if( it==d_min_term_size.end() ){
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      if (dt[i].getNumArgs() == 0)
      {
        d_min_term_size[tn] = 0;
        return 0;
      }
    }
    // TODO : improve
    d_min_term_size[tn] = 1;
    return 1;
  }else{
    return it->second;
  }
}

unsigned TermDbSygus::getMinConsTermSize( TypeNode tn, unsigned cindex ) {
  Assert( isRegistered( tn ) );
  std::map< unsigned, unsigned >::iterator it = d_min_cons_term_size[tn].find( cindex );
  if( it==d_min_cons_term_size[tn].end() ){
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    Assert( cindex<dt.getNumConstructors() );
    unsigned ret = 0;
    if( dt[cindex].getNumArgs()>0 ){
      ret = 1;
      for( unsigned i=0; i<dt[cindex].getNumArgs(); i++ ){
        ret += getMinTermSize( getArgType( dt[cindex], i ) );
      }
    }
    d_min_cons_term_size[tn][cindex] = ret;
    return ret;
  }else{
    return it->second;
  }
}

unsigned TermDbSygus::getSelectorWeight(TypeNode tn, Node sel)
{
  std::map<TypeNode, std::map<Node, unsigned> >::iterator itsw =
      d_sel_weight.find(tn);
  if (itsw == d_sel_weight.end())
  {
    d_sel_weight[tn].clear();
    itsw = d_sel_weight.find(tn);
    Type t = tn.toType();
    const Datatype& dt = static_cast<DatatypeType>(t).getDatatype();
    Trace("sygus-db") << "Compute selector weights for " << dt.getName()
                      << std::endl;
    for (unsigned i = 0, size = dt.getNumConstructors(); i < size; i++)
    {
      unsigned cw = dt[i].getWeight();
      for (unsigned j = 0, size2 = dt[i].getNumArgs(); j < size2; j++)
      {
        Node csel = Node::fromExpr(dt[i].getSelectorInternal(t, j));
        std::map<Node, unsigned>::iterator its = itsw->second.find(csel);
        if (its == itsw->second.end() || cw < its->second)
        {
          d_sel_weight[tn][csel] = cw;
          Trace("sygus-db") << "  w(" << csel << ") <= " << cw << std::endl;
        }
      }
    }
  }
  Assert(itsw->second.find(sel) != itsw->second.end());
  return itsw->second[sel];
}

void TermDbSygus::getSubfieldTypes(TypeNode tn, std::vector<TypeNode>& sf_types)
{
  std::map<TypeNode, std::map<TypeNode, unsigned> >::iterator it =
      d_min_type_depth.find(tn);
  Assert(it != d_min_type_depth.end());
  for (const std::pair<const TypeNode, unsigned>& st : it->second)
  {
    sf_types.push_back(st.first);
  }
}

int TermDbSygus::getKindConsNum( TypeNode tn, Kind k ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< Kind, int > >::iterator itt = d_kinds.find( tn );
  if( itt!=d_kinds.end() ){
    std::map< Kind, int >::iterator it = itt->second.find( k );
    if( it!=itt->second.end() ){
      return it->second;
    }
  }
  return -1;
}

int TermDbSygus::getConstConsNum( TypeNode tn, Node n ){
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< Node, int > >::iterator itt = d_consts.find( tn );
  if( itt!=d_consts.end() ){
    std::map< Node, int >::iterator it = itt->second.find( n );
    if( it!=itt->second.end() ){
      return it->second;
    }
  }
  return -1;
}

int TermDbSygus::getOpConsNum( TypeNode tn, Node n ) {
  std::map< Node, int >::iterator it = d_ops[tn].find( n );
  if( it!=d_ops[tn].end() ){
    return it->second;
  }else{
    return -1;
  }
}

bool TermDbSygus::hasKind( TypeNode tn, Kind k ) {
  return getKindConsNum( tn, k )!=-1;
}
bool TermDbSygus::hasConst( TypeNode tn, Node n ) {
  return getConstConsNum( tn, n )!=-1;
}
bool TermDbSygus::hasOp( TypeNode tn, Node n ) {
  return getOpConsNum( tn, n )!=-1;
}

Node TermDbSygus::getConsNumOp( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Node > >::iterator itt = d_arg_ops.find( tn );
  if( itt!=d_arg_ops.end() ){
    std::map< int, Node >::iterator itn = itt->second.find( i );
    if( itn!=itt->second.end() ){
      return itn->second;
    }
  }
  return Node::null();
}

Node TermDbSygus::getConsNumConst( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Node > >::iterator itt = d_arg_const.find( tn );
  if( itt!=d_arg_const.end() ){
    std::map< int, Node >::iterator itn = itt->second.find( i );
    if( itn!=itt->second.end() ){
      return itn->second;
    }
  }
  return Node::null();
}

Kind TermDbSygus::getConsNumKind( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Kind > >::iterator itt = d_arg_kind.find( tn );
  if( itt!=d_arg_kind.end() ){
    std::map< int, Kind >::iterator itk = itt->second.find( i );
    if( itk!=itt->second.end() ){
      return itk->second;
    }
  }
  return UNDEFINED_KIND;
}

bool TermDbSygus::isKindArg( TypeNode tn, int i ) {
  return getConsNumKind( tn, i )!=UNDEFINED_KIND;
}

bool TermDbSygus::isConstArg( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Node > >::iterator itt = d_arg_const.find( tn );
  if( itt!=d_arg_const.end() ){
    return itt->second.find( i )!=itt->second.end();
  }else{
    return false;
  }
}

TypeNode TermDbSygus::getArgType(const DatatypeConstructor& c, unsigned i) const
{
  Assert(i < c.getNumArgs());
  return TypeNode::fromType(
      static_cast<SelectorType>(c[i].getType()).getRangeType());
}

/** get first occurrence */
int TermDbSygus::getFirstArgOccurrence( const DatatypeConstructor& c, TypeNode tn ) {
  for( unsigned i=0; i<c.getNumArgs(); i++ ){
    TypeNode tni = getArgType( c, i );
    if( tni==tn ){
      return i;
    }
  }
  return -1;
}

bool TermDbSygus::isTypeMatch( const DatatypeConstructor& c1, const DatatypeConstructor& c2 ) {
  if( c1.getNumArgs()!=c2.getNumArgs() ){
    return false;
  }else{
    for( unsigned i=0; i<c1.getNumArgs(); i++ ){
      if( getArgType( c1, i )!=getArgType( c2, i ) ){
        return false;
      }
    }
    return true;
  }
}

int TermDbSygus::getAnyConstantConsNum(TypeNode tn) const
{
  Assert(isRegistered(tn));
  std::map<TypeNode, unsigned>::const_iterator itt =
      d_sym_cons_any_constant.find(tn);
  if (itt != d_sym_cons_any_constant.end())
  {
    return static_cast<int>(itt->second);
  }
  return -1;
}

bool TermDbSygus::hasSubtermSymbolicCons(TypeNode tn) const
{
  return d_has_subterm_sym_cons.find(tn) != d_has_subterm_sym_cons.end();
}

bool TermDbSygus::isSymbolicConsApp(Node n) const
{
  if (n.getKind() != APPLY_CONSTRUCTOR)
  {
    return false;
  }
  TypeNode tn = n.getType();
  Assert(tn.isDatatype());
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  Assert(dt.isSygus());
  unsigned cindex = datatypes::DatatypesRewriter::indexOf(n.getOperator());
  Node sygusOp = Node::fromExpr(dt[cindex].getSygusOp());
  // it is symbolic if it represents "any constant"
  return sygusOp.getAttribute(SygusAnyConstAttribute());
}

bool TermDbSygus::canConstructKind(TypeNode tn,
                                   Kind k,
                                   std::vector<TypeNode>& argts,
                                   bool aggr)
{
  int c = getKindConsNum(tn, k);
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  if (c != -1)
  {
    for (unsigned i = 0, nargs = dt[c].getNumArgs(); i < nargs; i++)
    {
      argts.push_back(TypeNode::fromType(dt[c].getArgType(i)));
    }
    return true;
  }
  if (!options::sygusSymBreakAgg())
  {
    return false;
  }
  if (sygusToBuiltinType(tn).isBoolean())
  {
    if (k == ITE)
    {
      // ite( b1, b2, b3 ) <---- and( or( ~b1, b2 ), or( b1, b3 ) )
      std::vector<TypeNode> conj_types;
      if (canConstructKind(tn, AND, conj_types, true) && conj_types.size() == 2)
      {
        bool success = true;
        std::vector<TypeNode> disj_types[2];
        for (unsigned c = 0; c < 2; c++)
        {
          if (!canConstructKind(conj_types[c], OR, disj_types[c], true)
              || disj_types[c].size() != 2)
          {
            success = false;
            break;
          }
        }
        if (success)
        {
          for (unsigned r = 0; r < 2; r++)
          {
            for (unsigned d = 0, size = disj_types[r].size(); d < size; d++)
            {
              TypeNode dtn = disj_types[r][d];
              // must have negation that occurs in the other conjunct
              std::vector<TypeNode> ntypes;
              if (canConstructKind(dtn, NOT, ntypes) && ntypes.size() == 1)
              {
                TypeNode ntn = ntypes[0];
                for (unsigned dd = 0, size = disj_types[1 - r].size();
                     dd < size;
                     dd++)
                {
                  if (disj_types[1 - r][dd] == ntn)
                  {
                    argts.push_back(ntn);
                    argts.push_back(disj_types[r][d]);
                    argts.push_back(disj_types[1 - r][1 - dd]);
                    if (Trace.isOn("sygus-cons-kind"))
                    {
                      Trace("sygus-cons-kind")
                          << "Can construct kind " << k << " in " << tn
                          << " via child types:" << std::endl;
                      for (unsigned i = 0; i < 3; i++)
                      {
                        Trace("sygus-cons-kind")
                            << "  " << argts[i] << std::endl;
                      }
                    }
                    return true;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  // could try aggressive inferences here, such as
  // (and b1 b2) <---- (not (or (not b1) (not b2)))
  // (or b1 b2)  <---- (not (and (not b1) (not b2)))
  return false;
}

Node TermDbSygus::minimizeBuiltinTerm( Node n ) {
  if( ( n.getKind()==EQUAL || n.getKind()==LEQ || n.getKind()==LT || n.getKind()==GEQ || n.getKind()==GT ) &&
      ( n[0].getType().isInteger() || n[0].getType().isReal() ) ){
    bool changed = false;
    std::vector< Node > mon[2];
    for( unsigned r=0; r<2; r++ ){
      unsigned ro = r==0 ? 1 : 0;
      Node c;
      Node nc;
      if( n[r].getKind()==PLUS ){
        for( unsigned i=0; i<n[r].getNumChildren(); i++ ){
          if (ArithMSum::getMonomial(n[r][i], c, nc)
              && c.getConst<Rational>().isNegativeOne())
          {
            mon[ro].push_back( nc );
            changed = true;
          }else{
            if( !n[r][i].isConst() || !n[r][i].getConst<Rational>().isZero() ){
              mon[r].push_back( n[r][i] );
            }
          }
        }
      }else{
        if (ArithMSum::getMonomial(n[r], c, nc)
            && c.getConst<Rational>().isNegativeOne())
        {
          mon[ro].push_back( nc );
          changed = true;
        }else{
          if( !n[r].isConst() || !n[r].getConst<Rational>().isZero() ){
            mon[r].push_back( n[r] );
          }
        }
      }
    }
    if( changed ){
      Node nn[2];
      for( unsigned r=0; r<2; r++ ){
        nn[r] = mon[r].size()==0 ? NodeManager::currentNM()->mkConst( Rational(0) ) : ( mon[r].size()==1 ? mon[r][0] : NodeManager::currentNM()->mkNode( PLUS, mon[r] ) );
      }
      return NodeManager::currentNM()->mkNode( n.getKind(), nn[0], nn[1] );
    }
  }
  return n;
}

Node TermDbSygus::expandBuiltinTerm( Node t ){
  if( t.getKind()==EQUAL ){
    if( t[0].getType().isReal() ){
      return NodeManager::currentNM()->mkNode( AND, NodeManager::currentNM()->mkNode( LEQ, t[0], t[1] ),
                                                    NodeManager::currentNM()->mkNode( LEQ, t[1], t[0] ) );
    }else if( t[0].getType().isBoolean() ){
      return NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, t[0], t[1] ),
                                                   NodeManager::currentNM()->mkNode( AND, t[0].negate(), t[1].negate() ) );
    }
  }else if( t.getKind()==ITE && t.getType().isBoolean() ){
    return NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, t[0], t[1] ),
                                                 NodeManager::currentNM()->mkNode( AND, t[0].negate(), t[2] ) );
  }
  return Node::null();
}


Kind TermDbSygus::getComparisonKind( TypeNode tn ) {
  if( tn.isInteger() || tn.isReal() ){
    return LT;
  }else if( tn.isBitVector() ){
    return BITVECTOR_ULT;
  }else{
    return UNDEFINED_KIND;
  }
}

Kind TermDbSygus::getPlusKind( TypeNode tn, bool is_neg ) {
  if( tn.isInteger() || tn.isReal() ){
    return is_neg ? MINUS : PLUS;
  }else if( tn.isBitVector() ){
    return is_neg ? BITVECTOR_SUB : BITVECTOR_PLUS;
  }else{
    return UNDEFINED_KIND;
  }
}

Node TermDbSygus::getSemanticSkolem( TypeNode tn, Node n, bool doMk ){
  std::map< Node, Node >::iterator its = d_semantic_skolem[tn].find( n );
  if( its!=d_semantic_skolem[tn].end() ){
    return its->second;
  }else if( doMk ){
    Node ss = NodeManager::currentNM()->mkSkolem( "sem", tn, "semantic skolem for sygus" );
    d_semantic_skolem[tn][n] = ss;
    return ss;
  }else{
    return Node::null();
  }
}

bool TermDbSygus::involvesDivByZero( Node n, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    Kind k = n.getKind();
    if( k==DIVISION || k==DIVISION_TOTAL || k==INTS_DIVISION || k==INTS_DIVISION_TOTAL || 
        k==INTS_MODULUS || k==INTS_MODULUS_TOTAL ){
      if( n[1].isConst() ){
        if (n[1]
            == d_quantEngine->getTermUtil()->getTypeValue(n[1].getType(), 0))
        {
          return true;
        }
      }else{
        // if it has free variables it might be a non-zero constant
        if( !hasFreeVar( n[1] ) ){
          return true;
        }
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( involvesDivByZero( n[i], visited ) ){
        return true;
      }
    }
  }
  return false;
}

bool TermDbSygus::involvesDivByZero( Node n ) {
  std::map< Node, bool > visited;
  return involvesDivByZero( n, visited );
}

void doStrReplace(std::string& str, const std::string& oldStr, const std::string& newStr){
  size_t pos = 0;
  while((pos = str.find(oldStr, pos)) != std::string::npos){
     str.replace(pos, oldStr.length(), newStr);
     pos += newStr.length();
  }
}

Node TermDbSygus::getAnchor( Node n ) {
  if( n.getKind()==APPLY_SELECTOR_TOTAL ){
    return getAnchor( n[0] );
  }else{
    return n;
  }
}

unsigned TermDbSygus::getAnchorDepth( Node n ) {
  if( n.getKind()==APPLY_SELECTOR_TOTAL ){
    return 1+getAnchorDepth( n[0] );
  }else{
    return 0;
  }
}

Node TermDbSygus::unfold( Node en, std::map< Node, Node >& vtm, std::vector< Node >& exp, bool track_exp ) {
  if (!datatypes::DatatypesRewriter::isSygusEvalApp(en))
  {
    Assert(en.isConst());
    return en;
  }
  Trace("sygus-db-debug") << "Unfold : " << en << std::endl;
  Node ev = en[0];
  if (track_exp)
  {
    std::map<Node, Node>::iterator itv = vtm.find(en[0]);
    Assert(itv != vtm.end());
    if (itv != vtm.end())
    {
      ev = itv->second;
    }
    Assert(en[0].getType() == ev.getType());
    Assert(ev.isConst());
  }
  Assert(ev.getKind() == kind::APPLY_CONSTRUCTOR);
  std::vector<Node> args;
  for (unsigned i = 1, nchild = en.getNumChildren(); i < nchild; i++)
  {
    args.push_back(en[i]);
  }

  Type headType = en[0].getType().toType();
  NodeManager* nm = NodeManager::currentNM();
  const Datatype& dt = static_cast<DatatypeType>(headType).getDatatype();
  unsigned i = datatypes::DatatypesRewriter::indexOf(ev.getOperator());
  if (track_exp)
  {
    // explanation
    Node ee = nm->mkNode(
        kind::APPLY_TESTER, Node::fromExpr(dt[i].getTester()), en[0]);
    if (std::find(exp.begin(), exp.end(), ee) == exp.end())
    {
      exp.push_back(ee);
    }
  }
  // if we are a symbolic constructor, unfolding returns the subterm itself
  Node sop = Node::fromExpr(dt[i].getSygusOp());
  if (sop.getAttribute(SygusAnyConstAttribute()))
  {
    Trace("sygus-db-debug") << "...it is an any-constant constructor"
                            << std::endl;
    Assert(dt[i].getNumArgs() == 1);
    if (en[0].getKind() == APPLY_CONSTRUCTOR)
    {
      return en[0][0];
    }
    else
    {
      return nm->mkNode(
          APPLY_SELECTOR_TOTAL, dt[i].getSelectorInternal(headType, 0), en[0]);
    }
  }

  Assert(!dt.isParametric());
  std::map<int, Node> pre;
  for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
  {
    std::vector<Node> cc;
    Node s;
    // get the j^th subfield of en
    if (en[0].getKind() == kind::APPLY_CONSTRUCTOR)
    {
      // if it is a concrete constructor application, as an optimization,
      // just return the argument
      s = en[0][j];
    }
    else
    {
      s = nm->mkNode(kind::APPLY_SELECTOR_TOTAL,
                     dt[i].getSelectorInternal(headType, j),
                     en[0]);
    }
    cc.push_back(s);
    if (track_exp)
    {
      // update vtm map
      vtm[s] = ev[j];
    }
    cc.insert(cc.end(), args.begin(), args.end());
    pre[j] = datatypes::DatatypesRewriter::mkSygusEvalApp(cc);
  }
  Node ret = mkGeneric(dt, i, pre);
  // if it is a variable, apply the substitution
  if (ret.getKind() == kind::BOUND_VARIABLE)
  {
    Assert(ret.hasAttribute(SygusVarNumAttribute()));
    int i = ret.getAttribute(SygusVarNumAttribute());
    Assert(Node::fromExpr(dt.getSygusVarList())[i] == ret);
    return args[i];
  }
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node TermDbSygus::unfold(Node en)
{
  std::map<Node, Node> vtm;
  std::vector<Node> exp;
  return unfold(en, vtm, exp, false);
}

Node TermDbSygus::getEagerUnfold( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator itv = visited.find( n );
  if( itv==visited.end() ){
    Trace("cegqi-eager-debug") << "getEagerUnfold " << n << std::endl;
    Node ret;
    if (datatypes::DatatypesRewriter::isSygusEvalApp(n))
    {
      TypeNode tn = n[0].getType();
      Trace("cegqi-eager-debug") << "check " << n[0].getType() << std::endl;
      if( tn.isDatatype() ){
        const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
        if( dt.isSygus() ){ 
          Trace("cegqi-eager") << "Unfold eager : " << n << std::endl;
          Node bTerm = sygusToBuiltin( n[0], tn );
          Trace("cegqi-eager") << "Built-in term : " << bTerm << std::endl;
          std::vector< Node > vars;
          std::vector< Node > subs;
          Node var_list = Node::fromExpr( dt.getSygusVarList() );
          Assert( var_list.getNumChildren()+1==n.getNumChildren() );
          for( unsigned j=0; j<var_list.getNumChildren(); j++ ){
            vars.push_back( var_list[j] );
          }
          for( unsigned j=1; j<n.getNumChildren(); j++ ){
            Node nc = getEagerUnfold( n[j], visited );
            subs.push_back( nc );
            Assert(subs[j - 1].getType().isComparableTo(
                var_list[j - 1].getType()));
          }
          Assert( vars.size()==subs.size() );
          bTerm = bTerm.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
          Trace("cegqi-eager") << "Built-in term after subs : " << bTerm << std::endl;
          Trace("cegqi-eager-debug") << "Types : " << bTerm.getType() << " " << n.getType() << std::endl;
          Assert(n.getType().isComparableTo(bTerm.getType()));
          ret = bTerm; 
        }
      }
    }
    if( ret.isNull() ){
      if( n.getKind()!=FORALL ){
        bool childChanged = false;
        std::vector< Node > children;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = getEagerUnfold( n[i], visited );
          childChanged = childChanged || n[i]!=nc;
          children.push_back( nc );
        }
        if( childChanged ){
          if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
            children.insert( children.begin(), n.getOperator() );
          }
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
      }
      if( ret.isNull() ){
        ret = n;
      }
    }
    visited[n] = ret;
    return ret;
  }else{
    return itv->second;
  }
}

Node TermDbSygus::evaluateBuiltin(TypeNode tn,
                                  Node bn,
                                  std::vector<Node>& args,
                                  bool tryEval)
{
  if( !args.empty() ){
    std::map< TypeNode, std::vector< Node > >::iterator it = d_var_list.find( tn );
    Assert( it!=d_var_list.end() );
    Assert( it->second.size()==args.size() );

    Node res;
    if (tryEval && options::sygusEvalOpt())
    {
      // Try evaluating, which is much faster than substitution+rewriting.
      // This may fail if there is a subterm of bn under the
      // substitution that is not constant, or if an operator in bn is not
      // supported by the evaluator
      res = d_eval->eval(bn, it->second, args);
    }
    if (!res.isNull())
    {
      Assert(res
             == Rewriter::rewrite(bn.substitute(it->second.begin(),
                                                it->second.end(),
                                                args.begin(),
                                                args.end())));
      return res;
    }
    else
    {
      return Rewriter::rewrite(bn.substitute(
          it->second.begin(), it->second.end(), args.begin(), args.end()));
    }
  }else{
    return Rewriter::rewrite( bn );
  }
}

Node TermDbSygus::evaluateWithUnfolding(
    Node n, std::unordered_map<Node, Node, NodeHashFunction>& visited)
{
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it =
      visited.find(n);
  if( it==visited.end() ){
    Node ret = n;
    while (datatypes::DatatypesRewriter::isSygusEvalApp(ret)
           && ret[0].getKind() == APPLY_CONSTRUCTOR)
    {
      ret = unfold( ret );
    }    
    if( ret.getNumChildren()>0 ){
      std::vector< Node > children;
      if( ret.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( ret.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<ret.getNumChildren(); i++ ){
        Node nc = evaluateWithUnfolding( ret[i], visited ); 
        childChanged = childChanged || nc!=ret[i];
        children.push_back( nc );
      }
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( ret.getKind(), children );
      }
      ret = getExtRewriter()->extendedRewrite(ret);
    }
    visited[n] = ret;
    return ret;
  }else{
    return it->second;
  }
}

Node TermDbSygus::evaluateWithUnfolding( Node n ) {
  std::unordered_map<Node, Node, NodeHashFunction> visited;
  return evaluateWithUnfolding( n, visited );
}

bool TermDbSygus::isEvaluationPoint(Node n) const
{
  if (!datatypes::DatatypesRewriter::isSygusEvalApp(n))
  {
    return false;
  }
  if (!n[0].isVar())
  {
    return false;
  }
  for (unsigned i = 1, nchild = n.getNumChildren(); i < nchild; i++)
  {
    if (!n[i].isConst())
    {
      return false;
    }
  }
  return true;
}

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

