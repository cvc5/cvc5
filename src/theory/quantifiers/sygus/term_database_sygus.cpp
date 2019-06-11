/*********************                                                        */
/*! \file term_database_sygus.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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

void TypeNodeIdTrie::add(Node v, std::vector<TypeNode>& types)
{
  TypeNodeIdTrie* tnt = this;
  for (unsigned i = 0, size = types.size(); i < size; i++)
  {
    tnt = &tnt->d_children[types[i]];
  }
  tnt->d_data.push_back(v);
}

void TypeNodeIdTrie::assignIds(std::map<Node, unsigned>& assign,
                               unsigned& idCount)
{
  if (!d_data.empty())
  {
    for (const Node& v : d_data)
    {
      assign[v] = idCount;
    }
    idCount++;
  }
  for (std::pair<const TypeNode, TypeNodeIdTrie>& c : d_children)
  {
    c.second.assignIds(assign, idCount);
  }
}

std::ostream& operator<<(std::ostream& os, EnumeratorRole r)
{
  switch (r)
  {
    case ROLE_ENUM_POOL: os << "POOL"; break;
    case ROLE_ENUM_SINGLE_SOLUTION: os << "SINGLE_SOLUTION"; break;
    case ROLE_ENUM_MULTI_SOLUTION: os << "MULTI_SOLUTION"; break;
    case ROLE_ENUM_CONSTRAINED: os << "CONSTRAINED"; break;
    default: os << "enum_" << static_cast<unsigned>(r); break;
  }
  return os;
}

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
          d_var_list[tn].clear();
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
            if (sk == ITE)
            {
              // mark that this type has an ITE
              d_hasIte[tn] = true;
            }
          }
          else if (sop.isConst() && dt[i].getNumArgs() == 0)
          {
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
            if (sop[0].getKind() == ITE)
            {
              // mark that this type has an ITE
              d_hasIte[tn] = true;
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
                                     SynthConjecture* conj,
                                     EnumeratorRole erole,
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

  Trace("sygus-db") << "  registering symmetry breaking clauses..."
                    << std::endl;
  d_enum_to_using_sym_cons[e] = useSymbolicCons;
  // depending on if we are using symbolic constructors, introduce symmetry
  // breaking lemma templates for each relevant subtype of the grammar
  std::vector<TypeNode> sf_types;
  getSubfieldTypes(et, sf_types);
  // maps variables to the list of subfield types they occur in
  std::map<Node, std::vector<TypeNode> > type_occurs;
  std::map<TypeNode, std::vector<Node> >::iterator itv = d_var_list.find(et);
  Assert(itv != d_var_list.end());
  for (const Node& v : itv->second)
  {
    type_occurs[v].clear();
  }
  // for each type of subfield type of this enumerator
  for (unsigned i = 0, ntypes = sf_types.size(); i < ntypes; i++)
  {
    std::vector<unsigned> rm_indices;
    TypeNode stn = sf_types[i];
    Assert(stn.isDatatype());
    const Datatype& dt = stn.getDatatype();
    int anyC = getAnyConstantConsNum(stn);
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      Expr sop = dt[i].getSygusOp();
      Assert(!sop.isNull());
      bool isAnyC = static_cast<int>(i) == anyC;
      Node sopn = Node::fromExpr(sop);
      if (type_occurs.find(sopn) != type_occurs.end())
      {
        // if it is a variable, store that it occurs in stn
        type_occurs[sopn].push_back(stn);
      }
      else if (isAnyC && !useSymbolicCons)
      {
        // if we are not using the any constant constructor
        // do not use the symbolic constructor
        rm_indices.push_back(i);
      }
      else if (anyC != -1 && !isAnyC && useSymbolicCons)
      {
        // if we are using the any constant constructor, do not use any
        // concrete constant
        Node c_op = getConsNumConst(stn, i);
        if (!c_op.isNull())
        {
          rm_indices.push_back(i);
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

  // determine if we are actively-generated
  bool isActiveGen = false;
  if (options::sygusActiveGenMode() != SYGUS_ACTIVE_GEN_NONE)
  {
    if (erole == ROLE_ENUM_MULTI_SOLUTION || erole == ROLE_ENUM_CONSTRAINED)
    {
      // If the enumerator is a solution for a conjecture with multiple
      // functions, we do not use active generation. If we did, we would have to
      // generate a "product" of two actively-generated enumerators. That is,
      // given a conjecture with two functions-to-synthesize with enumerators
      // e_f and e_g, and if these enumerators generated:
      // e_f -> t1, ..., tn
      // e_g -> s1, ..., sm
      // The sygus module in charge of this conjecture would expect
      // constructCandidates calls of the form
      //   (e_f,e_g) -> (ti, sj)
      // for each i,j. We instead use passive enumeration in this case.
      //
      // If the enumerator is constrained, it cannot be actively generated.
    }
    else if (erole == ROLE_ENUM_POOL)
    {
      // If the enumerator is used for generating a pool of values, we always
      // use active generation.
      isActiveGen = true;
    }
    else if (erole == ROLE_ENUM_SINGLE_SOLUTION)
    {
      // If the enumerator is the single function-to-synthesize, if auto is
      // enabled, we infer whether it is better to enable active generation.
      if (options::sygusActiveGenMode() == SYGUS_ACTIVE_GEN_AUTO)
      {
        // We use active generation if the grammar of the enumerator does not
        // have ITE and is not Boolean. Experimentally, it is better to
        // use passive generation for these cases since it enables useful
        // search space pruning techniques, e.g. evaluation unfolding,
        // conjecture-specific symmetry breaking. Also, if sygus-stream is
        // enabled, we always use active generation, since the use cases of
        // sygus stream are to find many solutions to an easy problem, where
        // the bottleneck often becomes the large number of "exclude the current
        // solution" clauses.
        const Datatype& dt = et.getDatatype();
        if (options::sygusStream()
            || (!hasIte(et) && !dt.getSygusType().isBoolean()))
        {
          isActiveGen = true;
        }
      }
      else
      {
        isActiveGen = true;
      }
    }
    else
    {
      Unreachable("Unknown enumerator mode in registerEnumerator");
    }
  }
  Trace("sygus-db") << "isActiveGen for " << e << ", role = " << erole
                    << " returned " << isActiveGen << std::endl;
  // Currently, actively-generated enumerators are either basic or variable
  // agnostic.
  bool isVarAgnostic =
      isActiveGen
      && options::sygusActiveGenMode() == SYGUS_ACTIVE_GEN_VAR_AGNOSTIC;
  d_enum_var_agnostic[e] = isVarAgnostic;
  if (isVarAgnostic)
  {
    // if not done so already, compute type class identifiers for each variable
    if (d_var_subclass_id.find(et) == d_var_subclass_id.end())
    {
      d_var_subclass_id[et].clear();
      TypeNodeIdTrie tnit;
      for (std::pair<const Node, std::vector<TypeNode> >& to : type_occurs)
      {
        tnit.add(to.first, to.second);
      }
      // 0 is reserved for "no type class id"
      unsigned typeIdCount = 1;
      tnit.assignIds(d_var_subclass_id[et], typeIdCount);
      // assign the list and reverse map to index
      for (std::pair<const Node, std::vector<TypeNode> >& to : type_occurs)
      {
        Node v = to.first;
        unsigned sc = d_var_subclass_id[et][v];
        Trace("sygus-db") << v << " has subclass id " << sc << std::endl;
        d_var_subclass_list_index[et][v] = d_var_subclass_list[et][sc].size();
        d_var_subclass_list[et][sc].push_back(v);
      }
    }
    // If no subclass has more than one variable, do not use variable agnostic
    // enumeration
    bool useVarAgnostic = false;
    for (std::pair<const unsigned, std::vector<Node> >& p :
         d_var_subclass_list[et])
    {
      if (p.second.size() > 1)
      {
        useVarAgnostic = true;
      }
    }
    if (!useVarAgnostic)
    {
      Trace("sygus-db")
          << "...disabling variable agnostic for " << e
          << " since it has no subclass with more than one variable."
          << std::endl;
      d_enum_var_agnostic[e] = false;
      isActiveGen = false;
    }
  }
  d_enum_active_gen[e] = isActiveGen;
  d_enum_basic[e] = isActiveGen && !isVarAgnostic;

  // We make an active guard if we will be explicitly blocking solutions for
  // the enumerator. This is the case if the role of the enumerator is to
  // populate a pool of terms, or (some cases) of when it is actively generated.
  if (isActiveGen || erole == ROLE_ENUM_POOL)
  {
    // make the guard
    Node ag = nm->mkSkolem("eG", nm->booleanType());
    // must ensure it is a literal immediately here
    ag = d_quantEngine->getValuation().ensureLiteral(ag);
    // must ensure that it is asserted as a literal before we begin solving
    Node lem = nm->mkNode(OR, ag, ag.negate());
    d_quantEngine->getOutputChannel().requirePhase(ag, true);
    d_quantEngine->getOutputChannel().lemma(lem);
    d_enum_to_active_guard[e] = ag;
  }
}

bool TermDbSygus::isEnumerator(Node e) const
{
  return d_enum_to_conjecture.find(e) != d_enum_to_conjecture.end();
}

SynthConjecture* TermDbSygus::getConjectureForEnumerator(Node e) const
{
  std::map<Node, SynthConjecture*>::const_iterator itm =
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

bool TermDbSygus::isVariableAgnosticEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_var_agnostic.find(e);
  if (itus != d_enum_var_agnostic.end())
  {
    return itus->second;
  }
  return false;
}

bool TermDbSygus::isBasicEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_basic.find(e);
  if (itus != d_enum_basic.end())
  {
    return itus->second;
  }
  return false;
}

bool TermDbSygus::isPassiveEnumerator(Node e) const
{
  std::map<Node, bool>::const_iterator itus = d_enum_active_gen.find(e);
  if (itus != d_enum_active_gen.end())
  {
    return !itus->second;
  }
  return true;
}

void TermDbSygus::getEnumerators(std::vector<Node>& mts)
{
  for (std::map<Node, SynthConjecture*>::iterator itm =
           d_enum_to_conjecture.begin();
       itm != d_enum_to_conjecture.end();
       ++itm)
  {
    mts.push_back( itm->first );
  }
}

void TermDbSygus::registerSymBreakLemma(
    Node e, Node lem, TypeNode tn, unsigned sz, bool isTempl)
{
  d_enum_to_sb_lemmas[e].push_back(lem);
  d_sb_lemma_to_type[lem] = tn;
  d_sb_lemma_to_size[lem] = sz;
  d_sb_lemma_to_isTempl[lem] = isTempl;
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

bool TermDbSygus::isSymBreakLemmaTemplate(Node lem) const
{
  std::map<Node, bool>::const_iterator it = d_sb_lemma_to_isTempl.find(lem);
  Assert(it != d_sb_lemma_to_isTempl.end());
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
    if (n.isNull())
    {
      Trace(c) << n;
    }
    else
    {
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, n);
      Trace(c) << ss.str();
    }
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
bool TermDbSygus::hasIte(TypeNode tn) const
{
  return d_hasIte.find(tn) != d_hasIte.end();
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

unsigned TermDbSygus::getSubclassForVar(TypeNode tn, Node n) const
{
  std::map<TypeNode, std::map<Node, unsigned> >::const_iterator itc =
      d_var_subclass_id.find(tn);
  if (itc == d_var_subclass_id.end())
  {
    Assert(false);
    return 0;
  }
  std::map<Node, unsigned>::const_iterator itcc = itc->second.find(n);
  if (itcc == itc->second.end())
  {
    Assert(false);
    return 0;
  }
  return itcc->second;
}

unsigned TermDbSygus::getNumSubclassVars(TypeNode tn, unsigned sc) const
{
  std::map<TypeNode, std::map<unsigned, std::vector<Node> > >::const_iterator
      itv = d_var_subclass_list.find(tn);
  if (itv == d_var_subclass_list.end())
  {
    Assert(false);
    return 0;
  }
  std::map<unsigned, std::vector<Node> >::const_iterator itvv =
      itv->second.find(sc);
  if (itvv == itv->second.end())
  {
    Assert(false);
    return 0;
  }
  return itvv->second.size();
}
Node TermDbSygus::getVarSubclassIndex(TypeNode tn,
                                      unsigned sc,
                                      unsigned i) const
{
  std::map<TypeNode, std::map<unsigned, std::vector<Node> > >::const_iterator
      itv = d_var_subclass_list.find(tn);
  if (itv == d_var_subclass_list.end())
  {
    Assert(false);
    return Node::null();
  }
  std::map<unsigned, std::vector<Node> >::const_iterator itvv =
      itv->second.find(sc);
  if (itvv == itv->second.end() || i >= itvv->second.size())
  {
    Assert(false);
    return Node::null();
  }
  return itvv->second[i];
}

bool TermDbSygus::getIndexInSubclassForVar(TypeNode tn,
                                           Node v,
                                           unsigned& index) const
{
  std::map<TypeNode, std::map<Node, unsigned> >::const_iterator itv =
      d_var_subclass_list_index.find(tn);
  if (itv == d_var_subclass_list_index.end())
  {
    return false;
  }
  std::map<Node, unsigned>::const_iterator itvv = itv->second.find(v);
  if (itvv == itv->second.end())
  {
    return false;
  }
  index = itvv->second;
  return true;
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
  if (en.getKind() != DT_SYGUS_EVAL)
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
    pre[j] = nm->mkNode(DT_SYGUS_EVAL, cc);
  }
  Node ret = mkGeneric(dt, i, pre);
  // apply the appropriate substitution to ret
  ret = datatypes::DatatypesRewriter::applySygusArgs(dt, sop, ret, args);
  // rewrite
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
    if (n.getKind() == DT_SYGUS_EVAL)
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
    while (ret.getKind() == DT_SYGUS_EVAL
           && ret[0].getKind() == APPLY_CONSTRUCTOR)
    {
      if (ret == n && ret[0].isConst())
      {
        Trace("dt-eval-unfold-debug")
            << "Optimize: evaluate constant head " << ret << std::endl;
        // can just do direct evaluation here
        std::vector<Node> args;
        bool success = true;
        for (unsigned i = 1, nchild = ret.getNumChildren(); i < nchild; i++)
        {
          if (!ret[i].isConst())
          {
            success = false;
            break;
          }
          args.push_back(ret[i]);
        }
        if (success)
        {
          TypeNode rt = ret[0].getType();
          Node bret = sygusToBuiltin(ret[0], rt);
          Node rete = evaluateBuiltin(rt, bret, args);
          visited[n] = rete;
          Trace("dt-eval-unfold-debug")
              << "Return " << rete << " for " << n << std::endl;
          return rete;
        }
      }
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
  if (n.getKind() != DT_SYGUS_EVAL)
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

