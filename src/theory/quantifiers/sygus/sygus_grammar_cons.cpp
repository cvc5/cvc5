/*********************                                                        */
/*! \file sygus_grammar_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for constructing inductive datatypes that correspond to
 ** grammars that encode syntactic restrictions for SyGuS.
 **/
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"

#include <stack>

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/sygus/sygus_grammar_norm.h"
#include "theory/quantifiers/sygus/sygus_process_conj.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegGrammarConstructor::CegGrammarConstructor(QuantifiersEngine* qe,
                                             SynthConjecture* p)
    : d_qe(qe), d_parent(p), d_is_syntax_restricted(false)
{
}

bool CegGrammarConstructor::hasSyntaxRestrictions(Node q)
{
  Assert(q.getKind() == FORALL);
  for (const Node& f : q[0])
  {
    Node gv = f.getAttribute(SygusSynthGrammarAttribute());
    if (!gv.isNull())
    {
      TypeNode tn = gv.getType();
      if (tn.isDatatype()
          && static_cast<DatatypeType>(tn.toType()).getDatatype().isSygus())
      {
        return true;
      }
    }
  }
  return false;
}

void CegGrammarConstructor::collectTerms(
    Node n,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& consts)
{
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);
    if (it == visited.end()) {
      visited[cur] = true;
      // is this a constant?
      if( cur.isConst() ){
        TypeNode tn = cur.getType();
        Node c = cur;
        if( tn.isReal() ){
          c = NodeManager::currentNM()->mkConst( c.getConst<Rational>().abs() );
        }
        if( std::find( consts[tn].begin(), consts[tn].end(), c )==consts[tn].end() ){
          Trace("cegqi-debug") << "...consider const : " << c << std::endl;
          consts[tn].insert(c);
        }
      }
      // recurse
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    }
  } while (!visit.empty());
}

Node CegGrammarConstructor::process(Node q,
                                    const std::map<Node, Node>& templates,
                                    const std::map<Node, Node>& templates_arg)
{
  // convert to deep embedding and finalize single invocation here
  // now, construct the grammar
  Trace("cegqi") << "SynthConjecture : convert to deep embedding..."
                 << std::endl;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> extra_cons;
  if( options::sygusAddConstGrammar() ){
    Trace("cegqi") << "SynthConjecture : collect constants..." << std::endl;
    collectTerms( q[1], extra_cons );
  }
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> exc_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> inc_cons;

  NodeManager* nm = NodeManager::currentNM();

  std::vector< Node > ebvl;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    Node sf = q[0][i];
    // if non-null, v encodes the syntactic restrictions (via an inductive
    // datatype) on sf from the input.
    Node v = sf.getAttribute(SygusSynthGrammarAttribute());
    TypeNode preGrammarType;
    if (!v.isNull())
    {
      preGrammarType = v.getType();
    }
    else
    {
      // otherwise, the grammar is the default for the range of the function
      preGrammarType = sf.getType();
      if (preGrammarType.isFunction())
      {
        preGrammarType = preGrammarType.getRangeType();
      }
    }

    // the actual sygus datatype we will use (normalized below)
    TypeNode tn;
    std::stringstream ss;
    ss << sf;
    Node sfvl;
    if (preGrammarType.isDatatype() && preGrammarType.getDatatype().isSygus())
    {
      sfvl = Node::fromExpr(preGrammarType.getDatatype().getSygusVarList());
      tn = preGrammarType;
    }else{
      sfvl = getSygusVarList(sf);
      // check which arguments are irrelevant
      std::unordered_set<unsigned> arg_irrelevant;
      d_parent->getProcess()->getIrrelevantArgs(sf, arg_irrelevant);
      std::unordered_set<Node, NodeHashFunction> term_irlv;
      // convert to term
      for (const unsigned& arg : arg_irrelevant)
      {
        Assert(arg < sfvl.getNumChildren());
        term_irlv.insert(sfvl[arg]);
      }

      // make the default grammar
      tn = mkSygusDefaultType(preGrammarType,
                              sfvl,
                              ss.str(),
                              extra_cons,
                              exc_cons,
                              inc_cons,
                              term_irlv);
    }
    // sfvl may be null for constant synthesis functions
    Trace("cegqi-debug") << "...sygus var list associated with " << sf << " is "
                         << sfvl << std::endl;

    // normalize type
    SygusGrammarNorm sygus_norm(d_qe);
    tn = sygus_norm.normalizeSygusType(tn, sfvl);

    std::map<Node, Node>::const_iterator itt = templates.find(sf);
    if( itt!=templates.end() ){
      Node templ = itt->second;
      std::map<Node, Node>::const_iterator itta = templates_arg.find(sf);
      Assert(itta != templates_arg.end());
      TNode templ_arg = itta->second;
      Assert( !templ_arg.isNull() );
      // if there is a template for this argument, make a sygus type on top of it
      if( options::sygusTemplEmbedGrammar() ){
        Trace("cegqi-debug") << "Template for " << sf << " is : " << templ
                             << " with arg " << templ_arg << std::endl;
        Trace("cegqi-debug") << "  embed this template as a grammar..." << std::endl;
        tn = mkSygusTemplateType( templ, templ_arg, tn, sfvl, ss.str() );
      }
    }

    // ev is the first-order variable corresponding to this synth fun
    std::stringstream ssf;
    ssf << "f" << sf;
    Node ev = nm->mkBoundVar(ssf.str(), tn);
    ebvl.push_back(ev);
    Trace("cegqi") << "...embedding synth fun : " << sf << " -> " << ev
                   << std::endl;
  }
  return process(q, templates, templates_arg, ebvl);
}

Node CegGrammarConstructor::process(Node q,
                                    const std::map<Node, Node>& templates,
                                    const std::map<Node, Node>& templates_arg,
                                    const std::vector<Node>& ebvl)
{
  Assert(q[0].getNumChildren() == ebvl.size());
  Assert(d_synth_fun_vars.empty());

  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> qchildren;
  Node qbody_subs = q[1];
  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
  for (unsigned i = 0, size = q[0].getNumChildren(); i < size; i++)
  {
    Node sf = q[0][i];
    d_synth_fun_vars[sf] = ebvl[i];
    Node sfvl = getSygusVarList(sf);
    TypeNode tn = ebvl[i].getType();
    // check if there is a template
    std::map<Node, Node>::const_iterator itt = templates.find(sf);
    if (itt != templates.end())
    {
      Node templ = itt->second;
      std::map<Node, Node>::const_iterator itta = templates_arg.find(sf);
      Assert(itta != templates_arg.end());
      TNode templ_arg = itta->second;
      Assert(!templ_arg.isNull());
      // if there is a template for this argument, make a sygus type on top of
      // it
      if (!options::sygusTemplEmbedGrammar())
      {
        // otherwise, apply it as a preprocessing pass
        Trace("cegqi-debug") << "Template for " << sf << " is : " << templ
                             << " with arg " << templ_arg << std::endl;
        Trace("cegqi-debug") << "  apply this template as a substituion during preprocess..." << std::endl;
        std::vector< Node > schildren;
        std::vector< Node > largs;
        for( unsigned j=0; j<sfvl.getNumChildren(); j++ ){
          schildren.push_back( sfvl[j] );
          largs.push_back(nm->mkBoundVar(sfvl[j].getType()));
        }
        std::vector< Node > subsfn_children;
        subsfn_children.push_back( sf );
        subsfn_children.insert( subsfn_children.end(), schildren.begin(), schildren.end() );
        Node subsfn = nm->mkNode(kind::APPLY_UF, subsfn_children);
        TNode subsf = subsfn;
        Trace("cegqi-debug") << "  substitute arg : " << templ_arg << " -> " << subsf << std::endl;
        templ = templ.substitute( templ_arg, subsf );
        // substitute lambda arguments
        templ = templ.substitute( schildren.begin(), schildren.end(), largs.begin(), largs.end() );
        Node subsn =
            nm->mkNode(kind::LAMBDA, nm->mkNode(BOUND_VAR_LIST, largs), templ);
        TNode var = sf;
        TNode subs = subsn;
        Trace("cegqi-debug") << "  substitute : " << var << " -> " << subs << std::endl;
        qbody_subs = qbody_subs.substitute( var, subs );
        Trace("cegqi-debug") << "  body is now : " << qbody_subs << std::endl;
      }
    }
    tds->registerSygusType(tn);
    Assert(tn.isDatatype());
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    Assert(dt.isSygus());
    if( !dt.getSygusAllowAll() ){
      d_is_syntax_restricted = true;
    }
  }
  qchildren.push_back(nm->mkNode(kind::BOUND_VAR_LIST, ebvl));
  if( qbody_subs!=q[1] ){
    Trace("cegqi") << "...rewriting : " << qbody_subs << std::endl;
    qbody_subs = Rewriter::rewrite( qbody_subs );
    Trace("cegqi") << "...got : " << qbody_subs << std::endl;
  }
  qchildren.push_back(convertToEmbedding(qbody_subs));
  if( q.getNumChildren()==3 ){
    qchildren.push_back( q[2] );
  }
  return nm->mkNode(kind::FORALL, qchildren);
}

Node CegGrammarConstructor::convertToEmbedding(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);
    if (it == visited.end()) {
      visited[cur] = Node::null();
      visit.push(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    } else if (it->second.isNull()) {
      Node ret = cur;
      Kind ret_k = cur.getKind();
      Node op;
      bool childChanged = false;
      std::vector<Node> children;
      // get the potential operator
      if( cur.getNumChildren()>0 ){
        if( cur.getKind()==kind::APPLY_UF ){
          op = cur.getOperator();
        }
      }else{
        op = cur;
      }
      // is the operator a synth function?
      bool makeEvalFun = false;
      if( !op.isNull() ){
        std::map<Node, Node>::iterator its = d_synth_fun_vars.find(op);
        if (its != d_synth_fun_vars.end())
        {
          children.push_back( its->second );
          makeEvalFun = true;
        }
      }
      if (!makeEvalFun)
      {
        // otherwise, we apply the previous operator
        if( cur.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.push_back( cur.getOperator() );
        }
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        it = visited.find(cur[i]);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
      }
      if (makeEvalFun)
      {
        // will make into an application of an evaluation function
        ret = nm->mkNode(DT_SYGUS_EVAL, children);
      }
      else if (childChanged)
      {
        ret = NodeManager::currentNM()->mkNode(ret_k, children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}


TypeNode CegGrammarConstructor::mkUnresolvedType(const std::string& name, std::set<Type>& unres) {
  TypeNode unresolved = NodeManager::currentNM()->mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER);
  unres.insert( unresolved.toType() );
  return unresolved;
}

void CegGrammarConstructor::mkSygusConstantsForType(TypeNode type,
                                                    std::vector<Node>& ops)
{
  NodeManager* nm = NodeManager::currentNM();
  if (type.isReal())
  {
    ops.push_back(nm->mkConst(Rational(0)));
    ops.push_back(nm->mkConst(Rational(1)));
  }
  else if (type.isBitVector())
  {
    unsigned size = type.getBitVectorSize();
    ops.push_back(bv::utils::mkZero(size));
    ops.push_back(bv::utils::mkOne(size));
  }
  else if (type.isBoolean())
  {
    ops.push_back(nm->mkConst(true));
    ops.push_back(nm->mkConst(false));
  }
  else if (type.isString())
  {
    ops.push_back(nm->mkConst(String("")));
  }
  else if (type.isArray())
  {
    // TODO #2694 : generate constant array over the first element of the
    // constituent type
  }
  // TODO #1178 : add other missing types
}

void CegGrammarConstructor::collectSygusGrammarTypesFor(
    TypeNode range, std::vector<TypeNode>& types)
{
  if( !range.isBoolean() ){
    if( std::find( types.begin(), types.end(), range )==types.end() ){
      Trace("sygus-grammar-def") << "...will make grammar for " << range << std::endl;
      types.push_back( range );
      if( range.isDatatype() ){
        const Datatype& dt = range.getDatatype();
        for (unsigned i = 0, size = dt.getNumConstructors(); i < size; ++i)
        {
          for (unsigned j = 0, size_args = dt[i].getNumArgs(); j < size_args;
               ++j)
          {
            collectSygusGrammarTypesFor(
                TypeNode::fromType(static_cast<SelectorType>(dt[i][j].getType())
                                       .getRangeType()),
                types);
          }
        }
      }
      else if (range.isArray())
      {
        ArrayType arrayType = static_cast<ArrayType>(range.toType());
        // add index and constituent type
        collectSygusGrammarTypesFor(
            TypeNode::fromType(arrayType.getIndexType()), types);
        collectSygusGrammarTypesFor(
            TypeNode::fromType(arrayType.getConstituentType()), types);
      }
    }
  }
}

void CegGrammarConstructor::mkSygusDefaultGrammar(
    TypeNode range,
    Node bvl,
    const std::string& fun,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& extra_cons,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& exc_cons,
    const std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>&
        inc_cons,
    std::unordered_set<Node, NodeHashFunction>& term_irrelevant,
    std::vector<CVC4::Datatype>& datatypes,
    std::set<Type>& unres)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-grammar-def") << "Construct default grammar for " << fun << " "
                             << range << std::endl;
  // collect the variables
  std::vector<Node> sygus_vars;
  if (!bvl.isNull())
  {
    for (unsigned i = 0, size = bvl.getNumChildren(); i < size; ++i)
    {
      if (term_irrelevant.find(bvl[i]) == term_irrelevant.end())
      {
        sygus_vars.push_back(bvl[i]);
      }
      else
      {
        Trace("sygus-grammar-def")
            << "...synth var " << bvl[i] << " has been marked irrelevant."
            << std::endl;
      }
    }
  }
  // operators for each constructor in type
  std::vector<std::vector<Expr>> ops;
  // names for the operators
  std::vector<std::vector<std::string>> cnames;
  // argument types of operators
  std::vector<std::vector<std::vector<Type>>> cargs;
  // set of callbacks for each constructor
  std::vector<std::vector<std::shared_ptr<SygusPrintCallback>>> pcs;
  // weights for each constructor
  std::vector<std::vector<int>> weights;
  // index of top datatype, i.e. the datatype for the range type
  int startIndex = -1;
  std::map< Type, Type > sygus_to_builtin;

  std::vector<TypeNode> types;
  // collect connected types for each of the variables
  for (unsigned i = 0, size = sygus_vars.size(); i < size; ++i)
  {
    collectSygusGrammarTypesFor(sygus_vars[i].getType(), types);
  }
  // collect connected types to range
  collectSygusGrammarTypesFor(range, types);

  // create placeholder for boolean type (kept apart since not collected)
  std::stringstream ssb;
  ssb << fun << "_Bool";
  std::string dbname = ssb.str();
  Type unres_bt = mkUnresolvedType(ssb.str(), unres).toType();

  // create placeholders for collected types
  std::vector< Type > unres_types;
  std::map< TypeNode, Type > type_to_unres;
  for (unsigned i = 0, size = types.size(); i < size; ++i)
  {
    std::stringstream ss;
    ss << fun << "_" << types[i];
    std::string dname = ss.str();
    datatypes.push_back(Datatype(dname));
    ops.push_back(std::vector< Expr >());
    cnames.push_back(std::vector<std::string>());
    cargs.push_back(std::vector<std::vector<Type>>());
    pcs.push_back(std::vector<std::shared_ptr<SygusPrintCallback>>());
    weights.push_back(std::vector<int>());
    //make unresolved type
    Type unres_t = mkUnresolvedType(dname, unres).toType();
    unres_types.push_back(unres_t);
    type_to_unres[types[i]] = unres_t;
    sygus_to_builtin[unres_t] = types[i].toType();
  }
  for (unsigned i = 0, size = types.size(); i < size; ++i)
  {
    Trace("sygus-grammar-def") << "Make grammar for " << types[i] << " " << unres_types[i] << std::endl;
    Type unres_t = unres_types[i];
    //add variables
    for (unsigned j = 0, size_j = sygus_vars.size(); j < size_j; ++j)
    {
      if( sygus_vars[j].getType()==types[i] ){
        std::stringstream ss;
        ss << sygus_vars[j];
        Trace("sygus-grammar-def") << "...add for variable " << ss.str() << std::endl;
        ops[i].push_back( sygus_vars[j].toExpr() );
        cnames[i].push_back(ss.str());
        cargs[i].push_back(std::vector<Type>());
        pcs[i].push_back(nullptr);
        weights[i].push_back(-1);
      }
    }
    //add constants
    std::vector< Node > consts;
    mkSygusConstantsForType( types[i], consts );
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>::iterator
        itec = extra_cons.find(types[i]);
    if( itec!=extra_cons.end() ){
      for (std::unordered_set<Node, NodeHashFunction>::iterator set_it =
               itec->second.begin();
           set_it != itec->second.end();
           set_it++)
      {
        if (std::find(consts.begin(), consts.end(), *set_it) == consts.end())
        {
          consts.push_back(*set_it);
        }
      }
    }
    for (unsigned j = 0, size_j = consts.size(); j < size_j; ++j)
    {
      std::stringstream ss;
      ss << consts[j];
      Trace("sygus-grammar-def") << "...add for constant " << ss.str() << std::endl;
      ops[i].push_back( consts[j].toExpr() );
      cnames[i].push_back(ss.str());
      cargs[i].push_back(std::vector<Type>());
      pcs[i].push_back(nullptr);
      weights[i].push_back(-1);
    }
    // ITE
    Kind k = ITE;
    Trace("sygus-grammar-def") << "...add for " << k << std::endl;
    ops[i].push_back(nm->operatorOf(k).toExpr());
    cnames[i].push_back(kindToString(k));
    cargs[i].push_back(std::vector<Type>());
    cargs[i].back().push_back(unres_bt);
    cargs[i].back().push_back(unres_t);
    cargs[i].back().push_back(unres_t);
    pcs[i].push_back(nullptr);
    weights[i].push_back(-1);

    if (types[i].isReal())
    {
      // Add PLUS, MINUS
      Kind kinds[2] = {PLUS, MINUS};
      for (const Kind k : kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << k << std::endl;
        ops[i].push_back(nm->operatorOf(k).toExpr());
        cnames[i].push_back(kindToString(k));
        cargs[i].push_back(std::vector<Type>());
        cargs[i].back().push_back(unres_t);
        cargs[i].back().push_back(unres_t);
        pcs[i].push_back(nullptr);
        weights[i].push_back(-1);
      }
      if (!types[i].isInteger())
      {
        Trace("sygus-grammar-def")
            << "  ...create auxiliary Positive Integers grammar\n";
        /* Creating type for positive integers */
        std::stringstream ss;
        ss << fun << "_PosInt";
        std::string pos_int_name = ss.str();
        // make unresolved type
        Type unres_pos_int_t = mkUnresolvedType(pos_int_name, unres).toType();
        // make data type
        datatypes.push_back(Datatype(pos_int_name));
        /* add placeholders */
        std::vector<Expr> ops_pos_int;
        std::vector<std::string> cnames_pos_int;
        std::vector<std::vector<Type>> cargs_pos_int;
        /* Add operator 1 */
        Trace("sygus-grammar-def") << "\t...add for 1 to Pos_Int\n";
        ops_pos_int.push_back(nm->mkConst(Rational(1)).toExpr());
        ss.str("");
        ss << "1";
        cnames_pos_int.push_back(ss.str());
        cargs_pos_int.push_back(std::vector<Type>());
        /* Add operator PLUS */
        Kind k = PLUS;
        Trace("sygus-grammar-def") << "\t...add for PLUS to Pos_Int\n";
        ops_pos_int.push_back(nm->operatorOf(k).toExpr());
        cnames_pos_int.push_back(kindToString(k));
        cargs_pos_int.push_back(std::vector<Type>());
        cargs_pos_int.back().push_back(unres_pos_int_t);
        cargs_pos_int.back().push_back(unres_pos_int_t);
        datatypes.back().setSygus(types[i].toType(), bvl.toExpr(), true, true);
        for (unsigned j = 0, size_j = ops_pos_int.size(); j < size_j; ++j)
        {
          datatypes.back().addSygusConstructor(
              ops_pos_int[j], cnames_pos_int[j], cargs_pos_int[j]);
        }
        Trace("sygus-grammar-def")
            << "  ...built datatype " << datatypes.back() << " ";
        /* Adding division at root */
        k = DIVISION;
        Trace("sygus-grammar-def") << "\t...add for " << k << std::endl;
        ops[i].push_back(nm->operatorOf(k).toExpr());
        cnames[i].push_back(kindToString(k));
        cargs[i].push_back(std::vector<Type>());
        cargs[i].back().push_back(unres_t);
        cargs[i].back().push_back(unres_pos_int_t);
        pcs[i].push_back(nullptr);
        weights[i].push_back(-1);
      }
    }
    else if (types[i].isBitVector())
    {
      // unary apps
      std::vector<Kind> un_kinds = {BITVECTOR_NOT, BITVECTOR_NEG};
      for (const Kind k : un_kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << k << std::endl;
        ops[i].push_back(nm->operatorOf(k).toExpr());
        cnames[i].push_back(kindToString(k));
        cargs[i].push_back(std::vector<Type>());
        cargs[i].back().push_back(unres_t);
        pcs[i].push_back(nullptr);
        weights[i].push_back(-1);
      }
      // binary apps
      std::vector<Kind> bin_kinds = {BITVECTOR_AND,
                                     BITVECTOR_OR,
                                     BITVECTOR_XOR,
                                     BITVECTOR_PLUS,
                                     BITVECTOR_SUB,
                                     BITVECTOR_MULT,
                                     BITVECTOR_UDIV_TOTAL,
                                     BITVECTOR_UREM_TOTAL,
                                     BITVECTOR_SDIV,
                                     BITVECTOR_SREM,
                                     BITVECTOR_SHL,
                                     BITVECTOR_LSHR,
                                     BITVECTOR_ASHR};
      for (const Kind k : bin_kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << k << std::endl;
        ops[i].push_back(nm->operatorOf(k).toExpr());
        cnames[i].push_back(kindToString(k));
        cargs[i].push_back(std::vector<Type>());
        cargs[i].back().push_back(unres_t);
        cargs[i].back().push_back(unres_t);
        pcs[i].push_back(nullptr);
        weights[i].push_back(-1);
      }
    }
    else if (types[i].isArray())
    {
      ArrayType arrayType = static_cast<ArrayType>(types[i].toType());
      Trace("sygus-grammar-def")
          << "...building for array type " << arrayType << "\n";
      Trace("sygus-grammar-def")
          << "......finding unres type for index type "
          << arrayType.getIndexType() << " with typenode "
          << TypeNode::fromType(arrayType.getIndexType()) << "\n";
      // retrieve index and constituent unresolved types
      Assert(std::find(types.begin(),
                       types.end(),
                       TypeNode::fromType(arrayType.getIndexType()))
             != types.end());
      unsigned i_indexType = std::distance(
          types.begin(),
          std::find(types.begin(),
                    types.end(),
                    TypeNode::fromType(arrayType.getIndexType())));
      Type unres_indexType = unres_types[i_indexType];
      Assert(std::find(types.begin(),
                       types.end(),
                       TypeNode::fromType(arrayType.getConstituentType()))
             != types.end());
      unsigned i_constituentType = std::distance(
          types.begin(),
          std::find(types.begin(),
                    types.end(),
                    TypeNode::fromType(arrayType.getConstituentType())));
      Type unres_constituentType = unres_types[i_constituentType];
      // add (store ArrayType IndexType ConstituentType)
      Trace("sygus-grammar-def") << "...add for STORE\n";
      ops[i].push_back(nm->operatorOf(STORE).toExpr());
      cnames[i].push_back(kindToString(STORE));
      cargs[i].push_back(std::vector<Type>());
      cargs[i].back().push_back(unres_t);
      cargs[i].back().push_back(unres_indexType);
      cargs[i].back().push_back(unres_constituentType);
      pcs[i].push_back(nullptr);
      weights[i].push_back(-1);
      // add to constituent type : (select ArrayType IndexType)
      Trace("sygus-grammar-def") << "...add select for constituent type"
                                 << unres_constituentType << "\n";
      ops[i_constituentType].push_back(nm->operatorOf(SELECT).toExpr());
      cnames[i_constituentType].push_back(kindToString(SELECT));
      cargs[i_constituentType].push_back(std::vector<Type>());
      cargs[i_constituentType].back().push_back(unres_t);
      cargs[i_constituentType].back().push_back(unres_indexType);
      pcs[i_constituentType].push_back(nullptr);
      weights[i_constituentType].push_back(-1);
    }
    else if (types[i].isDatatype())
    {
      Trace("sygus-grammar-def") << "...add for constructors" << std::endl;
      const Datatype& dt = types[i].getDatatype();
      for (unsigned k = 0, size_k = dt.getNumConstructors(); k < size_k; ++k)
      {
        Trace("sygus-grammar-def") << "...for " << dt[k].getName() << std::endl;
        Expr cop = dt[k].getConstructor();
        if (dt[k].getNumArgs() == 0)
        {
          // Nullary constructors are interpreted as terms, not operators.
          // Thus, we apply them to no arguments here.
          cop = nm->mkNode(APPLY_CONSTRUCTOR, Node::fromExpr(cop)).toExpr();
        }
        ops[i].push_back(cop);
        cnames[i].push_back(dt[k].getName());
        cargs[i].push_back(std::vector<Type>());
        Trace("sygus-grammar-def") << "...add for selectors" << std::endl;
        for (unsigned j = 0, size_j = dt[k].getNumArgs(); j < size_j; ++j)
        {
          Trace("sygus-grammar-def")
              << "...for " << dt[k][j].getName() << std::endl;
          TypeNode crange = TypeNode::fromType(
              static_cast<SelectorType>(dt[k][j].getType()).getRangeType());
          Assert(type_to_unres.find(crange) != type_to_unres.end());
          cargs[i].back().push_back(type_to_unres[crange]);
          // add to the selector type the selector operator

          Assert(std::find(types.begin(), types.end(), crange) != types.end());
          unsigned i_selType = std::distance(
              types.begin(), std::find(types.begin(), types.end(), crange));
          TypeNode arg_type = TypeNode::fromType(
              static_cast<SelectorType>(dt[k][j].getType()).getDomain());
          ops[i_selType].push_back(dt[k][j].getSelector());
          cnames[i_selType].push_back(dt[k][j].getName());
          cargs[i_selType].push_back(std::vector<Type>());
          Assert(type_to_unres.find(arg_type) != type_to_unres.end());
          cargs[i_selType].back().push_back(type_to_unres[arg_type]);
          pcs[i_selType].push_back(nullptr);
          weights[i_selType].push_back(-1);
        }
        pcs[i].push_back(nullptr);
        weights[i].push_back(-1);
      }
    }else{
      Warning()
          << "Warning: No implementation for default Sygus grammar of type "
          << types[i] << std::endl;
    }
  }
  // make datatypes
  for (unsigned i = 0, size = types.size(); i < size; ++i)
  {
    Trace("sygus-grammar-def") << "...make datatype " << datatypes[i] << std::endl;
    datatypes[i].setSygus( types[i].toType(), bvl.toExpr(), true, true );
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>::iterator
        itexc = exc_cons.find(types[i]);
    std::map<TypeNode,
             std::unordered_set<Node, NodeHashFunction>>::const_iterator itinc =
        inc_cons.find(types[i]);
    for (unsigned j = 0, size = ops[i].size(); j < size; ++j)
    {
      // add the constructor if it is not excluded,
      // and it is in inc_cons, in case it is not empty
      Node opn = Node::fromExpr(ops[i][j]);
      Trace("sygus-grammar-def")
          << "...considering " << opn.toString() << " of kind " << opn.getKind()
          << " and of type " << opn.getType() << " and of kind of type "
          << opn.getType().getKind() << " of metakind " << opn.getMetaKind()
          << std::endl;
      if (itexc == exc_cons.end()
          || std::find(itexc->second.begin(), itexc->second.end(), opn)
                 == itexc->second.end())
      {
        Trace("sygus-grammar-def") << "......not excluded " << std::endl;
        if ((opn.isVar()) || (opn.getType().getKind() != kind::TYPE_CONSTANT)
            || (itinc == inc_cons.end())
            || (std::find(itinc->second.begin(), itinc->second.end(), opn)
                != itinc->second.end()))
        {
          Trace("sygus-grammar-def") << "......included " << std::endl;
          datatypes[i].addSygusConstructor(
              ops[i][j], cnames[i][j], cargs[i][j], pcs[i][j], weights[i][j]);
        }
      }
    }
    Trace("sygus-grammar-def") << "...built datatype " << datatypes[i] << " ";
    //set start index if applicable
    if( types[i]==range ){
      startIndex = i;
    }
  }

  //------ make Boolean type
  TypeNode btype = nm->booleanType();
  datatypes.push_back(Datatype(dbname));
  ops.push_back(std::vector<Expr>());
  cnames.push_back(std::vector<std::string>());
  cargs.push_back(std::vector<std::vector<Type>>());
  pcs.push_back(std::vector<std::shared_ptr<SygusPrintCallback>>());
  weights.push_back(std::vector<int>());
  Trace("sygus-grammar-def") << "Make grammar for " << btype << " " << datatypes.back() << std::endl;
  //add variables
  for (unsigned i = 0, size = sygus_vars.size(); i < size; ++i)
  {
    if( sygus_vars[i].getType().isBoolean() ){
      std::stringstream ss;
      ss << sygus_vars[i];
      Trace("sygus-grammar-def") << "...add for variable " << ss.str() << std::endl;
      ops.back().push_back( sygus_vars[i].toExpr() );
      cnames.back().push_back(ss.str());
      cargs.back().push_back(std::vector<Type>());
      pcs.back().push_back(nullptr);
      // make boolean variables weight as non-nullary constructors
      weights.back().push_back(1);
    }
  }
  // add constants
  std::vector<Node> consts;
  mkSygusConstantsForType(btype, consts);
  for (unsigned i = 0, size = consts.size(); i < size; ++i)
  {
    std::stringstream ss;
    ss << consts[i];
    Trace("sygus-grammar-def") << "...add for constant " << ss.str()
                               << std::endl;
    ops.back().push_back(consts[i].toExpr());
    cnames.back().push_back(ss.str());
    cargs.back().push_back(std::vector<Type>());
    pcs.back().push_back(nullptr);
    weights.back().push_back(-1);
  }
  // add predicates for types
  for (unsigned i = 0, size = types.size(); i < size; ++i)
  {
    Trace("sygus-grammar-def") << "...add predicates for " << types[i] << std::endl;
    //add equality per type
    Kind k = EQUAL;
    Trace("sygus-grammar-def") << "...add for " << k << std::endl;
    ops.back().push_back(nm->operatorOf(k).toExpr());
    std::stringstream ss;
    ss << kindToString(k) << "_" << types[i];
    cnames.back().push_back(ss.str());
    cargs.back().push_back(std::vector<Type>());
    cargs.back().back().push_back(unres_types[i]);
    cargs.back().back().push_back(unres_types[i]);
    pcs.back().push_back(nullptr);
    weights.back().push_back(-1);
    // type specific predicates
    if (types[i].isReal())
    {
      Kind k = LEQ;
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      ops.back().push_back(nm->operatorOf(k).toExpr());
      cnames.back().push_back(kindToString(k));
      cargs.back().push_back(std::vector<Type>());
      cargs.back().back().push_back(unres_types[i]);
      cargs.back().back().push_back(unres_types[i]);
      pcs.back().push_back(nullptr);
      weights.back().push_back(-1);
    }
    else if (types[i].isBitVector())
    {
      Kind k = BITVECTOR_ULT;
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      ops.back().push_back(nm->operatorOf(k).toExpr());
      cnames.back().push_back(kindToString(k));
      cargs.back().push_back(std::vector<Type>());
      cargs.back().back().push_back(unres_types[i]);
      cargs.back().back().push_back(unres_types[i]);
      pcs.back().push_back(nullptr);
      weights.back().push_back(-1);
    }
    else if (types[i].isDatatype())
    {
      //add for testers
      Trace("sygus-grammar-def") << "...add for testers" << std::endl;
      const Datatype& dt = types[i].getDatatype();
      for (unsigned k = 0, size_k = dt.getNumConstructors(); k < size_k; ++k)
      {
        Trace("sygus-grammar-def") << "...for " << dt[k].getTesterName() << std::endl;
        ops.back().push_back(dt[k].getTester());
        cnames.back().push_back(dt[k].getTesterName());
        cargs.back().push_back(std::vector<Type>());
        cargs.back().back().push_back(unres_types[i]);
        pcs.back().push_back(nullptr);
        weights.back().push_back(-1);
      }
    }
  }
  // add Boolean connectives, if not in a degenerate case of (recursively)
  // having only constant constructors
  if (ops.back().size() > consts.size())
  {
    for (unsigned i = 0; i < 4; i++)
    {
      Kind k = i == 0 ? NOT : (i == 1 ? AND : (i == 2 ? OR : ITE));
      // TODO #1935 ITEs are added to Boolean grammars so that we can infer
      // unification strategies. We can do away with this if we can infer
      // unification strategies from and/or/not
      if (k == ITE && !options::sygusUnif())
      {
        continue;
      }
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      ops.back().push_back(nm->operatorOf(k).toExpr());
      cnames.back().push_back(kindToString(k));
      cargs.back().push_back(std::vector<Type>());
      cargs.back().back().push_back(unres_bt);
      if (k != NOT)
      {
        cargs.back().back().push_back(unres_bt);
        if (k == ITE)
        {
          cargs.back().back().push_back(unres_bt);
        }
      }
      pcs.back().push_back(nullptr);
      weights.back().push_back(-1);
    }
  }
  if( range==btype ){
    startIndex = datatypes.size()-1;
  }
  Trace("sygus-grammar-def") << "...make datatype " << datatypes.back() << std::endl;
  datatypes.back().setSygus( btype.toType(), bvl.toExpr(), true, true );
  for (unsigned i = 0, size = ops.back().size(); i < size; ++i)
  {
    datatypes.back().addSygusConstructor(ops.back()[i],
                                         cnames.back()[i],
                                         cargs.back()[i],
                                         pcs.back()[i],
                                         weights.back()[i]);
  }
  Trace("sygus-grammar-def") << "...built datatype " << datatypes.back() << " ";
  Trace("sygus-grammar-def") << "...finished make default grammar for " << fun << " " << range << std::endl;
  // make first datatype be the top level datatype
  if( startIndex>0 ){
    Datatype tmp_dt = datatypes[0];
    datatypes[0] = datatypes[startIndex];
    datatypes[startIndex] = tmp_dt;
  }
}

TypeNode CegGrammarConstructor::mkSygusDefaultType(
    TypeNode range,
    Node bvl,
    const std::string& fun,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& extra_cons,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>&
        exclude_cons,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>&
        include_cons,
    std::unordered_set<Node, NodeHashFunction>& term_irrelevant)
{
  Trace("sygus-grammar-def") << "*** Make sygus default type " << range << ", make datatypes..." << std::endl;
  for (std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>::iterator
           it = extra_cons.begin();
       it != extra_cons.end();
       ++it)
  {
    Trace("sygus-grammar-def") << "    ...using " << it->second.size() << " extra constants for " << it->first << std::endl;
  }
  std::set<Type> unres;
  std::vector< CVC4::Datatype > datatypes;
  mkSygusDefaultGrammar(range,
                        bvl,
                        fun,
                        extra_cons,
                        exclude_cons,
                        include_cons,
                        term_irrelevant,
                        datatypes,
                        unres);
  Trace("sygus-grammar-def")  << "...made " << datatypes.size() << " datatypes, now make mutual datatype types..." << std::endl;
  Assert( !datatypes.empty() );
  std::vector<DatatypeType> types =
      NodeManager::currentNM()->toExprManager()->mkMutualDatatypeTypes(
          datatypes, unres, ExprManager::DATATYPE_FLAG_PLACEHOLDER);
  Assert( types.size()==datatypes.size() );
  return TypeNode::fromType( types[0] );
}

TypeNode CegGrammarConstructor::mkSygusTemplateTypeRec( Node templ, Node templ_arg, TypeNode templ_arg_sygus_type, Node bvl,
                                              const std::string& fun, unsigned& tcount ) {
  if( templ==templ_arg ){
    //Assert( templ_arg.getType()==sygusToBuiltinType( templ_arg_sygus_type ) );
    return templ_arg_sygus_type;
  }else{
    tcount++;
    std::set<Type> unres;
    std::vector< CVC4::Datatype > datatypes;
    std::stringstream ssd;
    ssd << fun << "_templ_" << tcount;
    std::string dbname = ssd.str();
    datatypes.push_back(Datatype(dbname));
    Node op;
    std::vector< Type > argTypes;
    if( templ.getNumChildren()==0 ){
      // TODO : can short circuit to this case when !TermUtil::containsTerm( templ, templ_arg )
      op = templ;
    }else{
      Assert( templ.hasOperator() );
      op = templ.getOperator();
      // make constructor taking arguments types from children
      for( unsigned i=0; i<templ.getNumChildren(); i++ ){
        //recursion depth bound by the depth of SyGuS template expressions (low)
        TypeNode tnc = mkSygusTemplateTypeRec( templ[i], templ_arg, templ_arg_sygus_type, bvl, fun, tcount );
        argTypes.push_back( tnc.toType() );
      }
    }
    std::stringstream ssdc;
    ssdc << fun << "_templ_cons_" << tcount;
    std::string cname = ssdc.str();
    // we have a single sygus constructor that encodes the template
    datatypes.back().addSygusConstructor( op.toExpr(), cname, argTypes );
    datatypes.back().setSygus( templ.getType().toType(), bvl.toExpr(), true, true );
    std::vector<DatatypeType> types =
        NodeManager::currentNM()->toExprManager()->mkMutualDatatypeTypes(
            datatypes, unres, ExprManager::DATATYPE_FLAG_PLACEHOLDER);
    Assert( types.size()==1 );
    return TypeNode::fromType( types[0] );
  }
}

TypeNode CegGrammarConstructor::mkSygusTemplateType( Node templ, Node templ_arg, TypeNode templ_arg_sygus_type, Node bvl,
                                                     const std::string& fun ) {
  unsigned tcount = 0;
  return mkSygusTemplateTypeRec( templ, templ_arg, templ_arg_sygus_type, bvl, fun, tcount );
}

Node CegGrammarConstructor::getSygusVarList(Node f)
{
  Node sfvl = f.getAttribute(SygusSynthFunVarListAttribute());
  if (sfvl.isNull() && f.getType().isFunction())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<TypeNode> argTypes = f.getType().getArgTypes();
    // make default variable list if none was specified by input
    std::vector<Node> bvs;
    for (unsigned j = 0, size = argTypes.size(); j < size; j++)
    {
      std::stringstream ss;
      ss << "arg" << j;
      bvs.push_back(nm->mkBoundVar(ss.str(), argTypes[j]));
    }
    sfvl = nm->mkNode(BOUND_VAR_LIST, bvs);
    f.setAttribute(SygusSynthFunVarListAttribute(), sfvl);
  }
  return sfvl;
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
