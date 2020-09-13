/*********************                                                        */
/*! \file sygus_grammar_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for constructing inductive datatypes that correspond to
 ** grammars that encode syntactic restrictions for SyGuS.
 **/
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"

#include <stack>

#include "options/quantifiers_options.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_grammar_norm.h"
#include "theory/quantifiers/sygus/sygus_process_conj.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/strings/word.h"

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
      if (tn.isDatatype() && tn.getDType().isSygus())
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
    if (preGrammarType.isDatatype() && preGrammarType.getDType().isSygus())
    {
      sfvl = preGrammarType.getDType().getSygusVarList();
      tn = preGrammarType;
      // normalize type, if user-provided
      SygusGrammarNorm sygus_norm(d_qe);
      tn = sygus_norm.normalizeSygusType(tn, sfvl);
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

    std::map<Node, Node>::const_iterator itt = templates.find(sf);
    if( itt!=templates.end() ){
      Node templ = itt->second;
      std::map<Node, Node>::const_iterator itta = templates_arg.find(sf);
      Assert(itta != templates_arg.end());
      TNode templ_arg = itta->second;
      Assert(!templ_arg.isNull());
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
    const DType& dt = tn.getDType();
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
  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
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
        if (!cur.getType().isFunction())
        {
          // will make into an application of an evaluation function
          ret = nm->mkNode(DT_SYGUS_EVAL, children);
        }
        else
        {
          Assert(children.size() == 1);
          Node ef = children[0];
          // Otherwise, we are using the function-to-synthesize itself in a
          // higher-order setting. We must return the lambda term:
          //   lambda x1...xn. (DT_SYGUS_EVAL ef x1 ... xn)
          // where ef is the first order variable for the
          // function-to-synthesize.
          SygusTypeInfo& ti = tds->getTypeInfo(ef.getType());
          const std::vector<Node>& vars = ti.getVarList();
          Assert(!vars.empty());
          std::vector<Node> vs;
          for (const Node& v : vars)
          {
            vs.push_back(nm->mkBoundVar(v.getType()));
          }
          Node lvl = nm->mkNode(BOUND_VAR_LIST, vs);
          std::vector<Node> eargs;
          eargs.push_back(ef);
          eargs.insert(eargs.end(), vs.begin(), vs.end());
          ret = nm->mkNode(LAMBDA, lvl, nm->mkNode(DT_SYGUS_EVAL, eargs));
        }
      }
      else if (childChanged)
      {
        ret = nm->mkNode(ret_k, children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

TypeNode CegGrammarConstructor::mkUnresolvedType(const std::string& name,
                                                 std::set<TypeNode>& unres)
{
  TypeNode unresolved = NodeManager::currentNM()->mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER);
  unres.insert(unresolved);
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
  else if (type.isStringLike())
  {
    ops.push_back(strings::Word::mkEmptyWord(type));
    if (type.isString())  // string-only
    {
      // Dummy character "A". This is not necessary for sequences which
      // have the generic constructor seq.unit.
      ops.push_back(nm->mkConst(String("A")));
    }
  }
  else if (type.isArray() || type.isSet())
  {
    // generate constant array over the first element of the constituent type
    Node c = type.mkGroundTerm();
    ops.push_back(c);
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
        const DType& dt = range.getDType();
        for (unsigned i = 0, size = dt.getNumConstructors(); i < size; ++i)
        {
          for (unsigned j = 0, size_args = dt[i].getNumArgs(); j < size_args;
               ++j)
          {
            TypeNode tn = dt[i][j].getRangeType();
            collectSygusGrammarTypesFor(tn, types);
          }
        }
      }
      else if (range.isArray())
      {
        // add index and constituent type
        collectSygusGrammarTypesFor(range.getArrayIndexType(), types);
        collectSygusGrammarTypesFor(range.getArrayConstituentType(), types);
      }
      else if (range.isSet())
      {
        collectSygusGrammarTypesFor(range.getSetElementType(), types);
      }
      else if (range.isStringLike())
      {
        // theory of strings shares the integer type
        TypeNode intType = NodeManager::currentNM()->integerType();
        collectSygusGrammarTypesFor(intType,types);
        if (range.isSequence())
        {
          collectSygusGrammarTypesFor(range.getSequenceElementType(), types);
        }
      }
      else if (range.isFunction())
      {
        std::vector<TypeNode> atypes = range.getArgTypes();
        for (unsigned i = 0, ntypes = atypes.size(); i < ntypes; i++)
        {
          collectSygusGrammarTypesFor(atypes[i], types);
        }
        collectSygusGrammarTypesFor(range.getRangeType(), types);
      }
    }
  }
}

bool CegGrammarConstructor::isHandledType(TypeNode t)
{
  std::vector<TypeNode> types;
  collectSygusGrammarTypesFor(t, types);
  for (const TypeNode& tn : types)
  {
    if (tn.isSort() || tn.isFloatingPoint())
    {
      return false;
    }
  }
  return true;
}

Node CegGrammarConstructor::createLambdaWithZeroArg(
    Kind k, TypeNode bArgType)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> opLArgs;
  std::vector<Expr> opLArgsExpr;
  // get the builtin type
  opLArgs.push_back(nm->mkBoundVar(bArgType));
  opLArgsExpr.push_back(opLArgs.back().toExpr());
  // build zarg
  Node zarg;
  Assert(bArgType.isReal() || bArgType.isBitVector());
  if (bArgType.isReal())
  {
    zarg = nm->mkConst(Rational(0));
  }
  else
  {
    unsigned size = bArgType.getBitVectorSize();
    zarg = bv::utils::mkZero(size);
  }
  Node body = nm->mkNode(k, zarg, opLArgs.back());
  // create operator
  Node op = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, opLArgs), body);
  Trace("sygus-grammar-def") << "\t...building lambda op " << op << "\n";
  return op;
}

void CegGrammarConstructor::mkSygusDefaultGrammar(
    TypeNode range,
    Node bvl,
    const std::string& fun,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& extra_cons,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>&
        exclude_cons,
    const std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>&
        include_cons,
    std::unordered_set<Node, NodeHashFunction>& term_irrelevant,
    std::vector<SygusDatatypeGenerator>& sdts,
    std::set<TypeNode>& unres)
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
  // index of top datatype, i.e. the datatype for the range type
  int startIndex = -1;
  std::map<TypeNode, TypeNode> sygus_to_builtin;

  std::vector<TypeNode> types;
  // Collect connected types for each of the variables.
  for (unsigned i = 0, size = sygus_vars.size(); i < size; ++i)
  {
    TypeNode tni = sygus_vars[i].getType();
    collectSygusGrammarTypesFor(tni, types);
  }
  // collect connected types to range
  collectSygusGrammarTypesFor(range, types);

  // create placeholder for boolean type (kept apart since not collected)

  // create placeholders for collected types
  std::vector<TypeNode> unres_types;
  std::map<TypeNode, TypeNode> type_to_unres;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>::const_iterator
      itc;
  // maps types to the index of its "any term" grammar construction
  std::map<TypeNode, std::pair<unsigned, bool>> typeToGAnyTerm;
  options::SygusGrammarConsMode sgcm = options::sygusGrammarConsMode();
  for (unsigned i = 0, size = types.size(); i < size; ++i)
  {
    std::stringstream ss;
    ss << fun << "_" << types[i];
    std::string dname = ss.str();
    sdts.push_back(SygusDatatypeGenerator(dname));
    itc = exclude_cons.find(types[i]);
    if (itc != exclude_cons.end())
    {
      sdts.back().d_exclude_cons = itc->second;
    }
    itc = include_cons.find(types[i]);
    if (itc != include_cons.end())
    {
      sdts.back().d_include_cons = itc->second;
    }
    //make unresolved type
    TypeNode unres_t = mkUnresolvedType(dname, unres);
    unres_types.push_back(unres_t);
    type_to_unres[types[i]] = unres_t;
    sygus_to_builtin[unres_t] = types[i];
  }
  // make Boolean type
  std::stringstream ssb;
  ssb << fun << "_Bool";
  std::string dbname = ssb.str();
  sdts.push_back(SygusDatatypeGenerator(dbname));
  unsigned boolIndex = types.size();
  TypeNode bool_type = nm->booleanType();
  TypeNode unres_bt = mkUnresolvedType(ssb.str(), unres);
  types.push_back(bool_type);
  unres_types.push_back(unres_bt);
  type_to_unres[bool_type] = unres_bt;
  sygus_to_builtin[unres_bt] = bool_type;

  // We ensure an ordering on types such that parametric types are processed
  // before their consitituents. Since parametric types were added before their
  // arguments in collectSygusGrammarTypesFor above, we will construct the
  // sygus grammars by iterating on types in reverse order. This ensures
  // that we know all constructors coming from other types (e.g. select(A,i))
  // by the time we process the type. We start with types.size()-2, since
  // we construct the grammar for the Boolean type last.
  for (int i = (types.size() - 2); i >= 0; --i)
  {
    Trace("sygus-grammar-def") << "Make grammar for " << types[i] << " "
                               << unres_types[i] << std::endl;
    TypeNode unres_t = unres_types[i];
    options::SygusGrammarConsMode tsgcm = sgcm;
    if (tsgcm == options::SygusGrammarConsMode::ANY_TERM
        || tsgcm == options::SygusGrammarConsMode::ANY_TERM_CONCISE)
    {
      // If the type does not support any term, we do any constant instead.
      // We also fall back on any constant construction if the type has no
      // constructors at this point (e.g. it simply encodes all constants).
      if (!types[i].isReal())
      {
        tsgcm = options::SygusGrammarConsMode::ANY_CONST;
      }
      else
      {
        // Add a placeholder for the "any term" version of this datatype, to be
        // constructed later.
        std::stringstream ssat;
        ssat << sdts[i].d_sdt.getName() << "_any_term";
        sdts.push_back(SygusDatatypeGenerator(ssat.str()));
        TypeNode unresAnyTerm = mkUnresolvedType(ssat.str(), unres);
        unres_types.push_back(unresAnyTerm);
        // set tracking information for later addition at boolean type.
        std::pair<unsigned, bool> p(sdts.size() - 1, false);
        typeToGAnyTerm[types[i]] = p;
      }
    }
    Trace("sygus-grammar-def")
        << "Grammar constructor mode for this type is " << tsgcm << std::endl;
    //add variables
    for (const Node& sv : sygus_vars)
    {
      TypeNode svt = sv.getType();
      if (svt == types[i])
      {
        std::stringstream ss;
        ss << sv;
        Trace("sygus-grammar-def")
            << "...add for variable " << ss.str() << std::endl;
        std::vector<TypeNode> cargsEmpty;
        sdts[i].addConstructor(sv, ss.str(), cargsEmpty);
      }
      else if (svt.isFunction() && svt.getRangeType() == types[i])
      {
        // We add an APPLY_UF for all function whose return type is this type
        // whose argument types are the other sygus types we are constructing.
        std::vector<TypeNode> argTypes = svt.getArgTypes();
        std::vector<TypeNode> stypes;
        for (unsigned k = 0, ntypes = argTypes.size(); k < ntypes; k++)
        {
          unsigned index =
              std::distance(types.begin(),
                            std::find(types.begin(), types.end(), argTypes[k]));
          stypes.push_back(unres_types[index]);
        }
        std::stringstream ss;
        ss << "apply_" << sv;
        sdts[i].addConstructor(sv, ss.str(), stypes);
      }
    }
    //add constants
    std::vector<Node> consts;
    mkSygusConstantsForType(types[i], consts);
    if (tsgcm == options::SygusGrammarConsMode::ANY_CONST)
    {
      // Use the any constant constructor. Notice that for types that don't
      // have constants (e.g. uninterpreted or function types), we don't add
      // this constructor.
      if (!consts.empty())
      {
        sdts[i].d_sdt.addAnyConstantConstructor(types[i]);
      }
    }
    else
    {
      std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>::iterator
          itec = extra_cons.find(types[i]);
      if (itec != extra_cons.end())
      {
        for (std::unordered_set<Node, NodeHashFunction>::iterator set_it =
                 itec->second.begin();
             set_it != itec->second.end();
             ++set_it)
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
        Trace("sygus-grammar-def")
            << "...add for constant " << ss.str() << std::endl;
        std::vector<TypeNode> cargsEmpty;
        sdts[i].addConstructor(consts[j], ss.str(), cargsEmpty);
      }
    }

    if (types[i].isReal())
    {
      // Add PLUS, MINUS
      Kind kinds[2] = {PLUS, MINUS};
      for (const Kind kind : kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
        std::vector<TypeNode> cargsOp;
        cargsOp.push_back(unres_t);
        cargsOp.push_back(unres_t);
        sdts[i].addConstructor(kind, cargsOp);
      }
      if (!types[i].isInteger())
      {
        Trace("sygus-grammar-def")
            << "  ...create auxiliary Positive Integers grammar\n";
        // Creating type for positive integers. Notice we can't use the any
        // constant constructor here, since it admits zero.
        std::stringstream ss;
        ss << fun << "_PosInt";
        std::string pos_int_name = ss.str();
        // make unresolved type
        TypeNode unresPosInt = mkUnresolvedType(pos_int_name, unres);
        unres_types.push_back(unresPosInt);
        // make data type for positive constant integers
        sdts.push_back(SygusDatatypeGenerator(pos_int_name));
        /* Add operator 1 */
        Trace("sygus-grammar-def") << "\t...add for 1 to Pos_Int\n";
        std::vector<TypeNode> cargsEmpty;
        sdts.back().addConstructor(nm->mkConst(Rational(1)), "1", cargsEmpty);
        /* Add operator PLUS */
        Kind kind = PLUS;
        Trace("sygus-grammar-def") << "\t...add for PLUS to Pos_Int\n";
        std::vector<TypeNode> cargsPlus;
        cargsPlus.push_back(unresPosInt);
        cargsPlus.push_back(unresPosInt);
        sdts.back().addConstructor(kind, cargsPlus);
        sdts.back().d_sdt.initializeDatatype(types[i], bvl, true, true);
        Trace("sygus-grammar-def")
            << "  ...built datatype " << sdts.back().d_sdt.getDatatype() << " ";
        /* Adding division at root */
        kind = DIVISION;
        Trace("sygus-grammar-def") << "\t...add for " << kind << std::endl;
        std::vector<TypeNode> cargsDiv;
        cargsDiv.push_back(unres_t);
        cargsDiv.push_back(unresPosInt);
        sdts[i].addConstructor(kind, cargsDiv);
      }
    }
    else if (types[i].isBitVector())
    {
      // unary apps
      std::vector<Kind> un_kinds = {BITVECTOR_NOT, BITVECTOR_NEG};
      std::vector<TypeNode> cargsUnary;
      cargsUnary.push_back(unres_t);
      for (const Kind kind : un_kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
        sdts[i].addConstructor(kind, cargsUnary);
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
      std::vector<TypeNode> cargsBinary;
      cargsBinary.push_back(unres_t);
      cargsBinary.push_back(unres_t);
      for (const Kind kind : bin_kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
        sdts[i].addConstructor(kind, cargsBinary);
      }
    }
    else if (types[i].isStringLike())
    {
      // concatenation
      std::vector<TypeNode> cargsBinary;
      cargsBinary.push_back(unres_t);
      cargsBinary.push_back(unres_t);
      sdts[i].addConstructor(STRING_CONCAT, cargsBinary);
      // length
      TypeNode intType = nm->integerType();
      Assert(std::find(types.begin(), types.end(), intType) != types.end());
      unsigned i_intType = std::distance(
          types.begin(),
          std::find(types.begin(),
                    types.end(),
                    intType));
      std::vector<TypeNode> cargsLen;
      cargsLen.push_back(unres_t);
      sdts[i_intType].addConstructor(STRING_LENGTH, cargsLen);
      if (types[i].isSequence())
      {
        TypeNode etype = types[i].getSequenceElementType();
        // retrieve element unresolved type
        Assert(type_to_unres.find(etype) != type_to_unres.end());
        TypeNode unresElemType = type_to_unres[etype];

        Trace("sygus-grammar-def") << "...add for seq.unit" << std::endl;
        std::vector<TypeNode> cargsSeqUnit;
        cargsSeqUnit.push_back(unresElemType);
        sdts[i].addConstructor(SEQ_UNIT, cargsSeqUnit);
      }
    }
    else if (types[i].isArray())
    {
      Trace("sygus-grammar-def")
          << "...building for array type " << types[i] << "\n";
      TypeNode indexType = types[i].getArrayIndexType();
      TypeNode elemType = types[i].getArrayConstituentType();
      Trace("sygus-grammar-def")
          << "......finding unres type for index type " << indexType << "\n";
      // retrieve index and constituent unresolved types
      Assert(type_to_unres.find(indexType) != type_to_unres.end());
      TypeNode unres_indexType = type_to_unres[indexType];
      Assert(std::find(types.begin(), types.end(), elemType) != types.end());
      // must get this index since we add to sdt[i_constituentType] below.
      unsigned i_constituentType = std::distance(
          types.begin(), std::find(types.begin(), types.end(), elemType));
      TypeNode unres_constituentType = unres_types[i_constituentType];
      // add (store ArrayType IndexType ConstituentType)
      Trace("sygus-grammar-def") << "...add for STORE\n";

      std::vector<TypeNode> cargsStore;
      cargsStore.push_back(unres_t);
      cargsStore.push_back(unres_indexType);
      cargsStore.push_back(unres_constituentType);
      sdts[i].addConstructor(STORE, cargsStore);
      // add to constituent type : (select ArrayType IndexType)
      Trace("sygus-grammar-def") << "...add select for constituent type"
                                 << unres_constituentType << "\n";
      std::vector<TypeNode> cargsSelect;
      cargsSelect.push_back(unres_t);
      cargsSelect.push_back(unres_indexType);
      sdts[i_constituentType].addConstructor(SELECT, cargsSelect);
    }
    else if (types[i].isSet())
    {
      TypeNode etype = types[i].getSetElementType();
      // retrieve element unresolved type
      Assert(type_to_unres.find(etype) != type_to_unres.end());
      TypeNode unresElemType = type_to_unres[etype];

      // add for singleton
      Trace("sygus-grammar-def") << "...add for singleton" << std::endl;
      std::vector<TypeNode> cargsSingleton;
      cargsSingleton.push_back(unresElemType);
      sdts[i].addConstructor(SINGLETON, cargsSingleton);

      // add for union, difference, intersection
      std::vector<Kind> bin_kinds = {UNION, INTERSECTION, SETMINUS};
      std::vector<TypeNode> cargsBinary;
      cargsBinary.push_back(unres_t);
      cargsBinary.push_back(unres_t);
      for (const Kind kind : bin_kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
        sdts[i].addConstructor(kind, cargsBinary);
      }
    }
    else if (types[i].isDatatype())
    {
      Trace("sygus-grammar-def") << "...add for constructors" << std::endl;
      const DType& dt = types[i].getDType();
      for (unsigned l = 0, size_l = dt.getNumConstructors(); l < size_l; ++l)
      {
        Trace("sygus-grammar-def") << "...for " << dt[l].getName() << std::endl;
        Node cop = dt[l].getConstructor();
        if (dt[l].getNumArgs() == 0)
        {
          // Nullary constructors are interpreted as terms, not operators.
          // Thus, we apply them to no arguments here.
          cop = nm->mkNode(APPLY_CONSTRUCTOR, cop);
        }
        std::vector<TypeNode> cargsCons;
        Trace("sygus-grammar-def") << "...add for selectors" << std::endl;
        for (unsigned j = 0, size_j = dt[l].getNumArgs(); j < size_j; ++j)
        {
          Trace("sygus-grammar-def")
              << "...for " << dt[l][j].getName() << std::endl;
          TypeNode crange = dt[l][j].getRangeType();
          Assert(type_to_unres.find(crange) != type_to_unres.end());
          cargsCons.push_back(type_to_unres[crange]);
          // add to the selector type the selector operator

          Assert(std::find(types.begin(), types.end(), crange) != types.end());
          unsigned i_selType = std::distance(
              types.begin(), std::find(types.begin(), types.end(), crange));
          TypeNode arg_type = dt[l][j].getType();
          arg_type = arg_type.getSelectorDomainType();
          Assert(type_to_unres.find(arg_type) != type_to_unres.end());
          std::vector<TypeNode> cargsSel;
          cargsSel.push_back(type_to_unres[arg_type]);
          Node sel = dt[l][j].getSelector();
          sdts[i_selType].addConstructor(sel, dt[l][j].getName(), cargsSel);
        }
        sdts[i].addConstructor(cop, dt[l].getName(), cargsCons);
      }
    }
    else if (types[i].isSort() || types[i].isFunction())
    {
      // do nothing
    }
    else
    {
      Warning()
          << "Warning: No implementation for default Sygus grammar of type "
          << types[i] << std::endl;
    }

    if (sdts[i].d_sdt.getNumConstructors() == 0)
    {
      // if there are no constructors yet by this point, we cannot make
      // datatype, which can happen e.g. for unimplemented types
      // that have no variables in the argument list of the
      // function-to-synthesize.
      std::stringstream ss;
      ss << "Cannot make default grammar for " << types[i];
      throw LogicException(ss.str());
    }

    // always add ITE
    Kind k = ITE;
    Trace("sygus-grammar-def") << "...add for " << k << std::endl;
    std::vector<TypeNode> cargsIte;
    cargsIte.push_back(unres_bt);
    cargsIte.push_back(unres_t);
    cargsIte.push_back(unres_t);
    sdts[i].addConstructor(k, cargsIte);
  }
  std::map<TypeNode, std::pair<unsigned, bool>>::iterator itgat;
  // initialize the datatypes (except for the last one, reserved for Bool)
  for (unsigned i = 0, size = types.size() - 1; i < size; ++i)
  {
    sdts[i].d_sdt.initializeDatatype(types[i], bvl, true, true);
    Trace("sygus-grammar-def")
        << "...built datatype " << sdts[i].d_sdt.getDatatype() << " ";
    //set start index if applicable
    if( types[i]==range ){
      startIndex = i;
    }
    itgat = typeToGAnyTerm.find(types[i]);
    if (itgat == typeToGAnyTerm.end())
    {
      // no any term datatype, we are done
      continue;
    }
    unsigned iat = itgat->second.first;
    Trace("sygus-grammar-def")
        << "Build any-term datatype for " << types[i] << "..." << std::endl;

    // for now, only real has any term construction
    Assert(types[i].isReal());
    // We have initialized the given type sdts[i], which should now contain
    // a constructor for each relevant arithmetic term/variable. We now
    // construct a sygus datatype of one of the following two forms.
    //
    // (1) The "sum of monomials" grammar:
    //   I -> C*x1 | ... | C*xn | C | I + I | ite( B, I, I )
    //   C -> any_constant
    // where x1, ..., xn are the arithmetic terms/variables (non-arithmetic
    // builtin operators) terms we have considered thus far.
    //
    // (2) The "polynomial" grammar:
    //   I -> C*x1 + ... + C*xn + C | ite( B, I, I )
    //   C -> any_constant
    //
    // The advantage of the first is that it allows for sums of terms
    // constructible from other theories that share sorts with arithmetic, e.g.
    //   c1*str.len(x) + c2*str.len(y)
    // The advantage of the second is that there are fewer constructors, and
    // hence may be more efficient.

    // Before proceeding, we build the any constant datatype
    Trace("sygus-grammar-def")
        << "Build any-constant datatype for " << types[i] << std::endl;
    std::stringstream ss;
    ss << fun << "_AnyConst";
    // Make sygus datatype for any constant.
    TypeNode unresAnyConst = mkUnresolvedType(ss.str(), unres);
    unres_types.push_back(unresAnyConst);
    sdts.push_back(SygusDatatypeGenerator(ss.str()));
    sdts.back().d_sdt.addAnyConstantConstructor(types[i]);
    sdts.back().d_sdt.initializeDatatype(types[i], bvl, true, true);

    // Now get the reference to the sygus datatype at position i (important that
    // this comes after the modification to sdts above, which may modify
    // the references).
    const SygusDatatype& sdti = sdts[i].d_sdt;
    // whether we will use the polynomial grammar
    bool polynomialGrammar =
        sgcm == options::SygusGrammarConsMode::ANY_TERM_CONCISE;
    // A set of constructor indices that will be used in the overall sum we
    // are constructing; indices of constructors corresponding to builtin
    // arithmetic operators will be excluded from this set.
    std::set<unsigned> useConstructor;
    Trace("sygus-grammar-def")
        << "Look at operators, num = " << sdti.getNumConstructors() << "..."
        << std::endl;
    for (unsigned k = 0, ncons = sdti.getNumConstructors(); k < ncons; k++)
    {
      const SygusDatatypeConstructor& sdc = sdti.getConstructor(k);
      Node sop = sdc.d_op;
      bool isBuiltinArithOp = (sop.getKind() == CONST_RATIONAL);
      bool hasExternalType = false;
      for (unsigned j = 0, nargs = sdc.d_argTypes.size(); j < nargs; j++)
      {
        // Since we are accessing the fields of the sygus datatype, this
        // already corresponds to the correct sygus datatype type.
        TypeNode atype = sdc.d_argTypes[j];
        if (atype == unres_types[i])
        {
          // It is recursive, thus is (likely) a builtin arithmetic operator
          // as constructed above. It may also be an operator from another
          // theory that has both an arithmetic return type and an arithmetic
          // argument (e.g. str.indexof). In either case, we ignore it for the
          // sake of well-foundedness.
          isBuiltinArithOp = true;
          break;
        }
        else if (atype != unres_bt)
        {
          // It is an external type. This is the case of an operator of another
          // theory whose return type is arithmetic, e.g. select.
          hasExternalType = true;
        }
      }
      if (!isBuiltinArithOp)
      {
        useConstructor.insert(k);
        if (hasExternalType)
        {
          // If we have an external term in the sum, e.g. select(A,i), we
          // cannot use a fixed polynomial template. As mentioned above, we
          // cannot use a polynomial grammar when external terms (those built
          // from the symbols of other theories) are involved.
          Trace("sygus-grammar-def")
              << "Cannot use polynomial grammar due to " << sop << std::endl;
          polynomialGrammar = false;
        }
      }
    }
    Trace("sygus-grammar-def")
        << "Done look at operators, num = " << sdti.getNumConstructors()
        << "..." << std::endl;
    // we have now decided whether we will use sum-of-monomials or polynomial
    // Now, extract the terms and set up the polynomial
    std::vector<Node> sumChildren;
    std::vector<TypeNode> cargsAnyTerm;
    std::vector<Node> lambdaVars;
    for (unsigned k = 0, ncons = sdti.getNumConstructors(); k < ncons; k++)
    {
      Trace("sygus-grammar-def") << "Process #" << k << std::endl;
      if (useConstructor.find(k) == useConstructor.end())
      {
        Trace("sygus-grammar-def") << "Skip variable #" << k << std::endl;
        // builtin operator, as computed above, we skip
        continue;
      }
      const SygusDatatypeConstructor& sdc = sdti.getConstructor(k);
      Node sop = sdc.d_op;
      Trace("sygus-grammar-def")
          << "Monomial variable: #" << k << ": " << sop << std::endl;
      unsigned nargs = sdc.d_argTypes.size();
      std::vector<TypeNode> opCArgs;
      std::vector<Node> opLArgs;
      if (nargs > 0)
      {
        // Take its arguments. For example, if we are building a polynomial
        // over str.len(s), then our any term constructor would include an
        // argument of string type, e.g.:
        //   (lambda s : String, c1, c2 : Int. c1*len(s) + c2)
        for (unsigned j = 0; j < nargs; j++)
        {
          // this is already corresponds to the correct sygus datatype type
          TypeNode atype = sdc.d_argTypes[j];
          opCArgs.push_back(atype);
          // get the builtin type
          TypeNode btype = sygus_to_builtin[atype];
          opLArgs.push_back(nm->mkBoundVar(btype));
        }
        // Do beta reduction on the operator so that its arguments match the
        // fresh variables of the lambda (op) we are constructing below.
        sop = datatypes::utils::mkSygusTerm(sop, opLArgs);
        sop = Rewriter::rewrite(sop);
      }
      opCArgs.push_back(unresAnyConst);
      Node coeff = nm->mkBoundVar(types[i]);
      opLArgs.push_back(coeff);
      Node monomial = nm->mkNode(MULT, coeff, sop);
      if (polynomialGrammar)
      {
        // add the monomial c*t to the sum
        sumChildren.push_back(monomial);
        lambdaVars.insert(lambdaVars.end(), opLArgs.begin(), opLArgs.end());
        cargsAnyTerm.insert(cargsAnyTerm.end(), opCArgs.begin(), opCArgs.end());
      }
      else
      {
        Node op =
            nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, opLArgs), monomial);
        // add it as a constructor
        std::stringstream ssop;
        ssop << "monomial_" << sdc.d_name;
        // we use 0 as the weight, since this constructor should be seen as
        // a generalization of a non-Boolean variable (which has weight 0).
        // This ensures that e.g. ( c1*x >= 0 ) has the same weight as
        // ( x >= 0 ).
        sdts[iat].d_sdt.addConstructor(op, ssop.str(), opCArgs, 0);
      }
    }
    if (polynomialGrammar)
    {
      // add the constant
      Node coeff = nm->mkBoundVar(types[i]);
      lambdaVars.push_back(coeff);
      sumChildren.push_back(coeff);
      cargsAnyTerm.push_back(unresAnyConst);
      // make the sygus operator lambda X. c1*t1 + ... + cn*tn + c
      Assert(sumChildren.size() > 1);
      Node ops = nm->mkNode(PLUS, sumChildren);
      Node op = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, lambdaVars), ops);
      Trace("sygus-grammar-def") << "any term operator is " << op << std::endl;
      // make the any term datatype, add to back
      // do not consider the exclusion criteria of the generator
      // we use 0 as the weight, since this constructor should be seen as
      // a simultaneous generalization of set of non-Boolean variables.
      // This ensures that ( c1*x + c2*y >= 0 ) has the same weight as
      // e.g. ( x >= 0 ) or ( y >= 0 ).
      sdts[iat].d_sdt.addConstructor(op, "polynomial", cargsAnyTerm, 0);
      // mark that predicates should be of the form (= pol 0) and (<= pol 0)
      itgat->second.second = true;
    }
    else
    {
      // add the any constant constructor as a separate constructor
      sdts[iat].d_sdt.addAnyConstantConstructor(types[i]);
      // add plus
      std::vector<TypeNode> cargsPlus;
      cargsPlus.push_back(unres_types[iat]);
      cargsPlus.push_back(unres_types[iat]);
      sdts[iat].d_sdt.addConstructor(PLUS, cargsPlus);
    }
    // add the ITE, regardless of sum-of-monomials vs polynomial
    std::vector<TypeNode> cargsIte;
    cargsIte.push_back(unres_bt);
    cargsIte.push_back(unres_types[iat]);
    cargsIte.push_back(unres_types[iat]);
    sdts[iat].d_sdt.addConstructor(ITE, cargsIte);
    sdts[iat].d_sdt.initializeDatatype(types[i], bvl, true, true);
    Trace("sygus-grammar-def")
        << "...built datatype " << sdts[iat].d_sdt.getDatatype() << std::endl;
    // if the type is range, use it as the default type
    if (types[i] == range)
    {
      startIndex = iat;
    }
  }
  //------ make Boolean type
  SygusDatatypeGenerator& sdtBool = sdts[boolIndex];
  Trace("sygus-grammar-def") << "Make grammar for " << bool_type << std::endl;
  //add variables
  for (unsigned i = 0, size = sygus_vars.size(); i < size; ++i)
  {
    if( sygus_vars[i].getType().isBoolean() ){
      std::stringstream ss;
      ss << sygus_vars[i];
      Trace("sygus-grammar-def") << "...add for variable " << ss.str() << std::endl;
      std::vector<TypeNode> cargsEmpty;
      // make boolean variables weight as non-nullary constructors
      sdtBool.addConstructor(sygus_vars[i], ss.str(), cargsEmpty, 1);
    }
  }
  // add constants
  std::vector<Node> consts;
  mkSygusConstantsForType(bool_type, consts);
  for (unsigned i = 0, size = consts.size(); i < size; ++i)
  {
    std::stringstream ss;
    ss << consts[i];
    Trace("sygus-grammar-def") << "...add for constant " << ss.str()
                               << std::endl;
    std::vector<TypeNode> cargsEmpty;
    sdtBool.addConstructor(consts[i], ss.str(), cargsEmpty);
  }
  // add predicates for non-Boolean types
  for (unsigned i = 0, size = types.size() - 1; i < size; ++i)
  {
    if (!types[i].isFirstClass())
    {
      continue;
    }
    unsigned iuse = i;
    bool zarg = false;
    // use the any-term type if it exists and a zero argument if it is a
    // polynomial grammar
    itgat = typeToGAnyTerm.find(types[i]);
    if (itgat != typeToGAnyTerm.end())
    {
      iuse = itgat->second.first;
      zarg = itgat->second.second;
      Trace("sygus-grammar-def")
          << "...unres type " << unres_types[i] << " became "
          << (!zarg ? "polynomial " : "") << "unres anyterm type "
          << unres_types[iuse] << "\n";
    }
    Trace("sygus-grammar-def") << "...add predicates for " << types[i] << std::endl;
    //add equality per type
    Kind k = EQUAL;
    Trace("sygus-grammar-def") << "...add for " << k << std::endl;
    std::stringstream ss;
    std::vector<TypeNode> cargs;
    cargs.push_back(unres_types[iuse]);
    // if polynomial grammar, generate (= anyterm 0) and (<= anyterm 0) as the
    // predicates
    if (zarg)
    {
      Node op = createLambdaWithZeroArg(k, types[i]);
      ss << "eq_" << types[i];
      sdtBool.addConstructor(op, ss.str(), cargs);
    }
    else
    {
      ss << kindToString(k) << "_" << types[i];
      cargs.push_back(unres_types[iuse]);
      sdtBool.addConstructor(nm->operatorOf(k), ss.str(), cargs);
      cargs.pop_back();
    }
    // type specific predicates
    std::stringstream ssop;
    if (types[i].isReal())
    {
      Kind kind = LEQ;
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      if (zarg)
      {
        Node op = createLambdaWithZeroArg(kind, types[i]);
        ssop << "leq_" << types[i];
        sdtBool.addConstructor(op, ssop.str(), cargs);
      }
      else
      {
        cargs.push_back(unres_types[iuse]);
        sdtBool.addConstructor(kind, cargs);
      }
    }
    else if (types[i].isBitVector())
    {
      Kind kind = BITVECTOR_ULT;
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      if (zarg)
      {
        Node op = createLambdaWithZeroArg(kind, types[i]);
        ssop << "leq_" << types[i];
        sdtBool.addConstructor(op, ssop.str(), cargs);
      }
      else
      {
        cargs.push_back(unres_types[iuse]);
        sdtBool.addConstructor(kind, cargs);
      }
    }
    else if (types[i].isDatatype())
    {
      //add for testers
      Trace("sygus-grammar-def") << "...add for testers" << std::endl;
      const DType& dt = types[i].getDType();
      std::vector<TypeNode> cargsTester;
      cargsTester.push_back(unres_types[iuse]);
      for (unsigned kind = 0, size_k = dt.getNumConstructors(); kind < size_k;
           ++kind)
      {
        Trace("sygus-grammar-def")
            << "...for " << dt[kind].getTester() << std::endl;
        std::stringstream sst;
        sst << dt[kind].getTester();
        sdtBool.addConstructor(dt[kind].getTester(), sst.str(), cargsTester);
      }
    }
    else if (types[i].isSet())
    {
      // add for member
      TypeNode etype = types[i].getSetElementType();
      Assert(type_to_unres.find(etype) != type_to_unres.end());
      TypeNode unresElemType = type_to_unres[etype];
      std::vector<TypeNode> cargsMember;
      cargsMember.push_back(unresElemType);
      cargsMember.push_back(unres_types[iuse]);
      Trace("sygus-grammar-def") << "...for MEMBER" << std::endl;
      sdtBool.addConstructor(MEMBER, cargsMember);
    }
  }
  // add Boolean connectives, if not in a degenerate case of (recursively)
  // having only constant constructors
  Trace("sygus-grammar-def")
      << "...add Boolean connectives for unres type " << unres_bt << std::endl;
  if (sdtBool.d_sdt.getNumConstructors() > consts.size())
  {
    for (unsigned i = 0; i < 4; i++)
    {
      Kind k = i == 0 ? NOT : (i == 1 ? AND : (i == 2 ? OR : ITE));
      // TODO #1935 ITEs are added to Boolean grammars so that we can infer
      // unification strategies. We can do away with this if we can infer
      // unification strategies from and/or/not
      if (k == ITE && options::sygusUnifPi() == options::SygusUnifPiMode::NONE)
      {
        continue;
      }
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      std::vector<TypeNode> cargs;
      cargs.push_back(unres_bt);
      if (k != NOT)
      {
        cargs.push_back(unres_bt);
        if (k == ITE)
        {
          cargs.push_back(unres_bt);
        }
      }
      sdtBool.addConstructor(k, cargs);
    }
  }
  if (range == bool_type)
  {
    startIndex = boolIndex;
  }
  sdtBool.d_sdt.initializeDatatype(bool_type, bvl, true, true);
  Trace("sygus-grammar-def")
      << "...built datatype for Bool " << sdtBool.d_sdt.getDatatype() << " ";
  Trace("sygus-grammar-def") << "...finished make default grammar for " << fun << " " << range << std::endl;
  // make first datatype be the top level datatype
  if( startIndex>0 ){
    SygusDatatypeGenerator tmp_dt = sdts[0];
    sdts[0] = sdts[startIndex];
    sdts[startIndex] = tmp_dt;
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
  std::set<TypeNode> unres;
  std::vector<SygusDatatypeGenerator> sdts;
  mkSygusDefaultGrammar(range,
                        bvl,
                        fun,
                        extra_cons,
                        exclude_cons,
                        include_cons,
                        term_irrelevant,
                        sdts,
                        unres);
  // extract the datatypes from the sygus datatype generator objects
  std::vector<DType> datatypes;
  for (unsigned i = 0, ndts = sdts.size(); i < ndts; i++)
  {
    datatypes.push_back(sdts[i].d_sdt.getDatatype());
  }
  Trace("sygus-grammar-def")  << "...made " << datatypes.size() << " datatypes, now make mutual datatype types..." << std::endl;
  Assert(!datatypes.empty());
  std::vector<TypeNode> types = NodeManager::currentNM()->mkMutualDatatypeTypes(
      datatypes, unres, NodeManager::DATATYPE_FLAG_PLACEHOLDER);
  Trace("sygus-grammar-def") << "...finished" << std::endl;
  Assert(types.size() == datatypes.size());
  return types[0];
}

TypeNode CegGrammarConstructor::mkSygusTemplateTypeRec( Node templ, Node templ_arg, TypeNode templ_arg_sygus_type, Node bvl,
                                              const std::string& fun, unsigned& tcount ) {
  if( templ==templ_arg ){
    //Assert( templ_arg.getType()==sygusToBuiltinType( templ_arg_sygus_type ) );
    return templ_arg_sygus_type;
  }else{
    tcount++;
    std::set<TypeNode> unres;
    std::vector<SygusDatatype> sdts;
    std::stringstream ssd;
    ssd << fun << "_templ_" << tcount;
    std::string dbname = ssd.str();
    sdts.push_back(SygusDatatype(dbname));
    Node op;
    std::vector<TypeNode> argTypes;
    if( templ.getNumChildren()==0 ){
      // TODO : can short circuit to this case when !TermUtil::containsTerm( templ, templ_arg )
      op = templ;
    }else{
      Assert(templ.hasOperator());
      op = templ.getOperator();
      // make constructor taking arguments types from children
      for( unsigned i=0; i<templ.getNumChildren(); i++ ){
        //recursion depth bound by the depth of SyGuS template expressions (low)
        TypeNode tnc = mkSygusTemplateTypeRec( templ[i], templ_arg, templ_arg_sygus_type, bvl, fun, tcount );
        argTypes.push_back(tnc);
      }
    }
    std::stringstream ssdc;
    ssdc << fun << "_templ_cons_" << tcount;
    // we have a single sygus constructor that encodes the template
    sdts.back().addConstructor(op, ssdc.str(), argTypes);
    sdts.back().initializeDatatype(templ.getType(), bvl, true, true);
    // extract the datatypes from the sygus datatype objects
    std::vector<DType> datatypes;
    for (unsigned i = 0, ndts = sdts.size(); i < ndts; i++)
    {
      datatypes.push_back(sdts[i].getDatatype());
    }
    std::vector<TypeNode> types =
        NodeManager::currentNM()->mkMutualDatatypeTypes(
            datatypes, unres, NodeManager::DATATYPE_FLAG_PLACEHOLDER);
    Assert(types.size() == 1);
    return types[0];
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

CegGrammarConstructor::SygusDatatypeGenerator::SygusDatatypeGenerator(
    const std::string& name)
    : d_sdt(name)
{
}
void CegGrammarConstructor::SygusDatatypeGenerator::addConstructor(
    Node op,
    const std::string& name,
    const std::vector<TypeNode>& consTypes,
    int weight)
{
  if (shouldInclude(op))
  {
    d_sdt.addConstructor(op, name, consTypes, weight);
  }
}
void CegGrammarConstructor::SygusDatatypeGenerator::addConstructor(
    Kind k,
    const std::vector<TypeNode>& consTypes,
    int weight)
{
  NodeManager* nm = NodeManager::currentNM();
  addConstructor(nm->operatorOf(k), kindToString(k), consTypes, weight);
}
bool CegGrammarConstructor::SygusDatatypeGenerator::shouldInclude(Node op) const
{
  if (d_exclude_cons.find(op) != d_exclude_cons.end())
  {
    return false;
  }
  if (!d_include_cons.empty())
  {
    // special case, variables and terms of certain types are always included
    if (!op.isVar() && op.getType().getKind() == TYPE_CONSTANT)
    {
      if (d_include_cons.find(op) == d_include_cons.end())
      {
        return false;
      }
    }
  }
  return true;
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
