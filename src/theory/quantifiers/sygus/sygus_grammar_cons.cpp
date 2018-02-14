/*********************                                                        */
/*! \file sygus_grammar_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/sygus_process_conj.h"
#include "theory/quantifiers/sygus/sygus_grammar_norm.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegGrammarConstructor::CegGrammarConstructor(QuantifiersEngine* qe,
                                             CegConjecture* p)
    : d_qe(qe), d_parent(p), d_is_syntax_restricted(false), d_has_ite(true)
{
}

void CegGrammarConstructor::collectTerms( Node n, std::map< TypeNode, std::vector< Node > >& consts ){
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
          consts[tn].push_back( c );
        }
      }
      // recurse
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    }
  } while (!visit.empty());
}



Node CegGrammarConstructor::process( Node q, std::map< Node, Node >& templates, std::map< Node, Node >& templates_arg ) {
  // convert to deep embedding and finalize single invocation here
  // now, construct the grammar
  Trace("cegqi") << "CegConjecture : convert to deep embedding..." << std::endl;
  std::map< TypeNode, std::vector< Node > > extra_cons;
  if( options::sygusAddConstGrammar() ){
    Trace("cegqi") << "CegConjecture : collect constants..." << std::endl;
    collectTerms( q[1], extra_cons );
  }

  std::vector< Node > qchildren;
  std::map< Node, Node > synth_fun_vars;
  std::vector< Node > ebvl;
  Node qbody_subs = q[1];
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    Node sf = q[0][i];
    // v encodes the syntactic restrictions (via an inductive datatype) on sf
    // from the input
    Node v = sf.getAttribute(SygusSynthGrammarAttribute());
    Assert(!v.isNull());
    Node sfvl = sf.getAttribute(SygusSynthFunVarListAttribute());
    // sfvl may be null for constant synthesis functions
    Trace("cegqi-debug") << "...sygus var list associated with " << sf << " is " << sfvl << std::endl;

    TypeNode tn;
    std::stringstream ss;
    ss << sf;
    if( v.getType().isDatatype() && ((DatatypeType)v.getType().toType()).getDatatype().isSygus() ){
      tn = v.getType();
    }else{
      // check which arguments are irrelevant
      std::unordered_set<unsigned> arg_irrelevant;
      d_parent->getProcess()->getIrrelevantArgs(sf, arg_irrelevant);
      std::unordered_set<Node, NodeHashFunction> term_irrelevant;
      // convert to term
      for (std::unordered_set<unsigned>::iterator ita = arg_irrelevant.begin();
           ita != arg_irrelevant.end();
           ++ita)
      {
        unsigned arg = *ita;
        Assert(arg < sfvl.getNumChildren());
        term_irrelevant.insert(sfvl[arg]);
      }

      // make the default grammar
      tn = mkSygusDefaultType(
          v.getType(), sfvl, ss.str(), extra_cons, term_irrelevant);
    }
    // normalize type
    SygusGrammarNorm sygus_norm(d_qe);
    tn = sygus_norm.normalizeSygusType(tn, sfvl);
    // check if there is a template
    std::map< Node, Node >::iterator itt = templates.find( sf );
    if( itt!=templates.end() ){
      Node templ = itt->second;
      TNode templ_arg = templates_arg[sf];
      Assert( !templ_arg.isNull() );
      Trace("cegqi-debug") << "Template for " << sf << " is : " << templ << " with arg " << templ_arg << std::endl;
      // if there is a template for this argument, make a sygus type on top of it
      if( options::sygusTemplEmbedGrammar() ){
        Trace("cegqi-debug") << "  embed this template as a grammar..." << std::endl;
        tn = mkSygusTemplateType( templ, templ_arg, tn, sfvl, ss.str() );
      }else{
        // otherwise, apply it as a preprocessing pass 
        Trace("cegqi-debug") << "  apply this template as a substituion during preprocess..." << std::endl;
        std::vector< Node > schildren;
        std::vector< Node > largs;
        for( unsigned j=0; j<sfvl.getNumChildren(); j++ ){
          schildren.push_back( sfvl[j] );
          largs.push_back( NodeManager::currentNM()->mkBoundVar( sfvl[j].getType() ) );
        }
        std::vector< Node > subsfn_children;
        subsfn_children.push_back( sf );
        subsfn_children.insert( subsfn_children.end(), schildren.begin(), schildren.end() );
        Node subsfn = NodeManager::currentNM()->mkNode( kind::APPLY_UF, subsfn_children );
        TNode subsf = subsfn;
        Trace("cegqi-debug") << "  substitute arg : " << templ_arg << " -> " << subsf << std::endl;
        templ = templ.substitute( templ_arg, subsf );
        // substitute lambda arguments
        templ = templ.substitute( schildren.begin(), schildren.end(), largs.begin(), largs.end() );
        Node subsn = NodeManager::currentNM()->mkNode( kind::LAMBDA, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, largs ), templ );
        TNode var = sf;
        TNode subs = subsn;
        Trace("cegqi-debug") << "  substitute : " << var << " -> " << subs << std::endl;
        qbody_subs = qbody_subs.substitute( var, subs );
        Trace("cegqi-debug") << "  body is now : " << qbody_subs << std::endl;
      }
    }
    d_qe->getTermDatabaseSygus()->registerSygusType( tn );
    // check grammar restrictions
    if( !d_qe->getTermDatabaseSygus()->sygusToBuiltinType( tn ).isBoolean() ){
      if( !d_qe->getTermDatabaseSygus()->hasKind( tn, ITE ) ){
        d_has_ite = false;
      }
    }
    Assert( tn.isDatatype() );
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    Assert( dt.isSygus() );
    if( !dt.getSygusAllowAll() ){
      d_is_syntax_restricted = true;
    }

    // ev is the first-order variable corresponding to this synth fun
    std::stringstream ssf;
    ssf << "f" << sf;
    Node ev = NodeManager::currentNM()->mkBoundVar( ssf.str(), tn );
    ebvl.push_back( ev );
    synth_fun_vars[sf] = ev;
    Trace("cegqi") << "...embedding synth fun : " << sf << " -> " << ev << std::endl;
  }
  qchildren.push_back( NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, ebvl ) );
  if( qbody_subs!=q[1] ){
    Trace("cegqi") << "...rewriting : " << qbody_subs << std::endl;
    qbody_subs = Rewriter::rewrite( qbody_subs );
    Trace("cegqi") << "...got : " << qbody_subs << std::endl;
  }
  qchildren.push_back( convertToEmbedding( qbody_subs, synth_fun_vars ) );
  if( q.getNumChildren()==3 ){
    qchildren.push_back( q[2] );
  }
  return NodeManager::currentNM()->mkNode( kind::FORALL, qchildren );
}
  
Node CegGrammarConstructor::convertToEmbedding( Node n, std::map< Node, Node >& synth_fun_vars ){
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
      if( !op.isNull() ){
        std::map< Node, Node >::iterator its = synth_fun_vars.find( op );
        if( its!=synth_fun_vars.end() ){
          Assert( its->second.getType().isDatatype() );
          // will make into an application of an evaluation function
          const Datatype& dt = ((DatatypeType)its->second.getType().toType()).getDatatype();
          Assert( dt.isSygus() );
          children.push_back( Node::fromExpr( dt.getSygusEvaluationFunc() ) );
          children.push_back( its->second );
          childChanged = true;
          ret_k = kind::APPLY_UF;
        }
      }
      if( !childChanged ){
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
      if (childChanged) {
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

void CegGrammarConstructor::mkSygusConstantsForType( TypeNode type, std::vector<CVC4::Node>& ops ) {
  if (type.isReal())
  {
    ops.push_back(NodeManager::currentNM()->mkConst(Rational(0)));
    ops.push_back(NodeManager::currentNM()->mkConst(Rational(1)));
  }else if( type.isBitVector() ){
    unsigned sz = ((BitVectorType)type.toType()).getSize();
    BitVector bval0(sz, (unsigned int)0);
    ops.push_back( NodeManager::currentNM()->mkConst(bval0) );
    BitVector bval1(sz, (unsigned int)1);
    ops.push_back( NodeManager::currentNM()->mkConst(bval1) );
  }else if( type.isBoolean() ){
    ops.push_back(NodeManager::currentNM()->mkConst(true));
    ops.push_back(NodeManager::currentNM()->mkConst(false));
  }
  //TODO : others?
}

void CegGrammarConstructor::collectSygusGrammarTypesFor( TypeNode range, std::vector< TypeNode >& types, std::map< TypeNode, std::vector< DatatypeConstructorArg > >& sels ){
  if( !range.isBoolean() ){
    if( std::find( types.begin(), types.end(), range )==types.end() ){
      Trace("sygus-grammar-def") << "...will make grammar for " << range << std::endl;
      types.push_back( range );
      if( range.isDatatype() ){
        const Datatype& dt = ((DatatypeType)range.toType()).getDatatype();
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          for( unsigned j=0; j<dt[i].getNumArgs(); j++ ){
            TypeNode crange = TypeNode::fromType( ((SelectorType)dt[i][j].getType()).getRangeType() );
            sels[crange].push_back( dt[i][j] );
            collectSygusGrammarTypesFor( crange, types, sels );
          }
        }
      }
    }
  }
}

void CegGrammarConstructor::mkSygusDefaultGrammar(
    TypeNode range,
    Node bvl,
    const std::string& fun,
    std::map<TypeNode, std::vector<Node> >& extra_cons,
    std::unordered_set<Node, NodeHashFunction>& term_irrelevant,
    std::vector<CVC4::Datatype>& datatypes,
    std::set<Type>& unres)
{
  Trace("sygus-grammar-def") << "Construct default grammar for " << fun << " "
                             << range << std::endl;
  // collect the variables
  std::vector<Node> sygus_vars;
  if( !bvl.isNull() ){
    for( unsigned i=0; i<bvl.getNumChildren(); i++ ){
      if (term_irrelevant.find(bvl[i]) == term_irrelevant.end())
      {
        sygus_vars.push_back(bvl[i]);
      }
      else
      {
        Trace("sygus-grammar-def") << "...synth var " << bvl[i]
                                   << " has been marked irrelevant."
                                   << std::endl;
      }
    }
  }
  //if( !range.isBoolean() && !range.isInteger() && !range.isBitVector() && !range.isDatatype() ){
  //  parseError("No default grammar for type.");
  //}
  std::vector< std::vector< Expr > > ops;
  int startIndex = -1;
  std::map< Type, Type > sygus_to_builtin;

  std::vector< TypeNode > types;
  std::map< TypeNode, std::vector< DatatypeConstructorArg > > sels;
  //types for each of the variables of parametric sort
  for( unsigned i=0; i<sygus_vars.size(); i++ ){
    collectSygusGrammarTypesFor( sygus_vars[i].getType(), types, sels );
  }
  //types connected to range
  collectSygusGrammarTypesFor( range, types, sels );

  //name of boolean sort
  std::stringstream ssb;
  ssb << fun << "_Bool";
  std::string dbname = ssb.str();
  Type unres_bt = mkUnresolvedType(ssb.str(), unres).toType();

  std::vector< Type > unres_types;
  std::map< TypeNode, Type > type_to_unres;
  for( unsigned i=0; i<types.size(); i++ ){
    std::stringstream ss;
    ss << fun << "_" << types[i];
    std::string dname = ss.str();
    datatypes.push_back(Datatype(dname));
    ops.push_back(std::vector< Expr >());
    //make unresolved type
    Type unres_t = mkUnresolvedType(dname, unres).toType();
    unres_types.push_back(unres_t);
    type_to_unres[types[i]] = unres_t;
    sygus_to_builtin[unres_t] = types[i].toType();
  }
  for( unsigned i=0; i<types.size(); i++ ){
    Trace("sygus-grammar-def") << "Make grammar for " << types[i] << " " << unres_types[i] << std::endl;
    std::vector<std::string> cnames;
    std::vector<std::vector<CVC4::Type> > cargs;
    Type unres_t = unres_types[i];
    //add variables
    for( unsigned j=0; j<sygus_vars.size(); j++ ){
      if( sygus_vars[j].getType()==types[i] ){
        std::stringstream ss;
        ss << sygus_vars[j];
        Trace("sygus-grammar-def") << "...add for variable " << ss.str() << std::endl;
        ops[i].push_back( sygus_vars[j].toExpr() );
        cnames.push_back( ss.str() );
        cargs.push_back( std::vector< CVC4::Type >() );
      }
    }
    //add constants
    std::vector< Node > consts;
    mkSygusConstantsForType( types[i], consts );
    std::map< TypeNode, std::vector< Node > >::iterator itec = extra_cons.find( types[i] );
    if( itec!=extra_cons.end() ){
      //consts.insert( consts.end(), itec->second.begin(), itec->second.end() );
      for( unsigned j=0; j<itec->second.size(); j++ ){
        if( std::find( consts.begin(), consts.end(), itec->second[j] )==consts.end() ){
          consts.push_back( itec->second[j] );
        }
      }
    }
    for( unsigned j=0; j<consts.size(); j++ ){
      std::stringstream ss;
      ss << consts[j];
      Trace("sygus-grammar-def") << "...add for constant " << ss.str() << std::endl;
      ops[i].push_back( consts[j].toExpr() );
      cnames.push_back( ss.str() );
      cargs.push_back( std::vector< CVC4::Type >() );
    }
    //ITE
    CVC4::Kind k = kind::ITE;
    Trace("sygus-grammar-def") << "...add for " << k << std::endl;
    ops[i].push_back(NodeManager::currentNM()->operatorOf(k).toExpr());
    cnames.push_back( kind::kindToString(k) );
    cargs.push_back( std::vector< CVC4::Type >() );
    cargs.back().push_back(unres_bt);
    cargs.back().push_back(unres_t);
    cargs.back().push_back(unres_t);

    if (types[i].isReal())
    {
      for (unsigned j = 0; j < 2; j++)
      {
        Kind k = j == 0 ? PLUS : MINUS;
        Trace("sygus-grammar-def") << "...add for " << k << std::endl;
        ops[i].push_back(NodeManager::currentNM()->operatorOf(k).toExpr());
        cnames.push_back(kind::kindToString(k));
        cargs.push_back(std::vector<CVC4::Type>());
        cargs.back().push_back(unres_t);
        cargs.back().push_back(unres_t);
      }
      if (!types[i].isInteger())
      {
        Trace("sygus-grammar-def") << "...Dedicate to Real\n";
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
        ops_pos_int.push_back(
            NodeManager::currentNM()->mkConst(Rational(1)).toExpr());
        ss << "_1";
        cnames_pos_int.push_back(ss.str());
        cargs_pos_int.push_back(std::vector<Type>());
        /* Add operator PLUS */
        Kind k = PLUS;
        Trace("sygus-grammar-def") << "\t...add for PLUS to Pos_Int\n";
        ops_pos_int.push_back(NodeManager::currentNM()->operatorOf(k).toExpr());
        cnames_pos_int.push_back(kindToString(k));
        cargs_pos_int.push_back(std::vector<Type>());
        cargs_pos_int.back().push_back(unres_pos_int_t);
        cargs_pos_int.back().push_back(unres_pos_int_t);
        datatypes.back().setSygus(types[i].toType(), bvl.toExpr(), true, true);
        for (unsigned j = 0; j < ops_pos_int.size(); j++)
        {
          datatypes.back().addSygusConstructor(
              ops_pos_int[j], cnames_pos_int[j], cargs_pos_int[j]);
        }
        Trace("sygus-grammar-def")
            << "...built datatype " << datatypes.back() << " ";
        /* Adding division at root */
        k = DIVISION;
        Trace("sygus-grammar-def") << "\t...add for " << k << std::endl;
        ops[i].push_back(NodeManager::currentNM()->operatorOf(k).toExpr());
        cnames.push_back(kindToString(k));
        cargs.push_back(std::vector<Type>());
        cargs.back().push_back(unres_t);
        cargs.back().push_back(unres_pos_int_t);
      }
    }else if( types[i].isDatatype() ){
      Trace("sygus-grammar-def") << "...add for constructors" << std::endl;
      const Datatype& dt = ((DatatypeType)types[i].toType()).getDatatype();
      for( unsigned k=0; k<dt.getNumConstructors(); k++ ){
        Trace("sygus-grammar-def") << "...for " << dt[k].getName() << std::endl;
        ops[i].push_back( dt[k].getConstructor() );
        cnames.push_back( dt[k].getName() );
        cargs.push_back( std::vector< CVC4::Type >() );
        for( unsigned j=0; j<dt[k].getNumArgs(); j++ ){
          TypeNode crange = TypeNode::fromType( ((SelectorType)dt[k][j].getType()).getRangeType() );
          //Assert( type_to_unres.find(crange)!=type_to_unres.end() );
          cargs.back().push_back( type_to_unres[crange] );
        }
      }
    }else{
      std::stringstream sserr;
      sserr << "No implementation for default Sygus grammar of type " << types[i] << std::endl;
      //AlwaysAssert( false, sserr.str() );
      // FIXME
      AlwaysAssert( false );
    }
    //add for all selectors to this type
    if( !sels[types[i]].empty() ){
      Trace("sygus-grammar-def") << "...add for selectors" << std::endl;
      for( unsigned j=0; j<sels[types[i]].size(); j++ ){
        Trace("sygus-grammar-def") << "...for " << sels[types[i]][j].getName() << std::endl;
        TypeNode arg_type = TypeNode::fromType( ((SelectorType)sels[types[i]][j].getType()).getDomain() );
        ops[i].push_back( sels[types[i]][j].getSelector() );
        cnames.push_back( sels[types[i]][j].getName() );
        cargs.push_back( std::vector< CVC4::Type >() );
        //Assert( type_to_unres.find(arg_type)!=type_to_unres.end() );
        cargs.back().push_back( type_to_unres[arg_type] );
      }
    }
    Trace("sygus-grammar-def") << "...make datatype " << datatypes[i] << std::endl;
    datatypes[i].setSygus( types[i].toType(), bvl.toExpr(), true, true );
    for( unsigned j=0; j<ops[i].size(); j++ ){
      datatypes[i].addSygusConstructor( ops[i][j], cnames[j], cargs[j] );
    }
    Trace("sygus-grammar-def")
        << "...built datatype " << datatypes[i] << " ";
    //sorts.push_back( types[i] );
    //set start index if applicable
    if( types[i]==range ){
      startIndex = i;
    }
  }

  //make Boolean type
  TypeNode btype = NodeManager::currentNM()->booleanType();
  datatypes.push_back(Datatype(dbname));
  ops.push_back(std::vector<Expr>());
  std::vector<std::string> cnames;
  std::vector<std::vector< Type > > cargs;
  Trace("sygus-grammar-def") << "Make grammar for " << btype << " " << datatypes.back() << std::endl;
  //add variables
  for( unsigned i=0; i<sygus_vars.size(); i++ ){
    if( sygus_vars[i].getType().isBoolean() ){
      std::stringstream ss;
      ss << sygus_vars[i];
      Trace("sygus-grammar-def") << "...add for variable " << ss.str() << std::endl;
      ops.back().push_back( sygus_vars[i].toExpr() );
      cnames.push_back( ss.str() );
      cargs.push_back( std::vector< CVC4::Type >() );
    }
  }
  //add constants if no variables and no connected types
  if( ops.back().empty() && types.empty() ){
    std::vector< Node > consts;
    mkSygusConstantsForType( btype, consts );
    for( unsigned j=0; j<consts.size(); j++ ){
      std::stringstream ss;
      ss << consts[j];
      Trace("sygus-grammar-def") << "...add for constant " << ss.str() << std::endl;
      ops.back().push_back( consts[j].toExpr() );
      cnames.push_back( ss.str() );
      cargs.push_back( std::vector< CVC4::Type >() );
    }
  }
  //add operators
  for( unsigned i=0; i<3; i++ ){
    CVC4::Kind k = i==0 ? kind::NOT : ( i==1 ? kind::AND : kind::OR );
    Trace("sygus-grammar-def") << "...add for " << k << std::endl;
    ops.back().push_back(NodeManager::currentNM()->operatorOf(k).toExpr());
    cnames.push_back(kind::kindToString(k));
    cargs.push_back( std::vector< CVC4::Type >() );
    if( k==kind::NOT ){
      cargs.back().push_back(unres_bt);
    }else if( k==kind::AND || k==kind::OR ){
      cargs.back().push_back(unres_bt);
      cargs.back().push_back(unres_bt);
    }
  }
  //add predicates for types
  for( unsigned i=0; i<types.size(); i++ ){
    Trace("sygus-grammar-def") << "...add predicates for " << types[i] << std::endl;
    //add equality per type
    CVC4::Kind k = kind::EQUAL;
    Trace("sygus-grammar-def") << "...add for " << k << std::endl;
    ops.back().push_back(NodeManager::currentNM()->operatorOf(k).toExpr());
    std::stringstream ss;
    ss << kind::kindToString(k) << "_" << types[i];
    cnames.push_back(ss.str());
    cargs.push_back( std::vector< CVC4::Type >() );
    cargs.back().push_back(unres_types[i]);
    cargs.back().push_back(unres_types[i]);
    //type specific predicates
    if (types[i].isReal())
    {
      CVC4::Kind k = kind::LEQ;
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      ops.back().push_back(NodeManager::currentNM()->operatorOf(k).toExpr());
      cnames.push_back(kind::kindToString(k));
      cargs.push_back( std::vector< CVC4::Type >() );
      cargs.back().push_back(unres_types[i]);
      cargs.back().push_back(unres_types[i]);
    }else if( types[i].isDatatype() ){
      //add for testers
      Trace("sygus-grammar-def") << "...add for testers" << std::endl;
      const Datatype& dt = ((DatatypeType)types[i].toType()).getDatatype();
      for( unsigned k=0; k<dt.getNumConstructors(); k++ ){
        Trace("sygus-grammar-def") << "...for " << dt[k].getTesterName() << std::endl;
        ops.back().push_back(dt[k].getTester());
        cnames.push_back(dt[k].getTesterName());
        cargs.push_back( std::vector< CVC4::Type >() );
        cargs.back().push_back(unres_types[i]);
      }
    }
  }
  if( range==btype ){
    startIndex = datatypes.size()-1;
  }
  Trace("sygus-grammar-def") << "...make datatype " << datatypes.back() << std::endl;
  datatypes.back().setSygus( btype.toType(), bvl.toExpr(), true, true );
  for( unsigned j=0; j<ops.back().size(); j++ ){
    datatypes.back().addSygusConstructor( ops.back()[j], cnames[j], cargs[j] );
  }
  //sorts.push_back( btype );
  Trace("sygus-grammar-def") << "...finished make default grammar for " << fun << " " << range << std::endl;
  
  if( startIndex>0 ){
    CVC4::Datatype tmp_dt = datatypes[0];
    datatypes[0] = datatypes[startIndex];
    datatypes[startIndex] = tmp_dt;
  }
}

TypeNode CegGrammarConstructor::mkSygusDefaultType(
    TypeNode range,
    Node bvl,
    const std::string& fun,
    std::map<TypeNode, std::vector<Node> >& extra_cons,
    std::unordered_set<Node, NodeHashFunction>& term_irrelevant)
{
  Trace("sygus-grammar-def") << "*** Make sygus default type " << range << ", make datatypes..." << std::endl;
  for( std::map< TypeNode, std::vector< Node > >::iterator it = extra_cons.begin(); it != extra_cons.end(); ++it ){
    Trace("sygus-grammar-def") << "    ...using " << it->second.size() << " extra constants for " << it->first << std::endl;
  }
  std::set<Type> unres;
  std::vector< CVC4::Datatype > datatypes;
  mkSygusDefaultGrammar(
      range, bvl, fun, extra_cons, term_irrelevant, datatypes, unres);
  Trace("sygus-grammar-def")  << "...made " << datatypes.size() << " datatypes, now make mutual datatype types..." << std::endl;
  Assert( !datatypes.empty() );
  std::vector<DatatypeType> types = NodeManager::currentNM()->toExprManager()->mkMutualDatatypeTypes(datatypes, unres);
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
    std::vector<DatatypeType> types = NodeManager::currentNM()->toExprManager()->mkMutualDatatypeTypes(datatypes, unres);
    Assert( types.size()==1 );
    return TypeNode::fromType( types[0] );
  }
}

TypeNode CegGrammarConstructor::mkSygusTemplateType( Node templ, Node templ_arg, TypeNode templ_arg_sygus_type, Node bvl, 
                                                     const std::string& fun ) {
  unsigned tcount = 0;
  return mkSygusTemplateTypeRec( templ, templ_arg, templ_arg_sygus_type, bvl, fun, tcount );
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
