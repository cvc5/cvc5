/*********************                                                        */
/*! \file theory_strings.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
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

#include "theory/strings/theory_strings.h"

#include <cmath>

#include "expr/kind.h"
#include "options/strings_options.h"
#include "smt/command.h"
#include "smt/logic_exception.h"
#include "smt/smt_statistics_registry.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/type_enumerator.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

std::ostream& operator<<(std::ostream& out, Inference i)
{
  switch (i)
  {
    case INFER_SSPLIT_CST_PROP: out << "S-Split(CST-P)-prop"; break;
    case INFER_SSPLIT_VAR_PROP: out << "S-Split(VAR)-prop"; break;
    case INFER_LEN_SPLIT: out << "Len-Split(Len)"; break;
    case INFER_LEN_SPLIT_EMP: out << "Len-Split(Emp)"; break;
    case INFER_SSPLIT_CST_BINARY: out << "S-Split(CST-P)-binary"; break;
    case INFER_SSPLIT_CST: out << "S-Split(CST-P)"; break;
    case INFER_SSPLIT_VAR: out << "S-Split(VAR)"; break;
    case INFER_FLOOP: out << "F-Loop"; break;
    default: out << "?"; break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, InferStep s)
{
  switch (s)
  {
    case BREAK: out << "break"; break;
    case CHECK_INIT: out << "check_init"; break;
    case CHECK_CONST_EQC: out << "check_const_eqc"; break;
    case CHECK_EXTF_EVAL: out << "check_extf_eval"; break;
    case CHECK_CYCLES: out << "check_cycles"; break;
    case CHECK_FLAT_FORMS: out << "check_flat_forms"; break;
    case CHECK_NORMAL_FORMS_EQ: out << "check_normal_forms_eq"; break;
    case CHECK_NORMAL_FORMS_DEQ: out << "check_normal_forms_deq"; break;
    case CHECK_CODES: out << "check_codes"; break;
    case CHECK_LENGTH_EQC: out << "check_length_eqc"; break;
    case CHECK_EXTF_REDUCTION: out << "check_extf_reduction"; break;
    case CHECK_MEMBERSHIP: out << "check_membership"; break;
    case CHECK_CARDINALITY: out << "check_cardinality"; break;
    default: out << "?"; break;
  }
  return out;
}

Node TheoryStrings::TermIndex::add( TNode n, unsigned index, TheoryStrings* t, Node er, std::vector< Node >& c ) {
  if( index==n.getNumChildren() ){
    if( d_data.isNull() ){
      d_data = n;
    }
    return d_data;
  }else{
    Assert( index<n.getNumChildren() );
    TNode nir = t->getRepresentative( n[index] );
    //if it is empty, and doing CONCAT, ignore
    if( nir==er && n.getKind()==kind::STRING_CONCAT ){
      return add( n, index+1, t, er, c );
    }else{
      c.push_back( nir );
      return d_children[nir].add( n, index+1, t, er, c );
    }
  }
}

TheoryStrings::TheoryStrings(context::Context* c,
                             context::UserContext* u,
                             OutputChannel& out,
                             Valuation valuation,
                             const LogicInfo& logicInfo)
    : Theory(THEORY_STRINGS, c, u, out, valuation, logicInfo),
      d_notify(*this),
      d_equalityEngine(d_notify, c, "theory::strings", true),
      d_im(*this, c, u, d_equalityEngine, out),
      d_conflict(c, false),
      d_nf_pairs(c),
      d_pregistered_terms_cache(u),
      d_registered_terms_cache(u),
      d_length_lemma_terms_cache(u),
      d_preproc(&d_sk_cache, u),
      d_extf_infer_cache(c),
      d_extf_infer_cache_u(u),
      d_ee_disequalities(c),
      d_congruent(c),
      d_proxy_var(u),
      d_proxy_var_to_length(u),
      d_functionsTerms(c),
      d_has_extf(c, false),
      d_has_str_code(false),
      d_regexp_solver(*this, d_im, c, u),
      d_input_vars(u),
      d_input_var_lsum(u),
      d_cardinality_lits(u),
      d_curr_cardinality(c, 0),
      d_sslds(nullptr),
      d_strategy_init(false)
{
  setupExtTheory();
  getExtTheory()->addFunctionKind(kind::STRING_SUBSTR);
  getExtTheory()->addFunctionKind(kind::STRING_STRIDOF);
  getExtTheory()->addFunctionKind(kind::STRING_ITOS);
  getExtTheory()->addFunctionKind(kind::STRING_STOI);
  getExtTheory()->addFunctionKind(kind::STRING_STRREPL);
  getExtTheory()->addFunctionKind(kind::STRING_STRREPLALL);
  getExtTheory()->addFunctionKind(kind::STRING_STRCTN);
  getExtTheory()->addFunctionKind(kind::STRING_IN_REGEXP);
  getExtTheory()->addFunctionKind(kind::STRING_LEQ);
  getExtTheory()->addFunctionKind(kind::STRING_CODE);

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::STRING_LENGTH);
  d_equalityEngine.addFunctionKind(kind::STRING_CONCAT);
  d_equalityEngine.addFunctionKind(kind::STRING_IN_REGEXP);
  d_equalityEngine.addFunctionKind(kind::STRING_CODE);

  // extended functions
  d_equalityEngine.addFunctionKind(kind::STRING_STRCTN);
  d_equalityEngine.addFunctionKind(kind::STRING_LEQ);
  d_equalityEngine.addFunctionKind(kind::STRING_SUBSTR);
  d_equalityEngine.addFunctionKind(kind::STRING_ITOS);
  d_equalityEngine.addFunctionKind(kind::STRING_STOI);
  d_equalityEngine.addFunctionKind(kind::STRING_STRIDOF);
  d_equalityEngine.addFunctionKind(kind::STRING_STRREPL);
  d_equalityEngine.addFunctionKind(kind::STRING_STRREPLALL);

  d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );

  d_card_size = TheoryStringsRewriter::getAlphabetCardinality();
}

TheoryStrings::~TheoryStrings() {
  for( std::map< Node, EqcInfo* >::iterator it = d_eqc_info.begin(); it != d_eqc_info.end(); ++it ){
    delete it->second;
  }
}

Node TheoryStrings::getRepresentative( Node t ) {
  if( d_equalityEngine.hasTerm( t ) ){
    return d_equalityEngine.getRepresentative( t );
  }else{
    return t;
  }
}

bool TheoryStrings::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheoryStrings::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryStrings::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else{
    if( hasTerm( a ) && hasTerm( b ) ) {
      Node ar = d_equalityEngine.getRepresentative( a );
      Node br = d_equalityEngine.getRepresentative( b );
      return ( ar!=br && ar.isConst() && br.isConst() ) || d_equalityEngine.areDisequal( ar, br, false );
    }else{
      Node ar = getRepresentative( a );
      Node br = getRepresentative( b );
      return ar!=br && ar.isConst() && br.isConst();
    }
  }
}

bool TheoryStrings::areCareDisequal( TNode x, TNode y ) {
  Assert( d_equalityEngine.hasTerm(x) );
  Assert( d_equalityEngine.hasTerm(y) );
  if( d_equalityEngine.isTriggerTerm(x, THEORY_STRINGS) && d_equalityEngine.isTriggerTerm(y, THEORY_STRINGS) ){
    TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_STRINGS);
    TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_STRINGS);
    EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
    if( eqStatus==EQUALITY_FALSE_AND_PROPAGATED || eqStatus==EQUALITY_FALSE || eqStatus==EQUALITY_FALSE_IN_MODEL ){
      return true;
    }
  }
  return false;
}

Node TheoryStrings::getLengthExp( Node t, std::vector< Node >& exp, Node te ){
  Assert( areEqual( t, te ) );
  Node lt = mkLength( te );
  if( hasTerm( lt ) ){
    // use own length if it exists, leads to shorter explanation
    return lt;
  }else{
    EqcInfo * ei = getOrMakeEqcInfo( t, false );
    Node length_term = ei ? ei->d_length_term : Node::null();
    if( length_term.isNull() ){
      //typically shouldnt be necessary
      length_term = t;
    }
    Debug("strings") << "TheoryStrings::getLengthTerm " << t << " is " << length_term << std::endl;
    addToExplanation( length_term, te, exp );
    return Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, length_term ) );
  }
}

Node TheoryStrings::getLength( Node t, std::vector< Node >& exp ) {
  return getLengthExp( t, exp, t );
}

Node TheoryStrings::getNormalString(Node x, std::vector<Node>& nf_exp)
{
  if (!x.isConst())
  {
    Node xr = getRepresentative(x);
    std::map<Node, NormalForm>::iterator it = d_normal_form.find(xr);
    if (it != d_normal_form.end())
    {
      NormalForm& nf = it->second;
      Node ret = mkConcat(nf.d_nf);
      nf_exp.insert(nf_exp.end(), nf.d_exp.begin(), nf.d_exp.end());
      addToExplanation(x, nf.d_base, nf_exp);
      Trace("strings-debug")
          << "Term: " << x << " has a normal form " << ret << std::endl;
      return ret;
    }
    // if x does not have a normal form, then it should not occur in the
    // equality engine and hence should be its own representative.
    Assert(xr == x);
    if (x.getKind() == kind::STRING_CONCAT)
    {
      std::vector<Node> vec_nodes;
      for (unsigned i = 0; i < x.getNumChildren(); i++)
      {
        Node nc = getNormalString(x[i], nf_exp);
        vec_nodes.push_back(nc);
      }
      return mkConcat(vec_nodes);
    }
  }
  return x;
}

void TheoryStrings::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryStrings::addSharedTerm(TNode t) {
  Debug("strings") << "TheoryStrings::addSharedTerm(): "
                     << t << " " << t.getType().isBoolean() << endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_STRINGS);
  if (options::stringExp())
  {
    getExtTheory()->registerTermRec(t);
  }
  Debug("strings") << "TheoryStrings::addSharedTerm() finished" << std::endl;
}

EqualityStatus TheoryStrings::getEqualityStatus(TNode a, TNode b) {
  if( d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b) ){
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b, false)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EQUALITY_UNKNOWN;
}

void TheoryStrings::propagate(Effort e) {
  // direct propagation now
}

bool TheoryStrings::propagate(TNode literal) {
  Debug("strings-propagate") << "TheoryStrings::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("strings-propagate") << "TheoryStrings::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

/** explain */
void TheoryStrings::explain(TNode literal, std::vector<TNode>& assumptions) {
  Debug("strings-explain") << "Explain " << literal << " " << d_conflict << std::endl;
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  unsigned ps = assumptions.size();
  std::vector< TNode > tassumptions;
  if (atom.getKind() == kind::EQUAL) {
    if( atom[0]!=atom[1] ){
      Assert( hasTerm( atom[0] ) );
      Assert( hasTerm( atom[1] ) );
      d_equalityEngine.explainEquality(atom[0], atom[1], polarity, tassumptions);
    }
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, tassumptions);
  }
  for( unsigned i=0; i<tassumptions.size(); i++ ){
    if( std::find( assumptions.begin(), assumptions.end(), tassumptions[i] )==assumptions.end() ){
      assumptions.push_back( tassumptions[i] );
    }
  }
  if (Debug.isOn("strings-explain-debug"))
  {
    Debug("strings-explain-debug") << "Explanation for " << literal << " was "
                                   << std::endl;
    for (unsigned i = ps; i < assumptions.size(); i++)
    {
      Debug("strings-explain-debug") << "   " << assumptions[i] << std::endl;
    }
  }
}

Node TheoryStrings::explain( TNode literal ){
  Debug("strings-explain") << "explain called on " << literal << std::endl;
  std::vector< TNode > assumptions;
  explain( literal, assumptions );
  if( assumptions.empty() ){
    return d_true;
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}

bool TheoryStrings::getCurrentSubstitution( int effort, std::vector< Node >& vars, 
                                            std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp ) {
  Trace("strings-subs") << "getCurrentSubstitution, effort = " << effort << std::endl;
  for( unsigned i=0; i<vars.size(); i++ ){
    Node n = vars[i];
    Trace("strings-subs") << "  get subs for " << n << "..." << std::endl;
    if( effort>=3 ){
      //model values
      Node mv = d_valuation.getModel()->getRepresentative( n );
      Trace("strings-subs") << "   model val : " << mv << std::endl;
      subs.push_back( mv );
    }else{
      Node nr = getRepresentative( n );
      std::map< Node, Node >::iterator itc = d_eqc_to_const.find( nr );
      if( itc!=d_eqc_to_const.end() ){
        //constant equivalence classes
        Trace("strings-subs") << "   constant eqc : " << d_eqc_to_const_exp[nr] << " " << d_eqc_to_const_base[nr] << " " << nr << std::endl;
        subs.push_back( itc->second );
        if( !d_eqc_to_const_exp[nr].isNull() ){
          exp[n].push_back( d_eqc_to_const_exp[nr] );
        }
        if( !d_eqc_to_const_base[nr].isNull() ){
          addToExplanation( n, d_eqc_to_const_base[nr], exp[n] );
        }
      }else if( effort>=1 && effort<3 && n.getType().isString() ){
        //normal forms
        NormalForm& nfnr = getNormalForm(nr);
        Node ns = getNormalString(nfnr.d_base, exp[n]);
        subs.push_back( ns );
        Trace("strings-subs") << "   normal eqc : " << ns << " " << nfnr.d_base
                              << " " << nr << std::endl;
        if (!nfnr.d_base.isNull())
        {
          addToExplanation(n, nfnr.d_base, exp[n]);
        }
      }else{
        //representative?
        //Trace("strings-subs") << "   representative : " << nr << std::endl;
        //addToExplanation( n, nr, exp[n] );
        //subs.push_back( nr );
        subs.push_back( n );
      }
    }
  }
  return true;
}

bool TheoryStrings::doReduction(int effort, Node n, bool& isCd)
{
  Assert(d_extf_info_tmp.find(n) != d_extf_info_tmp.end());
  if (!d_extf_info_tmp[n].d_model_active)
  {
    // n is not active in the model, no need to reduce
    return false;
  }
  //determine the effort level to process the extf at
  // 0 - at assertion time, 1+ - after no other reduction is applicable
  int r_effort = -1;
  // polarity : 1 true, -1 false, 0 neither
  int pol = 0;
  Kind k = n.getKind();
  if (n.getType().isBoolean() && !d_extf_info_tmp[n].d_const.isNull())
  {
    pol = d_extf_info_tmp[n].d_const.getConst<bool>() ? 1 : -1;
  }
  if (k == STRING_STRCTN)
  {
    if (pol == 1)
    {
      r_effort = 1;
    }
    else if (pol == -1)
    {
      if (effort == 2)
      {
        Node x = n[0];
        Node s = n[1];
        std::vector<Node> lexp;
        Node lenx = getLength(x, lexp);
        Node lens = getLength(s, lexp);
        if (areEqual(lenx, lens))
        {
          Trace("strings-extf-debug")
              << "  resolve extf : " << n
              << " based on equal lengths disequality." << std::endl;
          // We can reduce negative contains to a disequality when lengths are
          // equal. In other words, len( x ) = len( s ) implies
          //   ~contains( x, s ) reduces to x != s.
          if (!areDisequal(x, s))
          {
            // len( x ) = len( s ) ^ ~contains( x, s ) => x != s
            lexp.push_back(lenx.eqNode(lens));
            lexp.push_back(n.negate());
            Node xneqs = x.eqNode(s).negate();
            d_im.sendInference(lexp, xneqs, "NEG-CTN-EQL", true);
          }
          // this depends on the current assertions, so we set that this
          // inference is context-dependent.
          isCd = true;
          return true;
        }
        else
        {
          r_effort = 2;
        }
      }
    }
  }
  else
  {
    if (k == STRING_SUBSTR)
    {
      r_effort = 1;
    }
    else if (k != STRING_IN_REGEXP)
    {
      r_effort = 2;
    }
  }
  if (effort != r_effort)
  {
    // not the right effort level to reduce
    return false;
  }
  Node c_n = pol == -1 ? n.negate() : n;
  Trace("strings-process-debug")
      << "Process reduction for " << n << ", pol = " << pol << std::endl;
  if (k == STRING_STRCTN && pol == 1)
  {
    Node x = n[0];
    Node s = n[1];
    // positive contains reduces to a equality
    Node sk1 =
        d_sk_cache.mkSkolemCached(x, s, SkolemCache::SK_FIRST_CTN_PRE, "sc1");
    Node sk2 =
        d_sk_cache.mkSkolemCached(x, s, SkolemCache::SK_FIRST_CTN_POST, "sc2");
    Node eq = Rewriter::rewrite(x.eqNode(mkConcat(sk1, s, sk2)));
    std::vector<Node> exp_vec;
    exp_vec.push_back(n);
    d_im.sendInference(d_empty_vec, exp_vec, eq, "POS-CTN", true);
    Trace("strings-extf-debug")
        << "  resolve extf : " << n << " based on positive contain reduction."
        << std::endl;
    Trace("strings-red-lemma") << "Reduction (positive contains) lemma : " << n
                               << " => " << eq << std::endl;
    // context-dependent because it depends on the polarity of n itself
    isCd = true;
  }
  else if (k != kind::STRING_CODE)
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(k == STRING_SUBSTR || k == STRING_STRCTN || k == STRING_STRIDOF
           || k == STRING_ITOS || k == STRING_STOI || k == STRING_STRREPL
           || k == STRING_STRREPLALL || k == STRING_LEQ);
    std::vector<Node> new_nodes;
    Node res = d_preproc.simplify(n, new_nodes);
    Assert(res != n);
    new_nodes.push_back(res.eqNode(n));
    Node nnlem =
        new_nodes.size() == 1 ? new_nodes[0] : nm->mkNode(AND, new_nodes);
    nnlem = Rewriter::rewrite(nnlem);
    Trace("strings-red-lemma")
        << "Reduction_" << effort << " lemma : " << nnlem << std::endl;
    Trace("strings-red-lemma") << "...from " << n << std::endl;
    d_im.sendInference(d_empty_vec, nnlem, "Reduction", true);
    Trace("strings-extf-debug")
        << "  resolve extf : " << n << " based on reduction." << std::endl;
    isCd = false;
  }
  return true;
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::presolve() {
  Debug("strings-presolve") << "TheoryStrings::Presolving : get fmf options " << (options::stringFMF() ? "true" : "false") << std::endl;
  initializeStrategy();

  // if strings fmf is enabled, register the strategy
  if (options::stringFMF())
  {
    d_sslds.reset(new StringSumLengthDecisionStrategy(
        getSatContext(), getUserContext(), d_valuation));
    Trace("strings-dstrat-reg")
        << "presolve: register decision strategy." << std::endl;
    std::vector<Node> inputVars;
    for (NodeSet::const_iterator itr = d_input_vars.begin();
         itr != d_input_vars.end();
         ++itr)
    {
      inputVars.push_back(*itr);
    }
    d_sslds->initialize(inputVars);
    getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_STRINGS_SUM_LENGTHS, d_sslds.get());
  }
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

bool TheoryStrings::collectModelInfo(TheoryModel* m)
{
  Trace("strings-model") << "TheoryStrings : Collect model info" << std::endl;
  Trace("strings-model") << "TheoryStrings : assertEqualityEngine." << std::endl;

  std::set<Node> termSet;

  // Compute terms appearing in assertions and shared terms
  computeRelevantTerms(termSet);
  // assert the (relevant) portion of the equality engine to the model
  if (!m->assertEqualityEngine(&d_equalityEngine, &termSet))
  {
    return false;
  }

  std::unordered_set<Node, NodeHashFunction> repSet;
  NodeManager* nm = NodeManager::currentNM();
  // Generate model
  // get the relevant string equivalence classes
  for (const Node& s : termSet)
  {
    if (s.getType().isString())
    {
      Node r = getRepresentative(s);
      repSet.insert(r);
    }
  }
  std::vector<Node> nodes(repSet.begin(), repSet.end());
  std::map< Node, Node > processed;
  std::vector< std::vector< Node > > col;
  std::vector< Node > lts;
  separateByLength( nodes, col, lts );
  //step 1 : get all values for known lengths
  std::vector< Node > lts_values;
  std::map<unsigned, Node> values_used;
  std::vector<Node> len_splits;
  for( unsigned i=0; i<col.size(); i++ ) {
    Trace("strings-model") << "Checking length for {";
    for( unsigned j=0; j<col[i].size(); j++ ) {
      if( j>0 ) {
        Trace("strings-model") << ", ";
      }
      Trace("strings-model") << col[i][j];
    }
    Trace("strings-model") << " } (length is " << lts[i] << ")" << std::endl;
    Node len_value;
    if( lts[i].isConst() ) {
      len_value = lts[i];
    }
    else if (!lts[i].isNull())
    {
      // get the model value for lts[i]
      len_value = d_valuation.getModelValue(lts[i]);
    }
    if (len_value.isNull())
    {
      lts_values.push_back(Node::null());
    }
    else
    {
      Assert(len_value.getConst<Rational>() <= Rational(String::maxSize()),
             "Exceeded UINT32_MAX in string model");
      unsigned lvalue =
          len_value.getConst<Rational>().getNumerator().toUnsignedInt();
      std::map<unsigned, Node>::iterator itvu = values_used.find(lvalue);
      if (itvu == values_used.end())
      {
        values_used[lvalue] = lts[i];
      }
      else
      {
        len_splits.push_back(lts[i].eqNode(itvu->second));
      }
      lts_values.push_back(len_value);
    }
  }
  ////step 2 : assign arbitrary values for unknown lengths?
  // confirmed by calculus invariant, see paper
  Trace("strings-model") << "Assign to equivalence classes..." << std::endl;
  std::map<Node, Node> pure_eq_assign;
  //step 3 : assign values to equivalence classes that are pure variables
  for( unsigned i=0; i<col.size(); i++ ){
    std::vector< Node > pure_eq;
    Trace("strings-model") << "The (" << col[i].size()
                           << ") equivalence classes ";
    for (const Node& eqc : col[i])
    {
      Trace("strings-model") << eqc << " ";
      //check if col[i][j] has only variables
      if (!eqc.isConst())
      {
        NormalForm& nfe = getNormalForm(eqc);
        if (nfe.d_nf.size() == 1)
        {
          // does it have a code and the length of these equivalence classes are
          // one?
          if (d_has_str_code && lts_values[i] == d_one)
          {
            EqcInfo* eip = getOrMakeEqcInfo(eqc, false);
            if (eip && !eip->d_code_term.get().isNull())
            {
              // its value must be equal to its code
              Node ct = nm->mkNode(kind::STRING_CODE, eip->d_code_term.get());
              Node ctv = d_valuation.getModelValue(ct);
              unsigned cvalue =
                  ctv.getConst<Rational>().getNumerator().toUnsignedInt();
              Trace("strings-model") << "(code: " << cvalue << ") ";
              std::vector<unsigned> vec;
              vec.push_back(String::convertCodeToUnsignedInt(cvalue));
              Node mv = nm->mkConst(String(vec));
              pure_eq_assign[eqc] = mv;
              m->getEqualityEngine()->addTerm(mv);
            }
          }
          pure_eq.push_back(eqc);
        }
      }
      else
      {
        processed[eqc] = eqc;
      }
    }
    Trace("strings-model") << "have length " << lts_values[i] << std::endl;

    //assign a new length if necessary
    if( !pure_eq.empty() ){
      if( lts_values[i].isNull() ){
        // start with length two (other lengths have special precendence)
        unsigned lvalue = 2;
        while( values_used.find( lvalue )!=values_used.end() ){
          lvalue++;
        }
        Trace("strings-model") << "*** Decide to make length of " << lvalue << std::endl;
        lts_values[i] = nm->mkConst(Rational(lvalue));
        values_used[lvalue] = Node::null();
      }
      Trace("strings-model") << "Need to assign values of length " << lts_values[i] << " to equivalence classes ";
      for( unsigned j=0; j<pure_eq.size(); j++ ){
        Trace("strings-model") << pure_eq[j] << " ";
      }
      Trace("strings-model") << std::endl;

      //use type enumerator
      Assert(lts_values[i].getConst<Rational>() <= Rational(String::maxSize()),
             "Exceeded UINT32_MAX in string model");
      StringEnumeratorLength sel(lts_values[i].getConst<Rational>().getNumerator().toUnsignedInt());
      for (const Node& eqc : pure_eq)
      {
        Node c;
        std::map<Node, Node>::iterator itp = pure_eq_assign.find(eqc);
        if (itp == pure_eq_assign.end())
        {
          Assert( !sel.isFinished() );
          c = *sel;
          while (m->hasTerm(c))
          {
            ++sel;
            if (sel.isFinished())
            {
              // We are in a case where model construction is impossible due to
              // an insufficient number of constants of a given length.

              // Consider an integer equivalence class E whose value is assigned
              // n in the model. Let { S_1, ..., S_m } be the set of string
              // equivalence classes such that len( x ) is a member of E for
              // some member x of each class S1, ...,Sm. Since our calculus is
              // saturated with respect to cardinality inference (see Liang
              // et al, Figure 6, CAV 2014), we have that m <= A^n, where A is
              // the cardinality of our alphabet.

              // Now, consider the case where there exists two integer
              // equivalence classes E1 and E2 that are assigned n, and moreover
              // we did not received notification from arithmetic that E1 = E2.
              // This typically should never happen, but assume in the following
              // that it does.

              // Now, it may be the case that there are string equivalence
              // classes { S_1, ..., S_m1 } whose lengths are in E1,
              // and classes { S'_1, ..., S'_m2 } whose lengths are in E2, where
              // m1 + m2 > A^n. In this case, we have insufficient strings to
              // assign to { S_1, ..., S_m1, S'_1, ..., S'_m2 }. If this
              // happens, we add a split on len( u1 ) = len( u2 ) for some
              // len( u1 ) in E1, len( u2 ) in E2. We do this for each pair of
              // integer equivalence classes that are assigned to the same value
              // in the model.
              AlwaysAssert(!len_splits.empty());
              for (const Node& sl : len_splits)
              {
                Node spl = nm->mkNode(OR, sl, sl.negate());
                d_out->lemma(spl);
              }
              return false;
            }
            c = *sel;
          }
          ++sel;
        }
        else
        {
          c = itp->second;
        }
        Trace("strings-model") << "*** Assigned constant " << c << " for "
                               << eqc << std::endl;
        processed[eqc] = c;
        if (!m->assertEquality(eqc, c, true))
        {
          return false;
        }
      }
    }
  }
  Trace("strings-model") << "String Model : Pure Assigned." << std::endl;
  //step 4 : assign constants to all other equivalence classes
  for( unsigned i=0; i<nodes.size(); i++ ){
    if( processed.find( nodes[i] )==processed.end() ){
      NormalForm& nf = getNormalForm(nodes[i]);
      if (Trace.isOn("strings-model"))
      {
        Trace("strings-model")
            << "Construct model for " << nodes[i] << " based on normal form ";
        for (unsigned j = 0, size = nf.d_nf.size(); j < size; j++)
        {
          Node n = nf.d_nf[j];
          if (j > 0)
          {
            Trace("strings-model") << " ++ ";
          }
          Trace("strings-model") << n;
          Node r = getRepresentative(n);
          if (!r.isConst() && processed.find(r) == processed.end())
          {
            Trace("strings-model") << "(UNPROCESSED)";
          }
        }
      }
      Trace("strings-model") << std::endl;
      std::vector< Node > nc;
      for (const Node& n : nf.d_nf)
      {
        Node r = getRepresentative(n);
        Assert( r.isConst() || processed.find( r )!=processed.end() );
        nc.push_back(r.isConst() ? r : processed[r]);
      }
      Node cc = mkConcat( nc );
      Assert( cc.getKind()==kind::CONST_STRING );
      Trace("strings-model") << "*** Determined constant " << cc << " for " << nodes[i] << std::endl;
      processed[nodes[i]] = cc;
      if (!m->assertEquality(nodes[i], cc, true))
      {
        return false;
      }
    }
  }
  //Trace("strings-model") << "String Model : Assigned." << std::endl;
  Trace("strings-model") << "String Model : Finished." << std::endl;
  return true;
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::preRegisterTerm(TNode n) {
  if( d_pregistered_terms_cache.find(n) == d_pregistered_terms_cache.end() ) {
    d_pregistered_terms_cache.insert(n);
    Trace("strings-preregister")
        << "TheoryString::preregister : " << n << std::endl;
    //check for logic exceptions
    Kind k = n.getKind();
    if( !options::stringExp() ){
      if (k == kind::STRING_STRIDOF || k == kind::STRING_ITOS
          || k == kind::STRING_STOI || k == kind::STRING_STRREPL
          || k == kind::STRING_STRREPLALL || k == kind::STRING_STRCTN
          || k == STRING_LEQ)
      {
        std::stringstream ss;
        ss << "Term of kind " << k
           << " not supported in default mode, try --strings-exp";
        throw LogicException(ss.str());
      }
    }
    switch (k)
    {
      case kind::EQUAL: {
        d_equalityEngine.addTriggerEquality(n);
        break;
      }
      case kind::STRING_IN_REGEXP: {
        d_out->requirePhase(n, true);
        d_equalityEngine.addTriggerPredicate(n);
        d_equalityEngine.addTerm(n[0]);
        d_equalityEngine.addTerm(n[1]);
        break;
      }
      default: {
        registerTerm(n, 0);
        TypeNode tn = n.getType();
        if (tn.isRegExp() && n.isVar())
        {
          std::stringstream ss;
          ss << "Regular expression variables are not supported.";
          throw LogicException(ss.str());
        }
        if( tn.isString() ) {
          // all characters of constants should fall in the alphabet
          if (n.isConst())
          {
            std::vector<unsigned> vec = n.getConst<String>().getVec();
            for (unsigned u : vec)
            {
              if (u >= d_card_size)
              {
                std::stringstream ss;
                ss << "Characters in string \"" << n
                   << "\" are outside of the given alphabet.";
                throw LogicException(ss.str());
              }
            }
          }
          // if finite model finding is enabled,
          // then we minimize the length of this term if it is a variable
          // but not an internally generated Skolem, or a term that does
          // not belong to this theory.
          if (options::stringFMF()
              && (n.isVar() ? !d_sk_cache.isSkolem(n)
                            : kindToTheoryId(k) != THEORY_STRINGS))
          {
            d_input_vars.insert(n);
            Trace("strings-dstrat-reg") << "input variable: " << n << std::endl;
          }
          d_equalityEngine.addTerm(n);
        } else if (tn.isBoolean()) {
          // Get triggered for both equal and dis-equal
          d_equalityEngine.addTriggerPredicate(n);
        } else {
          // Function applications/predicates
          d_equalityEngine.addTerm(n);
        }
        // Set d_functionsTerms stores all function applications that are
        // relevant to theory combination. Notice that this is a subset of
        // the applications whose kinds are function kinds in the equality
        // engine. This means it does not include applications of operators
        // like re.++, which is not a function kind in the equality engine.
        // Concatenation terms do not need to be considered here because
        // their arguments have string type and do not introduce any shared
        // terms.
        if (n.hasOperator() && d_equalityEngine.isFunctionKind(k)
            && k != kind::STRING_CONCAT)
        {
          d_functionsTerms.push_back( n );
        }
      }
    }
  }
}

Node TheoryStrings::expandDefinition(LogicRequest &logicRequest, Node node) {
  Trace("strings-exp-def") << "TheoryStrings::expandDefinition : " << node << std::endl;
  return node;
}

void TheoryStrings::check(Effort e) {
  if (done() && e<EFFORT_FULL) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  bool polarity;
  TNode atom;

  if( !done() && !hasTerm( d_emptyString ) ) {
    preRegisterTerm( d_emptyString );
  }

  // Trace("strings-process") << "Theory of strings, check : " << e << std::endl;
  Trace("strings-check") << "Theory of strings, check : " << e << std::endl;
  while ( !done() && !d_conflict ) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Trace("strings-assertion") << "get assertion: " << fact << endl;
    polarity = fact.getKind() != kind::NOT;
    atom = polarity ? fact : fact[0];

    //assert pending fact
    assertPendingFact( atom, polarity, fact );
  }
  d_im.doPendingFacts();

  Assert(d_strategy_init);
  std::map<Effort, std::pair<unsigned, unsigned> >::iterator itsr =
      d_strat_steps.find(e);
  if (!d_conflict && !d_valuation.needCheck() && itsr != d_strat_steps.end())
  {
    Trace("strings-check") << "Theory of strings " << e << " effort check "
                           << std::endl;
    if(Trace.isOn("strings-eqc")) {
      for( unsigned t=0; t<2; t++ ) {
        eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator( &d_equalityEngine );
        Trace("strings-eqc") << (t==0 ? "STRINGS:" : "OTHER:") << std::endl;
        while( !eqcs2_i.isFinished() ){
          Node eqc = (*eqcs2_i);
          bool print = (t==0 && eqc.getType().isString() ) || (t==1 && !eqc.getType().isString() );
          if (print) {
            eq::EqClassIterator eqc2_i = eq::EqClassIterator( eqc, &d_equalityEngine );
            Trace("strings-eqc") << "Eqc( " << eqc << " ) : { ";
            while( !eqc2_i.isFinished() ) {
              if( (*eqc2_i)!=eqc && (*eqc2_i).getKind()!=kind::EQUAL ){
                Trace("strings-eqc") << (*eqc2_i) << " ";
              }
              ++eqc2_i;
            }
            Trace("strings-eqc") << " } " << std::endl;
            EqcInfo * ei = getOrMakeEqcInfo( eqc, false );
            if( ei ){
              Trace("strings-eqc-debug") << "* Length term : " << ei->d_length_term.get() << std::endl;
              Trace("strings-eqc-debug") << "* Cardinality lemma k : " << ei->d_cardinality_lem_k.get() << std::endl;
              Trace("strings-eqc-debug") << "* Normalization length lemma : " << ei->d_normalized_length.get() << std::endl;
            }
          }
          ++eqcs2_i;
        }
        Trace("strings-eqc") << std::endl;
      }
      Trace("strings-eqc") << std::endl;
    }
    unsigned sbegin = itsr->second.first;
    unsigned send = itsr->second.second;
    bool addedLemma = false;
    bool addedFact;
    do{
      runStrategy(sbegin, send);
      // flush the facts
      addedFact = d_im.hasPendingFact();
      addedLemma = d_im.hasPendingLemma();
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
      // repeat if we did not add a lemma or conflict
    }while( !d_conflict && !addedLemma && addedFact );

    Trace("strings-check") << "Theory of strings done full effort check " << addedLemma << " " << d_conflict << std::endl;
  }
  Trace("strings-check") << "Theory of strings, done check : " << e << std::endl;
  Assert(!d_im.hasPendingFact());
  Assert(!d_im.hasPendingLemma());
}

bool TheoryStrings::needsCheckLastEffort() {
  if( options::stringGuessModel() ){
    return d_has_extf.get();
  }else{
    return false;
  }
}

void TheoryStrings::checkExtfReductions( int effort ) {
  // Notice we don't make a standard call to ExtTheory::doReductions here,
  // since certain optimizations like context-dependent reductions and
  // stratifying effort levels are done in doReduction below.
  std::vector< Node > extf = getExtTheory()->getActive();
  Trace("strings-process") << "  checking " << extf.size() << " active extf"
                           << std::endl;
  for( unsigned i=0; i<extf.size(); i++ ){
    Assert(!d_conflict);
    Node n = extf[i];
    Trace("strings-process") << "  check " << n << ", active in model="
                             << d_extf_info_tmp[n].d_model_active << std::endl;
    // whether the reduction was context-dependent
    bool isCd = false;
    bool ret = doReduction(effort, n, isCd);
    if (ret)
    {
      getExtTheory()->markReduced(extf[i], isCd);
      if (d_im.hasProcessed())
      {
        return;
      }
    }
  }
}

void TheoryStrings::checkMemberships()
{
  // add the memberships
  std::vector<Node> mems = getExtTheory()->getActive(kind::STRING_IN_REGEXP);
  for (unsigned i = 0; i < mems.size(); i++)
  {
    Node n = mems[i];
    Assert(d_extf_info_tmp.find(n) != d_extf_info_tmp.end());
    if (!d_extf_info_tmp[n].d_const.isNull())
    {
      bool pol = d_extf_info_tmp[n].d_const.getConst<bool>();
      Trace("strings-process-debug")
          << "  add membership : " << n << ", pol = " << pol << std::endl;
      d_regexp_solver.addMembership(pol ? n : n.negate());
    }
    else
    {
      Trace("strings-process-debug")
          << "  irrelevant (non-asserted) membership : " << n << std::endl;
    }
  }
  d_regexp_solver.check();
}

TheoryStrings::EqcInfo::EqcInfo(context::Context* c)
    : d_length_term(c),
      d_code_term(c),
      d_cardinality_lem_k(c),
      d_normalized_length(c)
{
}

TheoryStrings::EqcInfo * TheoryStrings::getOrMakeEqcInfo( Node eqc, bool doMake ) {
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( eqc );
  if( eqc_i==d_eqc_info.end() ){
    if( doMake ){
      EqcInfo* ei = new EqcInfo( getSatContext() );
      d_eqc_info[eqc] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*eqc_i).second;
  }
}


/** Conflict when merging two constants */
void TheoryStrings::conflict(TNode a, TNode b){
  if( !d_conflict ){
    Debug("strings-conflict") << "Making conflict..." << std::endl;
    d_conflict = true;
    Node conflictNode;
    conflictNode = explain( a.eqNode(b) );
    Trace("strings-conflict") << "CONFLICT: Eq engine conflict : " << conflictNode << std::endl;
    d_out->conflict( conflictNode );
  }
}

/** called when a new equivalance class is created */
void TheoryStrings::eqNotifyNewClass(TNode t){
  Kind k = t.getKind();
  if (k == kind::STRING_LENGTH || k == kind::STRING_CODE)
  {
    Trace("strings-debug") << "New length eqc : " << t << std::endl;
    Node r = d_equalityEngine.getRepresentative(t[0]);
    EqcInfo * ei = getOrMakeEqcInfo( r, true );
    if (k == kind::STRING_LENGTH)
    {
      ei->d_length_term = t[0];
    }
    else
    {
      ei->d_code_term = t[0];
    }
    //we care about the length of this string
    registerTerm( t[0], 1 );
  }else{
    //getExtTheory()->registerTerm( t );
  }
}

/** called when two equivalance classes will merge */
void TheoryStrings::eqNotifyPreMerge(TNode t1, TNode t2){
  EqcInfo * e2 = getOrMakeEqcInfo(t2, false);
  if( e2 ){
    EqcInfo * e1 = getOrMakeEqcInfo( t1 );
    //add information from e2 to e1
    if( !e2->d_length_term.get().isNull() ){
      e1->d_length_term.set( e2->d_length_term );
    }
    if (!e2->d_code_term.get().isNull())
    {
      e1->d_code_term.set(e2->d_code_term);
    }
    if( e2->d_cardinality_lem_k.get()>e1->d_cardinality_lem_k.get() ) {
      e1->d_cardinality_lem_k.set( e2->d_cardinality_lem_k );
    }
    if( !e2->d_normalized_length.get().isNull() ){
      e1->d_normalized_length.set( e2->d_normalized_length );
    }
  }
}

/** called when two equivalance classes have merged */
void TheoryStrings::eqNotifyPostMerge(TNode t1, TNode t2) {

}

/** called when two equivalance classes are disequal */
void TheoryStrings::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
  if( t1.getType().isString() ){
    //store disequalities between strings, may need to check if their lengths are equal/disequal
    d_ee_disequalities.push_back( t1.eqNode( t2 ) );
  }
}

void TheoryStrings::addCarePairs(TNodeTrie* t1,
                                 TNodeTrie* t2,
                                 unsigned arity,
                                 unsigned depth)
{
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      if( !d_equalityEngine.areEqual( f1, f2 ) ){
        Trace("strings-cg-debug") << "TheoryStrings::computeCareGraph(): checking function " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert( d_equalityEngine.hasTerm(x) );
          Assert( d_equalityEngine.hasTerm(y) );
          Assert( !d_equalityEngine.areDisequal( x, y, false ) );
          Assert( !areCareDisequal( x, y ) );
          if( !d_equalityEngine.areEqual( x, y ) ){
            if( d_equalityEngine.isTriggerTerm(x, THEORY_STRINGS) && d_equalityEngine.isTriggerTerm(y, THEORY_STRINGS) ){
              TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_STRINGS);
              TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_STRINGS);
              currentPairs.push_back(make_pair(x_shared, y_shared));
            }
          }
        }
        for (unsigned c = 0; c < currentPairs.size(); ++ c) {
          Trace("strings-cg-pair") << "TheoryStrings::computeCareGraph(): pair : " << currentPairs[c].first << " " << currentPairs[c].second << std::endl;
          addCarePair(currentPairs[c].first, currentPairs[c].second);
        }
      }
    }
  }else{
    if( t2==NULL ){
      if( depth<(arity-1) ){
        //add care pairs internal to each child
        for (std::pair<const TNode, TNodeTrie>& tt : t1->d_data)
        {
          addCarePairs(&tt.second, nullptr, arity, depth + 1);
        }
      }
      //add care pairs based on each pair of non-disequal arguments
      for (std::map<TNode, TNodeTrie>::iterator it = t1->d_data.begin();
           it != t1->d_data.end();
           ++it)
      {
        std::map<TNode, TNodeTrie>::iterator it2 = it;
        ++it2;
        for( ; it2 != t1->d_data.end(); ++it2 ){
          if( !d_equalityEngine.areDisequal(it->first, it2->first, false) ){
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1 );
            }
          }
        }
      }
    }else{
      //add care pairs based on product of indices, non-disequal arguments
      for (std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
      {
        for (std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
        {
          if (!d_equalityEngine.areDisequal(tt1.first, tt2.first, false))
          {
            if (!areCareDisequal(tt1.first, tt2.first))
            {
              addCarePairs(&tt1.second, &tt2.second, arity, depth + 1);
            }
          }
        }
      }
    }
  }
}

void TheoryStrings::computeCareGraph(){
  //computing the care graph here is probably still necessary, due to operators that take non-string arguments  TODO: verify
  Trace("strings-cg") << "TheoryStrings::computeCareGraph(): Build term indices..." << std::endl;
  std::map<Node, TNodeTrie> index;
  std::map< Node, unsigned > arity;
  unsigned functionTerms = d_functionsTerms.size();
  for (unsigned i = 0; i < functionTerms; ++ i) {
    TNode f1 = d_functionsTerms[i];
    Trace("strings-cg") << "...build for " << f1 << std::endl;
    Node op = f1.getOperator();
    std::vector< TNode > reps;
    bool has_trigger_arg = false;
    for( unsigned j=0; j<f1.getNumChildren(); j++ ){
      reps.push_back( d_equalityEngine.getRepresentative( f1[j] ) );
      if( d_equalityEngine.isTriggerTerm( f1[j], THEORY_STRINGS ) ){
        has_trigger_arg = true;
      }
    }
    if( has_trigger_arg ){
      index[op].addTerm( f1, reps );
      arity[op] = reps.size();
    }
  }
  //for each index
  for (std::pair<const Node, TNodeTrie>& tt : index)
  {
    Trace("strings-cg") << "TheoryStrings::computeCareGraph(): Process index "
                        << tt.first << "..." << std::endl;
    addCarePairs(&tt.second, nullptr, arity[tt.first], 0);
  }
}

void TheoryStrings::assertPendingFact(Node atom, bool polarity, Node exp) {
  Trace("strings-pending") << "Assert pending fact : " << atom << " " << polarity << " from " << exp << std::endl;
  Assert(atom.getKind() != kind::OR, "Infer error: a split.");
  if( atom.getKind()==kind::EQUAL ){
    Trace("strings-pending-debug") << "  Register term" << std::endl;
    for( unsigned j=0; j<2; j++ ) {
      if( !d_equalityEngine.hasTerm( atom[j] ) && atom[j].getType().isString() ) {
        registerTerm( atom[j], 0 );
      }
    }
    Trace("strings-pending-debug") << "  Now assert equality" << std::endl;
    d_equalityEngine.assertEquality( atom, polarity, exp );
    Trace("strings-pending-debug") << "  Finished assert equality" << std::endl;
  } else {
    d_equalityEngine.assertPredicate( atom, polarity, exp );
    //process extf
    if( atom.getKind()==kind::STRING_IN_REGEXP ){
      if( polarity && atom[1].getKind()==kind::REGEXP_RANGE ){
        if( d_extf_infer_cache_u.find( atom )==d_extf_infer_cache_u.end() ){
          d_extf_infer_cache_u.insert( atom );
          //length of first argument is one
          Node conc = d_one.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, atom[0] ) );
          Node lem = NodeManager::currentNM()->mkNode( kind::OR, atom.negate(), conc );
          Trace("strings-lemma") << "Strings::Lemma RE-Range-Len : " << lem << std::endl;
          d_out->lemma( lem );
        }
      }
    }
    //register the atom here, since it may not create a new equivalence class
    //getExtTheory()->registerTerm( atom );
  }
  Trace("strings-pending-debug") << "  Now collect terms" << std::endl;
  // Collect extended function terms in the atom. Notice that we must register
  // all extended functions occurring in assertions and shared terms. We
  // make a similar call to registerTermRec in addSharedTerm.
  getExtTheory()->registerTermRec( atom );
  Trace("strings-pending-debug") << "  Finished collect terms" << std::endl;
}

void TheoryStrings::addToExplanation( Node a, Node b, std::vector< Node >& exp ) {
  if( a!=b ){
    Debug("strings-explain") << "Add to explanation : " << a << " == " << b << std::endl;
    Assert( areEqual( a, b ) );
    exp.push_back( a.eqNode( b ) );
  }
}

void TheoryStrings::addToExplanation( Node lit, std::vector< Node >& exp ) {
  if( !lit.isNull() ){
    exp.push_back( lit );
  }
}

void TheoryStrings::checkInit() {
  //build term index
  d_eqc_to_const.clear();
  d_eqc_to_const_base.clear();
  d_eqc_to_const_exp.clear();
  d_eqc_to_len_term.clear();
  d_term_index.clear();
  d_strings_eqc.clear();

  std::map< Kind, unsigned > ncongruent;
  std::map< Kind, unsigned > congruent;
  d_emptyString_r = getRepresentative( d_emptyString );
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if( !tn.isRegExp() ){
      if( tn.isString() ){
        d_strings_eqc.push_back( eqc );
      }
      Node var;
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
      while( !eqc_i.isFinished() ) {
        Node n = *eqc_i;
        if( n.isConst() ){
          d_eqc_to_const[eqc] = n;
          d_eqc_to_const_base[eqc] = n;
          d_eqc_to_const_exp[eqc] = Node::null();
        }else if( tn.isInteger() ){
          if( n.getKind()==kind::STRING_LENGTH ){
            Node nr = getRepresentative( n[0] );
            d_eqc_to_len_term[nr] = n[0];
          }
        }else if( n.getNumChildren()>0 ){
          Kind k = n.getKind();
          if( k!=kind::EQUAL ){
            if( d_congruent.find( n )==d_congruent.end() ){
              std::vector< Node > c;
              Node nc = d_term_index[k].add( n, 0, this, d_emptyString_r, c );
              if( nc!=n ){
                //check if we have inferred a new equality by removal of empty components
                if( n.getKind()==kind::STRING_CONCAT && !areEqual( nc, n ) ){
                  std::vector< Node > exp;
                  unsigned count[2] = { 0, 0 };
                  while( count[0]<nc.getNumChildren() || count[1]<n.getNumChildren() ){
                    //explain empty prefixes
                    for( unsigned t=0; t<2; t++ ){
                      Node nn = t==0 ? nc : n;
                      while( count[t]<nn.getNumChildren() &&
                            ( nn[count[t]]==d_emptyString || areEqual( nn[count[t]], d_emptyString ) ) ){
                        if( nn[count[t]]!=d_emptyString ){
                          exp.push_back( nn[count[t]].eqNode( d_emptyString ) );
                        }
                        count[t]++;
                      }
                    }
                    //explain equal components
                    if( count[0]<nc.getNumChildren() ){
                      Assert( count[1]<n.getNumChildren() );
                      if( nc[count[0]]!=n[count[1]] ){
                        exp.push_back( nc[count[0]].eqNode( n[count[1]] ) );
                      }
                      count[0]++;
                      count[1]++;
                    }
                  }
                  //infer the equality
                  d_im.sendInference(exp, n.eqNode(nc), "I_Norm");
                }else if( getExtTheory()->hasFunctionKind( n.getKind() ) ){
                  //mark as congruent : only process if neither has been reduced
                  getExtTheory()->markCongruent( nc, n );
                }
                //this node is congruent to another one, we can ignore it
                Trace("strings-process-debug") << "  congruent term : " << n << std::endl;
                d_congruent.insert( n );
                congruent[k]++;
              }else if( k==kind::STRING_CONCAT && c.size()==1 ){
                Trace("strings-process-debug") << "  congruent term by singular : " << n << " " << c[0] << std::endl;
                //singular case
                if( !areEqual( c[0], n ) ){
                  Node ns;
                  std::vector< Node > exp;
                  //explain empty components
                  bool foundNEmpty = false;
                  for( unsigned i=0; i<n.getNumChildren(); i++ ){
                    if( areEqual( n[i], d_emptyString ) ){
                      if( n[i]!=d_emptyString ){
                        exp.push_back( n[i].eqNode( d_emptyString ) );
                      }
                    }else{
                      Assert( !foundNEmpty );
                      ns = n[i];
                      foundNEmpty = true;
                    }
                  }
                  AlwaysAssert( foundNEmpty );
                  //infer the equality
                  d_im.sendInference(exp, n.eqNode(ns), "I_Norm_S");
                }
                d_congruent.insert( n );
                congruent[k]++;
              }else{
                ncongruent[k]++;
              }
            }else{
              congruent[k]++;
            }
          }
        }else{
          if( d_congruent.find( n )==d_congruent.end() ){
            if( var.isNull() ){
              var = n;
            }else{
              Trace("strings-process-debug") << "  congruent variable : " << n << std::endl;
              d_congruent.insert( n );
            }
          }
        }
        ++eqc_i;
      }
    }
    ++eqcs_i;
  }
  if( Trace.isOn("strings-process") ){
    for( std::map< Kind, TermIndex >::iterator it = d_term_index.begin(); it != d_term_index.end(); ++it ){
      Trace("strings-process") << "  Terms[" << it->first << "] = " << ncongruent[it->first] << "/" << (congruent[it->first]+ncongruent[it->first]) << std::endl;
    }
  }
}

void TheoryStrings::checkConstantEquivalenceClasses()
{
  // do fixed point
  unsigned prevSize;
  std::vector<Node> vecc;
  do
  {
    vecc.clear();
    Trace("strings-process-debug") << "Check constant equivalence classes..."
                                   << std::endl;
    prevSize = d_eqc_to_const.size();
    checkConstantEquivalenceClasses(&d_term_index[kind::STRING_CONCAT], vecc);
  } while (!d_im.hasProcessed() && d_eqc_to_const.size() > prevSize);
}

void TheoryStrings::checkConstantEquivalenceClasses( TermIndex* ti, std::vector< Node >& vecc ) {
  Node n = ti->d_data;
  if( !n.isNull() ){
    //construct the constant
    Node c = mkConcat( vecc );
    if( !areEqual( n, c ) ){
      Trace("strings-debug") << "Constant eqc : " << c << " for " << n << std::endl;
      Trace("strings-debug") << "  ";
      for( unsigned i=0; i<vecc.size(); i++ ){
        Trace("strings-debug") << vecc[i] << " ";
      }
      Trace("strings-debug") << std::endl;
      unsigned count = 0;
      unsigned countc = 0;
      std::vector< Node > exp;
      while( count<n.getNumChildren() ){
        while( count<n.getNumChildren() && areEqual( n[count], d_emptyString ) ){
          addToExplanation( n[count], d_emptyString, exp );
          count++;
        }
        if( count<n.getNumChildren() ){
          Trace("strings-debug") << "...explain " << n[count] << " " << vecc[countc] << std::endl;
          if( !areEqual( n[count], vecc[countc] ) ){
            Node nrr = getRepresentative( n[count] );
            Assert( !d_eqc_to_const_exp[nrr].isNull() );
            addToExplanation( n[count], d_eqc_to_const_base[nrr], exp );
            exp.push_back( d_eqc_to_const_exp[nrr] );
          }else{
            addToExplanation( n[count], vecc[countc], exp );
          }
          countc++;
          count++;
        }
      }
      //exp contains an explanation of n==c
      Assert( countc==vecc.size() );
      if( hasTerm( c ) ){
        d_im.sendInference(exp, n.eqNode(c), "I_CONST_MERGE");
        return;
      }
      else if (!d_im.hasProcessed())
      {
        Node nr = getRepresentative( n );
        std::map< Node, Node >::iterator it = d_eqc_to_const.find( nr );
        if( it==d_eqc_to_const.end() ){
          Trace("strings-debug") << "Set eqc const " << n << " to " << c << std::endl;
          d_eqc_to_const[nr] = c;
          d_eqc_to_const_base[nr] = n;
          d_eqc_to_const_exp[nr] = utils::mkAnd(exp);
        }else if( c!=it->second ){
          //conflict
          Trace("strings-debug") << "Conflict, other constant was " << it->second << ", this constant was " << c << std::endl;
          if( d_eqc_to_const_exp[nr].isNull() ){
            // n==c ^ n == c' => false
            addToExplanation( n, it->second, exp );
          }else{
            // n==c ^ n == d_eqc_to_const_base[nr] == c' => false
            exp.push_back( d_eqc_to_const_exp[nr] );
            addToExplanation( n, d_eqc_to_const_base[nr], exp );
          }
          d_im.sendInference(exp, d_false, "I_CONST_CONFLICT");
          return;
        }else{
          Trace("strings-debug") << "Duplicate constant." << std::endl;
        }
      }
    }
  }
  for( std::map< TNode, TermIndex >::iterator it = ti->d_children.begin(); it != ti->d_children.end(); ++it ){
    std::map< Node, Node >::iterator itc = d_eqc_to_const.find( it->first );
    if( itc!=d_eqc_to_const.end() ){
      vecc.push_back( itc->second );
      checkConstantEquivalenceClasses( &it->second, vecc );
      vecc.pop_back();
      if (d_im.hasProcessed())
      {
        break;
      }
    }
  }
}

void TheoryStrings::checkExtfEval( int effort ) {
  Trace("strings-extf-list") << "Active extended functions, effort=" << effort << " : " << std::endl;
  d_extf_info_tmp.clear();
  bool has_nreduce = false;
  std::vector< Node > terms = getExtTheory()->getActive();
  std::vector< Node > sterms; 
  std::vector< std::vector< Node > > exp;
  getExtTheory()->getSubstitutedTerms( effort, terms, sterms, exp );
  for( unsigned i=0; i<terms.size(); i++ ){
    Node n = terms[i];
    Node sn = sterms[i];
    //setup information about extf
    ExtfInfoTmp& einfo = d_extf_info_tmp[n];
    Node r = getRepresentative(n);
    std::map<Node, Node>::iterator itcit = d_eqc_to_const.find(r);
    if (itcit != d_eqc_to_const.end())
    {
      einfo.d_const = itcit->second;
    }
    Trace("strings-extf-debug") << "Check extf " << n << " == " << sn
                                << ", constant = " << einfo.d_const
                                << ", effort=" << effort << "..." << std::endl;
    //do the inference
    Node to_reduce;
    if( n!=sn ){
      einfo.d_exp.insert(einfo.d_exp.end(), exp[i].begin(), exp[i].end());
      // inference is rewriting the substituted node
      Node nrc = Rewriter::rewrite( sn );
      //if rewrites to a constant, then do the inference and mark as reduced
      if( nrc.isConst() ){
        if( effort<3 ){
          getExtTheory()->markReduced( n );
          Trace("strings-extf-debug") << "  resolvable by evaluation..." << std::endl;
          std::vector< Node > exps;
          // The following optimization gets the "symbolic definition" of
          // an extended term. The symbolic definition of a term t is a term
          // t' where constants are replaced by their corresponding proxy
          // variables.
          // For example, if lsym is a proxy variable for "", then
          // str.replace( lsym, lsym, lsym ) is the symbolic definition for
          // str.replace( "", "", "" ). It is generally better to use symbolic
          // definitions when doing cd-rewriting for the purpose of minimizing
          // clauses, e.g. we infer the unit equality:
          //    str.replace( lsym, lsym, lsym ) == ""
          // instead of making this inference multiple times:
          //    x = "" => str.replace( x, x, x ) == ""
          //    y = "" => str.replace( y, y, y ) == ""
          Trace("strings-extf-debug") << "  get symbolic definition..." << std::endl;
          Node nrs = getSymbolicDefinition( sn, exps );
          if( !nrs.isNull() ){
            Trace("strings-extf-debug") << "  rewrite " << nrs << "..." << std::endl;
            Node nrsr = Rewriter::rewrite(nrs);
            // ensure the symbolic form is not rewritable
            if (nrsr != nrs)
            {
              // we cannot use the symbolic definition if it rewrites
              Trace("strings-extf-debug") << "  symbolic definition is trivial..." << std::endl;
              nrs = Node::null();
            }
          }else{
            Trace("strings-extf-debug") << "  could not infer symbolic definition." << std::endl;
          }
          Node conc;
          if( !nrs.isNull() ){
            Trace("strings-extf-debug") << "  symbolic def : " << nrs << std::endl;
            if( !areEqual( nrs, nrc ) ){
              //infer symbolic unit
              if( n.getType().isBoolean() ){
                conc = nrc==d_true ? nrs : nrs.negate();
              }else{
                conc = nrs.eqNode( nrc );
              }
              einfo.d_exp.clear();
            }
          }else{
            if( !areEqual( n, nrc ) ){
              if( n.getType().isBoolean() ){
                if( areEqual( n, nrc==d_true ? d_false : d_true )  ){
                  einfo.d_exp.push_back(nrc == d_true ? n.negate() : n);
                  conc = d_false;
                }else{
                  conc = nrc==d_true ? n : n.negate();
                }
              }else{
                conc = n.eqNode( nrc );
              }
            }
          }
          if( !conc.isNull() ){
            Trace("strings-extf") << "  resolve extf : " << sn << " -> " << nrc << std::endl;
            d_im.sendInference(
                einfo.d_exp, conc, effort == 0 ? "EXTF" : "EXTF-N", true);
            if( d_conflict ){
              Trace("strings-extf-debug") << "  conflict, return." << std::endl;
              return;
            }
          }
        }else{
          //check if it is already equal, if so, mark as reduced. Otherwise, do nothing.
          if( areEqual( n, nrc ) ){ 
            Trace("strings-extf") << "  resolved extf, since satisfied by model: " << n << std::endl;
            einfo.d_model_active = false;
          }
        }
      }
      else
      {
        // if this was a predicate which changed after substitution + rewriting
        if (!einfo.d_const.isNull() && nrc.getType().isBoolean() && nrc != n)
        {
          bool pol = einfo.d_const == d_true;
          Node nrcAssert = pol ? nrc : nrc.negate();
          Node nAssert = pol ? n : n.negate();
          Assert(effort < 3);
          einfo.d_exp.push_back(nAssert);
          Trace("strings-extf-debug") << "  decomposable..." << std::endl;
          Trace("strings-extf") << "  resolve extf : " << sn << " -> " << nrc
                                << ", const = " << einfo.d_const << std::endl;
          // We send inferences internal here, which may help show unsat.
          // However, we do not make a determination whether n can be marked
          // reduced since this argument may be circular: we may infer than n
          // can be reduced to something else, but that thing may argue that it
          // can be reduced to n, in theory.
          d_im.sendInternalInference(
              einfo.d_exp, nrcAssert, effort == 0 ? "EXTF_d" : "EXTF_d-N");
        }
        to_reduce = nrc;
      }
    }else{
      to_reduce = sterms[i];
    }
    //if not reduced
    if( !to_reduce.isNull() ){
      Assert( effort<3 );
      if( effort==1 ){
        Trace("strings-extf") << "  cannot rewrite extf : " << to_reduce << std::endl;
      }
      checkExtfInference(n, to_reduce, einfo, effort);
      if( Trace.isOn("strings-extf-list") ){
        Trace("strings-extf-list") << "  * " << to_reduce;
        if (!einfo.d_const.isNull())
        {
          Trace("strings-extf-list") << ", const = " << einfo.d_const;
        }
        if( n!=to_reduce ){
          Trace("strings-extf-list") << ", from " << n;
        }
        Trace("strings-extf-list") << std::endl;
      }
      if (getExtTheory()->isActive(n) && einfo.d_model_active)
      {
        has_nreduce = true;
      }
    }
  }
  d_has_extf = has_nreduce;
}

void TheoryStrings::checkExtfInference( Node n, Node nr, ExtfInfoTmp& in, int effort ){
  if (in.d_const.isNull())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  Trace("strings-extf-infer") << "checkExtfInference: " << n << " : " << nr
                              << " == " << in.d_const << std::endl;

  // add original to explanation
  if (n.getType().isBoolean())
  {
    // if Boolean, it's easy
    in.d_exp.push_back(in.d_const.getConst<bool>() ? n : n.negate());
  }
  else
  {
    // otherwise, must explain via base node
    Node r = getRepresentative(n);
    // we have that:
    //   d_eqc_to_const_exp[r] => d_eqc_to_const_base[r] = in.d_const
    // thus:
    //   n = d_eqc_to_const_base[r] ^ d_eqc_to_const_exp[r] => n = in.d_const
    Assert(d_eqc_to_const_base.find(r) != d_eqc_to_const_base.end());
    addToExplanation(n, d_eqc_to_const_base[r], in.d_exp);
    Assert(d_eqc_to_const_exp.find(r) != d_eqc_to_const_exp.end());
    in.d_exp.insert(in.d_exp.end(),
                    d_eqc_to_const_exp[r].begin(),
                    d_eqc_to_const_exp[r].end());
  }

  // d_extf_infer_cache stores whether we have made the inferences associated
  // with a node n,
  // this may need to be generalized if multiple inferences apply

  if (nr.getKind() == STRING_STRCTN)
  {
    Assert(in.d_const.isConst());
    bool pol = in.d_const.getConst<bool>();
    if ((pol && nr[1].getKind() == STRING_CONCAT)
        || (!pol && nr[0].getKind() == STRING_CONCAT))
    {
      // If str.contains( x, str.++( y1, ..., yn ) ),
      //   we may infer str.contains( x, y1 ), ..., str.contains( x, yn )
      // The following recognizes two situations related to the above reasoning:
      // (1) If ~str.contains( x, yi ) holds for some i, we are in conflict,
      // (2) If str.contains( x, yj ) already holds for some j, then the term
      // str.contains( x, yj ) is irrelevant since it is satisfied by all models
      // for str.contains( x, str.++( y1, ..., yn ) ).

      // Notice that the dual of the above reasoning also holds, i.e.
      // If ~str.contains( str.++( x1, ..., xn ), y ),
      //   we may infer ~str.contains( x1, y ), ..., ~str.contains( xn, y )
      // This is also handled here.
      if (d_extf_infer_cache.find(nr) == d_extf_infer_cache.end())
      {
        d_extf_infer_cache.insert(nr);

        int index = pol ? 1 : 0;
        std::vector<Node> children;
        children.push_back(nr[0]);
        children.push_back(nr[1]);
        for (const Node& nrc : nr[index])
        {
          children[index] = nrc;
          Node conc = nm->mkNode(STRING_STRCTN, children);
          conc = Rewriter::rewrite(pol ? conc : conc.negate());
          // check if it already (does not) hold
          if (hasTerm(conc))
          {
            if (areEqual(conc, d_false))
            {
              // we are in conflict
              d_im.sendInference(in.d_exp, conc, "CTN_Decompose");
            }
            else if (getExtTheory()->hasFunctionKind(conc.getKind()))
            {
              // can mark as reduced, since model for n implies model for conc
              getExtTheory()->markReduced(conc);
            }
          }
        }
      }
    }
    else
    {
      if (std::find(d_extf_info_tmp[nr[0]].d_ctn[pol].begin(),
                    d_extf_info_tmp[nr[0]].d_ctn[pol].end(),
                    nr[1])
          == d_extf_info_tmp[nr[0]].d_ctn[pol].end())
      {
        Trace("strings-extf-debug") << "  store contains info : " << nr[0]
                                    << " " << pol << " " << nr[1] << std::endl;
        // Store s (does not) contains t, since nr = (~)contains( s, t ) holds.
        d_extf_info_tmp[nr[0]].d_ctn[pol].push_back(nr[1]);
        d_extf_info_tmp[nr[0]].d_ctn_from[pol].push_back(n);
        // Do transistive closure on contains, e.g.
        // if contains( s, t ) and ~contains( s, r ), then ~contains( t, r ).

        // The following infers new (negative) contains based on the above
        // reasoning, provided that ~contains( t, r ) does not
        // already hold in the current context. We test this by checking that
        // contains( t, r ) is not already asserted false in the current
        // context. We also handle the case where contains( t, r ) is equivalent
        // to t = r, in which case we check that t != r does not already hold
        // in the current context.

        // Notice that form of the above inference is enough to find
        // conflicts purely due to contains predicates. For example, if we
        // have only positive occurrences of contains, then no conflicts due to
        // contains predicates are possible and this schema does nothing. For
        // example, note that contains( s, t ) and contains( t, r ) implies
        // contains( s, r ), which we could but choose not to infer. Instead,
        // we prefer being lazy: only if ~contains( s, r ) appears later do we
        // infer ~contains( t, r ), which suffices to show a conflict.
        bool opol = !pol;
        for (unsigned i = 0, size = d_extf_info_tmp[nr[0]].d_ctn[opol].size();
             i < size;
             i++)
        {
          Node onr = d_extf_info_tmp[nr[0]].d_ctn[opol][i];
          Node conc =
              nm->mkNode(STRING_STRCTN, pol ? nr[1] : onr, pol ? onr : nr[1]);
          conc = Rewriter::rewrite(conc);
          conc = conc.negate();
          bool do_infer = false;
          bool pol = conc.getKind() != NOT;
          Node lit = pol ? conc : conc[0];
          if (lit.getKind() == EQUAL)
          {
            do_infer = pol ? !areEqual(lit[0], lit[1])
                           : !areDisequal(lit[0], lit[1]);
          }
          else
          {
            do_infer = !areEqual(lit, pol ? d_true : d_false);
          }
          if (do_infer)
          {
            std::vector<Node> exp_c;
            exp_c.insert(exp_c.end(), in.d_exp.begin(), in.d_exp.end());
            Node ofrom = d_extf_info_tmp[nr[0]].d_ctn_from[opol][i];
            Assert(d_extf_info_tmp.find(ofrom) != d_extf_info_tmp.end());
            exp_c.insert(exp_c.end(),
                         d_extf_info_tmp[ofrom].d_exp.begin(),
                         d_extf_info_tmp[ofrom].d_exp.end());
            d_im.sendInference(exp_c, conc, "CTN_Trans");
          }
        }
      }
      else
      {
        // If we already know that s (does not) contain t, then n is redundant.
        // For example, if str.contains( x, y ), str.contains( z, y ), and x=z
        // are asserted in the current context, then str.contains( z, y ) is
        // satisfied by all models of str.contains( x, y ) ^ x=z and thus can
        // be ignored.
        Trace("strings-extf-debug") << "  redundant." << std::endl;
        getExtTheory()->markReduced(n);
      }
    }
    return;
  }

  // If it's not a predicate, see if we can solve the equality n = c, where c
  // is the constant that extended term n is equal to.
  Node inferEq = nr.eqNode(in.d_const);
  Node inferEqr = Rewriter::rewrite(inferEq);
  Node inferEqrr = inferEqr;
  if (inferEqr.getKind() == EQUAL)
  {
    // try to use the extended rewriter for equalities
    inferEqrr = TheoryStringsRewriter::rewriteEqualityExt(inferEqr);
  }
  if (inferEqrr != inferEqr)
  {
    inferEqrr = Rewriter::rewrite(inferEqrr);
    Trace("strings-extf-infer") << "checkExtfInference: " << inferEq
                                << " ...reduces to " << inferEqrr << std::endl;
    d_im.sendInternalInference(in.d_exp, inferEqrr, "EXTF_equality_rew");
  }
}

Node TheoryStrings::getProxyVariableFor(Node n) const
{
  NodeNodeMap::const_iterator it = d_proxy_var.find(n);
  if (it != d_proxy_var.end())
  {
    return (*it).second;
  }
  return Node::null();
}
Node TheoryStrings::getSymbolicDefinition(Node n, std::vector<Node>& exp) const
{
  if( n.getNumChildren()==0 ){
    Node pn = getProxyVariableFor(n);
    if (pn.isNull())
    {
      return Node::null();
    }
    Node eq = n.eqNode(pn);
    eq = Rewriter::rewrite(eq);
    if (std::find(exp.begin(), exp.end(), eq) == exp.end())
    {
      exp.push_back(eq);
    }
    return pn;
  }else{
    std::vector< Node > children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      children.push_back( n.getOperator() );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( n.getKind()==kind::STRING_IN_REGEXP && i==1 ){
        children.push_back( n[i] );
      }else{
        Node ns = getSymbolicDefinition( n[i], exp );
        if( ns.isNull() ){
          return Node::null();
        }else{
          children.push_back( ns );
        }
      }
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), children );
  }
}

Node TheoryStrings::getConstantEqc( Node eqc ) {
  std::map< Node, Node >::iterator it = d_eqc_to_const.find( eqc );
  if( it!=d_eqc_to_const.end() ){
    return it->second;
  }else{
    return Node::null();
  }
}

void TheoryStrings::debugPrintFlatForms( const char * tc ){
  for( unsigned k=0; k<d_strings_eqc.size(); k++ ){
    Node eqc = d_strings_eqc[k];
    if( d_eqc[eqc].size()>1 ){
      Trace( tc ) << "EQC [" << eqc << "]" << std::endl;
    }else{
      Trace( tc ) << "eqc [" << eqc << "]";
    }
    std::map< Node, Node >::iterator itc = d_eqc_to_const.find( eqc );
    if( itc!=d_eqc_to_const.end() ){
      Trace( tc ) << "  C: " << itc->second;
      if( d_eqc[eqc].size()>1 ){
        Trace( tc ) << std::endl;
      }
    }
    if( d_eqc[eqc].size()>1 ){
      for( unsigned i=0; i<d_eqc[eqc].size(); i++ ){
        Node n = d_eqc[eqc][i];
        Trace( tc ) << "    ";
        for( unsigned j=0; j<d_flat_form[n].size(); j++ ){
          Node fc = d_flat_form[n][j];
          itc = d_eqc_to_const.find( fc );
          Trace( tc ) << " ";
          if( itc!=d_eqc_to_const.end() ){
            Trace( tc ) << itc->second;
          }else{
            Trace( tc ) << fc;
          }
        }
        if( n!=eqc ){
          Trace( tc ) << ", from " << n;
        }
        Trace( tc ) << std::endl;
      }
    }else{
      Trace( tc ) << std::endl;
    }
  }
  Trace( tc ) << std::endl;
}

void TheoryStrings::debugPrintNormalForms( const char * tc ) {
}

struct sortConstLength {
  std::map< Node, unsigned > d_const_length;
  bool operator() (Node i, Node j) {
    std::map< Node, unsigned >::iterator it_i = d_const_length.find( i );
    std::map< Node, unsigned >::iterator it_j = d_const_length.find( j );
    if( it_i==d_const_length.end() ){
      if( it_j==d_const_length.end() ){
        return i<j;
      }else{
        return false;
      }
    }else{
      if( it_j==d_const_length.end() ){
        return true;
      }else{
        return it_i->second<it_j->second;
      }
    }
  }
};

void TheoryStrings::checkCycles()
{
  // first check for cycles, while building ordering of equivalence classes
  d_flat_form.clear();
  d_flat_form_index.clear();
  d_eqc.clear();
  //rebuild strings eqc based on acyclic ordering
  std::vector< Node > eqc;
  eqc.insert( eqc.end(), d_strings_eqc.begin(), d_strings_eqc.end() );
  d_strings_eqc.clear();
  if( options::stringBinaryCsp() ){
    //sort: process smallest constants first (necessary if doing binary splits)
    sortConstLength scl;
    for( unsigned i=0; i<eqc.size(); i++ ){
      std::map< Node, Node >::iterator itc = d_eqc_to_const.find( eqc[i] );
      if( itc!=d_eqc_to_const.end() ){
        scl.d_const_length[eqc[i]] = itc->second.getConst<String>().size();
      }
    }
    std::sort( eqc.begin(), eqc.end(), scl );
  }
  for( unsigned i=0; i<eqc.size(); i++ ){
    std::vector< Node > curr;
    std::vector< Node > exp;
    checkCycles( eqc[i], curr, exp );
    if (d_im.hasProcessed())
    {
      return;
    }
  }
}

void TheoryStrings::checkFlatForms()
{
  // debug print flat forms
  if (Trace.isOn("strings-ff"))
  {
    Trace("strings-ff") << "Flat forms : " << std::endl;
    debugPrintFlatForms("strings-ff");
  }

  // inferences without recursively expanding flat forms

  //(1) approximate equality by containment, infer conflicts
  for (const Node& eqc : d_strings_eqc)
  {
    Node c = getConstantEqc(eqc);
    if (!c.isNull())
    {
      // if equivalence class is constant, all component constants in flat forms
      // must be contained in it, in order
      std::map<Node, std::vector<Node> >::iterator it = d_eqc.find(eqc);
      if (it != d_eqc.end())
      {
        for (const Node& n : it->second)
        {
          int firstc, lastc;
          if (!TheoryStringsRewriter::canConstantContainList(
                  c, d_flat_form[n], firstc, lastc))
          {
            Trace("strings-ff-debug") << "Flat form for " << n
                                      << " cannot be contained in constant "
                                      << c << std::endl;
            Trace("strings-ff-debug") << "  indices = " << firstc << "/"
                                      << lastc << std::endl;
            // conflict, explanation is n = base ^ base = c ^ relevant portion
            // of ( n = f[n] )
            std::vector<Node> exp;
            Assert(d_eqc_to_const_base.find(eqc) != d_eqc_to_const_base.end());
            addToExplanation(n, d_eqc_to_const_base[eqc], exp);
            Assert(d_eqc_to_const_exp.find(eqc) != d_eqc_to_const_exp.end());
            if (!d_eqc_to_const_exp[eqc].isNull())
            {
              exp.push_back(d_eqc_to_const_exp[eqc]);
            }
            for (int e = firstc; e <= lastc; e++)
            {
              if (d_flat_form[n][e].isConst())
              {
                Assert(e >= 0 && e < (int)d_flat_form_index[n].size());
                Assert(d_flat_form_index[n][e] >= 0
                       && d_flat_form_index[n][e] < (int)n.getNumChildren());
                addToExplanation(
                    d_flat_form[n][e], n[d_flat_form_index[n][e]], exp);
              }
            }
            Node conc = d_false;
            d_im.sendInference(exp, conc, "F_NCTN");
            return;
          }
        }
      }
    }
  }

  //(2) scan lists, unification to infer conflicts and equalities
  for (const Node& eqc : d_strings_eqc)
  {
    std::map<Node, std::vector<Node> >::iterator it = d_eqc.find(eqc);
    if (it == d_eqc.end() || it->second.size() <= 1)
    {
      continue;
    }
    // iterate over start index
    for (unsigned start = 0; start < it->second.size() - 1; start++)
    {
      for (unsigned r = 0; r < 2; r++)
      {
        bool isRev = r == 1;
        checkFlatForm(it->second, start, isRev);
        if (d_conflict)
        {
          return;
        }
      }
    }
  }
}

void TheoryStrings::checkFlatForm(std::vector<Node>& eqc,
                                  unsigned start,
                                  bool isRev)
{
  unsigned count = 0;
  std::vector<Node> inelig;
  for (unsigned i = 0; i <= start; i++)
  {
    inelig.push_back(eqc[start]);
  }
  Node a = eqc[start];
  Node b;
  do
  {
    std::vector<Node> exp;
    Node conc;
    int inf_type = -1;
    unsigned eqc_size = eqc.size();
    unsigned asize = d_flat_form[a].size();
    if (count == asize)
    {
      for (unsigned i = start + 1; i < eqc_size; i++)
      {
        b = eqc[i];
        if (std::find(inelig.begin(), inelig.end(), b) == inelig.end())
        {
          unsigned bsize = d_flat_form[b].size();
          if (count < bsize)
          {
            // endpoint
            std::vector<Node> conc_c;
            for (unsigned j = count; j < bsize; j++)
            {
              conc_c.push_back(
                  b[d_flat_form_index[b][j]].eqNode(d_emptyString));
            }
            Assert(!conc_c.empty());
            conc = utils::mkAnd(conc_c);
            inf_type = 2;
            Assert(count > 0);
            // swap, will enforce is empty past current
            a = eqc[i];
            b = eqc[start];
            count--;
            break;
          }
          inelig.push_back(eqc[i]);
        }
      }
    }
    else
    {
      Node curr = d_flat_form[a][count];
      Node curr_c = getConstantEqc(curr);
      Node ac = a[d_flat_form_index[a][count]];
      std::vector<Node> lexp;
      Node lcurr = getLength(ac, lexp);
      for (unsigned i = 1; i < eqc_size; i++)
      {
        b = eqc[i];
        if (std::find(inelig.begin(), inelig.end(), b) == inelig.end())
        {
          if (count == d_flat_form[b].size())
          {
            inelig.push_back(b);
            // endpoint
            std::vector<Node> conc_c;
            for (unsigned j = count; j < asize; j++)
            {
              conc_c.push_back(
                  a[d_flat_form_index[a][j]].eqNode(d_emptyString));
            }
            Assert(!conc_c.empty());
            conc = utils::mkAnd(conc_c);
            inf_type = 2;
            Assert(count > 0);
            count--;
            break;
          }
          else
          {
            Node cc = d_flat_form[b][count];
            if (cc != curr)
            {
              Node bc = b[d_flat_form_index[b][count]];
              inelig.push_back(b);
              Assert(!areEqual(curr, cc));
              Node cc_c = getConstantEqc(cc);
              if (!curr_c.isNull() && !cc_c.isNull())
              {
                // check for constant conflict
                int index;
                Node s = TheoryStringsRewriter::splitConstant(
                    cc_c, curr_c, index, isRev);
                if (s.isNull())
                {
                  addToExplanation(ac, d_eqc_to_const_base[curr], exp);
                  addToExplanation(d_eqc_to_const_exp[curr], exp);
                  addToExplanation(bc, d_eqc_to_const_base[cc], exp);
                  addToExplanation(d_eqc_to_const_exp[cc], exp);
                  conc = d_false;
                  inf_type = 0;
                  break;
                }
              }
              else if ((d_flat_form[a].size() - 1) == count
                       && (d_flat_form[b].size() - 1) == count)
              {
                conc = ac.eqNode(bc);
                inf_type = 3;
                break;
              }
              else
              {
                // if lengths are the same, apply LengthEq
                std::vector<Node> lexp2;
                Node lcc = getLength(bc, lexp2);
                if (areEqual(lcurr, lcc))
                {
                  Trace("strings-ff-debug") << "Infer " << ac << " == " << bc
                                            << " since " << lcurr
                                            << " == " << lcc << std::endl;
                  // exp_n.push_back( getLength( curr, true ).eqNode(
                  // getLength( cc, true ) ) );
                  Trace("strings-ff-debug") << "Explanation for " << lcurr
                                            << " is ";
                  for (unsigned j = 0; j < lexp.size(); j++)
                  {
                    Trace("strings-ff-debug") << lexp[j] << std::endl;
                  }
                  Trace("strings-ff-debug") << "Explanation for " << lcc
                                            << " is ";
                  for (unsigned j = 0; j < lexp2.size(); j++)
                  {
                    Trace("strings-ff-debug") << lexp2[j] << std::endl;
                  }
                  exp.insert(exp.end(), lexp.begin(), lexp.end());
                  exp.insert(exp.end(), lexp2.begin(), lexp2.end());
                  addToExplanation(lcurr, lcc, exp);
                  conc = ac.eqNode(bc);
                  inf_type = 1;
                  break;
                }
              }
            }
          }
        }
      }
    }
    if (!conc.isNull())
    {
      Trace("strings-ff-debug")
          << "Found inference : " << conc << " based on equality " << a
          << " == " << b << ", " << isRev << " " << inf_type << std::endl;
      addToExplanation(a, b, exp);
      // explain why prefixes up to now were the same
      for (unsigned j = 0; j < count; j++)
      {
        Trace("strings-ff-debug") << "Add at " << d_flat_form_index[a][j] << " "
                                  << d_flat_form_index[b][j] << std::endl;
        addToExplanation(
            a[d_flat_form_index[a][j]], b[d_flat_form_index[b][j]], exp);
      }
      // explain why other components up to now are empty
      for (unsigned t = 0; t < 2; t++)
      {
        Node c = t == 0 ? a : b;
        int jj;
        if (inf_type == 3 || (t == 1 && inf_type == 2))
        {
          // explain all the empty components for F_EndpointEq, all for
          // the short end for F_EndpointEmp
          jj = isRev ? -1 : c.getNumChildren();
        }
        else
        {
          jj = t == 0 ? d_flat_form_index[a][count]
                      : d_flat_form_index[b][count];
        }
        int startj = isRev ? jj + 1 : 0;
        int endj = isRev ? c.getNumChildren() : jj;
        for (int j = startj; j < endj; j++)
        {
          if (areEqual(c[j], d_emptyString))
          {
            addToExplanation(c[j], d_emptyString, exp);
          }
        }
      }
      // notice that F_EndpointEmp is not typically applied, since
      // strict prefix equality ( a.b = a ) where a,b non-empty
      //  is conflicting by arithmetic len(a.b)=len(a)+len(b)!=len(a)
      //  when len(b)!=0.
      d_im.sendInference(
          exp,
          conc,
          inf_type == 0 ? "F_Const"
                        : (inf_type == 1 ? "F_Unify"
                                         : (inf_type == 2 ? "F_EndpointEmp"
                                                          : "F_EndpointEq")));
      if (d_conflict)
      {
        return;
      }
      break;
    }
    count++;
  } while (inelig.size() < eqc.size());

  for (const Node& n : eqc)
  {
    std::reverse(d_flat_form[n].begin(), d_flat_form[n].end());
    std::reverse(d_flat_form_index[n].begin(), d_flat_form_index[n].end());
  }
}

Node TheoryStrings::checkCycles( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp ){
  if( std::find( curr.begin(), curr.end(), eqc )!=curr.end() ){
    // a loop
    return eqc;
  }else if( std::find( d_strings_eqc.begin(), d_strings_eqc.end(), eqc )==d_strings_eqc.end() ){
    curr.push_back( eqc );
    //look at all terms in this equivalence class
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ) {
      Node n = (*eqc_i);
      if( d_congruent.find( n )==d_congruent.end() ){
        if( n.getKind() == kind::STRING_CONCAT ){
          Trace("strings-cycle") << eqc << " check term : " << n << " in " << eqc << std::endl;
          if( eqc!=d_emptyString_r ){
            d_eqc[eqc].push_back( n );
          }
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            Node nr = getRepresentative( n[i] );
            if( eqc==d_emptyString_r ){
              //for empty eqc, ensure all components are empty
              if( nr!=d_emptyString_r ){
                std::vector< Node > exp;
                exp.push_back( n.eqNode( d_emptyString ) );
                d_im.sendInference(
                    exp, n[i].eqNode(d_emptyString), "I_CYCLE_E");
                return Node::null();
              }
            }else{
              if( nr!=d_emptyString_r ){
                d_flat_form[n].push_back( nr );
                d_flat_form_index[n].push_back( i );
              }
              //for non-empty eqc, recurse and see if we find a loop
              Node ncy = checkCycles( nr, curr, exp );
              if( !ncy.isNull() ){
                Trace("strings-cycle") << eqc << " cycle: " << ncy << " at " << n << "[" << i << "] : " << n[i] << std::endl;
                addToExplanation( n, eqc, exp );
                addToExplanation( nr, n[i], exp );
                if( ncy==eqc ){
                  //can infer all other components must be empty
                  for( unsigned j=0; j<n.getNumChildren(); j++ ){
                    //take first non-empty
                    if( j!=i && !areEqual( n[j], d_emptyString ) ){
                      d_im.sendInference(
                          exp, n[j].eqNode(d_emptyString), "I_CYCLE");
                      return Node::null();
                    }
                  }
                  Trace("strings-error") << "Looping term should be congruent : " << n << " " << eqc << " " << ncy << std::endl;
                  //should find a non-empty component, otherwise would have been singular congruent (I_Norm_S)
                  Assert( false );
                }else{
                  return ncy;
                }
              }else{
                if (d_im.hasProcessed())
                {
                  return Node::null();
                }
              }
            }
          }
        }
      }
      ++eqc_i;
    }
    curr.pop_back();
    //now we can add it to the list of equivalence classes
    d_strings_eqc.push_back( eqc );
  }else{
    //already processed
  }
  return Node::null();
}

void TheoryStrings::checkNormalFormsEq()
{
  if( !options::stringEagerLen() ){
    for( unsigned i=0; i<d_strings_eqc.size(); i++ ) {
      Node eqc = d_strings_eqc[i];
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
      while( !eqc_i.isFinished() ) {
        Node n = (*eqc_i);
        if( d_congruent.find( n )==d_congruent.end() ){
          registerTerm( n, 2 );
        }
        ++eqc_i;
      }
    }
  }

  if (d_im.hasProcessed())
  {
    return;
  }
  // calculate normal forms for each equivalence class, possibly adding
  // splitting lemmas
  d_normal_form.clear();
  std::map<Node, Node> nf_to_eqc;
  std::map<Node, Node> eqc_to_nf;
  std::map<Node, Node> eqc_to_exp;
  for (const Node& eqc : d_strings_eqc)
  {
    Trace("strings-process-debug") << "- Verify normal forms are the same for "
                                   << eqc << std::endl;
    normalizeEquivalenceClass(eqc);
    Trace("strings-debug") << "Finished normalizing eqc..." << std::endl;
    if (d_im.hasProcessed())
    {
      return;
    }
    NormalForm& nfe = getNormalForm(eqc);
    Node nf_term = mkConcat(nfe.d_nf);
    std::map<Node, Node>::iterator itn = nf_to_eqc.find(nf_term);
    if (itn != nf_to_eqc.end())
    {
      NormalForm& nfe_eq = getNormalForm(itn->second);
      // two equivalence classes have same normal form, merge
      std::vector<Node> nf_exp;
      nf_exp.push_back(utils::mkAnd(nfe.d_exp));
      nf_exp.push_back(eqc_to_exp[itn->second]);
      Node eq = nfe.d_base.eqNode(nfe_eq.d_base);
      d_im.sendInference(nf_exp, eq, "Normal_Form");
      if (d_im.hasProcessed())
      {
        return;
      }
    }
    else
    {
      nf_to_eqc[nf_term] = eqc;
      eqc_to_nf[eqc] = nf_term;
      eqc_to_exp[eqc] = utils::mkAnd(nfe.d_exp);
    }
    Trace("strings-process-debug")
        << "Done verifying normal forms are the same for " << eqc << std::endl;
  }
  if (Trace.isOn("strings-nf"))
  {
    Trace("strings-nf") << "**** Normal forms are : " << std::endl;
    for (std::map<Node, Node>::iterator it = eqc_to_exp.begin();
         it != eqc_to_exp.end();
         ++it)
    {
      NormalForm& nf = getNormalForm(it->first);
      Trace("strings-nf") << "  N[" << it->first << "] (base " << nf.d_base
                          << ") = " << eqc_to_nf[it->first] << std::endl;
      Trace("strings-nf") << "     exp: " << it->second << std::endl;
    }
    Trace("strings-nf") << std::endl;
  }
}

void TheoryStrings::checkCodes()
{
  // ensure that lemmas regarding str.code been added for each constant string
  // of length one
  if (d_has_str_code)
  {
    NodeManager* nm = NodeManager::currentNM();
    // str.code applied to the code term for each equivalence class that has a
    // code term but is not a constant
    std::vector<Node> nconst_codes;
    // str.code applied to the proxy variables for each equivalence classes that
    // are constants of size one
    std::vector<Node> const_codes;
    for (const Node& eqc : d_strings_eqc)
    {
      NormalForm& nfe = getNormalForm(eqc);
      if (nfe.d_nf.size() == 1 && nfe.d_nf[0].isConst())
      {
        Node c = nfe.d_nf[0];
        Trace("strings-code-debug") << "Get proxy variable for " << c
                                    << std::endl;
        Node cc = nm->mkNode(kind::STRING_CODE, c);
        cc = Rewriter::rewrite(cc);
        Assert(cc.isConst());
        Node cp = getProxyVariableFor(c);
        AlwaysAssert(!cp.isNull());
        Node vc = nm->mkNode(STRING_CODE, cp);
        if (!areEqual(cc, vc))
        {
          d_im.sendInference(d_empty_vec, cc.eqNode(vc), "Code_Proxy");
        }
        const_codes.push_back(vc);
      }
      else
      {
        EqcInfo* ei = getOrMakeEqcInfo(eqc, false);
        if (ei && !ei->d_code_term.get().isNull())
        {
          Node vc = nm->mkNode(kind::STRING_CODE, ei->d_code_term.get());
          nconst_codes.push_back(vc);
        }
      }
    }
    if (d_im.hasProcessed())
    {
      return;
    }
    // now, ensure that str.code is injective
    std::vector<Node> cmps;
    cmps.insert(cmps.end(), const_codes.rbegin(), const_codes.rend());
    cmps.insert(cmps.end(), nconst_codes.rbegin(), nconst_codes.rend());
    for (unsigned i = 0, num_ncc = nconst_codes.size(); i < num_ncc; i++)
    {
      Node c1 = nconst_codes[i];
      cmps.pop_back();
      for (const Node& c2 : cmps)
      {
        Trace("strings-code-debug")
            << "Compare codes : " << c1 << " " << c2 << std::endl;
        if (!areDisequal(c1, c2) && !areEqual(c1, d_neg_one))
        {
          Node eq_no = c1.eqNode(d_neg_one);
          Node deq = c1.eqNode(c2).negate();
          Node eqn = c1[0].eqNode(c2[0]);
          // str.code(x)==-1 V str.code(x)!=str.code(y) V x==y
          Node inj_lem = nm->mkNode(kind::OR, eq_no, deq, eqn);
          d_im.sendInference(d_empty_vec, inj_lem, "Code_Inj");
        }
      }
    }
  }
}

//compute d_normal_forms_(base,exp,exp_depend)[eqc]
void TheoryStrings::normalizeEquivalenceClass( Node eqc ) {
  Trace("strings-process-debug") << "Process equivalence class " << eqc << std::endl;
  if( areEqual( eqc, d_emptyString ) ) {
#ifdef CVC4_ASSERTIONS
    for( unsigned j=0; j<d_eqc[eqc].size(); j++ ){
      Node n = d_eqc[eqc][j];
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Assert( areEqual( n[i], d_emptyString ) );
      }
    }
#endif
    //do nothing
    Trace("strings-process-debug") << "Return process equivalence class " << eqc << " : empty." << std::endl;
    d_normal_form[eqc].init(d_emptyString);
  } else {
    // should not have computed the normal form of this equivalence class yet
    Assert(d_normal_form.find(eqc) == d_normal_form.end());
    // Normal forms for the relevant terms in the equivalence class of eqc
    std::vector<NormalForm> normal_forms;
    // map each term to its index in the above vector
    std::map<Node, unsigned> term_to_nf_index;
    // get the normal forms
    getNormalForms(eqc, normal_forms, term_to_nf_index);
    if (d_im.hasProcessed())
    {
      return;
    }
    // process the normal forms
    processNEqc(normal_forms);
    if (d_im.hasProcessed())
    {
      return;
    }
    // debugPrintNormalForms( "strings-solve", eqc, normal_forms );

    //construct the normal form
    Assert( !normal_forms.empty() );
    unsigned nf_index = 0;
    std::map<Node, unsigned>::iterator it = term_to_nf_index.find(eqc);
    // we prefer taking the normal form whose base is the equivalence
    // class representative, since this leads to shorter explanations in
    // some cases.
    if (it != term_to_nf_index.end())
    {
      nf_index = it->second;
    }
    d_normal_form[eqc] = normal_forms[nf_index];
    Trace("strings-process-debug")
        << "Return process equivalence class " << eqc
        << " : returned, size = " << d_normal_form[eqc].d_nf.size()
        << std::endl;
  }
}

NormalForm& TheoryStrings::getNormalForm(Node n)
{
  std::map<Node, NormalForm>::iterator itn = d_normal_form.find(n);
  if (itn == d_normal_form.end())
  {
    Trace("strings-warn") << "WARNING: returning empty normal form for " << n
                          << std::endl;
    // Shouln't ask for normal forms of strings that weren't computed. This
    // likely means that n is not a representative or not a term in the current
    // context. We simply return a default normal form here in this case.
    Assert(false);
    return d_normal_form[n];
  }
  return itn->second;
}

void TheoryStrings::getNormalForms(Node eqc,
                                   std::vector<NormalForm>& normal_forms,
                                   std::map<Node, unsigned>& term_to_nf_index)
{
  //constant for equivalence class
  Node eqc_non_c = eqc;
  Trace("strings-process-debug") << "Get normal forms " << eqc << std::endl;
  eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
  while( !eqc_i.isFinished() ){
    Node n = (*eqc_i);
    if( d_congruent.find( n )==d_congruent.end() ){
      if (n.getKind() == CONST_STRING || n.getKind() == STRING_CONCAT)
      {
        Trace("strings-process-debug") << "Get Normal Form : Process term " << n << " in eqc " << eqc << std::endl;
        NormalForm nf_curr;
        if (n.getKind() == CONST_STRING)
        {
          nf_curr.init(n);
        }
        else if (n.getKind() == STRING_CONCAT)
        {
          // set the base to n, we construct the other portions of nf_curr in
          // the following.
          nf_curr.d_base = n;
          for( unsigned i=0; i<n.getNumChildren(); i++ ) {
            Node nr = d_equalityEngine.getRepresentative( n[i] );
            // get the normal form for the component
            NormalForm& nfr = getNormalForm(nr);
            std::vector<Node>& nfrv = nfr.d_nf;
            Trace("strings-process-debug") << "Normalizing subterm " << n[i] << " = "  << nr << std::endl;
            unsigned orig_size = nf_curr.d_nf.size();
            unsigned add_size = nfrv.size();
            //if not the empty string, add to current normal form
            if (!nfrv.empty())
            {
              // if in a build with assertions, we run the following block,
              // which checks that normal forms do not have concat terms.
              if (Configuration::isAssertionBuild())
              {
                for (const Node& nn : nfrv)
                {
                  if (Trace.isOn("strings-error"))
                  {
                    if (nn.getKind() == STRING_CONCAT)
                    {
                      Trace("strings-error")
                          << "Strings::Error: From eqc = " << eqc << ", " << n
                          << " index " << i << ", bad normal form : ";
                      for (unsigned rr = 0; rr < nfrv.size(); rr++)
                      {
                        Trace("strings-error") << nfrv[rr] << " ";
                      }
                      Trace("strings-error") << std::endl;
                    }
                  }
                  Assert(nn.getKind() != kind::STRING_CONCAT);
                }
              }
              nf_curr.d_nf.insert(nf_curr.d_nf.end(), nfrv.begin(), nfrv.end());
            }
            // Track explanation for the normal form. This is in two parts.
            // First, we must carry the explanation of the normal form computed
            // for the representative nr.
            for (const Node& exp : nfr.d_exp)
            {
              // The explanation is only relevant for the subsegment it was
              // previously relevant for, shifted now based on its relative
              // placement in the normal form of n.
              nf_curr.addToExplanation(
                  exp,
                  orig_size + nfr.d_expDep[exp][false],
                  orig_size + (add_size - nfr.d_expDep[exp][true]));
            }
            // Second, must explain that the component n[i] is equal to the
            // base of the normal form for nr.
            Node base = nfr.d_base;
            if (base != n[i])
            {
              Node eq = n[i].eqNode(base);
              // The equality is relevant for the entire current segment
              nf_curr.addToExplanation(eq, orig_size, orig_size + add_size);
            }
          }
          // Now that we are finished with the loop, we convert forward indices
          // to reverse indices in the explanation dependency information
          int total_size = nf_curr.d_nf.size();
          for (std::pair<const Node, std::map<bool, unsigned> >& ed :
               nf_curr.d_expDep)
          {
            ed.second[true] = total_size - ed.second[true];
            Assert(ed.second[true] >= 0);
          }
        }
        //if not equal to self
        std::vector<Node>& currv = nf_curr.d_nf;
        if (currv.size() > 1
            || (currv.size() == 1 && currv[0].getKind() == CONST_STRING))
        {
          // if in a build with assertions, check that normal form is acyclic
          if (Configuration::isAssertionBuild())
          {
            if (currv.size() > 1)
            {
              for (unsigned i = 0; i < currv.size(); i++)
              {
                if (Trace.isOn("strings-error"))
                {
                  Trace("strings-error") << "Cycle for normal form ";
                  printConcat(currv, "strings-error");
                  Trace("strings-error") << "..." << currv[i] << std::endl;
                }
                Assert(!areEqual(currv[i], n));
              }
            }
          }
          term_to_nf_index[n] = normal_forms.size();
          normal_forms.push_back(nf_curr);
        }else{
          //this was redundant: combination of self + empty string(s)
          Node nn = currv.size() == 0 ? d_emptyString : currv[0];
          Assert( areEqual( nn, eqc ) );
        }
      }else{
        eqc_non_c = n;
      }
    }
    ++eqc_i;
  }

  if( normal_forms.empty() ) {
    Trace("strings-solve-debug2") << "construct the normal form" << std::endl;
    // This case happens when there are no non-trivial normal forms for this
    // equivalence class. For example, given assertions:
    //   { x = y ++ z, x = y, z = "" }
    // The equivalence class of { x, y, y ++ z } is such that the normal form
    // of all terms is a variable (either x or y) in the equivalence class
    // itself. Thus, the normal form of this equivalence class can be assigned
    // to one of these variables.
    // We use a non-concatenation term among the terms in this equivalence
    // class, which is stored in eqc_non_c. The reason is this does not require
    // an explanation, whereas e.g. y ++ z would require the explanation z = ""
    // to justify its normal form is y.
    Assert(eqc_non_c.getKind() != STRING_CONCAT);
    NormalForm nf_triv;
    nf_triv.init(eqc_non_c);
    normal_forms.push_back(nf_triv);
  }else{
    if(Trace.isOn("strings-solve")) {
      Trace("strings-solve") << "--- Normal forms for equivalance class " << eqc << " : " << std::endl;
      for (unsigned i = 0, size = normal_forms.size(); i < size; i++)
      {
        NormalForm& nf = normal_forms[i];
        Trace("strings-solve") << "#" << i << " (from " << nf.d_base << ") : ";
        for (unsigned j = 0, sizej = nf.d_nf.size(); j < sizej; j++)
        {
          if(j>0) {
            Trace("strings-solve") << ", ";
          }
          Trace("strings-solve") << nf.d_nf[j];
        }
        Trace("strings-solve") << std::endl;
        Trace("strings-solve") << "   Explanation is : ";
        if (nf.d_exp.size() == 0)
        {
          Trace("strings-solve") << "NONE";
        } else {
          for (unsigned j = 0, sizej = nf.d_exp.size(); j < sizej; j++)
          {
            if(j>0) {
              Trace("strings-solve") << " AND ";
            }
            Trace("strings-solve") << nf.d_exp[j];
          }
          Trace("strings-solve") << std::endl;
          Trace("strings-solve") << "WITH DEPENDENCIES : " << std::endl;
          for (unsigned j = 0, sizej = nf.d_exp.size(); j < sizej; j++)
          {
            Node exp = nf.d_exp[j];
            Trace("strings-solve") << "   " << exp << " -> ";
            Trace("strings-solve") << nf.d_expDep[exp][false] << ",";
            Trace("strings-solve") << nf.d_expDep[exp][true] << std::endl;
          }
        }
        Trace("strings-solve") << std::endl;
        
      }
    } else {
      Trace("strings-solve") << "--- Single normal form for equivalence class " << eqc << std::endl;
    }
    
    //if equivalence class is constant, approximate as containment, infer conflicts
    Node c = getConstantEqc( eqc );
    if( !c.isNull() ){
      Trace("strings-solve") << "Eqc is constant " << c << std::endl;
      for (unsigned i = 0, size = normal_forms.size(); i < size; i++)
      {
        NormalForm& nf = normal_forms[i];
        int firstc, lastc;
        if (!TheoryStringsRewriter::canConstantContainList(
                c, nf.d_nf, firstc, lastc))
        {
          Node n = nf.d_base;
          //conflict
          Trace("strings-solve") << "Normal form for " << n << " cannot be contained in constant " << c << std::endl;
          //conflict, explanation is n = base ^ base = c ^ relevant porition of ( n = N[n] )
          std::vector< Node > exp;
          Assert( d_eqc_to_const_base.find( eqc )!=d_eqc_to_const_base.end() );
          addToExplanation( n, d_eqc_to_const_base[eqc], exp );
          Assert( d_eqc_to_const_exp.find( eqc )!=d_eqc_to_const_exp.end() );
          if( !d_eqc_to_const_exp[eqc].isNull() ){
            exp.push_back( d_eqc_to_const_exp[eqc] );
          }
          //TODO: this can be minimized based on firstc/lastc, normal_forms_exp_depend
          exp.insert(exp.end(), nf.d_exp.begin(), nf.d_exp.end());
          Node conc = d_false;
          d_im.sendInference(exp, conc, "N_NCTN");
        }
      }
    }
  }
}

void TheoryStrings::processNEqc(std::vector<NormalForm>& normal_forms)
{
  //the possible inferences
  std::vector< InferInfo > pinfer;
  // loop over all pairs 
  for(unsigned i=0; i<normal_forms.size()-1; i++) {
    //unify each normalform[j] with normal_forms[i]
    for(unsigned j=i+1; j<normal_forms.size(); j++ ) {
      NormalForm& nfi = normal_forms[i];
      NormalForm& nfj = normal_forms[j];
      //ensure that normal_forms[i] and normal_forms[j] are the same modulo equality, add to pinfer if not
      Trace("strings-solve") << "Strings: Process normal form #" << i << " against #" << j << "..." << std::endl;
      if (isNormalFormPair(nfi.d_base, nfj.d_base))
      {
        Trace("strings-solve") << "Strings: Already cached." << std::endl;
      }else{
        //process the reverse direction first (check for easy conflicts and inferences)
        unsigned rindex = 0;
        nfi.reverse();
        nfj.reverse();
        processSimpleNEq(nfi, nfj, rindex, true, 0, pinfer);
        nfi.reverse();
        nfj.reverse();
        if (d_im.hasProcessed())
        {
          return;
        }
        else if (!pinfer.empty() && pinfer.back().d_id == 1)
        {
          break;
        }
        //AJR: for less aggressive endpoint inference
        //rindex = 0;

        unsigned index = 0;
        processSimpleNEq(nfi, nfj, index, false, rindex, pinfer);
        if (d_im.hasProcessed())
        {
          return;
        }
        else if (!pinfer.empty() && pinfer.back().d_id == 1)
        {
          break;
        }
      }
    }
  }
  if (pinfer.empty())
  {
    return;
  }
  // now, determine which of the possible inferences we want to add
  unsigned use_index = 0;
  bool set_use_index = false;
  Trace("strings-solve") << "Possible inferences (" << pinfer.size()
                         << ") : " << std::endl;
  unsigned min_id = 9;
  unsigned max_index = 0;
  for (unsigned i = 0, size = pinfer.size(); i < size; i++)
  {
    Trace("strings-solve") << "From " << pinfer[i].d_i << " / " << pinfer[i].d_j
                           << " (rev=" << pinfer[i].d_rev << ") : ";
    Trace("strings-solve") << pinfer[i].d_conc << " by " << pinfer[i].d_id
                           << std::endl;
    if (!set_use_index || pinfer[i].d_id < min_id
        || (pinfer[i].d_id == min_id && pinfer[i].d_index > max_index))
    {
      min_id = pinfer[i].d_id;
      max_index = pinfer[i].d_index;
      use_index = i;
      set_use_index = true;
    }
  }
  // send the inference
  if (!pinfer[use_index].d_nf_pair[0].isNull())
  {
    Assert(!pinfer[use_index].d_nf_pair[1].isNull());
    addNormalFormPair(pinfer[use_index].d_nf_pair[0],
                      pinfer[use_index].d_nf_pair[1]);
  }
  std::stringstream ssi;
  ssi << pinfer[use_index].d_id;
  d_im.sendInference(pinfer[use_index].d_ant,
                     pinfer[use_index].d_antn,
                     pinfer[use_index].d_conc,
                     ssi.str().c_str(),
                     pinfer[use_index].sendAsLemma());
  // Register the new skolems from this inference. We register them here
  // (lazily), since the code above has now decided to use the inference
  // at use_index that involves them.
  for (const std::pair<const LengthStatus, std::vector<Node> >& sks :
       pinfer[use_index].d_new_skolem)
  {
    for (const Node& n : sks.second)
    {
      registerLength(n, sks.first);
    }
  }
}

bool TheoryStrings::InferInfo::sendAsLemma() {
  return true;
}

void TheoryStrings::processSimpleNEq(NormalForm& nfi,
                                     NormalForm& nfj,
                                     unsigned& index,
                                     bool isRev,
                                     unsigned rproc,
                                     std::vector<InferInfo>& pinfer)
{
  std::vector<Node>& nfiv = nfi.d_nf;
  std::vector<Node>& nfjv = nfj.d_nf;
  NodeManager* nm = NodeManager::currentNM();
  Assert(rproc <= nfiv.size() && rproc <= nfjv.size());
  bool success;
  do {
    success = false;
    //if we are at the end
    if (index == (nfiv.size() - rproc) || index == (nfjv.size() - rproc))
    {
      if (index == (nfiv.size() - rproc) && index == (nfjv.size() - rproc))
      {
        //we're done
      }else{
        //the remainder must be empty
        NormalForm& nfk = index == (nfiv.size() - rproc) ? nfj : nfi;
        std::vector<Node>& nfkv = nfk.d_nf;
        unsigned index_k = index;
        std::vector< Node > curr_exp;
        NormalForm::getExplanationForPrefixEq(nfi, nfj, -1, -1, curr_exp);
        while (!d_conflict && index_k < (nfkv.size() - rproc))
        {
          //can infer that this string must be empty
          Node eq = nfkv[index_k].eqNode(d_emptyString);
          //Trace("strings-lemma") << "Strings: Infer " << eq << " from " << eq_exp << std::endl;
          Assert(!areEqual(d_emptyString, nfkv[index_k]));
          d_im.sendInference(curr_exp, eq, "N_EndpointEmp");
          index_k++;
        }
      }
    }else{
      Trace("strings-solve-debug")
          << "Process " << nfiv[index] << " ... " << nfjv[index] << std::endl;
      if (nfiv[index] == nfjv[index])
      {
        Trace("strings-solve-debug") << "Simple Case 1 : strings are equal" << std::endl;
        index++;
        success = true;
      }else{
        Assert(!areEqual(nfiv[index], nfjv[index]));
        std::vector< Node > temp_exp;
        Node length_term_i = getLength(nfiv[index], temp_exp);
        Node length_term_j = getLength(nfjv[index], temp_exp);
        // check  length(nfiv[index]) == length(nfjv[index])
        if( areEqual( length_term_i, length_term_j ) ){
          Trace("strings-solve-debug") << "Simple Case 2 : string lengths are equal" << std::endl;
          Node eq = nfiv[index].eqNode(nfjv[index]);
          //eq = Rewriter::rewrite( eq );
          Node length_eq = length_term_i.eqNode( length_term_j );
          //temp_exp.insert(temp_exp.end(), curr_exp.begin(), curr_exp.end() );
          NormalForm::getExplanationForPrefixEq(
              nfi, nfj, index, index, temp_exp);
          temp_exp.push_back(length_eq);
          d_im.sendInference(temp_exp, eq, "N_Unify");
          return;
        }
        else if ((nfiv[index].getKind() != CONST_STRING
                  && index == nfiv.size() - rproc - 1)
                 || (nfjv[index].getKind() != CONST_STRING
                     && index == nfjv.size() - rproc - 1))
        {
          Trace("strings-solve-debug") << "Simple Case 3 : at endpoint" << std::endl;
          std::vector< Node > antec;
          //antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
          NormalForm::getExplanationForPrefixEq(nfi, nfj, -1, -1, antec);
          std::vector< Node > eqn;
          for( unsigned r=0; r<2; r++ ) {
            NormalForm& nfk = r == 0 ? nfi : nfj;
            std::vector<Node>& nfkv = nfk.d_nf;
            std::vector< Node > eqnc;
            for (unsigned index_l = index, size = (nfkv.size() - rproc);
                 index_l < size;
                 index_l++)
            {
              if(isRev) {
                eqnc.insert(eqnc.begin(), nfkv[index_l]);
              } else {
                eqnc.push_back(nfkv[index_l]);
              }
            }
            eqn.push_back( mkConcat( eqnc ) );
          }
          if( !areEqual( eqn[0], eqn[1] ) ){
            d_im.sendInference(
                antec, eqn[0].eqNode(eqn[1]), "N_EndpointEq", true);
            return;
          }else{
            Assert(nfiv.size() == nfjv.size());
            index = nfiv.size() - rproc;
          }
        }
        else if (nfiv[index].isConst() && nfjv[index].isConst())
        {
          Node const_str = nfiv[index];
          Node other_str = nfjv[index];
          Trace("strings-solve-debug") << "Simple Case 3 : Const Split : " << const_str << " vs " << other_str << " at index " << index << ", isRev = " << isRev << std::endl;
          unsigned len_short = const_str.getConst<String>().size() <= other_str.getConst<String>().size() ? const_str.getConst<String>().size() : other_str.getConst<String>().size();
          bool isSameFix = isRev ? const_str.getConst<String>().rstrncmp(other_str.getConst<String>(), len_short): const_str.getConst<String>().strncmp(other_str.getConst<String>(), len_short);
          if( isSameFix ) {
            //same prefix/suffix
            bool constCmp = const_str.getConst<String>().size()
                            < other_str.getConst<String>().size();
            //k is the index of the string that is shorter
            NormalForm& nfk = constCmp ? nfi : nfj;
            std::vector<Node>& nfkv = nfk.d_nf;
            NormalForm& nfl = constCmp ? nfj : nfi;
            std::vector<Node>& nflv = nfl.d_nf;
            Node remainderStr;
            if( isRev ){
              int new_len = nflv[index].getConst<String>().size() - len_short;
              remainderStr = nm->mkConst(
                  nflv[index].getConst<String>().substr(0, new_len));
            }else{
              remainderStr =
                  nm->mkConst(nflv[index].getConst<String>().substr(len_short));
            }
            Trace("strings-solve-debug-test")
                << "Break normal form of " << nflv[index] << " into "
                << nfkv[index] << ", " << remainderStr << std::endl;
            nfl.splitConstant(index, nfkv[index], remainderStr);
            index++;
            success = true;
          }else{
            //conflict
            std::vector< Node > antec;
            NormalForm::getExplanationForPrefixEq(
                nfi, nfj, index, index, antec);
            d_im.sendInference(antec, d_false, "N_Const", true);
            return;
          }
        }else{
          //construct the candidate inference "info"
          InferInfo info;
          info.d_index = index;
          //for debugging
          info.d_i = nfi.d_base;
          info.d_j = nfj.d_base;
          info.d_rev = isRev;
          bool info_valid = false;
          Assert(index < nfiv.size() - rproc && index < nfjv.size() - rproc);
          std::vector< Node > lexp;
          Node length_term_i = getLength(nfiv[index], lexp);
          Node length_term_j = getLength(nfjv[index], lexp);
          //split on equality between string lengths (note that splitting on equality between strings is worse since it is harder to process)
          if (!areDisequal(length_term_i, length_term_j)
              && !areEqual(length_term_i, length_term_j)
              && !nfiv[index].isConst() && !nfjv[index].isConst())
          {  // AJR: remove the latter 2 conditions?
            Trace("strings-solve-debug") << "Non-simple Case 1 : string lengths neither equal nor disequal" << std::endl;
            //try to make the lengths equal via splitting on demand
            Node length_eq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j );
            length_eq = Rewriter::rewrite( length_eq  );
            //set info
            info.d_conc = NodeManager::currentNM()->mkNode( kind::OR, length_eq, length_eq.negate() );
            info.d_pending_phase[ length_eq ] = true;
            info.d_id = INFER_LEN_SPLIT;
            info_valid = true;
          }else{
            Trace("strings-solve-debug") << "Non-simple Case 2 : must compare strings" << std::endl;
            int loop_in_i = -1;
            int loop_in_j = -1;
            ProcessLoopResult plr = ProcessLoopResult::SKIPPED;
            if (detectLoop(nfi, nfj, index, loop_in_i, loop_in_j, rproc))
            {
              if( !isRev ){  //FIXME
                NormalForm::getExplanationForPrefixEq(
                    nfi, nfj, -1, -1, info.d_ant);
                // set info
                plr = processLoop(loop_in_i != -1 ? nfi : nfj,
                                  loop_in_i != -1 ? nfj : nfi,
                                  loop_in_i != -1 ? loop_in_i : loop_in_j,
                                  index,
                                  info);
                if (plr == ProcessLoopResult::INFERENCE)
                {
                  info_valid = true;
                }
              }
            }

            if (plr == ProcessLoopResult::SKIPPED)
            {
              //AJR: length entailment here?
              if (nfiv[index].isConst() || nfjv[index].isConst())
              {
                NormalForm& nfc = nfiv[index].isConst() ? nfi : nfj;
                std::vector<Node>& nfcv = nfc.d_nf;
                NormalForm& nfnc = nfiv[index].isConst() ? nfj : nfi;
                std::vector<Node>& nfncv = nfnc.d_nf;
                Node other_str = nfncv[index];
                Assert( other_str.getKind()!=kind::CONST_STRING, "Other string is not constant." );
                Assert( other_str.getKind()!=kind::STRING_CONCAT, "Other string is not CONCAT." );
                if( !d_equalityEngine.areDisequal( other_str, d_emptyString, true ) ){
                  Node eq = other_str.eqNode( d_emptyString );
                  //set info
                  info.d_conc = NodeManager::currentNM()->mkNode( kind::OR, eq, eq.negate() );
                  info.d_id = INFER_LEN_SPLIT_EMP;
                  info_valid = true;
                }else{
                  if( !isRev ){  //FIXME
                  Node xnz = other_str.eqNode( d_emptyString ).negate();  
                  unsigned index_nc_k = index+1;
                  unsigned start_index_nc_k = index+1;
                  Node next_const_str =
                      TheoryStringsRewriter::getNextConstantAt(
                          nfncv, start_index_nc_k, index_nc_k, false);
                  if( !next_const_str.isNull() ) {         
                    unsigned index_c_k = index;
                    Node const_str =
                        TheoryStringsRewriter::collectConstantStringAt(
                            nfcv, index_c_k, false);
                    Assert( !const_str.isNull() );
                    CVC4::String stra = const_str.getConst<String>();
                    CVC4::String strb = next_const_str.getConst<String>();
                    //since non-empty, we start with charecter #1
                    size_t p;
                    if( isRev ){
                      CVC4::String stra1 = stra.prefix( stra.size()-1 );
                      p = stra.size() - stra1.roverlap(strb);
                      Trace("strings-csp-debug") << "Compute roverlap : " << const_str << " " << next_const_str << std::endl;
                      size_t p2 = stra1.rfind(strb); 
                      p = p2==std::string::npos ? p : ( p>p2+1? p2+1 : p );
                      Trace("strings-csp-debug") << "overlap : " << stra1 << " " << strb << " returned " << p << " " << p2 << " " << (p2==std::string::npos) << std::endl;
                    }else{
                      CVC4::String stra1 = stra.substr( 1 );
                      p = stra.size() - stra1.overlap(strb);
                      Trace("strings-csp-debug") << "Compute overlap : " << const_str << " " << next_const_str << std::endl;
                      size_t p2 = stra1.find(strb); 
                      p = p2==std::string::npos ? p : ( p>p2+1? p2+1 : p );
                      Trace("strings-csp-debug") << "overlap : " << stra1 << " " << strb << " returned " << p << " " << p2 << " " << (p2==std::string::npos) << std::endl;
                    }
                    if( p>1 ){
                      if( start_index_nc_k==index+1 ){
                        info.d_ant.push_back(xnz);
                        NormalForm::getExplanationForPrefixEq(
                            nfc, nfnc, index_c_k, index_nc_k, info.d_ant);
                        Node prea = p==stra.size() ? const_str : NodeManager::currentNM()->mkConst( isRev ? stra.suffix( p ) : stra.prefix( p ) );
                        Node sk = d_sk_cache.mkSkolemCached(
                            other_str,
                            prea,
                            isRev ? SkolemCache::SK_ID_C_SPT_REV
                                  : SkolemCache::SK_ID_C_SPT,
                            "c_spt");
                        Trace("strings-csp") << "Const Split: " << prea << " is removed from " << stra << " due to " << strb << ", p=" << p << std::endl;        
                        //set info
                        info.d_conc = other_str.eqNode( isRev ? mkConcat( sk, prea ) : mkConcat(prea, sk) );
                        info.d_new_skolem[LENGTH_SPLIT].push_back(sk);
                        info.d_id = INFER_SSPLIT_CST_PROP;
                        info_valid = true;
                      }
                    } 
                  }
                  if( !info_valid ){
                    info.d_ant.push_back( xnz );
                    Node const_str = nfcv[index];
                    NormalForm::getExplanationForPrefixEq(
                        nfi, nfj, index, index, info.d_ant);
                    CVC4::String stra = const_str.getConst<String>();
                    if( options::stringBinaryCsp() && stra.size()>3 ){
                      //split string in half
                      Node c_firstHalf =  NodeManager::currentNM()->mkConst( isRev ? stra.substr( stra.size()/2 ) : stra.substr(0, stra.size()/2 ) );
                      Node sk = d_sk_cache.mkSkolemCached(
                          other_str,
                          c_firstHalf,
                          isRev ? SkolemCache::SK_ID_VC_BIN_SPT_REV
                                : SkolemCache::SK_ID_VC_BIN_SPT,
                          "cb_spt");
                      Trace("strings-csp") << "Const Split: " << c_firstHalf << " is removed from " << const_str << " (binary) " << std::endl;
                      info.d_conc = NodeManager::currentNM()->mkNode( kind::OR, other_str.eqNode( isRev ? mkConcat( sk, c_firstHalf ) : mkConcat( c_firstHalf, sk ) ),
                                                                         NodeManager::currentNM()->mkNode( kind::AND,
                                                                           sk.eqNode( d_emptyString ).negate(),
                                                                           c_firstHalf.eqNode( isRev ? mkConcat( sk, other_str ) : mkConcat( other_str, sk ) ) ) );
                      info.d_new_skolem[LENGTH_SPLIT].push_back(sk);
                      info.d_id = INFER_SSPLIT_CST_BINARY;
                      info_valid = true;
                    }else{
                      // normal v/c split
                      Node firstChar = stra.size() == 1 ? const_str : NodeManager::currentNM()->mkConst( isRev ? stra.suffix( 1 ) : stra.prefix( 1 ) );
                      Node sk = d_sk_cache.mkSkolemCached(
                          other_str,
                          isRev ? SkolemCache::SK_ID_VC_SPT_REV
                                : SkolemCache::SK_ID_VC_SPT,
                          "c_spt");
                      Trace("strings-csp") << "Const Split: " << firstChar << " is removed from " << const_str << " (serial) " << std::endl;
                      info.d_conc = other_str.eqNode( isRev ? mkConcat( sk, firstChar ) : mkConcat(firstChar, sk) );
                      info.d_new_skolem[LENGTH_SPLIT].push_back(sk);
                      info.d_id = INFER_SSPLIT_CST;
                      info_valid = true;
                    }
                  }
                  }
                }
              }else{
                int lentTestSuccess = -1;
                Node lentTestExp;
                if( options::stringCheckEntailLen() ){
                  //check entailment
                  for( unsigned e=0; e<2; e++ ){
                    Node t = e == 0 ? nfiv[index] : nfjv[index];
                    //do not infer constants are larger than variables
                    if( t.getKind()!=kind::CONST_STRING ){
                      Node lt1 = e==0 ? length_term_i : length_term_j;
                      Node lt2 = e==0 ? length_term_j : length_term_i;
                      Node ent_lit = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::GT, lt1, lt2 ) );
                      std::pair<bool, Node> et = d_valuation.entailmentCheck( THEORY_OF_TYPE_BASED, ent_lit );
                      if( et.first ){
                        Trace("strings-entail") << "Strings entailment : " << ent_lit << " is entailed in the current context." << std::endl;
                        Trace("strings-entail") << "  explanation was : " << et.second << std::endl;
                        lentTestSuccess = e;
                        lentTestExp = et.second;
                        break;
                      }
                    }
                  }
                }

                NormalForm::getExplanationForPrefixEq(
                    nfi, nfj, index, index, info.d_ant);
                //x!=e /\ y!=e
                for(unsigned xory=0; xory<2; xory++) {
                  Node x = xory == 0 ? nfiv[index] : nfjv[index];
                  Node xgtz = x.eqNode( d_emptyString ).negate();
                  if( d_equalityEngine.areDisequal( x, d_emptyString, true ) ) {
                    info.d_ant.push_back( xgtz );
                  } else {
                    info.d_antn.push_back( xgtz );
                  }
                }
                Node sk = d_sk_cache.mkSkolemCached(
                    nfiv[index],
                    nfjv[index],
                    isRev ? SkolemCache::SK_ID_V_SPT_REV
                          : SkolemCache::SK_ID_V_SPT,
                    "v_spt");
                // must add length requirement
                info.d_new_skolem[LENGTH_GEQ_ONE].push_back(sk);
                Node eq1 =
                    nfiv[index].eqNode(isRev ? mkConcat(sk, nfjv[index])
                                             : mkConcat(nfjv[index], sk));
                Node eq2 =
                    nfjv[index].eqNode(isRev ? mkConcat(sk, nfiv[index])
                                             : mkConcat(nfiv[index], sk));

                if( lentTestSuccess!=-1 ){
                  info.d_antn.push_back( lentTestExp );
                  info.d_conc = lentTestSuccess==0 ? eq1 : eq2;
                  info.d_id = INFER_SSPLIT_VAR_PROP;
                  info_valid = true;
                }else{
                  Node ldeq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ).negate();
                  if( d_equalityEngine.areDisequal( length_term_i, length_term_j, true ) ){
                    info.d_ant.push_back( ldeq );
                  }else{
                    info.d_antn.push_back(ldeq);
                  }
                  //set info
                  info.d_conc = NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 );
                  info.d_id = INFER_SSPLIT_VAR;
                  info_valid = true;
                }
              }
            }
          }
          if( info_valid ){
            pinfer.push_back( info );
            Assert( !success );
          }
        }
      }
    }
  }while( success );
}

bool TheoryStrings::detectLoop(NormalForm& nfi,
                               NormalForm& nfj,
                               int index,
                               int& loop_in_i,
                               int& loop_in_j,
                               unsigned rproc)
{
  int has_loop[2] = { -1, -1 };
  if( options::stringLB() != 2 ) {
    for( unsigned r=0; r<2; r++ ) {
      NormalForm& nf = r == 0 ? nfi : nfj;
      NormalForm& nfo = r == 0 ? nfj : nfi;
      std::vector<Node>& nfv = nf.d_nf;
      std::vector<Node>& nfov = nfo.d_nf;
      if (!nfov[index].isConst())
      {
        for (unsigned lp = index + 1; lp < nfv.size() - rproc; lp++)
        {
          if (nfv[lp] == nfov[index])
          {
            has_loop[r] = lp;
            break;
          }
        }
      }
    }
  }
  if( has_loop[0]!=-1 || has_loop[1]!=-1 ) {
    loop_in_i = has_loop[0];
    loop_in_j = has_loop[1];
    return true;
  } else {
    Trace("strings-solve-debug") << "No loops detected." << std::endl;
    return false;
  }
}

//xs(zy)=t(yz)xr
TheoryStrings::ProcessLoopResult TheoryStrings::processLoop(NormalForm& nfi,
                                                            NormalForm& nfj,
                                                            int loop_index,
                                                            int index,
                                                            InferInfo& info)
{
  if (options::stringProcessLoopMode() == ProcessLoopMode::ABORT)
  {
    throw LogicException("Looping word equation encountered.");
  }
  else if (options::stringProcessLoopMode() == ProcessLoopMode::NONE)
  {
    d_out->setIncomplete();
    return ProcessLoopResult::SKIPPED;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node conc;
  const std::vector<Node>& veci = nfi.d_nf;
  const std::vector<Node>& vecoi = nfj.d_nf;

  Trace("strings-loop") << "Detected possible loop for " << veci[loop_index]
                        << std::endl;
  Trace("strings-loop") << " ... (X)= " << vecoi[index] << std::endl;
  Trace("strings-loop") << " ... T(Y.Z)= ";
  std::vector<Node> vec_t(veci.begin() + index, veci.begin() + loop_index);
  Node t_yz = mkConcat(vec_t);
  Trace("strings-loop") << " (" << t_yz << ")" << std::endl;
  Trace("strings-loop") << " ... S(Z.Y)= ";
  std::vector<Node> vec_s(vecoi.begin() + index + 1, vecoi.end());
  Node s_zy = mkConcat(vec_s);
  Trace("strings-loop") << s_zy << std::endl;
  Trace("strings-loop") << " ... R= ";
  std::vector<Node> vec_r(veci.begin() + loop_index + 1, veci.end());
  Node r = mkConcat(vec_r);
  Trace("strings-loop") << r << std::endl;

  if (s_zy.isConst() && r.isConst() && r != d_emptyString)
  {
    int c;
    bool flag = true;
    if (s_zy.getConst<String>().tailcmp(r.getConst<String>(), c))
    {
      if (c >= 0)
      {
        s_zy = nm->mkConst(s_zy.getConst<String>().substr(0, c));
        r = d_emptyString;
        vec_r.clear();
        Trace("strings-loop") << "Strings::Loop: Refactor S(Z.Y)= " << s_zy
                              << ", c=" << c << std::endl;
        flag = false;
      }
    }
    if (flag)
    {
      Trace("strings-loop") << "Strings::Loop: tails are different."
                            << std::endl;
      d_im.sendInference(info.d_ant, conc, "Loop Conflict", true);
      return ProcessLoopResult::CONFLICT;
    }
  }

  Node split_eq;
  for (unsigned r = 0; r < 2; r++)
  {
    Node t = r == 0 ? veci[loop_index] : t_yz;
    split_eq = t.eqNode(d_emptyString);
    Node split_eqr = Rewriter::rewrite(split_eq);
    // the equality could rewrite to false
    if (!split_eqr.isConst())
    {
      if (!areDisequal(t, d_emptyString))
      {
        // try to make t equal to empty to avoid loop
        info.d_conc = nm->mkNode(kind::OR, split_eq, split_eq.negate());
        info.d_id = INFER_LEN_SPLIT_EMP;
        return ProcessLoopResult::INFERENCE;
      }
      else
      {
        info.d_ant.push_back(split_eq.negate());
      }
    }
    else
    {
      Assert(!split_eqr.getConst<bool>());
    }
  }

  Node ant = mkExplain(info.d_ant);
  info.d_ant.clear();
  info.d_antn.push_back(ant);

  Node str_in_re;
  if (s_zy == t_yz && r == d_emptyString && s_zy.isConst()
      && s_zy.getConst<String>().isRepeated())
  {
    Node rep_c = nm->mkConst(s_zy.getConst<String>().substr(0, 1));
    Trace("strings-loop") << "Special case (X)=" << vecoi[index] << " "
                          << std::endl;
    Trace("strings-loop") << "... (C)=" << rep_c << " " << std::endl;
    // special case
    str_in_re = nm->mkNode(
        STRING_IN_REGEXP,
        vecoi[index],
        nm->mkNode(REGEXP_STAR, nm->mkNode(STRING_TO_REGEXP, rep_c)));
    conc = str_in_re;
  }
  else if (t_yz.isConst())
  {
    Trace("strings-loop") << "Strings::Loop: Const Normal Breaking."
                          << std::endl;
    CVC4::String s = t_yz.getConst<CVC4::String>();
    unsigned size = s.size();
    std::vector<Node> vconc;
    for (unsigned len = 1; len <= size; len++)
    {
      Node y = nm->mkConst(s.substr(0, len));
      Node z = nm->mkConst(s.substr(len, size - len));
      Node restr = s_zy;
      Node cc;
      if (r != d_emptyString)
      {
        std::vector<Node> v2(vec_r);
        v2.insert(v2.begin(), y);
        v2.insert(v2.begin(), z);
        restr = mkConcat(z, y);
        cc = Rewriter::rewrite(s_zy.eqNode(mkConcat(v2)));
      }
      else
      {
        cc = Rewriter::rewrite(s_zy.eqNode(mkConcat(z, y)));
      }
      if (cc == d_false)
      {
        continue;
      }
      Node conc2 = nm->mkNode(
          STRING_IN_REGEXP,
          vecoi[index],
          nm->mkNode(
              REGEXP_CONCAT,
              nm->mkNode(STRING_TO_REGEXP, y),
              nm->mkNode(REGEXP_STAR, nm->mkNode(STRING_TO_REGEXP, restr))));
      cc = cc == d_true ? conc2 : nm->mkNode(kind::AND, cc, conc2);
      vconc.push_back(cc);
    }
    conc = vconc.size() == 0 ? Node::null() : vconc.size() == 1
                                                  ? vconc[0]
                                                  : nm->mkNode(kind::OR, vconc);
  }
  else
  {
    if (options::stringProcessLoopMode() == ProcessLoopMode::SIMPLE_ABORT)
    {
      throw LogicException("Normal looping word equation encountered.");
    }
    else if (options::stringProcessLoopMode() == ProcessLoopMode::SIMPLE)
    {
      d_out->setIncomplete();
      return ProcessLoopResult::SKIPPED;
    }

    Trace("strings-loop") << "Strings::Loop: Normal Loop Breaking."
                          << std::endl;
    // right
    Node sk_w = d_sk_cache.mkSkolem("w_loop");
    Node sk_y = d_sk_cache.mkSkolem("y_loop");
    registerLength(sk_y, LENGTH_GEQ_ONE);
    Node sk_z = d_sk_cache.mkSkolem("z_loop");
    // t1 * ... * tn = y * z
    Node conc1 = t_yz.eqNode(mkConcat(sk_y, sk_z));
    // s1 * ... * sk = z * y * r
    vec_r.insert(vec_r.begin(), sk_y);
    vec_r.insert(vec_r.begin(), sk_z);
    Node conc2 = s_zy.eqNode(mkConcat(vec_r));
    Node conc3 = vecoi[index].eqNode(mkConcat(sk_y, sk_w));
    Node restr = r == d_emptyString ? s_zy : mkConcat(sk_z, sk_y);
    str_in_re =
        nm->mkNode(kind::STRING_IN_REGEXP,
                   sk_w,
                   nm->mkNode(kind::REGEXP_STAR,
                              nm->mkNode(kind::STRING_TO_REGEXP, restr)));

    std::vector<Node> vec_conc;
    vec_conc.push_back(conc1);
    vec_conc.push_back(conc2);
    vec_conc.push_back(conc3);
    vec_conc.push_back(str_in_re);
    // vec_conc.push_back(sk_y.eqNode(d_emptyString).negate());//by mkskolems
    conc = nm->mkNode(kind::AND, vec_conc);
  }  // normal case

  // we will be done
  info.d_conc = conc;
  info.d_id = INFER_FLOOP;
  info.d_nf_pair[0] = nfi.d_base;
  info.d_nf_pair[1] = nfj.d_base;
  return ProcessLoopResult::INFERENCE;
}

//return true for lemma, false if we succeed
void TheoryStrings::processDeq( Node ni, Node nj ) {
  NodeManager* nm = NodeManager::currentNM();
  //Assert( areDisequal( ni, nj ) );
  NormalForm& nfni = getNormalForm(ni);
  NormalForm& nfnj = getNormalForm(nj);
  if (nfni.d_nf.size() > 1 || nfnj.d_nf.size() > 1)
  {
    std::vector< Node > nfi;
    nfi.insert(nfi.end(), nfni.d_nf.begin(), nfni.d_nf.end());
    std::vector< Node > nfj;
    nfj.insert(nfj.end(), nfnj.d_nf.begin(), nfnj.d_nf.end());

    int revRet = processReverseDeq( nfi, nfj, ni, nj );
    if( revRet!=0 ){
      return;
    }

    nfi.clear();
    nfi.insert(nfi.end(), nfni.d_nf.begin(), nfni.d_nf.end());
    nfj.clear();
    nfj.insert(nfj.end(), nfnj.d_nf.begin(), nfnj.d_nf.end());

    unsigned index = 0;
    while( index<nfi.size() || index<nfj.size() ){
      int ret = processSimpleDeq( nfi, nfj, ni, nj, index, false );
      if( ret!=0 ) {
        return;
      }else{
        Assert( index<nfi.size() && index<nfj.size() );
        Node i = nfi[index];
        Node j = nfj[index];
        Trace("strings-solve-debug")  << "...Processing(DEQ) " << i << " " << j << std::endl;
        if( !areEqual( i, j ) ){
          Assert( i.getKind()!=kind::CONST_STRING || j.getKind()!=kind::CONST_STRING );
          std::vector< Node > lexp;
          Node li = getLength( i, lexp );
          Node lj = getLength( j, lexp );
          if( areDisequal( li, lj ) ){
            if( i.getKind()==kind::CONST_STRING || j.getKind()==kind::CONST_STRING ){
              //check if empty
              Node const_k = i.getKind() == kind::CONST_STRING ? i : j;
              Node nconst_k = i.getKind() == kind::CONST_STRING ? j : i;
              Node lnck = i.getKind() == kind::CONST_STRING ? lj : li;
              if( !d_equalityEngine.areDisequal( nconst_k, d_emptyString, true ) ){
                Node eq = nconst_k.eqNode( d_emptyString );
                Node conc = NodeManager::currentNM()->mkNode( kind::OR, eq, eq.negate() );
                d_im.sendInference(d_empty_vec, conc, "D-DISL-Emp-Split");
                return;
              }else{
                //split on first character
                CVC4::String str = const_k.getConst<String>();
                Node firstChar = str.size() == 1 ? const_k : NodeManager::currentNM()->mkConst( str.prefix( 1 ) );
                if( areEqual( lnck, d_one ) ){
                  if( areDisequal( firstChar, nconst_k ) ){
                    return;
                  }else if( !areEqual( firstChar, nconst_k ) ){
                    //splitting on demand : try to make them disequal
                    if (d_im.sendSplit(
                            firstChar, nconst_k, "S-Split(DEQL-Const)", false))
                    {
                      return;
                    }
                  }
                }else{
                  Node sk = d_sk_cache.mkSkolemCached(
                      nconst_k, SkolemCache::SK_ID_DC_SPT, "dc_spt");
                  registerLength(sk, LENGTH_ONE);
                  Node skr =
                      d_sk_cache.mkSkolemCached(nconst_k,
                                                SkolemCache::SK_ID_DC_SPT_REM,
                                                "dc_spt_rem");
                  Node eq1 = nconst_k.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk, skr ) );
                  eq1 = Rewriter::rewrite( eq1 );
                  Node eq2 = nconst_k.eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, firstChar, skr ) );
                  std::vector< Node > antec;
                  antec.insert(
                      antec.end(), nfni.d_exp.begin(), nfni.d_exp.end());
                  antec.insert(
                      antec.end(), nfnj.d_exp.begin(), nfnj.d_exp.end());
                  antec.push_back( nconst_k.eqNode( d_emptyString ).negate() );
                  d_im.sendInference(
                      antec,
                      nm->mkNode(
                          OR,
                          nm->mkNode(AND, eq1, sk.eqNode(firstChar).negate()),
                          eq2),
                      "D-DISL-CSplit");
                  d_im.sendPhaseRequirement(eq1, true);
                  return;
                }
              }
            }else{
              Trace("strings-solve") << "Non-Simple Case 1 : add lemma " << std::endl;
              //must add lemma
              std::vector< Node > antec;
              std::vector< Node > antec_new_lits;
              antec.insert(antec.end(), nfni.d_exp.begin(), nfni.d_exp.end());
              antec.insert(antec.end(), nfnj.d_exp.begin(), nfnj.d_exp.end());
              //check disequal
              if( areDisequal( ni, nj ) ){
                antec.push_back( ni.eqNode( nj ).negate() );
              }else{
                antec_new_lits.push_back( ni.eqNode( nj ).negate() );
              }
              antec_new_lits.push_back( li.eqNode( lj ).negate() );
              std::vector< Node > conc;
              Node sk1 = d_sk_cache.mkSkolemCached(
                  i, j, SkolemCache::SK_ID_DEQ_X, "x_dsplit");
              Node sk2 = d_sk_cache.mkSkolemCached(
                  i, j, SkolemCache::SK_ID_DEQ_Y, "y_dsplit");
              Node sk3 = d_sk_cache.mkSkolemCached(
                  i, j, SkolemCache::SK_ID_DEQ_Z, "z_dsplit");
              registerLength(sk3, LENGTH_GEQ_ONE);
              //Node nemp = sk3.eqNode(d_emptyString).negate();
              //conc.push_back(nemp);
              Node lsk1 = mkLength( sk1 );
              conc.push_back( lsk1.eqNode( li ) );
              Node lsk2 = mkLength( sk2 );
              conc.push_back( lsk2.eqNode( lj ) );
              conc.push_back( NodeManager::currentNM()->mkNode( kind::OR, j.eqNode( mkConcat( sk1, sk3 ) ), i.eqNode( mkConcat( sk2, sk3 ) ) ) );
              d_im.sendInference(
                  antec, antec_new_lits, nm->mkNode(AND, conc), "D-DISL-Split");
              ++(d_statistics.d_deq_splits);
              return;
            }
          }else if( areEqual( li, lj ) ){
            Assert( !areDisequal( i, j ) );
            //splitting on demand : try to make them disequal
            if (d_im.sendSplit(i, j, "S-Split(DEQL)", false))
            {
              return;
            }
          }else{
            //splitting on demand : try to make lengths equal
            if (d_im.sendSplit(li, lj, "D-Split"))
            {
              return;
            }
          }
        }
        index++;
      }
    }
    Assert( false );
  }
}

int TheoryStrings::processReverseDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj ) {
  //reverse normal form of i, j
  std::reverse( nfi.begin(), nfi.end() );
  std::reverse( nfj.begin(), nfj.end() );

  unsigned index = 0;
  int ret = processSimpleDeq( nfi, nfj, ni, nj, index, true );

  //reverse normal form of i, j
  std::reverse( nfi.begin(), nfi.end() );
  std::reverse( nfj.begin(), nfj.end() );

  return ret;
}

int TheoryStrings::processSimpleDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj, unsigned& index, bool isRev ){
  // See if one side is constant, if so, the disequality ni != nj is satisfied
  // since ni does not contain nj or vice versa.
  // This is only valid when isRev is false, since when isRev=true, the contents
  // of normal form vectors nfi and nfj are reversed.
  if (!isRev)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      Node c = getConstantEqc(i == 0 ? ni : nj);
      if (!c.isNull())
      {
        int findex, lindex;
        if (!TheoryStringsRewriter::canConstantContainList(
                c, i == 0 ? nfj : nfi, findex, lindex))
        {
          Trace("strings-solve-debug")
              << "Disequality: constant cannot contain list" << std::endl;
          return 1;
        }
      }
    }
  }
  NormalForm& nfni = getNormalForm(ni);
  NormalForm& nfnj = getNormalForm(nj);
  while( index<nfi.size() || index<nfj.size() ) {
    if( index>=nfi.size() || index>=nfj.size() ){
      Trace("strings-solve-debug") << "Disequality normalize empty" << std::endl;
      std::vector< Node > ant;
      //we have a conflict : because the lengths are equal, the remainder needs to be empty, which will lead to a conflict
      Node lni = getLengthExp(ni, ant, nfni.d_base);
      Node lnj = getLengthExp(nj, ant, nfnj.d_base);
      ant.push_back( lni.eqNode( lnj ) );
      ant.insert(ant.end(), nfni.d_exp.begin(), nfni.d_exp.end());
      ant.insert(ant.end(), nfnj.d_exp.begin(), nfnj.d_exp.end());
      std::vector< Node > cc;
      std::vector< Node >& nfk = index>=nfi.size() ? nfj : nfi;
      for( unsigned index_k=index; index_k<nfk.size(); index_k++ ){
        cc.push_back( nfk[index_k].eqNode( d_emptyString ) );
      }
      Node conc = cc.size()==1 ? cc[0] : NodeManager::currentNM()->mkNode( kind::AND, cc );
      conc = Rewriter::rewrite( conc );
      d_im.sendInference(ant, conc, "Disequality Normalize Empty", true);
      return -1;
    }else{
      Node i = nfi[index];
      Node j = nfj[index];
      Trace("strings-solve-debug")  << "...Processing(QED) " << i << " " << j << std::endl;
      if( !areEqual( i, j ) ) {
        if( i.getKind()==kind::CONST_STRING && j.getKind()==kind::CONST_STRING ) {
          unsigned int len_short = i.getConst<String>().size() < j.getConst<String>().size() ? i.getConst<String>().size() : j.getConst<String>().size();
          bool isSameFix = isRev ? i.getConst<String>().rstrncmp(j.getConst<String>(), len_short): i.getConst<String>().strncmp(j.getConst<String>(), len_short);
          if( isSameFix ) {
            //same prefix/suffix
            //k is the index of the string that is shorter
            Node nk = i.getConst<String>().size() < j.getConst<String>().size() ? i : j;
            Node nl = i.getConst<String>().size() < j.getConst<String>().size() ? j : i;
            Node remainderStr;
            if( isRev ){
              int new_len = nl.getConst<String>().size() - len_short;
              remainderStr = NodeManager::currentNM()->mkConst( nl.getConst<String>().substr(0, new_len) );
              Trace("strings-solve-debug-test") << "Rev. Break normal form of " << nl << " into " << nk << ", " << remainderStr << std::endl;
            } else {
              remainderStr = NodeManager::currentNM()->mkConst( nl.getConst<String>().substr( len_short ) );
              Trace("strings-solve-debug-test") << "Break normal form of " << nl << " into " << nk << ", " << remainderStr << std::endl;
            }
            if( i.getConst<String>().size() < j.getConst<String>().size() ) {
              nfj.insert( nfj.begin() + index + 1, remainderStr );
              nfj[index] = nfi[index];
            } else {
              nfi.insert( nfi.begin() + index + 1, remainderStr );
              nfi[index] = nfj[index];
            }
          }else{
            return 1;
          }
        }else{
          std::vector< Node > lexp;
          Node li = getLength( i, lexp );
          Node lj = getLength( j, lexp );
          if( areEqual( li, lj ) && areDisequal( i, j ) ){
            Trace("strings-solve") << "Simple Case 2 : found equal length disequal sub strings " << i << " " << j << std::endl;
            //we are done: D-Remove
            return 1;
          }else{
            return 0;
          }
        }
      }
      index++;
    }
  }
  return 0;
}

void TheoryStrings::addNormalFormPair( Node n1, Node n2 ){
  if( !isNormalFormPair( n1, n2 ) ){
    int index = 0;
    NodeIntMap::const_iterator it = d_nf_pairs.find( n1 );
    if( it!=d_nf_pairs.end() ){
      index = (*it).second;
    }
    d_nf_pairs[n1] = index + 1;
    if( index<(int)d_nf_pairs_data[n1].size() ){
      d_nf_pairs_data[n1][index] = n2;
    }else{
      d_nf_pairs_data[n1].push_back( n2 );
    } 
    Assert( isNormalFormPair( n1, n2 ) );
  } else {
    Trace("strings-nf-debug") << "Already a normal form pair " << n1 << " " << n2 << std::endl;
  }
}

bool TheoryStrings::isNormalFormPair( Node n1, Node n2 ) {
  //TODO: modulo equality?
  return isNormalFormPair2( n1, n2 ) || isNormalFormPair2( n2, n1 );
}

bool TheoryStrings::isNormalFormPair2( Node n1, Node n2 ) {
  //Trace("strings-debug") << "is normal form pair. " << n1 << " " << n2 << std::endl;
  NodeIntMap::const_iterator it = d_nf_pairs.find( n1 );
  if( it!=d_nf_pairs.end() ){
    Assert( d_nf_pairs_data.find( n1 )!=d_nf_pairs_data.end() );
    for( int i=0; i<(*it).second; i++ ){
      Assert( i<(int)d_nf_pairs_data[n1].size() );
      if( d_nf_pairs_data[n1][i]==n2 ){
        return true;
      }
    }
  }
  return false;
}

void TheoryStrings::registerTerm( Node n, int effort ) {
  TypeNode tn = n.getType();
  bool do_register = true;
  if (!tn.isString())
  {
    if (options::stringEagerLen())
    {
      do_register = effort == 0;
    }
    else
    {
      do_register = effort > 0 || n.getKind() != STRING_CONCAT;
    }
  }
  if (!do_register)
  {
    return;
  }
  if (d_registered_terms_cache.find(n) != d_registered_terms_cache.end())
  {
    return;
  }
  d_registered_terms_cache.insert(n);
  NodeManager* nm = NodeManager::currentNM();
  Debug("strings-register") << "TheoryStrings::registerTerm() " << n
                            << ", effort = " << effort << std::endl;
  if (tn.isString())
  {
    // register length information:
    //  for variables, split on empty vs positive length
    //  for concat/const/replace, introduce proxy var and state length relation
    Node lsum;
    if (n.getKind() != STRING_CONCAT && n.getKind() != CONST_STRING)
    {
      Node lsumb = nm->mkNode(STRING_LENGTH, n);
      lsum = Rewriter::rewrite(lsumb);
      // can register length term if it does not rewrite
      if (lsum == lsumb)
      {
        registerLength(n, LENGTH_SPLIT);
        return;
      }
    }
    Node sk = d_sk_cache.mkSkolemCached(n, SkolemCache::SK_PURIFY, "lsym");
    StringsProxyVarAttribute spva;
    sk.setAttribute(spva, true);
    Node eq = Rewriter::rewrite(sk.eqNode(n));
    Trace("strings-lemma") << "Strings::Lemma LENGTH Term : " << eq
                           << std::endl;
    d_proxy_var[n] = sk;
    // If we are introducing a proxy for a constant or concat term, we do not
    // need to send lemmas about its length, since its length is already
    // implied.
    if (n.isConst() || n.getKind() == STRING_CONCAT)
    {
      // add to length lemma cache, i.e. do not send length lemma for sk.
      d_length_lemma_terms_cache.insert(sk);
    }
    Trace("strings-assert") << "(assert " << eq << ")" << std::endl;
    d_out->lemma(eq);
    Node skl = nm->mkNode(STRING_LENGTH, sk);
    if (n.getKind() == STRING_CONCAT)
    {
      std::vector<Node> node_vec;
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        if (n[i].getAttribute(StringsProxyVarAttribute()))
        {
          Assert(d_proxy_var_to_length.find(n[i])
                 != d_proxy_var_to_length.end());
          node_vec.push_back(d_proxy_var_to_length[n[i]]);
        }
        else
        {
          Node lni = nm->mkNode(STRING_LENGTH, n[i]);
          node_vec.push_back(lni);
        }
      }
      lsum = nm->mkNode(PLUS, node_vec);
      lsum = Rewriter::rewrite(lsum);
    }
    else if (n.getKind() == CONST_STRING)
    {
      lsum = nm->mkConst(Rational(n.getConst<String>().size()));
    }
    Assert(!lsum.isNull());
    d_proxy_var_to_length[sk] = lsum;
    Node ceq = Rewriter::rewrite(skl.eqNode(lsum));
    Trace("strings-lemma") << "Strings::Lemma LENGTH : " << ceq << std::endl;
    Trace("strings-lemma-debug")
        << "  prerewrite : " << skl.eqNode(lsum) << std::endl;
    Trace("strings-assert") << "(assert " << ceq << ")" << std::endl;
    d_out->lemma(ceq);
  }
  else if (n.getKind() == STRING_CODE)
  {
    d_has_str_code = true;
    // ite( str.len(s)==1, 0 <= str.code(s) < num_codes, str.code(s)=-1 )
    Node code_len = mkLength(n[0]).eqNode(d_one);
    Node code_eq_neg1 = n.eqNode(d_neg_one);
    Node code_range = nm->mkNode(
        AND,
        nm->mkNode(GEQ, n, d_zero),
        nm->mkNode(LT, n, nm->mkConst(Rational(CVC4::String::num_codes()))));
    Node lem = nm->mkNode(ITE, code_len, code_range, code_eq_neg1);
    Trace("strings-lemma") << "Strings::Lemma CODE : " << lem << std::endl;
    Trace("strings-assert") << "(assert " << lem << ")" << std::endl;
    d_out->lemma(lem);
  }
  else if (n.getKind() == STRING_STRIDOF)
  {
    Node len = mkLength(n[0]);
    Node lem = nm->mkNode(AND,
                          nm->mkNode(GEQ, n, nm->mkConst(Rational(-1))),
                          nm->mkNode(LT, n, len));
    d_out->lemma(lem);
  }
}

void TheoryStrings::registerLength(Node n, LengthStatus s)
{
  if (d_length_lemma_terms_cache.find(n) != d_length_lemma_terms_cache.end())
  {
    return;
  }
  d_length_lemma_terms_cache.insert(n);

  NodeManager* nm = NodeManager::currentNM();
  Node n_len = nm->mkNode(kind::STRING_LENGTH, n);

  if (s == LENGTH_GEQ_ONE)
  {
    Node neq_empty = n.eqNode(d_emptyString).negate();
    Node len_n_gt_z = nm->mkNode(GT, n_len, d_zero);
    Node len_geq_one = nm->mkNode(AND, neq_empty, len_n_gt_z);
    Trace("strings-lemma") << "Strings::Lemma SK-GEQ-ONE : " << len_geq_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_geq_one << ")" << std::endl;
    d_out->lemma(len_geq_one);
    return;
  }

  if (s == LENGTH_ONE)
  {
    Node len_one = n_len.eqNode(d_one);
    Trace("strings-lemma") << "Strings::Lemma SK-ONE : " << len_one
                           << std::endl;
    Trace("strings-assert") << "(assert " << len_one << ")" << std::endl;
    d_out->lemma(len_one);
    return;
  }
  Assert(s == LENGTH_SPLIT);

  if( options::stringSplitEmp() || !options::stringLenGeqZ() ){
    Node n_len_eq_z = n_len.eqNode( d_zero );
    Node n_len_eq_z_2 = n.eqNode( d_emptyString );
    Node case_empty = nm->mkNode(AND, n_len_eq_z, n_len_eq_z_2);
    case_empty = Rewriter::rewrite(case_empty);
    Node case_nempty = nm->mkNode(GT, n_len, d_zero);
    if (!case_empty.isConst())
    {
      Node lem = nm->mkNode(OR, case_empty, case_nempty);
      d_out->lemma(lem);
      Trace("strings-lemma") << "Strings::Lemma LENGTH >= 0 : " << lem
                             << std::endl;
      // prefer trying the empty case first
      // notice that requirePhase must only be called on rewritten literals that
      // occur in the CNF stream.
      n_len_eq_z = Rewriter::rewrite(n_len_eq_z);
      Assert(!n_len_eq_z.isConst());
      d_out->requirePhase(n_len_eq_z, true);
      n_len_eq_z_2 = Rewriter::rewrite(n_len_eq_z_2);
      Assert(!n_len_eq_z_2.isConst());
      d_out->requirePhase(n_len_eq_z_2, true);
    }
    else if (!case_empty.getConst<bool>())
    {
      // the rewriter knows that n is non-empty
      Trace("strings-lemma")
          << "Strings::Lemma LENGTH > 0 (non-empty): " << case_nempty
          << std::endl;
      d_out->lemma(case_nempty);
    }
    else
    {
      // If n = "" ---> true or len( n ) = 0 ----> true, then we expect that
      // n ---> "". Since this method is only called on non-constants n, it must
      // be that n = "" ^ len( n ) = 0 does not rewrite to true.
      Assert(false);
    }
  }

  // additionally add len( x ) >= 0 ?
  if( options::stringLenGeqZ() ){
    Node n_len_geq = nm->mkNode(kind::GEQ, n_len, d_zero);
    n_len_geq = Rewriter::rewrite( n_len_geq );
    d_out->lemma( n_len_geq );
  }
}

Node TheoryStrings::mkConcat( Node n1, Node n2 ) {
  return Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, n1, n2 ) );
}

Node TheoryStrings::mkConcat( Node n1, Node n2, Node n3 ) {
  return Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, n1, n2, n3 ) );
}

Node TheoryStrings::mkConcat( const std::vector< Node >& c ) {
  return Rewriter::rewrite( c.size()>1 ? NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, c ) : ( c.size()==1 ? c[0] : d_emptyString ) );
}

Node TheoryStrings::mkLength( Node t ) {
  return Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t ) );
}

Node TheoryStrings::mkExplain( std::vector< Node >& a ) {
  std::vector< Node > an;
  return mkExplain( a, an );
}

Node TheoryStrings::mkExplain( std::vector< Node >& a, std::vector< Node >& an ) {
  std::vector< TNode > antec_exp;
  for( unsigned i=0; i<a.size(); i++ ) {
    if( std::find( a.begin(), a.begin() + i, a[i] )==a.begin() + i ) {
      bool exp = true;
      Debug("strings-explain") << "Ask for explanation of " << a[i] << std::endl;
      //assert
      if(a[i].getKind() == kind::EQUAL) {
        //Assert( hasTerm(a[i][0]) );
        //Assert( hasTerm(a[i][1]) );
        Assert( areEqual(a[i][0], a[i][1]) );
        if( a[i][0]==a[i][1] ){
          exp = false;
        }
      } else if( a[i].getKind()==kind::NOT && a[i][0].getKind()==kind::EQUAL ) {
        Assert( hasTerm(a[i][0][0]) );
        Assert( hasTerm(a[i][0][1]) );
        AlwaysAssert( d_equalityEngine.areDisequal(a[i][0][0], a[i][0][1], true) );
      }else if( a[i].getKind() == kind::AND ){
        for( unsigned j=0; j<a[i].getNumChildren(); j++ ){
          a.push_back( a[i][j] );
        }
        exp = false;
      }
      if( exp ) {
        unsigned ps = antec_exp.size();
        explain(a[i], antec_exp);
        Debug("strings-explain") << "Done, explanation was : " << std::endl;
        for( unsigned j=ps; j<antec_exp.size(); j++ ) {
          Debug("strings-explain") << "  " << antec_exp[j] << std::endl;
        }
        Debug("strings-explain") << std::endl;
      }
    }
  }
  for( unsigned i=0; i<an.size(); i++ ) {
    if( std::find( an.begin(), an.begin() + i, an[i] )==an.begin() + i ){
      Debug("strings-explain") << "Add to explanation (new literal) " << an[i] << std::endl;
      antec_exp.push_back(an[i]);
    }
  }
  Node ant;
  if( antec_exp.empty() ) {
    ant = d_true;
  } else if( antec_exp.size()==1 ) {
    ant = antec_exp[0];
  } else {
    ant = NodeManager::currentNM()->mkNode( kind::AND, antec_exp );
  }
  //ant = Rewriter::rewrite( ant );
  return ant;
}

void TheoryStrings::checkNormalFormsDeq()
{
  std::vector< std::vector< Node > > cols;
  std::vector< Node > lts;
  std::map< Node, std::map< Node, bool > > processed;
  
  //for each pair of disequal strings, must determine whether their lengths are equal or disequal
  for( NodeList::const_iterator id = d_ee_disequalities.begin(); id != d_ee_disequalities.end(); ++id ) {
    Node eq = *id;
    Node n[2];
    for( unsigned i=0; i<2; i++ ){
      n[i] = d_equalityEngine.getRepresentative( eq[i] );
    }
    if( processed[n[0]].find( n[1] )==processed[n[0]].end() ){
      processed[n[0]][n[1]] = true;
      Node lt[2];
      for( unsigned i=0; i<2; i++ ){
        EqcInfo* ei = getOrMakeEqcInfo( n[i], false );
        lt[i] = ei ? ei->d_length_term : Node::null();
        if( lt[i].isNull() ){
          lt[i] = eq[i];
        }
        lt[i] = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt[i] );
      }
      if( !areEqual( lt[0], lt[1] ) && !areDisequal( lt[0], lt[1] ) ){
        d_im.sendSplit(lt[0], lt[1], "DEQ-LENGTH-SP");
      }
    }
  }

  if (!d_im.hasProcessed())
  {
    separateByLength( d_strings_eqc, cols, lts );
    for( unsigned i=0; i<cols.size(); i++ ){
      if (cols[i].size() > 1 && !d_im.hasPendingLemma())
      {
        if (Trace.isOn("strings-solve"))
        {
          Trace("strings-solve") << "- Verify disequalities are processed for "
                                 << cols[i][0] << ", normal form : ";
          printConcat(getNormalForm(cols[i][0]).d_nf, "strings-solve");
          Trace("strings-solve")
              << "... #eql = " << cols[i].size() << std::endl;
        }
        //must ensure that normal forms are disequal
        for( unsigned j=0; j<cols[i].size(); j++ ){
          for( unsigned k=(j+1); k<cols[i].size(); k++ ){
            //for strings that are disequal, but have the same length
            if (cols[i][j].isConst() && cols[i][k].isConst())
            {
              // if both are constants, they should be distinct, and its trivial
              Assert(cols[i][j] != cols[i][k]);
            }
            else
            {
              if (areDisequal(cols[i][j], cols[i][k]))
              {
                Assert(!d_conflict);
                if (Trace.isOn("strings-solve"))
                {
                  Trace("strings-solve") << "- Compare " << cols[i][j] << " ";
                  printConcat(getNormalForm(cols[i][j]).d_nf, "strings-solve");
                  Trace("strings-solve") << " against " << cols[i][k] << " ";
                  printConcat(getNormalForm(cols[i][k]).d_nf, "strings-solve");
                  Trace("strings-solve") << "..." << std::endl;
                }
                processDeq(cols[i][j], cols[i][k]);
                if (d_im.hasProcessed())
                {
                  return;
                }
              }
            }
          }
        }
      }
    }
  }
}

void TheoryStrings::checkLengthsEqc() {
  if( options::stringLenNorm() ){
    for( unsigned i=0; i<d_strings_eqc.size(); i++ ){
      NormalForm& nfi = getNormalForm(d_strings_eqc[i]);
      Trace("strings-process-debug") << "Process length constraints for " << d_strings_eqc[i] << std::endl;
      //check if there is a length term for this equivalence class
      EqcInfo* ei = getOrMakeEqcInfo( d_strings_eqc[i], false );
      Node lt = ei ? ei->d_length_term : Node::null();
      if( !lt.isNull() ) {
        Node llt = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt );
        //now, check if length normalization has occurred
        if( ei->d_normalized_length.get().isNull() ) {
          Node nf = mkConcat(nfi.d_nf);
          if( Trace.isOn("strings-process-debug") ){
            Trace("strings-process-debug")
                << "  normal form is " << nf << " from base " << nfi.d_base
                << std::endl;
            Trace("strings-process-debug") << "  normal form exp is: " << std::endl;
            for (const Node& exp : nfi.d_exp)
            {
              Trace("strings-process-debug") << "   " << exp << std::endl;
            }
          }
          
          //if not, add the lemma
          std::vector< Node > ant;
          ant.insert(ant.end(), nfi.d_exp.begin(), nfi.d_exp.end());
          ant.push_back(nfi.d_base.eqNode(lt));
          Node lc = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, nf );
          Node lcr = Rewriter::rewrite( lc );
          Trace("strings-process-debug") << "Rewrote length " << lc << " to " << lcr << std::endl;
          if (!areEqual(llt, lcr))
          {
            Node eq = llt.eqNode(lcr);
            ei->d_normalized_length.set( eq );
            d_im.sendInference(ant, eq, "LEN-NORM", true);
          }
        }
      }else{
        Trace("strings-process-debug") << "No length term for eqc " << d_strings_eqc[i] << " " << d_eqc_to_len_term[d_strings_eqc[i]] << std::endl;
        if( !options::stringEagerLen() ){
          Node c = mkConcat(nfi.d_nf);
          registerTerm( c, 3 );
        }
      }
      //} else {
      //  Trace("strings-process-debug") << "Do not process length constraints for " << nodes[i] << " " << d_normal_forms[nodes[i]].size() << std::endl;
      //}
    }
  }
}

void TheoryStrings::checkCardinality() {
  //int cardinality = options::stringCharCardinality();
  //Trace("strings-solve-debug2") << "get cardinality: " << cardinality << endl;

  //AJR: this will create a partition of eqc, where each collection has length that are pairwise propagated to be equal.
  //  we do not require disequalities between the lengths of each collection, since we split on disequalities between lengths of string terms that are disequal (DEQ-LENGTH-SP).
  //  TODO: revisit this?
  std::vector< std::vector< Node > > cols;
  std::vector< Node > lts;
  separateByLength( d_strings_eqc, cols, lts );

  Trace("strings-card") << "Check cardinality...." << std::endl;
  for( unsigned i = 0; i<cols.size(); ++i ) {
    Node lr = lts[i];
    Trace("strings-card") << "Number of strings with length equal to " << lr << " is " << cols[i].size() << std::endl;
    if( cols[i].size() > 1 ) {
      // size > c^k
      unsigned card_need = 1;
      double curr = (double)cols[i].size();
      while( curr>d_card_size ){
        curr = curr/(double)d_card_size;
        card_need++;
      }
      Trace("strings-card") << "Need length " << card_need << " for this number of strings (where alphabet size is " << d_card_size << ")." << std::endl;
      //check if we need to split
      bool needsSplit = true;
      if( lr.isConst() ){
        // if constant, compare
        Node cmp = NodeManager::currentNM()->mkNode( kind::GEQ, lr, NodeManager::currentNM()->mkConst( Rational( card_need ) ) );
        cmp = Rewriter::rewrite( cmp );
        needsSplit = cmp!=d_true;
      }else{
        // find the minimimum constant that we are unknown to be disequal from, or otherwise stop if we increment such that cardinality does not apply
        unsigned r=0; 
        bool success = true;
        while( r<card_need && success ){
          Node rr = NodeManager::currentNM()->mkConst<Rational>( Rational(r) );
          if( areDisequal( rr, lr ) ){
            r++;
          }else{
            success = false;
          }
        }
        if( r>0 ){
          Trace("strings-card") << "Symbolic length " << lr << " must be at least " << r << " due to constant disequalities." << std::endl;
        }
        needsSplit = r<card_need;
      }

      if( needsSplit ){
        unsigned int int_k = (unsigned int)card_need;
        for( std::vector< Node >::iterator itr1 = cols[i].begin();
            itr1 != cols[i].end(); ++itr1) {
          for( std::vector< Node >::iterator itr2 = itr1 + 1;
            itr2 != cols[i].end(); ++itr2) {
            if(!areDisequal( *itr1, *itr2 )) {
              // add split lemma
              if (d_im.sendSplit(*itr1, *itr2, "CARD-SP"))
              {
                return;
              }
            }
          }
        }
        EqcInfo* ei = getOrMakeEqcInfo( lr, true );
        Trace("strings-card") << "Previous cardinality used for " << lr << " is " << ((int)ei->d_cardinality_lem_k.get()-1) << std::endl;
        if( int_k+1 > ei->d_cardinality_lem_k.get() ){
          Node k_node = NodeManager::currentNM()->mkConst( ::CVC4::Rational( int_k ) );
          //add cardinality lemma
          Node dist = NodeManager::currentNM()->mkNode( kind::DISTINCT, cols[i] );
          std::vector< Node > vec_node;
          vec_node.push_back( dist );
          for( std::vector< Node >::iterator itr1 = cols[i].begin();
              itr1 != cols[i].end(); ++itr1) {
            Node len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, *itr1 );
            if( len!=lr ) {
              Node len_eq_lr = len.eqNode(lr);
              vec_node.push_back( len_eq_lr );
            }
          }
          Node len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, cols[i][0] );
          Node cons = NodeManager::currentNM()->mkNode( kind::GEQ, len, k_node );
          cons = Rewriter::rewrite( cons );
          ei->d_cardinality_lem_k.set( int_k+1 );
          if( cons!=d_true ){
            d_im.sendInference(
                d_empty_vec, vec_node, cons, "CARDINALITY", true);
            return;
          }
        }
      }
    }
  }
  Trace("strings-card") << "...end check cardinality" << std::endl;
}

void TheoryStrings::getEquivalenceClasses( std::vector< Node >& eqcs ) {
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ) {
    Node eqc = (*eqcs_i);
    //if eqc.getType is string
    if (eqc.getType().isString()) {
      eqcs.push_back( eqc );
    }
    ++eqcs_i;
  }
}

void TheoryStrings::separateByLength(std::vector< Node >& n,
  std::vector< std::vector< Node > >& cols,
  std::vector< Node >& lts ) {
  unsigned leqc_counter = 0;
  std::map< Node, unsigned > eqc_to_leqc;
  std::map< unsigned, Node > leqc_to_eqc;
  std::map< unsigned, std::vector< Node > > eqc_to_strings;
  for( unsigned i=0; i<n.size(); i++ ) {
    Node eqc = n[i];
    Assert( d_equalityEngine.getRepresentative(eqc)==eqc );
    EqcInfo* ei = getOrMakeEqcInfo( eqc, false );
    Node lt = ei ? ei->d_length_term : Node::null();
    if( !lt.isNull() ){
      lt = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt );
      Node r = d_equalityEngine.getRepresentative( lt );
      if( eqc_to_leqc.find( r )==eqc_to_leqc.end() ){
        eqc_to_leqc[r] = leqc_counter;
        leqc_to_eqc[leqc_counter] = r;
        leqc_counter++;
      }
      eqc_to_strings[ eqc_to_leqc[r] ].push_back( eqc );
    }else{
      eqc_to_strings[leqc_counter].push_back( eqc );
      leqc_counter++;
    }
  }
  for( std::map< unsigned, std::vector< Node > >::iterator it = eqc_to_strings.begin(); it != eqc_to_strings.end(); ++it ){
    cols.push_back( std::vector< Node >() );
    cols.back().insert( cols.back().end(), it->second.begin(), it->second.end() );
    lts.push_back( leqc_to_eqc[it->first] );
  }
}

void TheoryStrings::printConcat( std::vector< Node >& n, const char * c ) {
  for( unsigned i=0; i<n.size(); i++ ){
    if( i>0 ) Trace(c) << " ++ ";
    Trace(c) << n[i];
  }
}


//// Finite Model Finding

TheoryStrings::StringSumLengthDecisionStrategy::StringSumLengthDecisionStrategy(
    context::Context* c, context::UserContext* u, Valuation valuation)
    : DecisionStrategyFmf(c, valuation), d_input_var_lsum(u)
{
}

bool TheoryStrings::StringSumLengthDecisionStrategy::isInitialized()
{
  return !d_input_var_lsum.get().isNull();
}

void TheoryStrings::StringSumLengthDecisionStrategy::initialize(
    const std::vector<Node>& vars)
{
  if (d_input_var_lsum.get().isNull() && !vars.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> sum;
    for (const Node& v : vars)
    {
      sum.push_back(nm->mkNode(STRING_LENGTH, v));
    }
    Node sumn = sum.size() == 1 ? sum[0] : nm->mkNode(PLUS, sum);
    d_input_var_lsum.set(sumn);
  }
}

Node TheoryStrings::StringSumLengthDecisionStrategy::mkLiteral(unsigned i)
{
  if (d_input_var_lsum.get().isNull())
  {
    return Node::null();
  }
  NodeManager* nm = NodeManager::currentNM();
  Node lit = nm->mkNode(LEQ, d_input_var_lsum.get(), nm->mkConst(Rational(i)));
  Trace("strings-fmf") << "StringsFMF::mkLiteral: " << lit << std::endl;
  return lit;
}
std::string TheoryStrings::StringSumLengthDecisionStrategy::identify() const
{
  return std::string("string_sum_len");
}

Node TheoryStrings::ppRewrite(TNode atom) {
  Trace("strings-ppr") << "TheoryStrings::ppRewrite " << atom << std::endl;
  Node atomElim;
  if (options::regExpElim() && atom.getKind() == STRING_IN_REGEXP)
  {
    // aggressive elimination of regular expression membership
    atomElim = d_regexp_elim.eliminate(atom);
    if (!atomElim.isNull())
    {
      Trace("strings-ppr") << "  rewrote " << atom << " -> " << atomElim
                           << " via regular expression elimination."
                           << std::endl;
      atom = atomElim;
    }
  }
  if( !options::stringLazyPreproc() ){
    //eager preprocess here
    std::vector< Node > new_nodes;
    Node ret = d_preproc.processAssertion( atom, new_nodes );
    if( ret!=atom ){
      Trace("strings-ppr") << "  rewrote " << atom << " -> " << ret << ", with " << new_nodes.size() << " lemmas." << std::endl; 
      for( unsigned i=0; i<new_nodes.size(); i++ ){
        Trace("strings-ppr") << "    lemma : " << new_nodes[i] << std::endl;
        d_out->lemma( new_nodes[i] );
      }
      return ret;
    }else{
      Assert( new_nodes.empty() );
    }
  }
  return atom;
}

// Stats
TheoryStrings::Statistics::Statistics()
    : d_splits("theory::strings::NumOfSplitOnDemands", 0),
      d_eq_splits("theory::strings::NumOfEqSplits", 0),
      d_deq_splits("theory::strings::NumOfDiseqSplits", 0),
      d_loop_lemmas("theory::strings::NumOfLoops", 0)
{
  smtStatisticsRegistry()->registerStat(&d_splits);
  smtStatisticsRegistry()->registerStat(&d_eq_splits);
  smtStatisticsRegistry()->registerStat(&d_deq_splits);
  smtStatisticsRegistry()->registerStat(&d_loop_lemmas);
}

TheoryStrings::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_splits);
  smtStatisticsRegistry()->unregisterStat(&d_eq_splits);
  smtStatisticsRegistry()->unregisterStat(&d_deq_splits);
  smtStatisticsRegistry()->unregisterStat(&d_loop_lemmas);
}

/** run the given inference step */
void TheoryStrings::runInferStep(InferStep s, int effort)
{
  Trace("strings-process") << "Run " << s;
  if (effort > 0)
  {
    Trace("strings-process") << ", effort = " << effort;
  }
  Trace("strings-process") << "..." << std::endl;
  switch (s)
  {
    case CHECK_INIT: checkInit(); break;
    case CHECK_CONST_EQC: checkConstantEquivalenceClasses(); break;
    case CHECK_EXTF_EVAL: checkExtfEval(effort); break;
    case CHECK_CYCLES: checkCycles(); break;
    case CHECK_FLAT_FORMS: checkFlatForms(); break;
    case CHECK_NORMAL_FORMS_EQ: checkNormalFormsEq(); break;
    case CHECK_NORMAL_FORMS_DEQ: checkNormalFormsDeq(); break;
    case CHECK_CODES: checkCodes(); break;
    case CHECK_LENGTH_EQC: checkLengthsEqc(); break;
    case CHECK_EXTF_REDUCTION: checkExtfReductions(effort); break;
    case CHECK_MEMBERSHIP: checkMemberships(); break;
    case CHECK_CARDINALITY: checkCardinality(); break;
    default: Unreachable(); break;
  }
  Trace("strings-process") << "Done " << s
                           << ", addedFact = " << d_im.hasPendingFact()
                           << ", addedLemma = " << d_im.hasPendingLemma()
                           << ", d_conflict = " << d_conflict << std::endl;
}

bool TheoryStrings::hasStrategyEffort(Effort e) const
{
  return d_strat_steps.find(e) != d_strat_steps.end();
}

void TheoryStrings::addStrategyStep(InferStep s, int effort, bool addBreak)
{
  // must run check init first
  Assert((s == CHECK_INIT)==d_infer_steps.empty());
  // must use check cycles when using flat forms
  Assert(s != CHECK_FLAT_FORMS
         || std::find(d_infer_steps.begin(), d_infer_steps.end(), CHECK_CYCLES)
                != d_infer_steps.end());
  d_infer_steps.push_back(s);
  d_infer_step_effort.push_back(effort);
  if (addBreak)
  {
    d_infer_steps.push_back(BREAK);
    d_infer_step_effort.push_back(0);
  }
}

void TheoryStrings::initializeStrategy()
{
  // initialize the strategy if not already done so
  if (!d_strategy_init)
  {
    std::map<Effort, unsigned> step_begin;
    std::map<Effort, unsigned> step_end;
    d_strategy_init = true;
    // beginning indices
    step_begin[EFFORT_FULL] = 0;
    if (options::stringEager())
    {
      step_begin[EFFORT_STANDARD] = 0;
    }
    // add the inference steps
    addStrategyStep(CHECK_INIT);
    addStrategyStep(CHECK_CONST_EQC);
    addStrategyStep(CHECK_EXTF_EVAL, 0);
    addStrategyStep(CHECK_CYCLES);
    if (options::stringFlatForms())
    {
      addStrategyStep(CHECK_FLAT_FORMS);
    }
    addStrategyStep(CHECK_EXTF_REDUCTION, 1);
    if (options::stringEager())
    {
      // do only the above inferences at standard effort, if applicable
      step_end[EFFORT_STANDARD] = d_infer_steps.size() - 1;
    }
    addStrategyStep(CHECK_NORMAL_FORMS_EQ);
    addStrategyStep(CHECK_EXTF_EVAL, 1);
    if (!options::stringEagerLen())
    {
      addStrategyStep(CHECK_LENGTH_EQC);
    }
    addStrategyStep(CHECK_NORMAL_FORMS_DEQ);
    addStrategyStep(CHECK_CODES);
    if (options::stringEagerLen())
    {
      addStrategyStep(CHECK_LENGTH_EQC);
    }
    if (options::stringExp() && !options::stringGuessModel())
    {
      addStrategyStep(CHECK_EXTF_REDUCTION, 2);
    }
    addStrategyStep(CHECK_MEMBERSHIP);
    addStrategyStep(CHECK_CARDINALITY);
    step_end[EFFORT_FULL] = d_infer_steps.size() - 1;
    if (options::stringExp() && options::stringGuessModel())
    {
      step_begin[EFFORT_LAST_CALL] = d_infer_steps.size();
      // these two steps are run in parallel
      addStrategyStep(CHECK_EXTF_REDUCTION, 2, false);
      addStrategyStep(CHECK_EXTF_EVAL, 3);
      step_end[EFFORT_LAST_CALL] = d_infer_steps.size() - 1;
    }
    // set the beginning/ending ranges
    for (const std::pair<const Effort, unsigned>& it_begin : step_begin)
    {
      Effort e = it_begin.first;
      std::map<Effort, unsigned>::iterator it_end = step_end.find(e);
      Assert(it_end != step_end.end());
      d_strat_steps[e] =
          std::pair<unsigned, unsigned>(it_begin.second, it_end->second);
    }
  }
}

void TheoryStrings::runStrategy(unsigned sbegin, unsigned send)
{
  Trace("strings-process") << "----check, next round---" << std::endl;
  for (unsigned i = sbegin; i <= send; i++)
  {
    InferStep curr = d_infer_steps[i];
    if (curr == BREAK)
    {
      if (d_im.hasProcessed())
      {
        break;
      }
    }
    else
    {
      runInferStep(curr, d_infer_step_effort[i]);
      if (d_conflict)
      {
        break;
      }
    }
  }
  Trace("strings-process") << "----finished round---" << std::endl;
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
