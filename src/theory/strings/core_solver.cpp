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

#include "theory/strings/core_solver.h"

#include "theory/strings/theory_strings_utils.h"
#include "options/strings_options.h"
#include "theory/strings/theory_strings_rewriter.h"


using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

Node CoreSolver::TermIndex::add(TNode n,
                                   unsigned index,
                                   const SolverState& s,
                                   Node er,
                                   std::vector<Node>& c)
{
  if( index==n.getNumChildren() ){
    if( d_data.isNull() ){
      d_data = n;
    }
    return d_data;
  }else{
    Assert(index < n.getNumChildren());
    TNode nir = s.getRepresentative(n[index]);
    //if it is empty, and doing CONCAT, ignore
    if( nir==er && n.getKind()==kind::STRING_CONCAT ){
      return add(n, index + 1, s, er, c);
    }else{
      c.push_back( nir );
      return d_children[nir].add(n, index + 1, s, er, c);
    }
  }
}

CoreSolver::CoreSolver(context::Context* c, context::UserContext* u, SolverState& s, InferenceManager& im, SkolemCache& skc) :
d_state(s), d_im(im), d_skCache(skc),
d_nf_pairs(c),
d_congruent(c)
{
  d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

CoreSolver::~CoreSolver() {

}


void CoreSolver::checkInit() {
  //build term index
  d_eqc_to_const.clear();
  d_eqc_to_const_base.clear();
  d_eqc_to_const_exp.clear();
  d_term_index.clear();
  d_strings_eqc.clear();

  std::map< Kind, unsigned > ncongruent;
  std::map< Kind, unsigned > congruent;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  d_emptyString_r = d_state.getRepresentative(d_emptyString);
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if( !tn.isRegExp() ){
      if( tn.isString() ){
        d_strings_eqc.push_back( eqc );
      }
      Node var;
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
      while( !eqc_i.isFinished() ) {
        Node n = *eqc_i;
        if( n.isConst() ){
          d_eqc_to_const[eqc] = n;
          d_eqc_to_const_base[eqc] = n;
          d_eqc_to_const_exp[eqc] = Node::null();
        }else if( tn.isInteger() ){
          // do nothing
        }else if( n.getNumChildren()>0 ){
          Kind k = n.getKind();
          if( k!=kind::EQUAL ){
            if( d_congruent.find( n )==d_congruent.end() ){
              std::vector< Node > c;
              Node nc = d_term_index[k].add(n, 0, d_state, d_emptyString_r, c);
              if( nc!=n ){
                //check if we have inferred a new equality by removal of empty components
                if (n.getKind() == kind::STRING_CONCAT
                    && !d_state.areEqual(nc, n))
                {
                  std::vector< Node > exp;
                  unsigned count[2] = { 0, 0 };
                  while( count[0]<nc.getNumChildren() || count[1]<n.getNumChildren() ){
                    //explain empty prefixes
                    for( unsigned t=0; t<2; t++ ){
                      Node nn = t==0 ? nc : n;
                      while (
                          count[t] < nn.getNumChildren()
                          && (nn[count[t]] == d_emptyString
                              || d_state.areEqual(nn[count[t]], d_emptyString)))
                      {
                        if( nn[count[t]]!=d_emptyString ){
                          exp.push_back( nn[count[t]].eqNode( d_emptyString ) );
                        }
                        count[t]++;
                      }
                    }
                    //explain equal components
                    if( count[0]<nc.getNumChildren() ){
                      Assert(count[1] < n.getNumChildren());
                      if( nc[count[0]]!=n[count[1]] ){
                        exp.push_back( nc[count[0]].eqNode( n[count[1]] ) );
                      }
                      count[0]++;
                      count[1]++;
                    }
                  }
                  //infer the equality
                  d_im.sendInference(exp, n.eqNode(nc), "I_Norm");
                }
                /*
                // FIXME
                else if (getExtTheory()->hasFunctionKind(n.getKind()))
                {
                  //mark as congruent : only process if neither has been reduced
                  getExtTheory()->markCongruent( nc, n );
                }
                */
                //this node is congruent to another one, we can ignore it
                Trace("strings-process-debug")
                    << "  congruent term : " << n << " (via " << nc << ")"
                    << std::endl;
                d_congruent.insert( n );
                congruent[k]++;
              }else if( k==kind::STRING_CONCAT && c.size()==1 ){
                Trace("strings-process-debug") << "  congruent term by singular : " << n << " " << c[0] << std::endl;
                //singular case
                if (!d_state.areEqual(c[0], n))
                {
                  Node ns;
                  std::vector< Node > exp;
                  //explain empty components
                  bool foundNEmpty = false;
                  for( unsigned i=0; i<n.getNumChildren(); i++ ){
                    if (d_state.areEqual(n[i], d_emptyString))
                    {
                      if( n[i]!=d_emptyString ){
                        exp.push_back( n[i].eqNode( d_emptyString ) );
                      }
                    }
                    else
                    {
                      Assert(!foundNEmpty);
                      ns = n[i];
                      foundNEmpty = true;
                    }
                  }
                  AlwaysAssert(foundNEmpty);
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
            // We mark all but the oldest variable in the equivalence class as
            // congruent.
            if (var.isNull())
            {
              var = n;
            }
            else if (var > n)
            {
              Trace("strings-process-debug")
                  << "  congruent variable : " << var << std::endl;
              d_congruent.insert(var);
              var = n;
            }
            else
            {
              Trace("strings-process-debug")
                  << "  congruent variable : " << n << std::endl;
              d_congruent.insert(n);
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

void CoreSolver::checkConstantEquivalenceClasses()
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

void CoreSolver::checkConstantEquivalenceClasses( TermIndex* ti, std::vector< Node >& vecc ) {
  Node n = ti->d_data;
  if( !n.isNull() ){
    //construct the constant
    Node c = utils::mkNConcat(vecc);
    if (!d_state.areEqual(n, c))
    {
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
        while (count < n.getNumChildren()
               && d_state.areEqual(n[count], d_emptyString))
        {
          d_im.addToExplanation(n[count], d_emptyString, exp);
          count++;
        }
        if( count<n.getNumChildren() ){
          Trace("strings-debug") << "...explain " << n[count] << " " << vecc[countc] << std::endl;
          if (!d_state.areEqual(n[count], vecc[countc]))
          {
            Node nrr = d_state.getRepresentative(n[count]);
            Assert(!d_eqc_to_const_exp[nrr].isNull());
            d_im.addToExplanation(n[count], d_eqc_to_const_base[nrr], exp);
            exp.push_back( d_eqc_to_const_exp[nrr] );
          }
          else
          {
            d_im.addToExplanation(n[count], vecc[countc], exp);
          }
          countc++;
          count++;
        }
      }
      //exp contains an explanation of n==c
      Assert(countc == vecc.size());
      if (d_state.hasTerm(c))
      {
        d_im.sendInference(exp, n.eqNode(c), "I_CONST_MERGE");
        return;
      }
      else if (!d_im.hasProcessed())
      {
        Node nr = d_state.getRepresentative(n);
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
            d_im.addToExplanation(n, it->second, exp);
          }else{
            // n==c ^ n == d_eqc_to_const_base[nr] == c' => false
            exp.push_back( d_eqc_to_const_exp[nr] );
            d_im.addToExplanation(n, d_eqc_to_const_base[nr], exp);
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


Node CoreSolver::getConstantEqc( Node eqc ) {
  std::map< Node, Node >::iterator it = d_eqc_to_const.find( eqc );
  if( it!=d_eqc_to_const.end() ){
    return it->second;
  }else{
    return Node::null();
  }
}

void CoreSolver::debugPrintFlatForms( const char * tc ){
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

void CoreSolver::checkCycles()
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

void CoreSolver::checkFlatForms()
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
            d_im.addToExplanation(n, d_eqc_to_const_base[eqc], exp);
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
                d_im.addToExplanation(
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
        if (d_state.isInConflict())
        {
          return;
        }

        for (const Node& n : it->second)
        {
          std::reverse(d_flat_form[n].begin(), d_flat_form[n].end());
          std::reverse(d_flat_form_index[n].begin(),
                       d_flat_form_index[n].end());
        }
      }
    }
  }
}

namespace {

enum class FlatFormInfer
{
  NONE,
  CONST,
  UNIFY,
  ENDPOINT_EMP,
  ENDPOINT_EQ,
};

std::ostream& operator<<(std::ostream& os, FlatFormInfer inf)
{
  switch (inf)
  {
    case FlatFormInfer::NONE: os << "<None>"; break;
    case FlatFormInfer::CONST: os << "F_Const"; break;
    case FlatFormInfer::UNIFY: os << "F_Unify"; break;
    case FlatFormInfer::ENDPOINT_EMP: os << "F_EndpointEmp"; break;
    case FlatFormInfer::ENDPOINT_EQ: os << "F_EndpointEq"; break;
    default: os << "<Unknown>"; break;
  }
  return os;
}

}  // namespace

void CoreSolver::checkFlatForm(std::vector<Node>& eqc,
                                  size_t start,
                                  bool isRev)
{
  size_t count = 0;
  // We check for flat form inferences involving `eqc[start]` and terms past
  // `start`. If there was a flat form inference involving `eqc[start]` and a
  // term at a smaller index `i`, we would have found it with when `start` was
  // `i`. Thus, we mark the preceeding terms in the equivalence class as
  // ineligible.
  std::vector<Node> inelig(eqc.begin(), eqc.begin() + start + 1);
  Node a = eqc[start];
  Trace("strings-ff-debug")
      << "Check flat form for a = " << a << ", whose flat form is "
      << d_flat_form[a] << ")" << std::endl;
  Node b;
  do
  {
    std::vector<Node> exp;
    Node conc;
    FlatFormInfer infType = FlatFormInfer::NONE;
    size_t eqc_size = eqc.size();
    size_t asize = d_flat_form[a].size();
    if (count == asize)
    {
      for (size_t i = start + 1; i < eqc_size; i++)
      {
        b = eqc[i];
        if (std::find(inelig.begin(), inelig.end(), b) != inelig.end())
        {
          continue;
        }

        size_t bsize = d_flat_form[b].size();
        if (count < bsize)
        {
          Trace("strings-ff-debug")
              << "Found endpoint (in a) with non-empty b = " << b
              << ", whose flat form is " << d_flat_form[b] << std::endl;
          // endpoint
          std::vector<Node> conc_c;
          for (unsigned j = count; j < bsize; j++)
          {
            conc_c.push_back(b[d_flat_form_index[b][j]].eqNode(d_emptyString));
          }
          Assert(!conc_c.empty());
          conc = utils::mkAnd(conc_c);
          infType = FlatFormInfer::ENDPOINT_EMP;
          Assert(count > 0);
          // swap, will enforce is empty past current
          a = eqc[i];
          b = eqc[start];
          break;
        }
        inelig.push_back(eqc[i]);
      }
    }
    else
    {
      Node curr = d_flat_form[a][count];
      Node curr_c = getConstantEqc(curr);
      Node ac = a[d_flat_form_index[a][count]];
      std::vector<Node> lexp;
      Node lcurr = d_state.getLength(ac, lexp);
      for (size_t i = start + 1; i < eqc_size; i++)
      {
        b = eqc[i];
        if (std::find(inelig.begin(), inelig.end(), b) != inelig.end())
        {
          continue;
        }

        if (count == d_flat_form[b].size())
        {
          inelig.push_back(b);
          Trace("strings-ff-debug")
              << "Found endpoint in b = " << b << ", whose flat form is "
              << d_flat_form[b] << std::endl;
          // endpoint
          std::vector<Node> conc_c;
          for (size_t j = count; j < asize; j++)
          {
            conc_c.push_back(a[d_flat_form_index[a][j]].eqNode(d_emptyString));
          }
          Assert(!conc_c.empty());
          conc = utils::mkAnd(conc_c);
          infType = FlatFormInfer::ENDPOINT_EMP;
          Assert(count > 0);
          break;
        }
        else
        {
          Node cc = d_flat_form[b][count];
          if (cc != curr)
          {
            Node bc = b[d_flat_form_index[b][count]];
            inelig.push_back(b);
            Assert(!d_state.areEqual(curr, cc));
            Node cc_c = getConstantEqc(cc);
            if (!curr_c.isNull() && !cc_c.isNull())
            {
              // check for constant conflict
              int index;
              Node s = TheoryStringsRewriter::splitConstant(
                  cc_c, curr_c, index, isRev);
              if (s.isNull())
              {
                d_im.addToExplanation(ac, d_eqc_to_const_base[curr], exp);
                d_im.addToExplanation(d_eqc_to_const_exp[curr], exp);
                d_im.addToExplanation(bc, d_eqc_to_const_base[cc], exp);
                d_im.addToExplanation(d_eqc_to_const_exp[cc], exp);
                conc = d_false;
                infType = FlatFormInfer::CONST;
                break;
              }
            }
            else if ((d_flat_form[a].size() - 1) == count
                     && (d_flat_form[b].size() - 1) == count)
            {
              conc = ac.eqNode(bc);
              infType = FlatFormInfer::ENDPOINT_EQ;
              break;
            }
            else
            {
              // if lengths are the same, apply LengthEq
              std::vector<Node> lexp2;
              Node lcc = d_state.getLength(bc, lexp2);
              if (d_state.areEqual(lcurr, lcc))
              {
                if (Trace.isOn("strings-ff-debug"))
                {
                  Trace("strings-ff-debug")
                      << "Infer " << ac << " == " << bc << " since " << lcurr
                      << " == " << lcc << std::endl;
                  Trace("strings-ff-debug")
                      << "Explanation for " << lcurr << " is ";
                  for (size_t j = 0; j < lexp.size(); j++)
                  {
                    Trace("strings-ff-debug") << lexp[j] << std::endl;
                  }
                  Trace("strings-ff-debug")
                      << "Explanation for " << lcc << " is ";
                  for (size_t j = 0; j < lexp2.size(); j++)
                  {
                    Trace("strings-ff-debug") << lexp2[j] << std::endl;
                  }
                }

                exp.insert(exp.end(), lexp.begin(), lexp.end());
                exp.insert(exp.end(), lexp2.begin(), lexp2.end());
                d_im.addToExplanation(lcurr, lcc, exp);
                conc = ac.eqNode(bc);
                infType = FlatFormInfer::UNIFY;
                break;
              }
            }
          }
        }
      }
    }
    if (!conc.isNull())
    {
      Trace("strings-ff-debug") << "Found inference (" << infType
                                << "): " << conc << " based on equality " << a
                                << " == " << b << ", " << isRev << std::endl;
      d_im.addToExplanation(a, b, exp);
      // explain why prefixes up to now were the same
      for (size_t j = 0; j < count; j++)
      {
        Trace("strings-ff-debug") << "Add at " << d_flat_form_index[a][j] << " "
                                  << d_flat_form_index[b][j] << std::endl;
        d_im.addToExplanation(
            a[d_flat_form_index[a][j]], b[d_flat_form_index[b][j]], exp);
      }
      // explain why other components up to now are empty
      for (unsigned t = 0; t < 2; t++)
      {
        Node c = t == 0 ? a : b;
        ssize_t jj;
        if (infType == FlatFormInfer::ENDPOINT_EQ
            || (t == 1 && infType == FlatFormInfer::ENDPOINT_EMP))
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
        ssize_t startj = isRev ? jj + 1 : 0;
        ssize_t endj = isRev ? c.getNumChildren() : jj;
        for (ssize_t j = startj; j < endj; j++)
        {
          if (d_state.areEqual(c[j], d_emptyString))
          {
            d_im.addToExplanation(c[j], d_emptyString, exp);
          }
        }
      }
      // Notice that F_EndpointEmp is not typically applied, since
      // strict prefix equality ( a.b = a ) where a,b non-empty
      // is conflicting by arithmetic len(a.b)=len(a)+len(b)!=len(a)
      // when len(b)!=0. Although if we do not infer this conflict eagerly,
      // it may be applied (see #3272).
      std::stringstream ss;
      ss << infType;
      d_im.sendInference(exp, conc, ss.str().c_str());
      if (d_state.isInConflict())
      {
        return;
      }
      break;
    }
    count++;
  } while (inelig.size() < eqc.size());
}

Node CoreSolver::checkCycles( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp ){
  if( std::find( curr.begin(), curr.end(), eqc )!=curr.end() ){
    // a loop
    return eqc;
  }else if( std::find( d_strings_eqc.begin(), d_strings_eqc.end(), eqc )==d_strings_eqc.end() ){
    curr.push_back( eqc );
    //look at all terms in this equivalence class
    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
    while( !eqc_i.isFinished() ) {
      Node n = (*eqc_i);
      if( d_congruent.find( n )==d_congruent.end() ){
        if( n.getKind() == kind::STRING_CONCAT ){
          Trace("strings-cycle") << eqc << " check term : " << n << " in " << eqc << std::endl;
          if( eqc!=d_emptyString_r ){
            d_eqc[eqc].push_back( n );
          }
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            Node nr = d_state.getRepresentative(n[i]);
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
                d_im.addToExplanation(n, eqc, exp);
                d_im.addToExplanation(nr, n[i], exp);
                if( ncy==eqc ){
                  //can infer all other components must be empty
                  for( unsigned j=0; j<n.getNumChildren(); j++ ){
                    //take first non-empty
                    if (j != i && !d_state.areEqual(n[j], d_emptyString))
                    {
                      d_im.sendInference(
                          exp, n[j].eqNode(d_emptyString), "I_CYCLE");
                      return Node::null();
                    }
                  }
                  Trace("strings-error") << "Looping term should be congruent : " << n << " " << eqc << " " << ncy << std::endl;
                  //should find a non-empty component, otherwise would have been singular congruent (I_Norm_S)
                  Assert(false);
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

void CoreSolver::checkNormalFormsEq()
{
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
    Node nf_term = utils::mkNConcat(nfe.d_nf);
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

//compute d_normal_forms_(base,exp,exp_depend)[eqc]
void CoreSolver::normalizeEquivalenceClass( Node eqc ) {
  Trace("strings-process-debug") << "Process equivalence class " << eqc << std::endl;
  if (d_state.areEqual(eqc, d_emptyString))
  {
#ifdef CVC4_ASSERTIONS
    for( unsigned j=0; j<d_eqc[eqc].size(); j++ ){
      Node n = d_eqc[eqc][j];
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Assert(d_state.areEqual(n[i], d_emptyString));
      }
    }
#endif
    //do nothing
    Trace("strings-process-debug") << "Return process equivalence class " << eqc << " : empty." << std::endl;
    d_normal_form[eqc].init(d_emptyString);
  }
  else
  {
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

    //construct the normal form
    Assert(!normal_forms.empty());
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

NormalForm& CoreSolver::getNormalForm(Node n)
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

void CoreSolver::getNormalForms(Node eqc,
                                   std::vector<NormalForm>& normal_forms,
                                   std::map<Node, unsigned>& term_to_nf_index)
{
  //constant for equivalence class
  Node eqc_non_c = eqc;
  Trace("strings-process-debug") << "Get normal forms " << eqc << std::endl;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
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
            Node nr = ee->getRepresentative( n[i] );
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
                  utils::printConcatTrace(currv, "strings-error");
                  Trace("strings-error") << "..." << currv[i] << std::endl;
                }
                Assert(!d_state.areEqual(currv[i], n));
              }
            }
          }
          term_to_nf_index[n] = normal_forms.size();
          normal_forms.push_back(nf_curr);
        }else{
          //this was redundant: combination of self + empty string(s)
          Node nn = currv.size() == 0 ? d_emptyString : currv[0];
          Assert(d_state.areEqual(nn, eqc));
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
          Assert(d_eqc_to_const_base.find(eqc) != d_eqc_to_const_base.end());
          d_im.addToExplanation(n, d_eqc_to_const_base[eqc], exp);
          Assert(d_eqc_to_const_exp.find(eqc) != d_eqc_to_const_exp.end());
          if( !d_eqc_to_const_exp[eqc].isNull() ){
            exp.push_back( d_eqc_to_const_exp[eqc] );
          }
          // Notice although not implemented, this can be minimized based on
          // firstc/lastc, normal_forms_exp_depend.
          exp.insert(exp.end(), nf.d_exp.begin(), nf.d_exp.end());
          Node conc = d_false;
          d_im.sendInference(exp, conc, "N_NCTN");
        }
      }
    }
  }
}

void CoreSolver::processNEqc(std::vector<NormalForm>& normal_forms)
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
    Trace("strings-solve") << "#" << i << ": From " << pinfer[i].d_i << " / "
                           << pinfer[i].d_j << " (rev=" << pinfer[i].d_rev
                           << ") : ";
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
  Trace("strings-solve") << "...choose #" << use_index << std::endl;
  doInferInfo(pinfer[use_index]);
}

void CoreSolver::processSimpleNEq(NormalForm& nfi,
                                     NormalForm& nfj,
                                     unsigned& index,
                                     bool isRev,
                                     unsigned rproc,
                                     std::vector<InferInfo>& pinfer)
{
  std::vector<Node>& nfiv = nfi.d_nf;
  std::vector<Node>& nfjv = nfj.d_nf;
  NodeManager* nm = NodeManager::currentNM();
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
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
        while (!d_state.isInConflict() && index_k < (nfkv.size() - rproc))
        {
          //can infer that this string must be empty
          Node eq = nfkv[index_k].eqNode(d_emptyString);
          //Trace("strings-lemma") << "Strings: Infer " << eq << " from " << eq_exp << std::endl;
          Assert(!d_state.areEqual(d_emptyString, nfkv[index_k]));
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
        Assert(!d_state.areEqual(nfiv[index], nfjv[index]));
        std::vector< Node > temp_exp;
        Node length_term_i = d_state.getLength(nfiv[index], temp_exp);
        Node length_term_j = d_state.getLength(nfjv[index], temp_exp);
        // check  length(nfiv[index]) == length(nfjv[index])
        if (d_state.areEqual(length_term_i, length_term_j))
        {
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
            eqn.push_back(utils::mkNConcat(eqnc));
          }
          if (!d_state.areEqual(eqn[0], eqn[1]))
          {
            d_im.sendInference(
                antec, eqn[0].eqNode(eqn[1]), "N_EndpointEq", true);
            return;
          }
          else
          {
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
          Node length_term_i = d_state.getLength(nfiv[index], lexp);
          Node length_term_j = d_state.getLength(nfjv[index], lexp);
          //split on equality between string lengths (note that splitting on equality between strings is worse since it is harder to process)
          if (!d_state.areDisequal(length_term_i, length_term_j)
              && !d_state.areEqual(length_term_i, length_term_j)
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
                Assert(other_str.getKind() != kind::CONST_STRING)
                    << "Other string is not constant.";
                Assert(other_str.getKind() != kind::STRING_CONCAT)
                    << "Other string is not CONCAT.";
                if( !ee->areDisequal( other_str, d_emptyString, true ) ){
                  Node eq = other_str.eqNode( d_emptyString );
                  eq = Rewriter::rewrite(eq);
                  if (eq.isConst())
                  {
                    // If the equality rewrites to a constant, we must use the
                    // purify variable for this string to communicate that
                    // we have inferred whether it is empty.
                    Node p = d_skCache.mkSkolemCached(
                        other_str, SkolemCache::SK_PURIFY, "lsym");
                    Node pEq = p.eqNode(d_emptyString);
                    // should not be constant
                    Assert(!Rewriter::rewrite(pEq).isConst());
                    // infer the purification equality, and the (dis)equality
                    // with the empty string in the direction that the rewriter
                    // inferred
                    info.d_conc =
                        nm->mkNode(AND,
                                   p.eqNode(other_str),
                                   !eq.getConst<bool>() ? pEq.negate() : pEq);
                    info.d_id = INFER_INFER_EMP;
                  }
                  else
                  {
                    info.d_conc = nm->mkNode(OR, eq, eq.negate());
                    info.d_id = INFER_LEN_SPLIT_EMP;
                  }
                  //set info
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
                    Assert(!const_str.isNull());
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
                        Node sk = d_skCache.mkSkolemCached(
                            other_str,
                            prea,
                            isRev ? SkolemCache::SK_ID_C_SPT_REV
                                  : SkolemCache::SK_ID_C_SPT,
                            "c_spt");
                        Trace("strings-csp") << "Const Split: " << prea << " is removed from " << stra << " due to " << strb << ", p=" << p << std::endl;        
                        //set info
                        info.d_conc = other_str.eqNode(
                            isRev ? utils::mkNConcat(sk, prea)
                                  : utils::mkNConcat(prea, sk));
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
                      Node sk = d_skCache.mkSkolemCached(
                          other_str,
                          c_firstHalf,
                          isRev ? SkolemCache::SK_ID_VC_BIN_SPT_REV
                                : SkolemCache::SK_ID_VC_BIN_SPT,
                          "cb_spt");
                      Trace("strings-csp") << "Const Split: " << c_firstHalf << " is removed from " << const_str << " (binary) " << std::endl;
                      info.d_conc = nm->mkNode(
                          OR,
                          other_str.eqNode(
                              isRev ? utils::mkNConcat(sk, c_firstHalf)
                                    : utils::mkNConcat(c_firstHalf, sk)),
                          nm->mkNode(
                              AND,
                              sk.eqNode(d_emptyString).negate(),
                              c_firstHalf.eqNode(
                                  isRev ? utils::mkNConcat(sk, other_str)
                                        : utils::mkNConcat(other_str, sk))));
                      info.d_new_skolem[LENGTH_SPLIT].push_back(sk);
                      info.d_id = INFER_SSPLIT_CST_BINARY;
                      info_valid = true;
                    }else{
                      // normal v/c split
                      Node firstChar = stra.size() == 1 ? const_str : NodeManager::currentNM()->mkConst( isRev ? stra.suffix( 1 ) : stra.prefix( 1 ) );
                      Node sk = d_skCache.mkSkolemCached(
                          other_str,
                          isRev ? SkolemCache::SK_ID_VC_SPT_REV
                                : SkolemCache::SK_ID_VC_SPT,
                          "c_spt");
                      Trace("strings-csp") << "Const Split: " << firstChar << " is removed from " << const_str << " (serial) " << std::endl;
                      info.d_conc = other_str.eqNode(
                          isRev ? utils::mkNConcat(sk, firstChar)
                                : utils::mkNConcat(firstChar, sk));
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
                      std::pair<bool, Node> et = d_state.entailmentCheck(
                          options::TheoryOfMode::THEORY_OF_TYPE_BASED, ent_lit);
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
                  if( ee->areDisequal( x, d_emptyString, true ) ) {
                    info.d_ant.push_back( xgtz );
                  } else {
                    info.d_antn.push_back( xgtz );
                  }
                }
                Node sk = d_skCache.mkSkolemCached(
                    nfiv[index],
                    nfjv[index],
                    isRev ? SkolemCache::SK_ID_V_SPT_REV
                          : SkolemCache::SK_ID_V_SPT,
                    "v_spt");
                // must add length requirement
                info.d_new_skolem[LENGTH_GEQ_ONE].push_back(sk);
                Node eq1 = nfiv[index].eqNode(
                    isRev ? utils::mkNConcat(sk, nfjv[index])
                          : utils::mkNConcat(nfjv[index], sk));
                Node eq2 = nfjv[index].eqNode(
                    isRev ? utils::mkNConcat(sk, nfiv[index])
                          : utils::mkNConcat(nfiv[index], sk));

                if( lentTestSuccess!=-1 ){
                  info.d_antn.push_back( lentTestExp );
                  info.d_conc = lentTestSuccess==0 ? eq1 : eq2;
                  info.d_id = INFER_SSPLIT_VAR_PROP;
                  info_valid = true;
                }else{
                  Node ldeq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ).negate();
                  if( ee->areDisequal( length_term_i, length_term_j, true ) ){
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
            Assert(!success);
          }
        }
      }
    }
  }while( success );
}

bool CoreSolver::detectLoop(NormalForm& nfi,
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
CoreSolver::ProcessLoopResult CoreSolver::processLoop(NormalForm& nfi,
                                                            NormalForm& nfj,
                                                            int loop_index,
                                                            int index,
                                                            InferInfo& info)
{
  if (options::stringProcessLoopMode() == options::ProcessLoopMode::ABORT)
  {
    throw LogicException("Looping word equation encountered.");
  }
  else if (options::stringProcessLoopMode() == options::ProcessLoopMode::NONE)
  {
    d_im.setIncomplete();
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
  Node t_yz = utils::mkNConcat(vec_t);
  Trace("strings-loop") << " (" << t_yz << ")" << std::endl;
  Trace("strings-loop") << " ... S(Z.Y)= ";
  std::vector<Node> vec_s(vecoi.begin() + index + 1, vecoi.end());
  Node s_zy = utils::mkNConcat(vec_s);
  Trace("strings-loop") << s_zy << std::endl;
  Trace("strings-loop") << " ... R= ";
  std::vector<Node> vec_r(veci.begin() + loop_index + 1, veci.end());
  Node r = utils::mkNConcat(vec_r);
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
      if (!d_state.areDisequal(t, d_emptyString))
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

  Node ant = d_im.mkExplain(info.d_ant);
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
        restr = utils::mkNConcat(z, y);
        cc = Rewriter::rewrite(s_zy.eqNode(utils::mkNConcat(v2)));
      }
      else
      {
        cc = Rewriter::rewrite(s_zy.eqNode(utils::mkNConcat(z, y)));
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
    if (options::stringProcessLoopMode()
        == options::ProcessLoopMode::SIMPLE_ABORT)
    {
      throw LogicException("Normal looping word equation encountered.");
    }
    else if (options::stringProcessLoopMode()
             == options::ProcessLoopMode::SIMPLE)
    {
      d_im.setIncomplete();
      return ProcessLoopResult::SKIPPED;
    }

    Trace("strings-loop") << "Strings::Loop: Normal Loop Breaking."
                          << std::endl;
    // right
    Node sk_w = d_skCache.mkSkolem("w_loop");
    Node sk_y = d_skCache.mkSkolem("y_loop");
    d_im.registerLength(sk_y, LENGTH_GEQ_ONE);
    Node sk_z = d_skCache.mkSkolem("z_loop");
    // t1 * ... * tn = y * z
    Node conc1 = t_yz.eqNode(utils::mkNConcat(sk_y, sk_z));
    // s1 * ... * sk = z * y * r
    vec_r.insert(vec_r.begin(), sk_y);
    vec_r.insert(vec_r.begin(), sk_z);
    Node conc2 = s_zy.eqNode(utils::mkNConcat(vec_r));
    Node conc3 = vecoi[index].eqNode(utils::mkNConcat(sk_y, sk_w));
    Node restr = r == d_emptyString ? s_zy : utils::mkNConcat(sk_z, sk_y);
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
void CoreSolver::processDeq( Node ni, Node nj ) {
  NodeManager* nm = NodeManager::currentNM();
  NormalForm& nfni = getNormalForm(ni);
  NormalForm& nfnj = getNormalForm(nj);
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
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
        Assert(index < nfi.size() && index < nfj.size());
        Node i = nfi[index];
        Node j = nfj[index];
        Trace("strings-solve-debug")  << "...Processing(DEQ) " << i << " " << j << std::endl;
        if (!d_state.areEqual(i, j))
        {
          Assert(i.getKind() != kind::CONST_STRING
                 || j.getKind() != kind::CONST_STRING);
          std::vector< Node > lexp;
          Node li = d_state.getLength(i, lexp);
          Node lj = d_state.getLength(j, lexp);
          if (d_state.areDisequal(li, lj))
          {
            if( i.getKind()==kind::CONST_STRING || j.getKind()==kind::CONST_STRING ){
              //check if empty
              Node const_k = i.getKind() == kind::CONST_STRING ? i : j;
              Node nconst_k = i.getKind() == kind::CONST_STRING ? j : i;
              Node lnck = i.getKind() == kind::CONST_STRING ? lj : li;
              if( !ee->areDisequal( nconst_k, d_emptyString, true ) ){
                Node eq = nconst_k.eqNode( d_emptyString );
                Node conc = NodeManager::currentNM()->mkNode( kind::OR, eq, eq.negate() );
                d_im.sendInference(d_emptyVec, conc, "D-DISL-Emp-Split");
                return;
              }else{
                //split on first character
                CVC4::String str = const_k.getConst<String>();
                Node firstChar = str.size() == 1 ? const_k : NodeManager::currentNM()->mkConst( str.prefix( 1 ) );
                if (d_state.areEqual(lnck, d_one))
                {
                  if (d_state.areDisequal(firstChar, nconst_k))
                  {
                    return;
                  }
                  else if (!d_state.areEqual(firstChar, nconst_k))
                  {
                    //splitting on demand : try to make them disequal
                    if (d_im.sendSplit(
                            firstChar, nconst_k, "S-Split(DEQL-Const)", false))
                    {
                      return;
                    }
                  }
                }
                else
                {
                  Node sk = d_skCache.mkSkolemCached(
                      nconst_k, SkolemCache::SK_ID_DC_SPT, "dc_spt");
                  d_im.registerLength(sk, LENGTH_ONE);
                  Node skr =
                      d_skCache.mkSkolemCached(nconst_k,
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
              if (d_state.areDisequal(ni, nj))
              {
                antec.push_back( ni.eqNode( nj ).negate() );
              }
              else
              {
                antec_new_lits.push_back( ni.eqNode( nj ).negate() );
              }
              antec_new_lits.push_back( li.eqNode( lj ).negate() );
              std::vector< Node > conc;
              Node sk1 = d_skCache.mkSkolemCached(
                  i, j, SkolemCache::SK_ID_DEQ_X, "x_dsplit");
              Node sk2 = d_skCache.mkSkolemCached(
                  i, j, SkolemCache::SK_ID_DEQ_Y, "y_dsplit");
              Node sk3 = d_skCache.mkSkolemCached(
                  i, j, SkolemCache::SK_ID_DEQ_Z, "z_dsplit");
              d_im.registerLength(sk3, LENGTH_GEQ_ONE);
              //Node nemp = sk3.eqNode(d_emptyString).negate();
              //conc.push_back(nemp);
              Node lsk1 = utils::mkNLength(sk1);
              conc.push_back( lsk1.eqNode( li ) );
              Node lsk2 = utils::mkNLength(sk2);
              conc.push_back( lsk2.eqNode( lj ) );
              conc.push_back(nm->mkNode(OR,
                                        j.eqNode(utils::mkNConcat(sk1, sk3)),
                                        i.eqNode(utils::mkNConcat(sk2, sk3))));
              d_im.sendInference(
                  antec, antec_new_lits, nm->mkNode(AND, conc), "D-DISL-Split");
              return;
            }
          }
          else if (d_state.areEqual(li, lj))
          {
            Assert(!d_state.areDisequal(i, j));
            //splitting on demand : try to make them disequal
            if (d_im.sendSplit(i, j, "S-Split(DEQL)", false))
            {
              return;
            }
          }
          else
          {
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
    Assert(false);
  }
}

int CoreSolver::processReverseDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj ) {
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

int CoreSolver::processSimpleDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj, unsigned& index, bool isRev ){
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
      Node lni = d_state.getLengthExp(ni, ant, nfni.d_base);
      Node lnj = d_state.getLengthExp(nj, ant, nfnj.d_base);
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
      if (!d_state.areEqual(i, j))
      {
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
          Node li = d_state.getLength(i, lexp);
          Node lj = d_state.getLength(j, lexp);
          if (d_state.areEqual(li, lj) && d_state.areDisequal(i, j))
          {
            Trace("strings-solve") << "Simple Case 2 : found equal length disequal sub strings " << i << " " << j << std::endl;
            //we are done: D-Remove
            return 1;
          }
          else
          {
            return 0;
          }
        }
      }
      index++;
    }
  }
  return 0;
}

void CoreSolver::addNormalFormPair( Node n1, Node n2 ){
  if (n1>n2)
  {
    addNormalFormPair(n2,n1);
    return;
  }
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
    Assert(isNormalFormPair(n1, n2));
  } else {
    Trace("strings-nf-debug") << "Already a normal form pair " << n1 << " " << n2 << std::endl;
  }
}

bool CoreSolver::isNormalFormPair( Node n1, Node n2 ) {
  if (n1>n2)
  {
    return isNormalFormPair(n2,n1);
  }
  //Trace("strings-debug") << "is normal form pair. " << n1 << " " << n2 << std::endl;
  NodeIntMap::const_iterator it = d_nf_pairs.find( n1 );
  if( it!=d_nf_pairs.end() ){
    Assert(d_nf_pairs_data.find(n1) != d_nf_pairs_data.end());
    for( int i=0; i<(*it).second; i++ ){
      Assert(i < (int)d_nf_pairs_data[n1].size());
      if( d_nf_pairs_data[n1][i]==n2 ){
        return true;
      }
    }
  }
  return false;
}

void CoreSolver::checkNormalFormsDeq()
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  std::vector< std::vector< Node > > cols;
  std::vector< Node > lts;
  std::map< Node, std::map< Node, bool > > processed;
  
  const context::CDList<Node>& deqs = d_state.getDisequalityList();

  //for each pair of disequal strings, must determine whether their lengths are equal or disequal
  for (const Node& eq : deqs)
  {
    Node n[2];
    for( unsigned i=0; i<2; i++ ){
      n[i] = ee->getRepresentative( eq[i] );
    }
    if( processed[n[0]].find( n[1] )==processed[n[0]].end() ){
      processed[n[0]][n[1]] = true;
      Node lt[2];
      for( unsigned i=0; i<2; i++ ){
        EqcInfo* ei = d_state.getOrMakeEqcInfo(n[i], false);
        lt[i] = ei ? ei->d_lengthTerm : Node::null();
        if( lt[i].isNull() ){
          lt[i] = eq[i];
        }
        lt[i] = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt[i] );
      }
      if (!d_state.areEqual(lt[0], lt[1]) && !d_state.areDisequal(lt[0], lt[1]))
      {
        d_im.sendSplit(lt[0], lt[1], "DEQ-LENGTH-SP");
      }
    }
  }

  if (!d_im.hasProcessed())
  {
    d_state.separateByLength(d_strings_eqc, cols, lts);
    for( unsigned i=0; i<cols.size(); i++ ){
      if (cols[i].size() > 1 && !d_im.hasPendingLemma())
      {
        if (Trace.isOn("strings-solve"))
        {
          Trace("strings-solve") << "- Verify disequalities are processed for "
                                 << cols[i][0] << ", normal form : ";
          utils::printConcatTrace(getNormalForm(cols[i][0]).d_nf, "strings-solve");
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
              if (d_state.areDisequal(cols[i][j], cols[i][k]))
              {
                Assert(!d_state.isInConflict());
                if (Trace.isOn("strings-solve"))
                {
                  Trace("strings-solve") << "- Compare " << cols[i][j] << " ";
                  utils::printConcatTrace(getNormalForm(cols[i][j]).d_nf, "strings-solve");
                  Trace("strings-solve") << " against " << cols[i][k] << " ";
                  utils::printConcatTrace(getNormalForm(cols[i][k]).d_nf, "strings-solve");
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

void CoreSolver::checkLengthsEqc() {
  for (unsigned i = 0; i < d_strings_eqc.size(); i++)
  {
    NormalForm& nfi = getNormalForm(d_strings_eqc[i]);
    Trace("strings-process-debug")
        << "Process length constraints for " << d_strings_eqc[i] << std::endl;
    // check if there is a length term for this equivalence class
    EqcInfo* ei = d_state.getOrMakeEqcInfo(d_strings_eqc[i], false);
    Node lt = ei ? ei->d_lengthTerm : Node::null();
    if (lt.isNull())
    {
      Trace("strings-process-debug")
          << "No length term for eqc " << d_strings_eqc[i] << std::endl;
      continue;
    }
    Node llt = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, lt);
    // now, check if length normalization has occurred
    if (ei->d_normalizedLength.get().isNull())
    {
      Node nf = utils::mkNConcat(nfi.d_nf);
      if (Trace.isOn("strings-process-debug"))
      {
        Trace("strings-process-debug")
            << "  normal form is " << nf << " from base " << nfi.d_base
            << std::endl;
        Trace("strings-process-debug") << "  normal form exp is: " << std::endl;
        for (const Node& exp : nfi.d_exp)
        {
          Trace("strings-process-debug") << "   " << exp << std::endl;
        }
      }

      // if not, add the lemma
      std::vector<Node> ant;
      ant.insert(ant.end(), nfi.d_exp.begin(), nfi.d_exp.end());
      ant.push_back(nfi.d_base.eqNode(lt));
      Node lc = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, nf);
      Node lcr = Rewriter::rewrite(lc);
      Trace("strings-process-debug")
          << "Rewrote length " << lc << " to " << lcr << std::endl;
      if (!d_state.areEqual(llt, lcr))
      {
        Node eq = llt.eqNode(lcr);
        ei->d_normalizedLength.set(eq);
        d_im.sendInference(ant, eq, "LEN-NORM", true);
      }
    }
  }
}

void CoreSolver::doInferInfo(const InferInfo& ii)
{
  // send the inference
  if (!ii.d_nf_pair[0].isNull())
  {
    Assert(!ii.d_nf_pair[1].isNull());
    addNormalFormPair(ii.d_nf_pair[0], ii.d_nf_pair[1]);
  }
  // send the inference
  d_im.sendInference(ii);
  // Register the new skolems from this inference. We register them here
  // (lazily), since the code above has now decided to use the inference
  // at use_index that involves them.
  for (const std::pair<const LengthStatus, std::vector<Node> >& sks :
       ii.d_new_skolem)
  {
    for (const Node& n : sks.second)
    {
      d_im.registerLength(n, sks.first);
    }
  }
}


}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
