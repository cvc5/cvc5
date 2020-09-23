/*********************                                                        */
/*! \file type_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for datatypes
 **
 ** Enumerators for datatypes.
 **/

#include "theory/datatypes/type_enumerator.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes_utils.h"

using namespace CVC4;
using namespace theory;
using namespace datatypes;

Node DatatypesEnumerator::getTermEnum( TypeNode tn, unsigned i ){
   Node ret;
   if( i<d_terms[tn].size() ){
     ret = d_terms[tn][i];
   }else{
     Debug("dt-enum-debug") << "get term enum " << tn << " " << i << std::endl;
     std::map< TypeNode, unsigned >::iterator it = d_te_index.find( tn );
     unsigned tei;
     if( it==d_te_index.end() ){
       //initialize child enumerator for type
       tei = d_children.size();
       d_te_index[tn] = tei;
       if( tn.isDatatype() && d_has_debruijn ){
         //must indicate that this is a child enumerator (do not normalize constants for it)
         DatatypesEnumerator * dte = new DatatypesEnumerator( tn, true, d_tep );
         d_children.push_back( TypeEnumerator( dte ) );
       }else{
         d_children.push_back( TypeEnumerator( tn, d_tep ) );
       }
       d_terms[tn].push_back( *d_children[tei] );
     }else{
       tei = it->second;
     }
     //enumerate terms until index is reached
     while( i>=d_terms[tn].size() ){
       ++d_children[tei];
       if( d_children[tei].isFinished() ){
         Debug("dt-enum-debug") << "...fail term enum " << tn << " " << i << std::endl;
         return Node::null();
       }
       d_terms[tn].push_back( *d_children[tei] );
     }
     Debug("dt-enum-debug") << "...return term enum " << tn << " " << i << " : " << d_terms[tn][i] << std::endl;
     ret = d_terms[tn][i];
   }
   return ret;
 }

 bool DatatypesEnumerator::increment( unsigned index ){
   Debug("dt-enum") << "Incrementing " << d_type << " " << d_ctor << " at size " << d_sel_sum[index] << "/" << d_size_limit << std::endl;
   if( d_sel_sum[index]==-1 ){
     //first time
     d_sel_sum[index] = 0;
     //special case: no children to iterate
     if( index>=d_has_debruijn && d_sel_types[index].empty() ){
       Debug("dt-enum") << "...success (nc) = " << (d_size_limit==0) << std::endl;
       return d_size_limit==0;
     }else{
       Debug("dt-enum") << "...success" << std::endl;
       return true;
     }
   }else{
     unsigned i = 0;
     while( i < d_sel_index[index].size() ){
       //increment if the sum of iterations on arguments is less than the limit
       if( d_sel_sum[index]<(int)d_size_limit ){
         //also check if child enumerator has enough terms
         if( !getTermEnum( d_sel_types[index][i], d_sel_index[index][i]+1 ).isNull() ){
           Debug("dt-enum") << "...success increment child " << i << std::endl;
           d_sel_index[index][i]++;
           d_sel_sum[index]++;
           return true;
         }
       }
       Debug("dt-enum") << "......failed increment child " << i << std::endl;
       //reset child, iterate next
       d_sel_sum[index] -= d_sel_index[index][i];
       d_sel_index[index][i] = 0;
       i++;
     }
     Debug("dt-enum") << "...failure." << std::endl;
     return false;
   }
 }

 Node DatatypesEnumerator::getCurrentTerm(unsigned index)
 {
   Debug("dt-enum-debug") << "Get current term at " << index << " " << d_type
                          << std::endl;
   Node ret;
   if (index < d_has_debruijn)
   {
     if (d_child_enum)
     {
       ret = NodeManager::currentNM()->mkConst(
           UninterpretedConstant(d_type, d_size_limit));
     }
     else
     {
       // no top-level variables
       return Node::null();
     }
   }
   else
   {
     Debug("dt-enum-debug")
         << "Look at constructor " << (index - d_has_debruijn) << std::endl;
     const DTypeConstructor& ctor = d_datatype[index - d_has_debruijn];
     Debug("dt-enum-debug") << "Check last term..." << std::endl;
     // we first check if the last argument (which is forced to make sum of
     // iterated arguments equal to d_size_limit) is defined
     Node lc;
     if (ctor.getNumArgs() > 0)
     {
       Assert(index < d_sel_types.size());
       Assert(ctor.getNumArgs() - 1 < d_sel_types[index].size());
       lc = getTermEnum(d_sel_types[index][ctor.getNumArgs() - 1],
                        d_size_limit - d_sel_sum[index]);
       if (lc.isNull())
       {
         Debug("dt-enum-debug") << "Current infeasible." << std::endl;
         return Node::null();
       }
     }
     Debug("dt-enum-debug") << "Get constructor..." << std::endl;
     NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
     if (d_datatype.isParametric())
     {
       NodeManager* nm = NodeManager::currentNM();
       TypeNode typ = ctor.getSpecializedConstructorType(d_type);
       b << nm->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                       nm->mkConst(AscriptionType(typ.toType())),
                       ctor.getConstructor());
     }
     else
     {
       b << ctor.getConstructor();
     }
     Debug("dt-enum-debug") << "Get arguments..." << std::endl;
     if (ctor.getNumArgs() > 0)
     {
       Assert(index < d_sel_types.size());
       Assert(index < d_sel_index.size());
       Assert(d_sel_types[index].size() == ctor.getNumArgs());
       Assert(d_sel_index[index].size() == ctor.getNumArgs() - 1);
       for (int i = 0; i < (int)(ctor.getNumArgs() - 1); i++)
       {
         Node c = getTermEnum(d_sel_types[index][i], d_sel_index[index][i]);
         Assert(!c.isNull());
         b << c;
       }
       b << lc;
     }
     Node nnn = Node(b);
     Debug("dt-enum-debug") << "Return... " << nnn << std::endl;
     ret = nnn;
   }

   if (!d_child_enum && d_has_debruijn)
   {
     Node nret = DatatypesRewriter::normalizeCodatatypeConstant(ret);
     if (nret != ret)
     {
       if (nret.isNull())
       {
         Trace("dt-enum-nn") << "Invalid constant : " << ret << std::endl;
       }
       else
       {
         Trace("dt-enum-nn") << "Non-normal constant : " << ret << std::endl;
         Trace("dt-enum-nn") << "  ...normal form is : " << nret << std::endl;
       }
       return Node::null();
     }
   }

   return ret;
 }

 void DatatypesEnumerator::init()
 {
   Debug("dt-enum") << "datatype is datatype? " << d_type.isDatatype()
                    << std::endl;
   Debug("dt-enum") << "datatype is kind " << d_type.getKind() << std::endl;
   Debug("dt-enum") << "datatype is " << d_type << std::endl;
   Debug("dt-enum") << "properties : " << d_datatype.isCodatatype() << " "
                    << d_datatype.isRecursiveSingleton(d_type);
   Debug("dt-enum") << " " << d_datatype.isInterpretedFinite(d_type)
                    << std::endl;

   if (d_datatype.isCodatatype() && hasCyclesDt(d_datatype))
   {
     // start with uninterpreted constant
     d_has_debruijn = 1;
     d_sel_types.push_back(std::vector<TypeNode>());
     d_sel_index.push_back(std::vector<unsigned>());
     d_sel_sum.push_back(-1);
   }
   else
   {
     // find the "zero" term via mkGroundTerm
     Debug("dt-enum-debug") << "make ground term..." << std::endl;
     // Start with the ground term constructed via mkGroundValue, which does
     // a traversal over the structure of the datatype to find a finite term.
     // Notice that mkGroundValue may be dependent upon extracting the first
     // value of type enumerators for *other non-datatype* subfield types of
     // this datatype. Since datatypes can not be embedded in non-datatype
     // types (e.g. (Array D D) cannot be a subfield type of datatype D), this
     // call is guaranteed to avoid infinite recursion.
     d_zeroTerm = d_datatype.mkGroundValue(d_type);
     d_zeroTermActive = true;
     Debug("dt-enum-debug") << "done : " << d_zeroTerm << std::endl;
     Assert(d_zeroTerm.getKind() == kind::APPLY_CONSTRUCTOR);
     d_has_debruijn = 0;
   }
   Debug("dt-enum") << "zero term : " << d_zeroTerm << std::endl;
   d_ctor = 0;
   for (unsigned i = 0, ncons = d_datatype.getNumConstructors(); i < ncons; ++i)
   {
     d_sel_types.push_back(std::vector<TypeNode>());
     d_sel_index.push_back(std::vector<unsigned>());
     d_sel_sum.push_back(-1);
     const DTypeConstructor& ctor = d_datatype[i];
     TypeNode typ;
     if (d_datatype.isParametric())
     {
       typ = ctor.getSpecializedConstructorType(d_type);
     }
     for (unsigned a = 0; a < ctor.getNumArgs(); ++a)
     {
       TypeNode tn;
       if (d_datatype.isParametric())
       {
         tn = typ[a];
       }
       else
       {
         tn = ctor[a].getSelector().getType()[1];
       }
       d_sel_types.back().push_back(tn);
       d_sel_index.back().push_back(0);
     }
     if (!d_sel_index.back().empty())
     {
       d_sel_index.back().pop_back();
     }
   }
   d_size_limit = 0;
   if (!d_zeroTermActive)
   {
     // Set up initial conditions (should always succeed). Here, we are calling
     // the increment function of this class, which ensures a term is ready to
     // read via a dereference of this class. We use the same method for
     // setting up the first term, if it is not already set up
     // (d_zeroTermActive) using the increment function, for uniformity.
     ++*this;
   }
   AlwaysAssert(!isFinished());
 }

 DatatypesEnumerator& DatatypesEnumerator::operator++()
 {
   Debug("dt-enum-debug") << ": increment " << this << std::endl;
   if (d_zeroTermActive)
   {
     d_zeroTermActive = false;
   }
   unsigned prevSize = d_size_limit;
   while (d_ctor < d_has_debruijn + d_datatype.getNumConstructors())
   {
     // increment at index
     while (increment(d_ctor))
     {
       Node n = getCurrentTerm(d_ctor);
       if (!n.isNull())
       {
         if (n == d_zeroTerm)
         {
           d_zeroTerm = Node::null();
         }
         else
         {
           return *this;
         }
       }
     }
     // Here, we need to step from the current constructor to the next one

     // Go to the next constructor
     d_ctor = d_ctor + 1;
     if (d_ctor >= d_has_debruijn + d_datatype.getNumConstructors())
     {
       // try next size limit as long as new terms were generated at last size,
       // or other cases
       if (prevSize == d_size_limit
           || (d_size_limit == 0 && d_datatype.isCodatatype())
           || !d_datatype.isInterpretedFinite(d_type))
       {
         d_size_limit++;
         d_ctor = 0;
         for (unsigned i = 0; i < d_sel_sum.size(); i++)
         {
           d_sel_sum[i] = -1;
         }
       }
     }
   }
   return *this;
 }
