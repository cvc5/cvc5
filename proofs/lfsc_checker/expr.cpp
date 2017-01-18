#include "expr.h"
#include <stdlib.h>
#include <sstream>
#ifdef _MSC_VER
#include <algorithm>
#endif
#include "check.h"

using namespace std;

int HoleExpr::next_id = 0;
int Expr::markedCount = 0;

C_MACROS__ADD_CHUNKING_MEMORY_MANAGEMENT_CC(CExpr,kids,32768);

//C_MACROS__ADD_CHUNKING_MEMORY_MANAGEMENT_CC(IntCExpr,_n,32768);

#define USE_HOLE_PATH_COMPRESSION

void Expr::debug() {
  print(cout);
  /*
  cout << "\nAt " << this << "\n";
  cout << "marked = " << getmark() << "\n";
  */
  cout << "\n";
  cout.flush();
}

bool destroy_progs = false;

#define destroydec(rr) \
  do { \
    Expr *r = rr;	    \
    int ref = r->data >> 9; \
    ref = ref - 1; \
    if (ref == 0) {  \
      _e = r;		  \
      goto start_destroy; \
    } \
    else \
      r->data = (ref << 9) | (r->data & 511); \
  } while(0)

//removed from below "ref = ref -1;":   r->debugrefcnt(ref,DEC);

void Expr::destroy(Expr *_e, bool dec_kids) {
 start_destroy:
  switch (_e->getclass()) {
  case INT_EXPR:
    delete (IntExpr *)_e;
    break;
  case SYMS_EXPR:  {
    SymSExpr *e = (SymSExpr *)_e;
    if (e->val && e->val->getop() != PROG) {
      Expr *tmp = e->val;
      delete e;
      destroydec(tmp);
    }
    else
      delete e;
    break;
  }
  case SYM_EXPR: {
    SymExpr *e = (SymExpr *)_e;
    if (e->val && e->val->getop() != PROG) {
      Expr *tmp = e->val;
      delete e;
      destroydec(tmp);
    }
    else
      delete e;
    break;
  }
  case HOLE_EXPR: {
    HoleExpr *e = (HoleExpr *)_e;
    if (e->val) {
      Expr *tmp = e->val;
      delete e;
      destroydec(tmp);
    }
    else
      delete e;
    break;
  }
  case CEXPR: {
    CExpr *e = (CExpr *)_e;
    if (dec_kids) {
      Expr **cur = e->kids;
      Expr *tmp;
      while((tmp = *cur++)) {
	if (*cur)
	  tmp->dec();
	else {
	  delete e;
	  destroydec(tmp);
	  break;
	}
      }
    }
    else
      delete e;
    break;
  }
  }
}

Expr *Expr::clone() {
  switch (getclass()) {
  case INT_EXPR:
  case RAT_EXPR:
    inc();
    return this;
  case SYMS_EXPR: 
  case SYM_EXPR: {
    SymExpr *e = (SymExpr *)this;
    if (e->val)
      if (e->val->getop() != PROG)
	return e->val->clone();
    e->inc();
    return e;
  }
  case HOLE_EXPR: {
    HoleExpr *e = (HoleExpr *)this;
    if (e->val)
      return e->val->clone();
    e->inc();
    return e;
  }
  case CEXPR: {
    CExpr *e = (CExpr *)this;
    int op = e->getop();
    switch(op) {
    case LAM: {
#ifdef DEBUG_SYM_NAMES
      SymSExpr *var = (SymSExpr *)e->kids[0];
      SymSExpr *newvar = new SymSExpr(*var,SYMS_EXPR);
#else
      SymExpr *var = (SymExpr *)e->kids[0];
      SymExpr *newvar = new SymExpr(*var);
#endif
      Expr *prev = var->val;
      var->val = newvar;
      Expr *bod = e->kids[1]->clone();
      var->val = prev;
      return new CExpr(LAM,newvar,bod);
    }
    case PI: {
#ifdef DEBUG_SYM_NAMES
      SymSExpr *var = (SymSExpr *)e->kids[0];
      SymSExpr *newvar = new SymSExpr(*var,SYMS_EXPR);
#else
      SymExpr *var = (SymExpr *)e->kids[0];
      SymExpr *newvar = new SymExpr(*var);
#endif
      Expr *tp = e->kids[1]->clone();
      Expr *prev = var->val;
      var->val = newvar;
      Expr *bod = e->kids[2]->clone();
      var->val = prev;
      Expr* ret = new CExpr(PI,newvar,tp,bod);
      if( data&256 )
         ret->data |=256;
      return ret;
    }
    default: {
      Expr **cur = e->kids;
      Expr *tmp;
      int size = 0;
      while((*cur++))
	      size++;
      Expr **kids = new Expr*[size+1];
      kids[size]=0;
      cur = e->kids;
      bool diff_kid = false;
      int i = 0;
      while((tmp = *cur++)) {
	      Expr *c = tmp->clone();
	      diff_kid |= (c != tmp);
	      kids[i++] = c;
      }
      if (diff_kid)
	      return new CExpr(op, true /* dummy */, kids);
      for (int i = 0, iend = size; i != iend; i++)
	kids[i]->dec();
      delete[] kids;
      e->inc();
      return e;
    }
    }
  }
  }
  std::abort();  // should never be reached
}


Expr* Expr::build_app(Expr *hd, const std::vector<Expr *> &args, int start) {
#ifndef USE_FLAT_APP
  Expr *ret = hd;
  for (int i = start, iend = args.size(); i < iend; i++)
    ret = new CExpr(APP,ret,args[i]);
  return ret;
#else
  if( start>=(int)args.size() )
    return hd;
  else
  {
    Expr **kids = new Expr *[args.size() - start + 2];
    kids[0] = hd;
    for (int i = start, iend = args.size(); i < iend; i++)
      kids[i - start + 1] = args[i];
    kids[args.size() - start + 1] = NULL;
    return new CExpr(APP, true /* dummy */, kids);
  }
#endif
}

Expr* Expr::make_app(Expr* e1, Expr* e2 )
{
   //std::cout << "make app from ";
   //e1->print( std::cout );
   //std::cout << " ";
   //e2->print( std::cout );
   //std::cout << std::endl;
   CExpr *ret;
   if( e1->getclass()==CEXPR ){
      int counter = 0;
      while( ((CExpr*)e1)->kids[counter] ){
         counter++;
      }
      Expr **kids = new Expr *[counter + 2];
      counter = 0;
      while( ((CExpr*)e1)->kids[counter] ){
        kids[counter] = ((CExpr *)e1)->kids[counter];
        kids[counter]->inc();
        counter++;
      }
      kids[counter] = e2;
      kids[counter + 1] = NULL;
      ret = new CExpr(APP, true /* dummy */, kids);
   }else{
      ret = new CExpr( APP, e1, e2 );
   }
   //ret->print( std::cout );
   //std::cout << std::endl;
   return ret;
}

int Expr::cargCount = 0;

Expr *Expr::collect_args(std::vector<Expr *> &args, bool follow_defs) {
   //cargCount++;
   //if( cargCount%1000==0)
   //std::cout << cargCount << std::endl;
#ifndef USE_FLAT_APP
  CExpr *e = (CExpr *)this;
  args.reserve(16);
  while( e->getop() == APP ) {
    args.push_back(e->kids[1]);
    e = (CExpr *)e->kids[0];
    if (follow_defs)
      e = (CExpr *)e->followDefs();
  }
  std::reverse(args.begin(),args.end());
  return e;
#else
  CExpr *e = (CExpr *)this;
  args.reserve(16);
  if( e->getop()==APP ){
      int counter = 1;
      while( e->kids[counter] ) {
         args.push_back(e->kids[counter]);
         counter++;
      }
      e = (CExpr*)e->kids[0];
  }
  if (follow_defs)
      return e->followDefs();
  else
      return e;
#endif
}

Expr *Expr::get_head(bool follow_defs) const {
  CExpr *e = (CExpr *)this;
  while( e->getop() == APP ) {
    e = (CExpr *)e->kids[0];
    if (follow_defs)
      e = (CExpr *)e->followDefs();
  }
  return e;
}

Expr *Expr::get_body(int op, bool follow_defs) const {
  CExpr *e = (CExpr *)this;
  while( e->getop() == op ) {
    e = (CExpr *)e->kids[2];
    if (follow_defs)
      e = (CExpr *)e->followDefs();
  }
  return e;
}

// if the return value is different from this, then it is a new reference
Expr *CExpr::whr() {
  vector<Expr *> args;
  if (get_head()->getop() == LAM) {
    CExpr *head = (CExpr *)collect_args(args, true);
    Expr *cloned_head;
    if (head->cloned()) {
      // we must clone
      head = (CExpr *)head->clone();
      cloned_head = head;
    }
    else {
      head->setcloned();
      cloned_head = 0;
    }
    int i = 0;
    int iend = args.size();

    /* we will end up incrementing the ref count for all the args,
       since each is either pointed to by a var (following a
       beta-reduction), or else just an argument in the new
       application we build below. */

    do {
      Expr *tmp = args[i++]->followDefs();
      ((SymExpr *)head->kids[0])->val = tmp;
      tmp->inc();
      head = (CExpr *)head->kids[1];
    } while(head->getop() == LAM && i < iend);
    for (; i < iend; i++)
      args[i]->inc();
    head->inc();
    if (cloned_head)
      cloned_head->dec();
    return build_app(head,args,i);
  }
  else 
    return this;
}

Expr* CExpr::convert_to_tree_app( Expr* e )
{
  if( e->getop()==APP )
  {
    std::vector< Expr* > kds;
    int counter = 1;
    while( ((CExpr*)e)->kids[counter] )
    {
      kds.push_back( convert_to_tree_app( ((CExpr*)e)->kids[counter] ) );
      counter++;
    }
    Expr* app = Expr::build_app( e->get_head(), kds );
    //app->inc();
    return app;
  }
  else
  {
    return e;
  }
}

Expr* CExpr::convert_to_flat_app( Expr* e )
{
  if( e->getop()==APP )
  {
    std::vector< Expr* > args;
    Expr* hd = ((CExpr*)e)->collect_args( args );
    Expr **kids = new Expr *[args.size() + 2];
    kids[0] = hd;
    for (size_t a = 0; a < args.size(); a++) {
      kids[a + 1] = convert_to_flat_app(args[a]);
    }
    kids[args.size() + 1] = 0;
    CExpr *nce = new CExpr(APP, true /* dummy */, kids);
    nce->inc();
    return nce;
  }
  else
  {
    return e;
  }
}

bool Expr::defeq(Expr *e) {
  /* we handle a few special cases up front, where this Expr might
     equal e, even though they have different opclass (i.e., different
     structure). */

  if (this == e)
    return true;
  int op1 = getop();
  int op2 = e->getop();
  switch (op1) {
  case ASCRIBE:
    return ((CExpr *)this)->kids[0]->defeq(e);
  case APP: {
    Expr *tmp = ((CExpr *)this)->whr();
    if (tmp != this) {
      bool b = tmp->defeq(e);
      tmp->dec();
      return b;
    }
    if (get_head()->getclass() == HOLE_EXPR) {
      vector<Expr *> args;
      Expr *head = collect_args(args, true);
      Expr *t = e;
      t->inc();
      for (int i = 0, iend = args.size(); i < iend; i++) {
	      // don't worry about SYMS_EXPR's, since we should not be in code here.
	      if (args[i]->getclass() != SYM_EXPR || args[i]->getexmark())
	        /* we cannot fill the hole in this case.  Either this is not
	          a variable or we are using a variable again. */
	        return false;
	      SymExpr *v = (SymExpr *)args[i];

	      // we may have been mapping from expected var v to a computed var
	      Expr *tmp = (v->val ? v->val : v);

	      tmp->inc();
	      t = new CExpr(LAM, tmp, t);
	      args[i]->setexmark();
      }
      for (int i = 0, iend = args.size(); i < iend; i++) 
	      args[i]->clearexmark();
#ifdef DEBUG_HOLES
      cout << "Filling hole ";
      head->debug();
      cout << "with ";
      t->debug();
#endif
      ((HoleExpr *)head)->val = t;
      return true;
    }
    break;
  }
  case NOT_CEXPR:
    switch (getclass()) {
    case HOLE_EXPR: {
      HoleExpr *h = (HoleExpr *)this;
      if (h->val)
	      return h->val->defeq(e);
#ifdef DEBUG_HOLES
      cout << "Filling hole ";
      h->debug();
      cout << "with ";
      e->debug();
#endif
#ifdef USE_HOLE_PATH_COMPRESSION
      Expr *tmp = e->followDefs();
#else
      Expr *tmp = e;
#endif
      h->val = tmp;
      tmp->inc();
      return true;
    }
    case SYMS_EXPR: 
    case SYM_EXPR: {
      SymExpr *s = (SymExpr *)this;
      if (s->val)
	return s->val->defeq(e);
      break;
    }
    }
    break;
  }
  
  switch (op2) {
  case ASCRIBE:
    return defeq(((CExpr *)e)->kids[0]);
  case APP: {
    Expr *tmp = ((CExpr *)e)->whr();
    if (tmp != e) {
      bool b = defeq(tmp);
      tmp->dec();
      return b;
    }
    break;
  }
  case NOT_CEXPR:
    switch (e->getclass()) {
    case HOLE_EXPR: {
      HoleExpr *h = (HoleExpr *)e;
      if (h->val)
	return defeq(h->val);

#ifdef DEBUG_HOLES
      cout << "Filling hole ";
      h->debug();
      cout << "with ";
      debug();
#endif
#ifdef USE_HOLE_PATH_COMPRESSION
      Expr *tmp = followDefs();
#else
      Expr *tmp = this;
#endif
      h->val = tmp;
      tmp->inc();
      return true;
    }
    case SYMS_EXPR: 
    case SYM_EXPR: {
      SymExpr *s = (SymExpr *)e;
      if (s->val)
	return defeq(s->val);
      break;
    }
    }
    break;
  }

  /* at this point, e1 and e2 must have the same opclass if they are 
     to be equal. */

  if (op1 != op2)
    return false;
  
  if (op1 == NOT_CEXPR) {
    switch(getclass()) {
    case INT_EXPR: {
      IntExpr *i1 = (IntExpr *)this;
      IntExpr *i2 = (IntExpr *)e;
      return (mpz_cmp(i1->n,i2->n) == 0);
    }
    case RAT_EXPR: {
      RatExpr *r1 = (RatExpr *)this;
      RatExpr *r2 = (RatExpr *)e;
      return (mpq_cmp(r1->n,r2->n) == 0);
    }
    case SYMS_EXPR: 
    case SYM_EXPR: 
      return (this == e);
    }
  }

  /* Now op1 and op2 must both be CExprs, and must have the same op to be
     equal. */

  CExpr *e1 = (CExpr *)this;
  CExpr *e2 = (CExpr *)e;

  int last = 1;
  switch (op1) {
  case PI:
    if (!e1->kids[1]->defeq(e2->kids[1]))
      return false;
    last++;
    // fall through to LAM case
  case LAM: {

    /* It is critical that we point e1's var. (v1) back to e2's (call
       it v2).  The reason this is critical is that we assume any
       holes are in e1.  So we could end up with (_ v1) = t. We wish
       to fill _ in this case with (\ v2 t).  If v2 pointed to v1, we
       could not return (\ v1 t), because the fact that v2 points to
       v1 would then be lost.
    */
    SymExpr *v1 = (SymExpr *)e1->kids[0];
    Expr *prev_v1_val = v1->val;
    v1->val = e2->kids[0]->followDefs();
    bool bodies_equal = e1->kids[last]->defeq(e2->kids[last]);
    v1->val = prev_v1_val;
    return bodies_equal;
  }
  case APP: 
#ifndef USE_FLAT_APP
    return (e1->kids[0]->defeq(e2->kids[0]) &&
	    e1->kids[1]->defeq(e2->kids[1]));
#else
    {
      int counter = 0;
      while( e1->kids[counter] ){
         if( e1->kids[counter]!=e2->kids[counter] ){
           if( !e2->kids[counter] || !e1->kids[counter]->defeq( e2->kids[counter] ) )
              return false;
           //--- optimization : replace child with equivalent pointer if was defeq
           // Heuristic: prefer symbolic kids because they may be cheaper to
           // deal with (e.g. in free_in()).
           if (e2->kids[counter]->isSymbolic() ||
               (!e1->kids[counter]->isSymbolic() &&
                e1->kids[counter]->getrefcnt() <
                    e2->kids[counter]->getrefcnt())) {
             e1->kids[counter]->dec();
             e2->kids[counter]->inc();
             e1->kids[counter] = e2->kids[counter];
           }else{
             e2->kids[counter]->dec();
             e1->kids[counter]->inc();
             e2->kids[counter] = e1->kids[counter];
           }
         }
         //---
         counter++;
      }
      return e2->kids[counter]==NULL;
    }
#endif
  case TYPE:
  case KIND:
  case MPZ:
    // already checked that both exprs have the same opclass.
    return true;
  } // switch(op1)

  std::abort();  // never reached.
}

int Expr::fiCounter = 0;

bool Expr::_free_in(Expr *x, expr_ptr_set_t *visited) {
  // fiCounter++;
  // if( fiCounter%1==0 )
  //   std::cout << fiCounter << std::endl;
  if (visited->find(this) != visited->end()) {
    return false;
  }

  switch (getop()) {
    case NOT_CEXPR:
      switch (getclass()) {
      case HOLE_EXPR: {
         HoleExpr *h = (HoleExpr *)this;
         if (h->val) return h->val->_free_in(x, visited);
         return (h == x);
      }
      case SYMS_EXPR: 
      case SYM_EXPR: {
         SymExpr *s = (SymExpr *)this;
         if (s->val && s->val->getclass() == HOLE_EXPR)
           /* we do not need to follow the "val" pointer except in this
             one case, when x is a hole (which we do not bother to check
             here) */
           return s->val->_free_in(x, visited);
         return (s == x);
      }
      case INT_EXPR:
         return false;
      }
      break;
   case LAM:
   case PI:
      if (x == ((CExpr *)this)->kids[0])
         return false;
      // fall through
   default: {
      // must be a CExpr
      assert(this->getclass() == CEXPR);
      CExpr *e = (CExpr *)this;
      Expr *tmp;
      Expr **cur = e->kids;
      visited->insert(this);
      while ((tmp = *cur++))
        if (tmp->_free_in(x, visited)) return true;
      return false;
   }
   }
   std::abort();  // should not be reached
}

void Expr::calc_free_in(){
   data &= ~256;
   data |= 256*((CExpr *)this)->kids[2]->free_in( ((CExpr *)this)->kids[0] );
}

string Expr::toString() {
  ostringstream oss;
  print(oss);
  return oss.str();
}

static void print_kids(ostream &os, Expr **kids) {
  Expr *tmp;
  while ((tmp = *kids++)) {
    os << " ";
    tmp->print(os);
  }
}

static void print_vector(ostream &os, const vector<Expr *> &v) {
  for(int i = 0, iend = v.size(); i < iend; i++) {
    os << " ";
    v[i]->print(os);
  }
}

void Expr::print(ostream &os) {
  CExpr *e = (CExpr *)this; // for CEXPR cases

  //std::cout << e->getop() << " ";
  /*
#ifdef DEBUG_REFCNT
  os << "<";
  char tmp[10];
  sprintf(tmp,"%d",getrefcnt());
  os << tmp << "> ";
#endif
*/

  switch(getop()) {
  case NOT_CEXPR: {
    switch(getclass()) {
    case INT_EXPR: 
    {
      IntExpr *e = (IntExpr *)this;
      if (mpz_sgn(e->n) < 0) {
	      os << "(~ ";
	      mpz_t tmp;
	      mpz_init(tmp);
	      mpz_neg(tmp,e->n);
	      char *s = mpz_get_str(0,10,tmp);
	      os << s;
	      free(s);
	      mpz_clear(tmp);
	      os << ")";
        //os << "mpz";
      }
      else {
	      char *s = mpz_get_str(0,10,e->n);
	      os << s;
	      free(s);
        //os << "mpz";
      }
      break;
    }
    case RAT_EXPR: 
    {
      RatExpr *e = (RatExpr *)this;
      char *s = mpq_get_str(0,10,e->n);
      os << s;
      if (mpq_sgn(e->n) < 0) {
	      os << "(~ ";
	      mpq_t tmp;
	      mpq_init(tmp);
	      mpq_neg(tmp,e->n);
	      char *s = mpq_get_str(0,10,tmp);
	      os << s;
	      free(s);
	      mpq_clear(tmp);
	      os << ")";
      }
      else {
	      char *s = mpq_get_str(0,10,e->n);
	      os << s;
	      free(s);
      }
      break;
    }
#ifndef DEBUG_SYM_NAMES
    case SYM_EXPR: 
    {
      SymExpr *e = (SymExpr *)this;
      if (e->val) {
	      if (e->val->getop() == PROG) {
	        os << e;
#ifdef DEBUG_SYMS
	        os << "[PROG]";
#endif
	      }else{
#ifdef DEBUG_SYMS
	        os << e;
	        os << "[SYM ";
#endif
	        e->val->print(os);
#ifdef DEBUG_SYMS
	        os << "]";
#endif
        }
      }
      else
	      os << e;
      break;
    }
#else
    case SYM_EXPR: /* if we are debugging sym names, then
		      SYM_EXPRs are really SymSExprs. */
#endif
    case SYMS_EXPR: {
      SymSExpr *e = (SymSExpr *)this;
      if (e->val) {
	      if (e->val->getop() == PROG) {
	        os << e->s;
#ifdef DEBUG_SYMS
	        os << "[PROG]";
#endif
	      }else{
#ifdef DEBUG_SYMS
	        os << e->s;
	        os << "[SYM ";
#endif
	        e->val->print(os);
#ifdef DEBUG_SYMS
	        os << "]";
#endif
	      }
      }
      else
	      os << e->s;
      break;
    }
    case HOLE_EXPR: 
    {
      HoleExpr *e = (HoleExpr *)this;
      if (e->val) {
#ifdef DEBUG_SYMS
	      os << "_" << "[HOLE ";
#endif
	      e->val->print(os);
#ifdef DEBUG_SYMS
	      os << "]";
#endif
      }else {
	      os << "_";
#ifdef DEBUG_HOLE_NAMES
	      char tmp[100];
	      sprintf(tmp,"%d",e->id);
	      os << "[ " << tmp << "]";
#else
	      os << "[ " << e << "]";
#endif
      }
      break;
    }
    default:
      os << "; unrecognized form of expr";
      break;
    }
    break;
  } // case NOT_CEXPR
  case APP: {
    os << "(";
    vector<Expr *> args;
    Expr *head = collect_args(args, false /* follow_defs */);
    head->print(os);
    print_vector(os, args);
    os << ")";
    break;
  }
  case LAM: 
    os << "(\\";
    print_kids(os, e->kids);
    os << ")";
    break;
  case PI: 
    os << "(!";
    print_kids(os, e->kids);
    os << ")";
    break;
  case TYPE: 
    os << "type";
    break;
  case KIND: 
    os << "kind";
    break;
  case MPZ: 
    os << "mpz";
    break;
  case MPQ:
    os << "mpq";
    break;
  case ADD: 
    os << "(mp_add";  
    print_kids(os,e->kids);
    os << ")";
    break;
  case MUL:
    os << "(mp_mul";  
    print_kids(os,e->kids);
    os << ")";
    break;
  case DIV:
    os << "(mp_div";  
    print_kids(os,e->kids);
    os << ")";
    break;
  case NEG: 
    os << "(mp_neg";
    print_kids(os,e->kids);
    os << ")";
    break;
  case IFNEG:
    os << "(ifneg";
    print_kids(os,e->kids);
    os << ")";
    break;
  case IFZERO:
    os << "(ifzero";
    print_kids(os,e->kids);
    os << ")";
    break;
  case RUN: 
    os << "(run";
    print_kids(os,e->kids);
    os << ")";
    break;
  case PROG: 
    os << "(prog";
    print_kids(os,e->kids);
    os << ")";
    break;
  case PROGVARS: 
    os << "(";
    print_kids(os,e->kids);
    os << ")";
    break;
  case MATCH: 
    os << "(match";
    print_kids(os,e->kids);
    os << ")";
    break;
  case CASE: 
    os << "(";
    print_kids(os,e->kids);
    os << ")";
    break;
  case LET: 
    os << "(let";
    print_kids(os,e->kids);
    os << ")";
    break;
  case DO: 
    os << "(do";
    print_kids(os,e->kids);
    os << ")";
    break;
  case IFMARKED: 
    os << "(ifmarked";
    print_kids(os,e->kids);
    os << ")";
    break;
  case COMPARE:
    os << "(compare";
    print_kids(os,e->kids);
    os << ")";
    break;
  case MARKVAR: 
    os << "(markvar";
    print_kids(os,e->kids);
    os << ")";
    break;
  case FAIL: 
    os << "(fail ";
    print_kids(os, e->kids);
    os << ")";
    break;
  case ASCRIBE: 
    os << "(:";
    print_kids(os, e->kids);
    os << ")";
    break;
  default:
    os << "; unrecognized form of expr(2) " << getop() << " " << getclass();
  } // switch(getop())
}

bool Expr::isType( Expr* statType ){
  Expr* typ = this;
  while( typ!=statType ){
    if( typ->getop()==PI ){
      typ = ((CExpr*)typ)->kids[2];
    }else{
      return false;
    }
  }
  return true;
}

int SymExpr::symmCount = 0;
#ifdef MARKVAR_32
int SymExpr::mark()
{
  if( mark_map.find( this )== mark_map.end() )
  {
    symmCount++;
    mark_map[this] = 0;
  }
  return mark_map[this];
}
void SymExpr::smark( int m )
{
  mark_map[this] = m;
}
#endif
