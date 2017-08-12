#include "position.h"
#include "check.h"
#include "code.h"
#include "expr.h"
#include "trie.h"
#include "sccwriter.h"
#include "libwriter.h"
#ifndef _MSC_VER
#include <libgen.h>
#endif
#include <stack>
#include <string.h>
#include <time.h>
#include "scccode.h"
#include "print_smt2.h"

using namespace std;
#ifndef _MSC_VER
using namespace __gnu_cxx;
#endif

int linenum = 1;
int colnum = 1;
const char *filename = 0;
FILE *curfile = 0;

//#define USE_HASH_MAPS  //AJR: deprecated

symmap2 progs;
std::vector< Expr* > ascHoles;

#ifdef USE_HASH_MAPS
hash_map<string, Expr *> symbols;
hash_map<string, Expr *> symbol_types;
#else
Trie<pair<Expr *, Expr *> > *symbols = new Trie<pair<Expr *, Expr *> >;
#endif

hash_map<string, bool > imports;
std::map<SymExpr*, int > mark_map;
std::vector< std::pair< std::string, std::pair<Expr *, Expr *> > > local_sym_names;

Expr *not_defeq1 = 0;
Expr *not_defeq2 = 0;

bool tail_calls = true;
bool big_check = true;

void report_error(const string &msg) {
  if (filename) {
    Position p(filename,linenum,colnum);
    p.print(cout);
  }
  cout << "\n";
  cout << msg;
  cout << "\n";
  if (not_defeq1 && not_defeq2) {
    cout << "The following terms are not definitionally equal:\n1. ";
    not_defeq1->print(cout);
    cout << "\n2. ";
    not_defeq2->print(cout);
  }
  cout.flush();
  exit(1);
}

Expr *call_run_code(Expr *code) {
  if (dbg_prog) {
    cout << "[Running ";
    code->print(cout);
    cout << "\n";
  }
  Expr *computed_result = run_code(code);
  if (dbg_prog) {
    cout << "] returning ";
    if (computed_result)
      computed_result->print(cout);
    else
      cout << "fail";
    cout << "\n";
  }
  return computed_result;
}

char our_getc_c = 0;

int IDBUF_LEN = 2048;
char idbuf[2048];

Expr *statType = new CExpr(TYPE);
Expr *statKind = new CExpr(KIND);
Expr *statMpz = new CExpr(MPZ);
Expr *statMpq = new CExpr(MPQ);

int open_parens = 0;

// only call in check()
void eat_rparen() {
  eat_char(')');
  open_parens--;
}

void eat_excess(int prev) {
  while(open_parens > prev)
    eat_rparen();
}

/* There are four cases for check():

1. expected=0, create is false: check() sets computed to be the classifier of
   the checked term.

2. expected=0, create is true: check() returns
   the checked expression and sets computed to be its classifier.

3. expected is non-null, create is false: check returns NULL.

4. expected is non-null, create is true: check returns the term that
   was checked.

We consume the reference for expected, to enable tail calls in the
application case.

If is_hole is NULL, then the expression parsed may not be a hole.
Otherwise, it may be, and we will set *is_hole to true if it is
(but leave *is_hole alone if it is not).

*/

bool allow_run = false;
int app_rec_level = 0;

Expr *check(bool create, Expr *expected, Expr **computed = NULL,
	    bool *is_hole = 0, bool return_pos = false, bool inAsc = false ) {
 start_check:
        //std::cout << "check code ";
        //if( expected )
        //  expected->print( std::cout );
        //std::cout << std::endl;
  char d = non_ws();
  switch(d) {
  case '(': {

    open_parens++;

    char c = non_ws();
    switch (c) {
    case EOF:
      report_error("Unexpected end of file.");
      break;
    case '!': { // the pi case
      string id(prefix_id());
#ifdef DEBUG_SYM_NAMES
      Expr *sym = new SymSExpr(id,SYMS_EXPR);
#else
      Expr *sym = new SymExpr(id);
      //std::cout << "name " << id << " " << sym << std::endl;
#endif
      allow_run = true;
      int prevo = open_parens;
      Expr *domain = check(true, statType);
      eat_excess(prevo);
      allow_run = false;
#ifdef USE_HASH_MAPS
      Expr *prev = symbols[id];
      Expr *prevtp = symbol_types[id];
      symbols[id] = sym;
      symbol_types[id] = domain;
#else
      pair<Expr *,Expr *>prev =
	symbols->insert(id.c_str(),pair<Expr *,Expr *>(sym,domain));
#endif
      if (expected)
	      expected->inc();
      Expr *range = check(create, expected, computed, NULL, return_pos);
      eat_excess(prevo);
      eat_rparen();

#ifdef USE_HASH_MAPS
      symbols[id] = prev;
      symbol_types[id] = prevtp;
#else
      symbols->insert(id.c_str(),prev);
#endif
      if (expected) {
	int o = expected->followDefs()->getop();
	expected->dec();
	if (o != TYPE && o != KIND)
	  report_error(string("The expected classifier for a pi abstraction")
		       +string("is neither \"type\" nor \"kind\".\n")
		       +string("1. the expected classifier: ")
		       +expected->toString());
   if (create){
	  CExpr* ret = new CExpr(PI, sym, domain, range);
      ret->calc_free_in();
      return ret;
   }
	return 0;
      }
      else {
         if (create){
	         CExpr* ret = new CExpr(PI, sym, domain, range);
            ret->calc_free_in();
            return ret;
         }
	int o = (*computed)->followDefs()->getop();
	if (o != TYPE && o != KIND)
	  report_error(string("The classifier for the range of a pi")
		       +string("abstraction is neither \"type\" nor ")
		       +string("\"kind\".\n1. the computed classifier: ")
		       +range->toString());
	return 0;
      }
    }
    case '%': { // the case for big lambda
      if (expected || create || !return_pos || !big_check)
	report_error(string("Big lambda abstractions can only be used")
		     +string("in the return position of a \"bigcheck\"\n")
		     +string("command."));
      string id(prefix_id());
#ifdef DEBUG_SYM_NAMES
      SymExpr *sym = new SymSExpr(id, SYMS_EXPR);
#else
      SymExpr *sym = new SymExpr(id);
      //std::cout << "name " << id << " " << sym << std::endl;
#endif

      int prevo = open_parens;
      Expr *expected_domain = check(true, statType);
      eat_excess(prevo);

#ifdef USE_HASH_MAPS
      Expr *prev = symbols[id];
      Expr *prevtp = symbol_types[id];
      symbols[id] = sym;
      symbol_types[id] = expected_domain;
#else
      pair<Expr *, Expr *> prevpr =
	      symbols->insert(id.c_str(), pair<Expr *, Expr *>(sym,expected_domain));
      Expr *prev = prevpr.first;
      Expr *prevtp = prevpr.second;
#endif
      expected_domain->inc(); // because we have stored it in the symbol table

      //will clean up local sym name eventually
      local_sym_names.push_back( std::pair< std::string, std::pair<Expr *, Expr *> >( id, prevpr ) );
      if (prev)
	      prev->dec();
      if (prevtp)
	      prevtp->dec();
      create = false;
      expected = NULL;
      // computed unchanged
      is_hole = NULL;
      // return_pos unchanged

      // note we will not store the proper return type in computed.

      goto start_check;
    }

    case '\\': { // the lambda case
      if (!expected)
	report_error(string("We are computing a type for a lambda ")
		     +string("abstraction, but we can only check\n")
		     +string("such against a type.  Try inserting an ")
		     +string("ascription (using ':').\n"));
      Expr *orig_expected = expected;
      expected = expected->followDefs();
      if (expected->getop() != PI)
	report_error(string("We are type-checking a lambda abstraction, but\n")
		     +string("the expected type is not a pi abstraction.\n")
		     +string("1. The expected type: ") + expected->toString());
      string id(prefix_id());
#ifdef DEBUG_SYM_NAMES
      SymExpr *sym = new SymSExpr(id, SYMS_EXPR);
#else
      SymExpr *sym = new SymExpr(id);
      //std::cout << "name " << id << " " << sym << std::endl;
#endif

      CExpr *pitp = (CExpr *)expected;
      Expr *expected_domain = pitp->kids[1];
      Expr *expected_range = pitp->kids[2];
      SymExpr *pivar = (SymExpr *)pitp->kids[0];
      if (expected_range->followDefs()->getop() == TYPE)
	report_error(string("The expected classifier for a lambda abstraction")
		     +string(" a kind, not a type.\n")
		     +string("1. The expected classifier: ")
		     +expected->toString());

      /* we need to map the pivar to the new sym, because in our
	 higher-order matching we may have (_ x) to unify with t.
	 The x must be something from an expected type, since only these
	 can have holes.  We want to map expected vars x to computed vars y,
	 so that we can set the hole to be \ y t, where t contains ys but
         not xs. */

#ifdef USE_HASH_MAPS
      Expr *prev = symbols[id];
      Expr *prevtp = symbol_types[id];
      symbols[id] = sym;
      symbol_types[id] = expected_domain;
#else
      pair<Expr *, Expr *> prevpr =
	      symbols->insert(id.c_str(), pair<Expr *, Expr *>(sym,expected_domain));
      Expr *prev = prevpr.first;
      Expr *prevtp = prevpr.second;
#endif
      Expr *prev_pivar_val = pivar->val;
      sym->inc();
      pivar->val = sym;

      expected_domain->inc(); // because we have stored it in the symbol table
      expected_range->inc(); // because we will pass it to a recursive call

      if (tail_calls && big_check && return_pos && !create) {
        //will clean up local sym name eventually
        local_sym_names.push_back( std::pair< std::string, std::pair<Expr *, Expr *> >( id, prevpr ) );
	      if (prev_pivar_val)
	        prev_pivar_val->dec();
	      if (prev)
	        prev->dec();
	      if (prevtp)
	        prevtp->dec();
	      orig_expected->dec();
	      create = false;
	      expected = expected_range;
	      computed = NULL;
	      is_hole = NULL;
	      // return_pos unchanged
	      goto start_check;
      }
      else {

	      int prev = open_parens;
	      Expr *range = check(create, expected_range, NULL, NULL, return_pos);
	      eat_excess(prev);
	      eat_rparen();

#ifdef USE_HASH_MAPS
	      symbols[id] = prev;
	      symbol_types[id] = prevtp;
#else
	      symbols->insert(id.c_str(), prevpr);
#endif
	      expected_domain->dec(); // because removed from the symbol table now

	      pivar->val = prev_pivar_val;

	      orig_expected->dec();

	      sym->dec(); // the pivar->val reference
	      if (create)
	        return new CExpr(LAM, sym, range);
	      sym->dec(); // the symbol table reference, otherwise in the new LAM
	      return 0;
      }
    }
    case '^': { // the run case
      if (!allow_run || !create || !expected)
	      report_error(string("A run expression (operator \"^\") appears in")
		          +string(" a disallowed position."));

      Expr *code = read_code();
      //string errstr = (string("The first argument in a run expression must be")
		    //   +string(" a call to a program.\n1. the argument: ")
		    //   +code->toString());

      /* determine expected type of the result term, and make sure
	 the code term is an allowed one. */
#if 0
      Expr *progret;
      if (code->isArithTerm())
	      progret = statMpz;
      else {
	      if (code->getop() != APP)
	        report_error(errstr);

	      CExpr *call = (CExpr *)code;

	      // prog is not known to be a SymExpr yet
	      CExpr *prog = (CExpr *)call->get_head();

	      if (prog->getop() != PROG)
	        report_error(errstr);

	      progret = prog->kids[0]->get_body();
      }
#else
      Expr *progret = NULL;
      if (code->isArithTerm())
	      progret = statMpz;
      else {
	      if (code->getop() == APP)
        {
	        CExpr *call = (CExpr *)code;

	        // prog is not known to be a SymExpr yet
	        CExpr *prog = (CExpr *)call->get_head();

	        if (prog->getop() == PROG)
	          progret = prog->kids[0]->get_body();
        }
      }
#endif
      /* determine expected type of the result term, and make sure
	      the code term is an allowed one. */
      //Expr* progret = check_code( code );

      /* the next term cannot be a hole where run expressions are introduced.
	      When they are checked in applications, it can be. */
      int prev = open_parens;
      if( progret )
        progret->inc();
      Expr *trm = check(true, progret);
      eat_excess(prev);
      eat_rparen();

      if (expected->getop() != TYPE)
	      report_error(string("The expected type for a run expression is not ")
		          +string("\"type\".\n")
		          +string("1. The expected type: ")+expected->toString());
      expected->dec();
      return new CExpr(RUN, code, trm);
    }

    case ':': { // the ascription case
      statType->inc();
      int prev = open_parens;
      Expr *tp = check(true, statType, NULL, NULL, false, true );
      eat_excess(prev);

      if (!expected)
	      tp->inc();

      Expr *trm = check(create, tp, NULL, NULL, return_pos);
      eat_excess(prev);
      eat_rparen();
      if (expected) {
	      if (!expected->defeq(tp))
	        report_error(string("The expected type does not match the ")
		            +string("ascribed type in an ascription.\n")
		            +string("1. The expected type: ")+expected->toString()
		            +string("\n2. The ascribed type: ")+tp->toString());

	      // no need to dec tp, since it was consumed by the call to check
	      expected->dec();
	      if (create)
	        return trm;
	      trm->dec();
	      return 0;
      }
      else {
	      *computed = tp;
	      if (create)
	        return trm;
	      return 0;
      }
    }
    case '@': { // the local definition case
      string id(prefix_id());
#ifdef DEBUG_SYM_NAMES
      SymExpr *sym = new SymSExpr(id, SYMS_EXPR);
#else
      SymExpr *sym = new SymExpr(id);
#endif
      int prev_open = open_parens;
      Expr *tp_of_trm = NULL;
      Expr *trm = check(true, NULL, &tp_of_trm);
      eat_excess(prev_open);

      sym->val = trm;

#ifdef USE_HASH_MAPS
      Expr *prev = symbols[id];
      Expr *prevtp = symbol_types[id];
      symbols[id] = sym;
      symbol_types[id] = tp_of_trm;
#else
      pair<Expr *, Expr *> prevpr =
	symbols->insert(id.c_str(), pair<Expr *, Expr *>(sym,tp_of_trm));
      Expr *prev = prevpr.first;
      Expr *prevtp = prevpr.second;
#endif

      if (tail_calls && big_check && return_pos && !create) {
	      if (prev)
	        prev->dec();
	      if (prevtp)
	        prevtp->dec();
	      // all parameters to check() unchanged here
	      goto start_check;
      }
      else {
	      int prev_open = open_parens;
	      Expr *body = check(create, expected, computed, is_hole, return_pos);
	      eat_excess(prev_open);
	      eat_rparen();

#ifdef USE_HASH_MAPS
	      symbols[id] = prev;
	      symbol_types[id] = prevtp;
#else
	      symbols->insert(id.c_str(), prevpr);
#endif
	      tp_of_trm->dec(); // because removed from the symbol table now

	      sym->dec();
	      return body;
      }
    }
    case '~': {
      int prev = open_parens;
      Expr *e = check(create, expected, computed, is_hole, return_pos);
      eat_excess(prev);
      eat_rparen();

      // this has been only very lightly tested -- ads.

      if (expected) {
	      if (expected != statMpz && expected != statMpq)
	        report_error("Negative sign where an numeric expression is expected.");
      }
      else {
	      if ((*computed) != statMpz && (*computed) != statMpq)
	        report_error("Negative sign where an numeric expression is expected.");
      }

      if (create) {
	      if (e->getclass() == INT_EXPR)
        {
	        IntExpr *ee = (IntExpr *)e;
	        mpz_neg(ee->n, ee->n);
	        return ee;
        }
        else if( e->getclass() == RAT_EXPR )
        {
	        RatExpr *ee = (RatExpr *)e;
	        mpq_neg(ee->n, ee->n);
	        return ee;
        }
        else
        {
          report_error("Negative sign with expr that is not an int. literal.");
        }
      }
      else
	      return 0;
    }
    default: { // the application case
      our_ungetc(c);
      Expr *head_computed;
      int prev = open_parens;
      Expr *headtrm = check(create,0,&head_computed);
      eat_excess(prev);

      CExpr *headtp = (CExpr *)head_computed->followDefs();
      headtp->inc();
      head_computed->dec();
      if ( headtp->cloned()) {
	      // we must clone
	      Expr *orig_headtp = headtp;
	      headtp = (CExpr *)headtp->clone();
	      orig_headtp->dec();
      }
      else
	      headtp->setcloned();
#ifdef DEBUG_APPS
      char tmp[100];
      sprintf(tmp,"(%d) ", app_rec_level++);
      cout << tmp << "{ headtp = ";
      headtp->debug();
#endif
      char c;
      vector<HoleExpr *> holes;
      vector<bool> free_holes;
      while ((c = non_ws()) != ')') {
	our_ungetc(c);
	if (headtp->getop() != PI)
	  report_error(string("The type of an applied term is not ")
		       + string("a pi-type.\n")
		       + string("\n1. the type of the term: ")
		       + headtp->toString()
		       + (headtrm ? (string("\n2. the term: ")
				     + headtrm->toString())
			  : string("")));
	SymExpr *headtp_var = (SymExpr *)headtp->kids[0];
	Expr *headtp_domain = headtp->kids[1];
	Expr *headtp_range = headtp->kids[2];
	if (headtp_domain->getop() == RUN) {
	  CExpr *run = (CExpr *)headtp_domain;
	  Expr *code = run->kids[0];
	  Expr *expected_result = run->kids[1];
	  Expr *computed_result = call_run_code(code);
	  if (!computed_result)
	    report_error(string("A side condition failed.\n")
			 +string("1. the side condition: ")
			 +code->toString());
	  if (!expected_result->defeq(computed_result))
	    report_error(string("The expected result of a side condition ")
			 +string("does not match the computed result.\n")
			 +string("1. expected result: ")
			 +expected_result->toString()
			 +string("\n2. computed result: ")
			   +computed_result->toString());
	  computed_result->dec();
	}
	else {
	  // check an argument
      bool var_in_range = headtp->get_free_in();//headtp_range->free_in(headtp_var);
	  bool arg_is_hole = false;
	  bool consumed_arg = false;

	  bool create_arg = (create || var_in_range);

	  headtp_domain->inc();

	  if (tail_calls && !create_arg && headtp_range->getop() != PI) {
	    // we can make a tail call to check() here.

	    if (expected) {
	      if (!expected->defeq(headtp_range))
		      report_error(string("The type expected for an application ")
			          + string("does not match the computed type.\n")
			          + string("1. The expected type: ")
			          + expected->toString()
			          + string("\n2. The computed type: ")
			          + headtp_range->toString()
			          + (headtrm ? (string("\n3. the application: ")
					        + headtrm->toString())
				    : string("")));
	      expected->dec();
	    }
	    else {
	      headtp_range->inc();
	      *computed = headtp_range;
	    }

	    headtp->dec();

	    // same as below
	    for (int i = 0, iend = holes.size(); i < iend; i++) {
	      if (!holes[i]->val)
		/* if the hole is free in the domain, we will be filling
		   it in when we make our tail call, since the domain
		   is the expected type for the argument */
		if (!headtp_domain->free_in(holes[i]))
		  report_error(string("A hole was left unfilled after ")
			       +string("checking an application.\n"));
	      holes[i]->dec();
	    }

	    create = false;
	    expected = headtp_domain;
	    computed = NULL;
	    is_hole = NULL; // the argument cannot be a hole
	    // return_pos is unchanged

#ifdef DEBUG_APPS
	    cout << "Making tail call.\n";
#endif

	    goto start_check;
	  }

	    Expr *arg = check(create_arg, headtp_domain, NULL, &arg_is_hole);
	    eat_excess(prev);
	    if (create) {
#ifndef USE_FLAT_APP
	      headtrm = new CExpr(APP, headtrm, arg);
#else
        Expr* orig_headtrm = headtrm;
        headtrm = Expr::make_app( headtrm, arg );
        if( orig_headtrm->getclass()==CEXPR ){
          orig_headtrm->dec();
        }
#endif
	      consumed_arg = true;
	    }
	    if (var_in_range) {
	      Expr *tmp = arg->followDefs();
	      tmp->inc();
	      headtp_var->val = tmp;
	    }
	    if (arg_is_hole) {
	      if (consumed_arg)
	        arg->inc();
	      else
	        consumed_arg = true; // not used currently
#ifdef DEBUG_HOLES
	        cout << "An argument is a hole: ";
	        arg->debug();
#endif
	          holes.push_back((HoleExpr *)arg);
	        }
	      }
	      headtp_range->inc();
	      headtp->dec();
	      headtp = (CExpr *)headtp_range;
      }
      open_parens--;

      // check for remaining RUN in the head's type after all the arguments

      if (headtp->getop() == PI && headtp->kids[1]->getop() == RUN) {
	      CExpr *run = (CExpr *)headtp->kids[1];
	      Expr *code = run->kids[0]->followDefs();
	      Expr *expected_result = run->kids[1];
	      Expr *computed_result = call_run_code(code);
	      if (!computed_result)
	        report_error(string("A side condition failed.\n")
		            +string("1. the side condition: ")+code->toString());
	      if (!expected_result->defeq(computed_result))
	        report_error(string("The expected result of a side condition ")
		            +string("does not match the computed result.\n")
		            +string("1. expected result: ")
		            +expected_result->toString()
		            +string("\n2. computed result: ")
		            +computed_result->toString());
	      Expr *tmp = headtp->kids[2];
	      tmp->inc();
	      headtp->dec();
	      headtp = (CExpr *)tmp;
	      computed_result->dec();
      }

#ifdef DEBUG_APPS
      for (int i = 0, iend = holes.size(); i < iend; i++) {
	      cout << tmp << "hole ";
	      holes[i]->debug();
      }
      cout << "}";
      app_rec_level--;
#endif

      Expr *ret = 0;
      if (expected) {
        if (!expected->defeq(headtp)){
	        report_error(string("The type expected for an application does not")
		            + string(" match the computed type.(2) \n")
		            + string("1. The expected type: ")
		            + expected->toString()
		            + string("\n2. The computed type: ")
		            + headtp->toString()
		            + (headtrm ? (string("\n3. the application: ")
				          + headtrm->toString())
			        : string("")));

        }
	      expected->dec();
	      headtp->dec();
	      if (create)
	        ret = headtrm;
      }
      else {
	      *computed = headtp;
	      if (create)
	        ret = headtrm;
      }

      /* do this check here to give the defeq() call above a
	 chance to fill in some holes */
      for (int i = 0, iend = holes.size(); i < iend; i++) {
        if (!holes[i]->val){
          if( inAsc ){
#ifdef DEBUG_HOLES
            std::cout << "Ascription Hole: ";
            holes[i]->print( std::cout );
            std::cout << std::endl;
#endif
            ascHoles.push_back( holes[i] );
          }else{
	          report_error(string("A hole was left unfilled after checking")
		              +string(" an application (2).\n"));
          }
        }
	      holes[i]->dec();
      }

      return ret;

    } // end application case
  }
  }
  case EOF:
    report_error("Unexpected end of file.");
    break;

  case '_':
    if (!is_hole)
      report_error("A hole is being used in a disallowed position.");
    *is_hole = true;
    if (expected)
      expected->dec();
    return new HoleExpr();
  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9': {
    our_ungetc(d);
    string v;
    char c;
    while (isdigit(c = our_getc()))
      v.push_back(c);
    bool parseMpq = false;
    string v2;
    if( c=='/' )
    {
      parseMpq = true;
      v.push_back( c );
      while(isdigit(c = our_getc()))
        v.push_back(c);
    }
    our_ungetc(c);


    Expr *i = 0;
    if (create) {
      if( parseMpq )
      {
        mpq_t num;
        mpq_init(num);
        if (mpq_set_str(num,v.c_str(),10) == -1)
	        report_error("Error reading a numeral.");
        i = new RatExpr(num);
      }
      else
      {
        mpz_t num;
        if (mpz_init_set_str(num,v.c_str(),10) == -1)
	        report_error("Error reading a numeral.");
        i = new IntExpr(num);
      }
    }

    if (expected) {
      if( ( !parseMpq && expected != statMpz ) || ( parseMpq && expected != statMpq ) )
	      report_error(string("We parsed a numeric literal, but were ")
		          +string("expecting a term of a different type.\n")
		          +string("1. the expected type: ")+expected->toString());
      expected->dec();
      if (create)
	      return i;
      return 0;
    }
    else {
      if( parseMpq )
      {
        statMpq->inc();
        *computed = statMpq;
        if (create)
	        return i;
        return statMpq;
      }
      else
      {
        statMpz->inc();
        *computed = statMpz;
        if (create)
	        return i;
        return statMpz;
      }
    }
  }
  default: {
    our_ungetc(d);
    string id(prefix_id());
#ifdef USE_HASH_MAPS
    Expr *ret = symbols[id];
    Expr *rettp = symbol_types[id];
#else
    pair<Expr *, Expr *> p = symbols->get(id.c_str());
    Expr *ret = p.first;
    Expr *rettp = p.second;
#endif
    if (!ret)
      report_error(string("Undeclared identifier: ")+id);
    if (expected) {
      if (!expected->defeq(rettp))
	report_error(string("The type expected for a symbol does not")
		     + string(" match the symbol's type.\n")
		     + string("1. The symbol: ")
		     + id
		     + string("\n2. The expected type: ")
		     + expected->toString()
		     + string("\n3. The symbol's type: ")
		     + rettp->toString());
      expected->dec();
      if (create) {
	      ret->inc();
	      return ret;
      }
      return 0;
    }
    else {
      if( computed ){
        *computed = rettp;
        (*computed)->inc();
      }
      if (create) {
	      ret->inc();
	      return ret;
      }
      return 0;
    }
  }
  }

  report_error("Unexpected operator at the start of a term.");
  return 0;
}

#ifdef USE_HASH_MAPS
void discard_old_symbol(const string &id) {
  Expr *tmp = symbols[id];
  if (tmp)
    tmp->dec();
  tmp = symbol_types[id];
  if (tmp)
    tmp->dec();
}
#endif

int check_time;

void check_file(const char *_filename, args a, sccwriter* scw, libwriter* lw) {
  int prev_linenum = linenum;
  int prev_colnum = colnum;
  const char *prev_filename = filename;
  FILE * prev_curfile = curfile;

  // from code.h
  dbg_prog = a.show_runs;
  run_scc = a.run_scc;
  tail_calls = !a.no_tail_calls;

  std::string f;
  if (strcmp(_filename,"stdin") == 0) {
    curfile = stdin;
    f = std::string(_filename);
  }
  else {
    if (prev_curfile) {
      f = std::string(prev_filename);
#ifdef _MSC_VER
	    std::string str( f );
	    for( int n=str.length(); n>=0; n-- ){
		    if( str[n]=='\\' || str[n]=='/' ){
          str = str.erase( n, str.length()-n );
          break;
		    }
	    }
	    char *tmp = (char*)str.c_str();
#else
      // Note: dirname may modify its argument, so we create a non-const copy.
      char *f_copy = strdup(f.c_str());
      std::string str = std::string(dirname(f_copy));
      free(f_copy);
#endif
            f = str + std::string("/") + std::string(_filename);
    } else {
      f = std::string(_filename);
    }
    curfile = fopen(f.c_str(), "r");
    if (!curfile)
      report_error(string("Could not open file \"") + f +
                   string("\" for reading.\n"));
  }

  linenum = 1;
  colnum = 1;
  filename = f.c_str();

  char c;
  while ((c = non_ws()) && c!=EOF ) {
    if( c == '(' )
    {
      char d;
      switch ((d = non_ws())) {
      case 'd':
        char b;
        if ((b = our_getc()) != 'e')
	        report_error(string("Unexpected start of command."));

        switch ((b = our_getc())) {
          case 'f': {// expecting "define"

	          if (our_getc() != 'i' || our_getc() != 'n' || our_getc() != 'e')
	            report_error(string("Unexpected start of command."));

	          string id(prefix_id());
	          Expr *ttp;
	          int prevo = open_parens;
	          Expr *t = check(true, 0, &ttp, NULL, true);
	          eat_excess(prevo);

	          int o = ttp->followDefs()->getop();
	          if (o == KIND)
	            report_error(string("Kind-level definitions are not supported.\n"));
	          SymSExpr *s = new SymSExpr(id);
	          s->val = t;
#ifdef USE_HASH_MAPS
	          discard_old_symbol(id);
	          symbols[id] = s;
	          symbol_types[id] = ttp;
#else
	          pair<Expr *, Expr *> prev =
	            symbols->insert(id.c_str(), pair<Expr *, Expr *>(s,ttp));
	          if (prev.first)
	            prev.first->dec();
	          if (prev.second)
	            prev.second->dec();
#endif
	        break;
          }
          case 'c': {// expecting "declare"
	          if (our_getc() != 'l' || our_getc() != 'a' || our_getc() != 'r'
	              || our_getc() != 'e')
	            report_error(string("Unexpected start of command."));

	          string id(prefix_id());
	          Expr *ttp;
	          int prevo = open_parens;
	          Expr *t = check(true, 0, &ttp, NULL, true);
	          eat_excess(prevo);

	          ttp = ttp->followDefs();
	          if (ttp->getop() != TYPE && ttp->getop() != KIND)
	            report_error(string("The expression declared for \"")
		                +id+string("\" is neither\na type nor a kind.\n")
		                +string("1. The expression: ")
		                +t->toString()
		                +string("\n2. Its classifier (should be \"type\" ")
		                +string("or \"kind\"): ")+ttp->toString());
	          ttp->dec();
	          SymSExpr *s = new SymSExpr(id);
#ifdef USE_HASH_MAPS
	          discard_old_symbol(id);
	          symbols[id] = s;
	          symbol_types[id] = t;
#else
	          pair<Expr *, Expr *> prev =
	            symbols->insert(id.c_str(), pair<Expr *, Expr *>(s,t));
            if( lw )
              lw->add_symbol( s, t );
	          if (prev.first)
	            prev.first->dec();
	          if (prev.second)
	            prev.second->dec();
#endif
	          break;
            }
            default:
	            report_error(string("Unexpected start of command."));
            } // switch((b = our_getc())) following "de"
         break;
    case 'c': {
      if (our_getc() != 'h' || our_getc() != 'e' || our_getc() != 'c' || our_getc() != 'k')
	      report_error(string("Unexpected start of command."));
      if( run_scc ){
        init_compiled_scc();
      }
      Expr *computed;
      big_check = true;
      int prev = open_parens;
      (void)check(false, 0, &computed, NULL, true);

      //print out ascription holes
      for( int a=0; a<(int)ascHoles.size(); a++ ){
#ifdef PRINT_SMT2
        print_smt2( ascHoles[a], std::cout );
#else
        ascHoles[a]->print( std::cout );
#endif
        std::cout << std::endl;
      }
      if( !ascHoles.empty() )
        std::cout << std::endl;
      ascHoles.clear();

      //clean up local symbols
      for( int a=0; a<(int)local_sym_names.size(); a++ ){
#ifdef USE_HASH_MAPS
#else
        symbols->insert( local_sym_names[a].first.c_str(), local_sym_names[a].second );
#endif
      }
      local_sym_names.clear();
      mark_map.clear();

      eat_excess(prev);

      computed->dec();
      //cleanup();
      //exit(0);
      break;
    }
    case 'o': { // opaque case
      if (our_getc() != 'p' || our_getc() != 'a' || our_getc() != 'q'
	        || our_getc() != 'u' || our_getc() != 'e')
	      report_error(string("Unexpected start of command."));

      string id(prefix_id());
      Expr *ttp;
      int prevo = open_parens;
      (void)check(false, 0, &ttp, NULL, true);
      eat_excess(prevo);

      int o = ttp->followDefs()->getop();
      if (o == KIND)
	      report_error(string("Kind-level definitions are not supported.\n"));
      SymSExpr *s = new SymSExpr(id);
#ifdef USE_HASH_MAPS
	    discard_old_symbol(id);
	    symbols[id] = s;
	    symbol_types[id] = ttp;
#else
	    pair<Expr *, Expr *> prev =
	      symbols->insert(id.c_str(), pair<Expr *, Expr *>(s,ttp));
	    if (prev.first)
	      prev.first->dec();
	    if (prev.second)
	      prev.second->dec();
#endif
        break;
      }
      case 'r': { // run case
        if (our_getc() != 'u' || our_getc() != 'n')
	        report_error(string("Unexpected start of command."));
        Expr *code = read_code();
        check_code(code);
        cout << "[Running-sc ";
        code->print(cout);
        Expr *tmp = run_code(code);
        cout << "] = \n";
        if (tmp) {
	        tmp->print(cout);
	        tmp->dec();
        }
        else
	        cout << "fail";
        cout << "\n";
        code->dec();
        break;
      }
      case 'p': { // program case
        if (our_getc() != 'r' || our_getc() != 'o' || our_getc() != 'g'
	         || our_getc() != 'r' || our_getc() != 'a' || our_getc() != 'm')
	        report_error(string("Unexpected start of command."));

        string progstr(prefix_id());
        SymSExpr *prog = new SymSExpr(progstr);
        if (progs.find(progstr) != progs.end())
	        report_error(string("Redeclaring program ")+progstr+string("."));
        progs[progstr] = prog;
        eat_char('(');
        char d;
        vector<Expr *> vars;
        vector<Expr *> tps;
        Expr *tmp;
        while ((d = non_ws()) != ')') {
	        our_ungetc(d);
	        eat_char('(');
	        string varstr = prefix_id();
#ifdef USE_HASH_MAPS
	        if (symbols.find(varstr) != symbols.end())
#else
          if (symbols->get(varstr.c_str()).first != NULL)
#endif
	          report_error(string("A program variable is already declared")
		              +string(" (as a constant).\n1. The variable: ")
		              +varstr);
	        Expr *var = new SymSExpr(varstr);
	        vars.push_back(var);
	        statType->inc();
	        int prev = open_parens;
	        Expr *tp = check(true, NULL, &tmp, 0, true);
          if( tp->getclass()==SYMS_EXPR ){
#ifdef USE_HASH_MAPS
            Expr *tptp = symbol_types[((SymSExpr*)tp)->s];
#else
            pair<Expr *, Expr *> p = symbols->get(((SymSExpr*)tp)->s.c_str());
            Expr *tptp = p.second;
#endif
            if( !tptp->isType( statType ) ){
              report_error(string("Bad argument for side condition"));
            }
          }else{
            if (!tp->isDatatype()){
	            report_error(string("Type for a program variable is not a ")
		                +string("datatype.\n1. the type: ")+tp->toString());
            }
          }
	        eat_excess(prev);

	        tps.push_back(tp);
	        eat_char(')');

#ifdef USE_HASH_MAPS
	        symbols[varstr] = var;
	        symbol_types[varstr] = tp;
#else
	        symbols->insert(varstr.c_str(), pair<Expr *, Expr *>(var,tp));
#endif
        }

        if (!vars.size())
	        report_error("A program lacks input variables.");

        statType->inc();
        int prev = open_parens;
        Expr *progtp = check(true,statType,&tmp,0, true);
        eat_excess(prev);

        if (!progtp->isDatatype())
	        report_error(string("Return type for a program is not a")
		            +string(" datatype.\n1. the type: ")+progtp->toString());

        Expr *progcode = read_code();

        for (int i = vars.size() - 1, iend = 0; i >= iend; i--) {
	        vars[i]->inc(); // used below for the program code (progcode)
	        progtp = new CExpr(PI, vars[i], tps[i], progtp);
          progtp->calc_free_in();
        }

        // just put the type here for type checking.  Make sure progtp is kid 0.
        prog->val = new CExpr(PROG, progtp);

        check_code(progcode);

        progcode = new CExpr(PROG, progtp, new CExpr(PROGVARS, vars), progcode);
        //if compiling side condition code, give this code to the side condition code writer
        if( a.compile_scc ){
          if( scw ){
            scw->add_scc( progstr, (CExpr*)progcode );
          }
        }

	// remove the variables from the symbol table.
        for (int i = 0, iend = vars.size(); i < iend; i++) {
	        string &s = ((SymSExpr *)vars[i])->s;

#ifdef USE_HASH_MAPS
	        symbols[s] = NULL;
	        symbol_types[s] = NULL;
#else
	        symbols->insert(s.c_str(), pair<Expr*,Expr*>(NULL,NULL));
#endif
        }

        progtp->inc();
        prog->val->dec();

        prog->val = progcode;

        break;
      }

      default:
	      report_error(string("Unexpected start of command."));
      } // switch((d = non_ws())

      eat_char(')');
    } // while
    else
    {
      if( c != ')' )
      {
        char c2[2];
        c2[1] = 0;
        c2[0] = c;
        string syn = string("Bad syntax (mismatched parentheses?): ");
        syn.append(string(c2));
        report_error(syn);
      }
    }
  }
  if (curfile != stdin)
    fclose(curfile);
  linenum = prev_linenum;
  colnum = prev_colnum;
  filename = prev_filename;
  curfile = prev_curfile;

}

class Deref : public Trie<pair<Expr *, Expr *> >::Cleaner {
public:
  ~Deref() {}
  void clean(pair<Expr *, Expr *> p) {
    Expr *tmp = p.first;
    if (tmp) {
#ifdef DEBUG
      cout << "Cleaning up ";
      tmp->debug();
#endif
      tmp->dec();
    }
    tmp = p.second;
    if (tmp) {
#ifdef DEBUG
      cout << " : ";
      tmp->debug();
#endif
      tmp->dec();
    }
#ifdef DEBUG
      cout << "\n";
#endif
  }
};

template <>
Trie<pair<Expr *, Expr *> >::Cleaner *
Trie<pair<Expr *, Expr *> >::cleaner = new Deref;

void cleanup() {
  symmap::iterator i, iend;
#ifdef USE_HASH_MAPS
  Expr *tmp;
  for (i = symbols.begin(), iend = symbols.end(); i != iend; i++) {
    tmp = i->second;
    if (tmp) {
#ifdef DEBUG
      cout << "Cleaning up " << i->first << " : ";
      tmp->debug();
#endif
      tmp->dec();
    }
  }
  for (i = symbol_types.begin(), iend = symbol_types.end(); i != iend; i++) {
    tmp = i->second;
    if (tmp) {
#ifdef DEBUG
      cout << "Cleaning up " << i->first << " : ";
      tmp->debug();
#endif
      tmp->dec();
    }
  }
#else
  delete symbols;
#endif

  // clean up programs

  symmap2::iterator j, jend;
  for (j = progs.begin(), jend = progs.end(); j != jend; j++) {
    SymExpr *p = j->second;
    if (p) {
      Expr *progcode = p->val;
      p->val = NULL;
      progcode->dec();
      p->dec();
    }
  }
}

void init() {
#ifdef USE_HASH_MAPS
  string tp("type");
  symbols[tp] = statType;
  symbol_types[tp] = statKind;
  string mpz("mpz");
  symbols[mpz] = statMpz;
  symbol_types[mpz] = statType;
  statType->inc();
  sym
#else
  symbols->insert("type", pair<Expr *, Expr *>(statType, statKind));
  statType->inc();
  symbols->insert("mpz", pair<Expr *, Expr *>(statMpz, statType));
  symbols->insert("mpq", pair<Expr *, Expr *>(statMpq, statType));
#endif
}
