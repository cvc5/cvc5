#include "check.h"
#include "code.h"
#include <string>

#include "scccode.h"

using namespace std;

string *eat_str(const char *str, bool check_end = true) {
  string *s = new string();
  char c, d;
  while ((c = *str++)) {
    d = our_getc();
    if (c != d) {
      our_ungetc(d);
      return s;
    }
    s->push_back(d);
  }

  if (check_end &&
      (d = our_getc()) != ' ' && d != '(' && d != '\n' && d != '\t') {
    our_ungetc(d);
    return s;
  }

  delete s;
  return 0;
}

SymSExpr *read_ctor() {
  string id(prefix_id());
#ifdef USE_HASH_TABLES
  Expr *s = symbols[id];
  Expr *stp = symbol_types[id];
#else
  pair<Expr *, Expr *> p = symbols->get(id.c_str());
  Expr *s = p.first;
  Expr *stp = p.second;
#endif

  if (!stp)
    report_error("Undeclared identifier parsing a pattern.");

  if (s->getclass() != SYMS_EXPR || ((SymExpr *)s)->val)
    report_error("The head of a pattern is not a constructor.");

  s->inc();

  return (SymSExpr *)s;
}

Expr *read_case() {
  eat_char('(');
  Expr *pat = NULL;
  vector<SymSExpr *> vars;

#ifdef USE_HASH_MAPS
  vector<Expr *>prevs;
#else
  vector<pair<Expr *,Expr *> >prevs;
#endif
  char d = non_ws();
  switch(d) {
  case '(': {
    // parse application
    SymSExpr *s = read_ctor();
    pat = s;
    char c;
    while ((c = non_ws()) != ')') {
	    our_ungetc(c);
	    string varstr(prefix_id());
	    SymSExpr *var = new SymSExpr(varstr);
	    vars.push_back(var);
#ifdef USE_HASH_MAPS
	    prevs.push_back(symbols[varstr]);
	    symbols[varstr] = var;
#else
	    prevs.push_back(symbols->insert(varstr.c_str(),
					    pair<Expr *, Expr *>(var,NULL)));
#endif
#ifndef USE_FLAT_APP
	    pat = new CExpr(APP,pat,var);
#else
      Expr* orig_pat = pat;
      pat = Expr::make_app(pat,var);
      if( orig_pat->getclass()==CEXPR ){
        orig_pat->dec();
      }
#endif
    }
    break;
  }
  // default case
  case 'd': {
    delete eat_str("efault");
  }
    break;
  case EOF:
    report_error("Unexpected end of file parsing a pattern.");
    break;
  default:
    // could be an identifier
    our_ungetc(d);
    pat = read_ctor();
    break;
  }

  Expr *ret = read_code();
  if( pat )
    ret = new CExpr(CASE, pat, ret);

  for (int i = 0, iend = prevs.size(); i < iend; i++) {
    string &s = vars[i]->s;
#ifdef USE_HASH_MAPS
    symbols[s] = prevs[i];
#else
    symbols->insert(s.c_str(), prevs[i]);
#endif
  }

  eat_char(')');

  return ret;
}

Expr *read_code() {
  string *pref = NULL;
  char d = non_ws();
  switch(d) {
    case '(':
    {
      char c = non_ws();
      switch (c)
      {
        case 'd':
        {
          our_ungetc('d');
          pref = eat_str("do");
          if (pref)
	          break;
          Expr *ret = read_code();
          while ((c = non_ws()) != ')') {
	          our_ungetc(c);
	          ret = new CExpr(DO,ret,read_code());
          }
          return ret;
        }
        case 'f':
        {
          our_ungetc('f');
          pref = eat_str("fail");
          if (pref)
	          break;

          Expr *c = read_code();
          eat_char(')');

          //do we need to check this???
          //if (c->getclass() != SYMS_EXPR || ((SymExpr *)c)->val)
	         // report_error(string("\"fail\" must be used with a (undefined) base ")
		        //  +string("type.\n1. the expression used: "+c->toString()));

          return new CExpr(FAIL, c);
        }
        case 'l':
        {
          our_ungetc('l');
          pref = eat_str("let");
          if (pref)
	          break;

          string id(prefix_id());
          SymSExpr *var = new SymSExpr(id);

          Expr *t1 = read_code();

#ifdef USE_HASH_MAPS
          Expr *prev = symbols[id];
          symbols[id] = var;
#else
          pair<Expr *, Expr *> prev =
	          symbols->insert(id.c_str(), pair<Expr *, Expr *>(var,NULL));
#endif

          Expr *t2 = read_code();

#ifdef USE_HASH_MAPS
          symbols[id] = prev;
#else
          symbols->insert(id.c_str(), prev);
#endif
          eat_char(')');
          return new CExpr(LET, var, t1, t2);
        }
        case 'i':
        {
          our_ungetc('i');
          pref = eat_str("ifmarked",false);
          if (pref)
	          break;
#ifndef MARKVAR_32
          Expr *e1 = read_code();
          Expr *e2 = read_code();
          Expr *e3 = read_code();
          Expr *ret = new CExpr(IFMARKED, e1, e2, e3);
#else
          int index = read_index();
          Expr *e1 = read_code();
          Expr *e2 = read_code();
          Expr *e3 = read_code();
          Expr *ret = NULL;
          if( index>=1 && index<=32 )
          {
            ret = new CExpr( IFMARKED, new IntExpr( index-1 ), e1, e2, e3 );
          }
          else
          {
            std::cout << "Can't make IFMARKED with index = " << index << std::endl;
          }
          Expr::markedCount++;
          //Expr *ret = new CExpr(IFMARKED, e1, e2, e3);
#endif
          eat_char(')');
          return ret;
        }
        case 'm':
        {
          char c;
          switch ((c = our_getc()))
          {
            case 'a':
            {
	            char cc;
	            switch ((cc = our_getc())) {
	              case 't':
                {
	                our_ungetc('t');
	                pref = eat_str("tch");
	                if (pref) {
	                  pref->insert(0,"ma");
	                  break;
	                }
	                vector<Expr *> cases;
	                cases.push_back(read_code()); // the scrutinee
	                while ((c = non_ws()) != ')' && c != 'd') {
	                  our_ungetc(c);
	                  cases.push_back(read_case());
	                }
	                if (cases.size() == 1) // counting scrutinee
	                  report_error("A match has no cases.");
                  if (c == 'd') {
                    // we have a default case
                    //delete eat_str("efault");
                    our_ungetc(c);
                    cases.push_back(read_case());
                  }
	                return new CExpr(MATCH,cases);
                }
	              case 'r':
                {
	                our_ungetc('r');
	                pref = eat_str("rkvar", false);
	                if (pref) {
	                  pref->insert(0,"ma");
	                  break;
	                }
    #ifndef MARKVAR_32
	                Expr *ret = new CExpr(MARKVAR,read_code());
    #else
                  int index = read_index();
                  CExpr* ret = NULL;
                  if( index>=1 && index<=32 )
                  {
                    ret = new CExpr( MARKVAR, new IntExpr( index-1 ), read_code() );
                  }
                  else
                  {
                    std::cout << "Can't make MARKVAR with index = " << index << std::endl;
                  }
          Expr::markedCount++;
	                //Expr *ret = new CExpr(MARKVAR,read_code());
              #endif

	                eat_char(')');
	                return ret;
                }
	              default:
                  our_ungetc(c);
	                pref = new string("ma");
	                break;
              }
            }
            case 'p':
            {
	            our_ungetc('p');
	            pref = eat_str("p_",false);
	            if (pref) {
	              pref->insert(0,"m");
	              break;
              }
	            char c = our_getc();
	            switch(c) {
	            case 'a':
              {
	              our_ungetc('a');
	              pref = eat_str("add");
	              if (pref) {
	                pref->insert(0,"mp_");
	                break;
	              }
                Expr* e1 = read_code();
                Expr* e2 = read_code();
	              Expr *ret = new CExpr(ADD, e1, e2);
	              eat_char(')');
	              return ret;
	            }
	            case 'n':
              {
	              our_ungetc('n');
	              pref = eat_str("neg");
	              if (pref) {
	                pref->insert(0,"mp_");
	                break;
	              }

	              Expr *ret = new CExpr(NEG, read_code());
	              eat_char(')');
	              return ret;
	            }
	            case 'i':
              {	// mpz_if_neg
                char c = our_getc();
                if( c=='f' )
                {
                  c = our_getc();
                  switch( c )
                  {
                  case 'n': {
                    our_ungetc('n');
		                pref = eat_str("neg");
		                if( pref ) {
			                pref->insert(0,"mp_if");
			                break;
		                }
		                Expr* e1 = read_code();
                    Expr* e2 = read_code();
                    Expr* e3 = read_code();
		                Expr*	ret = new CExpr(IFNEG, e1, e2, e3 );
		                eat_char(')');
                    return ret;
                  }
                  case 'z': {
                    our_ungetc('z');
		                pref = eat_str("zero");
		                if( pref ) {
			                pref->insert(0,"mp_if");
			                break;
		                }
		                Expr* e1 = read_code();
                    Expr* e2 = read_code();
                    Expr* e3 = read_code();
		                Expr*	ret = new CExpr(IFZERO, e1, e2, e3 );
		                eat_char(')');
                    return ret;
                  }
                  default:
                    our_ungetc(c);
                    pref = new string("mp_if");
                    break;
                  }
                }
                else
                {
                  our_ungetc(c);
                  pref = new string("mp_i");
                  break;
                }
              }
              case 'm':
              {
                our_ungetc('m');
                pref = eat_str("mul");
                if( pref ){
                  pref->insert(0,"mp_");
                  break;
                }
		            Expr* e1 = read_code();
                Expr* e2 = read_code();
		            Expr*	ret = new CExpr(MUL, e1, e2 );
		            eat_char(')');
		            return ret;
              }
              case 'd':
              {
                our_ungetc('d');
                pref = eat_str("div");
                if( pref ){
                  pref->insert(0,"mp_");
                  break;
                }
		            Expr* e1 = read_code();
                Expr* e2 = read_code();
		            Expr*	ret = new CExpr(DIV, e1, e2 );
		            eat_char(')');
		            return ret;
              }
	            default:
                our_ungetc(c);
	              pref = new string("mp_");
	              break;
	            }
            }
            default:
              our_ungetc(c);
	            pref = new string("m");
	            break;
            }
            break;
        }
        case '~': {
          Expr *e = read_code();
          if( e->getclass()==INT_EXPR )
          {
            IntExpr *ee = (IntExpr *)e;
            mpz_neg(ee->n, ee->n);
            eat_char(')');
            return ee;
          }
          else if( e->getclass() == RAT_EXPR )
          {
            RatExpr *ee = (RatExpr *)e;
            mpq_neg(ee->n, ee->n);
            eat_char(')');
            return ee;
          }
          else
          {
            report_error("Negative sign with expr that is not an int. literal.");
          }
        }
        case 'c':
        {
          our_ungetc('c');
          pref = eat_str("compare");
          if (pref)
	          break;
          Expr *e1 = read_code();
          Expr *e2 = read_code();
          Expr *e3 = read_code();
          Expr *e4 = read_code();
          eat_char(')');
          return new CExpr(COMPARE, e1, e2, e3, e4);
        }
          break;
        case EOF:
          report_error("Unexpected end of file.");
          break;
        default:
        { // the application case
          our_ungetc(c);
          break;
        }
      }
      // parse application
      if (pref)
        // we have eaten part of the name of an applied identifier
        pref->append(prefix_id());
      else
        pref = new string(prefix_id());

      Expr *ret = progs[*pref];
      if (!ret)
#ifdef USE_HASH_TABLES
        ret = symbols[*pref];
#else
        ret = symbols->get(pref->c_str()).first;
#endif

      if (!ret)
        report_error(string("Undeclared identifier at head of an application: ")
		    +*pref);

      ret->inc();
      delete pref;

      while ((c = non_ws()) != ')') {
        our_ungetc(c);
#ifndef USE_FLAT_APP
        ret = new CExpr(APP,ret,read_code());
#else
        Expr* ke = read_code();
        Expr* orig_ret = ret;
        ret = Expr::make_app(ret,ke);
        if( orig_ret->getclass()==CEXPR ){
          orig_ret->dec();
        }
#endif
        }
      return ret;
    } // end case '('
    case EOF:
      report_error("Unexpected end of file.");
      break;
    case '_':
      report_error("Holes may not be used in code.");
      return NULL;
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
    {
      our_ungetc(d);
      string v;
      char c;
      while (isdigit(c = our_getc()))
        v.push_back(c);
      bool parseMpq = false;
      if( c=='/' )
      {
        parseMpq = true;
        v.push_back(c);
        while(isdigit(c = our_getc()))
          v.push_back(c);
      }
      our_ungetc(c);
      if( parseMpq )
      {
        mpq_t num;
        mpq_init(num);
        if (mpq_set_str(num,v.c_str(),10) == -1  )
	        report_error("Error reading a mpq numeral.");

        Expr* e = new RatExpr( num );
        return e;
      }
      else
      {
        mpz_t num;
        if (mpz_init_set_str(num,v.c_str(),10) == -1)
          report_error("Error reading a numeral.");
        return new IntExpr(num);
      }
    }
    default:
    {
      our_ungetc(d);
      string id(prefix_id());
#ifdef USE_HASH_MAPS
      Expr *ret = symbols[id];
#else
      pair<Expr *, Expr *> p = symbols->get(id.c_str());
      Expr *ret = p.first;
#endif
      if (!ret)
        ret = progs[id];
      if (!ret)
        report_error(string("Undeclared identifier: ")+id);
      ret->inc();
      return ret;
    }
  }
  report_error("Unexpected operator in a piece of code.");
  return 0;
}

// the input is owned by the caller, the output by us (so do not dec it).
Expr *check_code(Expr *_e) {
  CExpr *e = (CExpr *)_e;
  switch (e->getop()) {
  case NOT_CEXPR:
    switch (e->getclass()) {
    case INT_EXPR:
      return statMpz;
    case RAT_EXPR:
      return statMpq;
    case SYM_EXPR: {
      report_error("Internal error: an LF variable is encountered in code");
      break;
    }
    case SYMS_EXPR: {
#ifdef USE_HASH_MAPS
      Expr *tp = symbol_types[((SymSExpr *)e)->s];
#else
      Expr *tp = symbols->get(((SymSExpr *)e)->s.c_str()).second;
#endif
      if (!tp)
	report_error(string("A symbol is missing a type in a piece of code.")
		     +string("\n1. the symbol: ")+((SymSExpr *)e)->s);
      return tp;
    }
    case HOLE_EXPR:
      report_error("Encountered a hole unexpectedly in code.");
    default:
      report_error("Unrecognized form of expr in code.");
    }
  case APP: {
#ifdef USE_FLAT_APP
    Expr* h = e->kids[0]->followDefs();
    vector<Expr *> argtps;
    int counter = 1;
    while( e->kids[counter] )
    {
       argtps.push_back( check_code( e->kids[counter] ) );
       counter++;
    }
    int iend = counter-1;
#else
    vector<Expr *> args;
    Expr *h = (Expr *)e->collect_args(args);

    int iend = args.size();
    vector<Expr *> argtps(iend);
    for (int i = 0; i < iend; i++)
      argtps[i] = check_code(args[i]);
#endif

    Expr *tp = NULL;
    if (h->getop() == PROG){
      tp = ((CExpr *)h)->kids[0];
    }else {
#ifdef USE_HASH_MAPS
      tp = symbol_types[((SymSExpr *)h)->s];
#else
      tp = symbols->get(((SymSExpr *)h)->s.c_str()).second;
#endif
    }

    if (!tp)
      report_error(string("The head of an application is missing a type in ")
		   +string("code.\n1. the application: ")+e->toString());

    tp = tp->followDefs();

    if (tp->getop() != PI)
      report_error(string("The head of an application does not have ")
		   +string("functional type in code.")
		   +string("\n1. the application: ")+e->toString());

    CExpr *cur = (CExpr *)tp;
    int i = 0;
    while (cur->getop() == PI) {
      if (i >= iend)
	      report_error(string("A function is not being fully applied in code.\n")
		          +string("1. the application: ")+e->toString()
		          +string("\n2. its (functional) type: ")+cur->toString());
      if( argtps[i]->getop()==APP )
        argtps[i] = ((CExpr*)argtps[i])->kids[0];
      if (argtps[i] != cur->kids[1]) {
	      char buf[1024];
	      sprintf(buf,"%d",i);
	      report_error(string("Type mismatch for argument ")
		          + string(buf)
		          + string(" in application in code.\n")
		          + string("1. the application: ")+e->toString()
		          + string("\n2. the head's type: ")+tp->toString()
#ifdef USE_FLAT_APP
                + string("\n3. the argument: ")+e->kids[i+1]->toString()
#else
		          + string("\n3. the argument: ")+args[i]->toString()
#endif
		          + string("\n4. computed type: ")+argtps[i]->toString()
		          + string("\n5. expected type: ")
		          +cur->kids[1]->toString());
      }

      //if (cur->kids[2]->free_in((SymExpr *)cur->kids[0]))
      if( cur->get_free_in() ){
        cur->calc_free_in();
        //are you sure?
        if( cur->get_free_in() )
	        report_error(string("A dependently typed function is being applied in")
		            +string(" code.\n1. the application: ")+e->toString()
		            +string("\n2. the head's type: ")+tp->toString());
        //ok, reset the mark
        cur->setexmark();
      }

      i++;
      cur = (CExpr *)cur->kids[2];
    }
    if (i < iend)
      report_error(string("A function is being fully applied to too many ")
		   +string("arguments in code.\n")
		   +string("1. the application: ")+e->toString()
		   +string("\n2. the head's type: ")+tp->toString());


    return cur;
  }
  //is this right?
  case MPZ:
    return statType;
    break;
  case MPQ:
    return statType;
    break;
  case DO:
    check_code(e->kids[0]);
    return check_code(e->kids[1]);

  case LET: {
    SymSExpr * var = (SymSExpr *)e->kids[0];

    Expr *tp1 = check_code(e->kids[1]);

#ifdef USE_HASH_MAPS
    Expr *prevtp = symbol_types[var->s];
    symbol_types[var->s] = tp1;
#else
    pair<Expr *, Expr *> prev =
      symbols->insert(var->s.c_str(), pair<Expr *, Expr *>(NULL,tp1));
#endif

    Expr *tp2 = check_code(e->kids[2]);

#ifdef USE_HASH_MAPS
    symbol_types[var->s] = prevtp;
#else
    symbols->insert(var->s.c_str(), prev);
#endif

    return tp2;
  }

  case ADD:
  case MUL:
  case DIV:
  {
    Expr *tp0 = check_code(e->kids[0]);
    Expr *tp1 = check_code(e->kids[1]);

    if (tp0 != statMpz && tp0 != statMpq )
      report_error(string("Argument to mp_[arith] does not have type \"mpz\" or \"mpq\".\n")
		   +string("1. the argument: ")+e->kids[0]->toString()
		   +string("\n1. its type: ")+tp0->toString());

    if (tp0 != tp1)
      report_error(string("Arguments to mp_[arith] have differing types.\n")
		   +string("1. argument 1: ")+e->kids[0]->toString()
		   +string("\n1. its type: ")+tp0->toString()
		   +string("2. argument 2: ")+e->kids[1]->toString()
		   +string("\n2. its type: ")+tp1->toString());

    return tp0;
  }

  case NEG: {
    Expr *tp0 = check_code(e->kids[0]);
    if (tp0 != statMpz && tp0 != statMpq )
      report_error(string("Argument to mp_neg does not have type \"mpz\" or \"mpq\".\n")
		   +string("1. the argument: ")+e->kids[0]->toString()
		   +string("\n1. its type: ")+tp0->toString());

    return tp0;
  }

  case IFNEG:
  case IFZERO: {
    Expr *tp0 = check_code(e->kids[0]);
    if (tp0 != statMpz && tp0 != statMpq)
      report_error(string("Argument to mp_if does not have type \"mpz\" or \"mpq\".\n")
		   +string("1. the argument: ")+e->kids[0]->toString()
		   +string("\n1. its type: ")+tp0->toString());

    SymSExpr *tp1 = (SymSExpr *)check_code(e->kids[1]);
    SymSExpr *tp2 = (SymSExpr *)check_code(e->kids[2]);
    if (tp1->getclass() != SYMS_EXPR || tp1->val || tp1 != tp2)
      report_error(string("\"mp_if\" used with expressions that do not ")
       +string("have equal simple datatypes\nfor their types.\n")
       +string("0. 0'th expression: ")+e->kids[0]->toString()
		   +string("\n1. first expression: ")+e->kids[1]->toString()
		   +string("\n2. second expression: ")+e->kids[2]->toString()
		   +string("\n3. first expression's type: ")+tp1->toString()
		   +string("\n4. second expression's type: ")+tp2->toString());
    return tp1;
  }

  case FAIL: {
    Expr *tp = check_code(e->kids[0]);
    if (tp != statType)
      report_error(string("\"fail\" is used with an expression which is ")
		   +string("not a type.\n1. the expression :")
		   +e->kids[0]->toString()
		   +string("\n2. its type: ")+tp->toString());
    return e->kids[0];
  }
  case MARKVAR: {
    SymSExpr *tp = (SymSExpr *)check_code(e->kids[1]);

    Expr* tptp = NULL;

    if (tp->getclass() == SYMS_EXPR && !tp->val){
#ifdef USE_HASH_MAPS
      tptp = symbol_types[tp->s];
#else
      tptp = symbols->get(tp->s.c_str()).second;
#endif
    }

    if (!tptp->isType( statType )){
      string errstr = (string("\"markvar\" is used with an expression which ")
		      +string("cannot be a lambda-bound variable.\n")
		      +string("1. the expression :")
		      +e->kids[1]->toString()
		      +string("\n2. its type: ")+tp->toString());
      report_error(errstr);
    }

    return tp;
  }

  case IFMARKED:
  {
    SymSExpr *tp = (SymSExpr *)check_code(e->kids[1]);

    Expr* tptp = NULL;

    if (tp->getclass() == SYMS_EXPR && !tp->val){
#ifdef USE_HASH_MAPS
      tptp = symbol_types[tp->s];
#else
      tptp = symbols->get(tp->s.c_str()).second;
#endif
    }

    if (!tptp->isType( statType ) ){
      string errstr = (string("\"ifmarked\" is used with an expression which ")
		      +string("cannot be a lambda-bound variable.\n")
		      +string("1. the expression :")
		      +e->kids[1]->toString()
		      +string("\n2. its type: ")+tp->toString());
      report_error(errstr);
    }

    SymSExpr *tp1 = (SymSExpr *)check_code(e->kids[2]);
    SymSExpr *tp2 = (SymSExpr *)check_code(e->kids[3]);
    if (tp1->getclass() != SYMS_EXPR || tp1->val || tp1 != tp2)
      report_error(string("\"ifmarked\" used with expressions that do not ")
       +string("have equal simple datatypes\nfor their types.\n")
       +string("0. 0'th expression: ")+e->kids[1]->toString()
		   +string("\n1. first expression: ")+e->kids[2]->toString()
		   +string("\n2. second expression: ")+e->kids[3]->toString()
		   +string("\n3. first expression's type: ")+tp1->toString()
		   +string("\n4. second expression's type: ")+tp2->toString());
    return tp1;
  }
  case COMPARE:
  {
    SymSExpr *tp0 = (SymSExpr *)check_code(e->kids[0]);
    if (tp0->getclass() != SYMS_EXPR || tp0->val){
      string errstr0 = (string("\"compare\" is used with a first expression which ")
		      +string("cannot be a lambda-bound variable.\n")
		      +string("1. the expression :")
		      +e->kids[0]->toString()
		      +string("\n2. its type: ")+tp0->toString());
      report_error(errstr0);
    }

    SymSExpr *tp1 = (SymSExpr *)check_code(e->kids[1]);

    if (tp1->getclass() != SYMS_EXPR || tp1->val){
      string errstr1 = (string("\"compare\" is used with a second expression which ")
		      +string("cannot be a lambda-bound variable.\n")
		      +string("1. the expression :")
		      +e->kids[1]->toString()
		      +string("\n2. its type: ")+tp1->toString());
      report_error(errstr1);
    }

    SymSExpr *tp2 = (SymSExpr *)check_code(e->kids[2]);
    SymSExpr *tp3 = (SymSExpr *)check_code(e->kids[3]);
    if (tp2->getclass() != SYMS_EXPR || tp2->val || tp2 != tp3)
      report_error(string("\"compare\" used with expressions that do not ")
       +string("have equal simple datatypes\nfor their types.\n")
		   +string("\n1. first expression: ")+e->kids[2]->toString()
		   +string("\n2. second expression: ")+e->kids[3]->toString()
		   +string("\n3. first expression's type: ")+tp2->toString()
		   +string("\n4. second expression's type: ")+tp3->toString());
    return tp2;
  }
  case MATCH:
  {
    SymSExpr *scruttp = (SymSExpr *)check_code(e->kids[0]);
    Expr *tptp = NULL;
    if (scruttp->getclass() == SYMS_EXPR && !scruttp->val){
#ifdef USE_HASH_MAPS
      tptp = symbol_types[scruttp->s];
#else
      tptp = symbols->get(scruttp->s.c_str()).second;
#endif
    }
    if (!tptp->isType( statType )){
      string errstr = (string("The scrutinee of a match is not ")
		      +string("a plain piece of data.\n")
		      +string("1. the scrutinee: ")
		      +e->kids[0]->toString()
		      +string("\n2. its type: ")+scruttp->toString());
      report_error(errstr);
    }

    int i = 1;
    Expr **cur = &e->kids[i];
    Expr *mtp = NULL;
    Expr *c_or_default;
    CExpr *c;
    while ((c_or_default = *cur++)) {
      Expr *tp = NULL;
      CExpr *pat = NULL;
      if (c_or_default->getop() != CASE)
        // this is the default of the MATCH
        tp = check_code(c_or_default);
      else {
        // this is a CASE of the MATCH
        c = (CExpr *)c_or_default;
        pat = (CExpr *)c->kids[0]; // might be just a SYMS_EXPR
        if (pat->getclass() == SYMS_EXPR)
          tp = check_code(c->kids[1]);
        else {
          // extend type context and then check the body of the case
#ifdef USE_HASH_MAPS
          vector<Expr *>prevs;
#else
          vector<pair<Expr *,Expr *> >prevs;
#endif
          vector<Expr *> vars;
          SymSExpr *ctor = (SymSExpr *)pat->collect_args(vars);
#ifdef USE_HASH_MAPS
          CExpr *ctortp = (CExpr *)symbol_types[ctor->s];
#else
          CExpr *ctortp = (CExpr *)symbols->get(ctor->s.c_str()).second;
#endif
          CExpr *curtp = ctortp;
          for (int i = 0, iend = vars.size(); i < iend; i++) {
            if ( curtp->followDefs()->getop() != PI)
              report_error(string("Too many arguments to a constructor in")
                           +string(" a pattern.\n1. the pattern: ")
                           +pat->toString()
                           +string("\n2. the head's type: "
                                   +ctortp->toString()));
#ifdef USE_HASH_MAPS
            prevs.push_back(symbol_types[((SymSExpr *)vars[i])->s]);
            symbol_types[((SymSExpr *)vars[i])] = curtp->followDefs()->kids[1];
#else
            prevs.push_back
              (symbols->insert(((SymSExpr *)vars[i])->s.c_str(),
                               pair<Expr *, Expr *>(NULL,
                                                    ((CExpr *)(curtp->followDefs()))->kids[1])));
#endif
            curtp = (CExpr *)((CExpr *)(curtp->followDefs()))->kids[2];
          }

          tp = check_code(c->kids[1]);

          for (int i = 0, iend = prevs.size(); i < iend; i++) {
#ifdef USE_HASH_MAPS
            symbol_types[((SymSExpr *)vars[i])->s] = prevs[i];
#else
            symbols->insert(((SymSExpr *)vars[i])->s.c_str(), prevs[i]);
#endif
          }
        }
      }

      // check that the type for the body of this case -- or the default value --
      // matches the type for the previous case if we had one.

      if (!mtp)
        mtp = tp;
      else
        if (mtp != tp)
          report_error(string("Types for bodies of match cases or the default differ.")
                       +string("\n1. type for first case's body: ")
                       +mtp->toString()
                       +(pat == NULL ? string("\n2. type for the default")
                         : (string("\n2. type for the body of case for ")
                            +pat->toString()))
                       +string(": ")+tp->toString());

    }

    return mtp;
              }
  } // end switch

  report_error("Type checking an unrecognized form of code (internal error).");
  return NULL;
}

bool dbg_prog;
bool run_scc;
int dbg_prog_indent_lvl = 0;

void dbg_prog_indent(std::ostream &os) {
  for (int i = 0; i < dbg_prog_indent_lvl; i++)
    os << " ";
}

Expr *run_code(Expr *_e) {
 start_run_code:
  CExpr *e = (CExpr *)_e;
  if( e )
  {
    //std::cout << ". ";
    //e->print( std::cout );
    //std::cout << std::endl;
    //std::cout << e->getop() << " " << e->getclass() << std::endl;
  }
  switch (e->getop()) {
  case NOT_CEXPR:
    switch(e->getclass()) {
    case INT_EXPR:
    case RAT_EXPR:
      e->inc();
      return e;
    case HOLE_EXPR: {
      Expr *tmp = e->followDefs();
      if (tmp == e)
	      report_error("Encountered an unfilled hole running code.");
      tmp->inc();
      return tmp;
    }
    case SYMS_EXPR:
    case SYM_EXPR: {
      Expr *tmp = e->followDefs();
      //std::cout << "follow def = ";
      //tmp->print( std::cout );
      //std::cout << std::endl;
      if (tmp == e) {
	      e->inc();
	      return e;
      }
      tmp->inc();
      return tmp;
    }
    }
  case FAIL:
    return NULL;
  case DO: {
    Expr *tmp = run_code(e->kids[0]);
    if (!tmp)
      return NULL;
    tmp->dec();
    _e = e->kids[1];
    goto start_run_code;
  }
  case LET: {
    Expr *r0 = run_code(e->kids[1]);
    if (!r0)
      return NULL;
    SymExpr *var = (SymExpr *)e->kids[0];
    Expr *prev = var->val;
    var->val = r0;
    Expr *r1 = run_code(e->kids[2]);
    var->val = prev;
    r0->dec();
    return r1;
  }
  case ADD:
  case MUL:
  case DIV:
  {
    Expr *r1 = run_code(e->kids[0]);
    if (!r1)
      return NULL;
    Expr *r2 = run_code(e->kids[1]);
    if (!r2)
      return NULL;
    if( r1->getclass()==INT_EXPR && r2->getclass()==INT_EXPR )
    {
      mpz_t r;
      mpz_init(r);
      if( e->getop()==ADD )
        mpz_add(r, ((IntExpr *)r1)->n, ((IntExpr *)r2)->n);
      else if( e->getop()==MUL )
        mpz_mul(r, ((IntExpr *)r1)->n, ((IntExpr *)r2)->n);
      else if( e->getop()==DIV )
        mpz_cdiv_q(r, ((IntExpr *)r1)->n, ((IntExpr *)r2)->n);
      r1->dec();
      r2->dec();
      return new IntExpr(r);
    }
    else if( r1->getclass()==RAT_EXPR && r2->getclass()==RAT_EXPR )
    {
      mpq_t q;
      mpq_init(q);
      if( e->getop()==ADD )
        mpq_add(q, ((RatExpr *)r1)->n, ((RatExpr *)r2)->n);
      else if( e->getop()==MUL )
        mpq_mul(q, ((RatExpr *)r1)->n, ((RatExpr *)r2)->n);
      else if( e->getop()==DIV )
        mpq_div(q, ((RatExpr *)r1)->n, ((RatExpr *)r2)->n);
      r1->dec();
      r2->dec();
      return new RatExpr(q);
    }
    else
    {
      //std::cout << "An arithmetic operation failed. " << r1->getclass() << " " << r2->getclass() << std::endl;
      r1->dec();
      r2->dec();
      return NULL;
    }
  }
  case NEG: {
    Expr *r1 = run_code(e->kids[0]);
    if (!r1)
      return NULL;
    if (r1->getclass() == INT_EXPR) {
      mpz_t r;
      mpz_init(r);
      mpz_neg(r, ((IntExpr *)r1)->n);
      r1->dec();
      return new IntExpr(r);
    }
    else if( r1->getclass() == RAT_EXPR ) {
      mpq_t q;
      mpq_init(q);
      mpq_neg(q, ((RatExpr *)r1)->n);
      r1->dec();
      return new RatExpr(q);
    }
    else
    {
      std::cout << "An arithmetic negation failed. " << r1->getclass() << std::endl;
      //((SymSExpr*)r1)->val->print( std::cout );
      std::cout << ((SymSExpr*)r1)->val << std::endl;
      r1->dec();
      return NULL;
    }
  }
  case IFNEG:
  case IFZERO:{
    Expr *r1 = run_code(e->kids[0]);
    if (!r1)
      return NULL;

    bool cond = true;
    if( r1->getclass() == INT_EXPR ){
      if( e->getop() == IFNEG )
        cond = mpz_sgn( ((IntExpr *)r1)->n )<0;
      else if( e->getop() == IFZERO )
        cond = mpz_sgn( ((IntExpr *)r1)->n )==0;
    }else if( r1->getclass() == RAT_EXPR ){
      if( e->getop() == IFNEG )
        cond = mpq_sgn( ((RatExpr *)r1)->n )<0;
      else if( e->getop() == IFZERO )
        cond = mpq_sgn( ((RatExpr *)r1)->n )==0;
    }
    else
    {
      std::cout << "An arithmetic if-expression failed. " << r1->getclass() << std::endl;
      r1->dec();
      return NULL;
    }
    r1->dec();


    if( cond )
      _e = e->kids[1];
    else
      _e = e->kids[2];
    goto start_run_code;
  }
  case IFMARKED: {
    Expr *r1 = run_code(e->kids[1]);
    if (!r1)
      return NULL;
    if(r1->getclass() != SYM_EXPR && r1->getclass() != SYMS_EXPR ){
      r1->dec();
      return NULL;
    }
#ifndef MARKVAR_32
    if (r1->getexmark()) {
#else
    if(((SymExpr*)r1)->getmark( ((IntExpr*)e->kids[0])->get_num() ) ){
#endif
      r1->dec();
      _e = e->kids[2];
      goto start_run_code;
    }
    // else
    r1->dec();
    _e = e->kids[3];
    goto start_run_code;
  }
  case COMPARE:
  {
    Expr *r1 = run_code(e->kids[0]);
    if (!r1)
      return NULL;
    if (r1->getclass() != SYM_EXPR && r1->getclass() != SYMS_EXPR) {
      r1->dec();
      return NULL;
    }
    Expr *r2 = run_code(e->kids[1]);
    if (!r2)
      return NULL;
    if (r2->getclass() != SYM_EXPR && r2->getclass() != SYMS_EXPR) {
      r2->dec();
      return NULL;
    }
    if( r1<r2 ){
      r1->dec();
      _e = e->kids[2];
      goto start_run_code;
    }
    //else
    r2->dec();
    _e = e->kids[3];
    goto start_run_code;
  }
  case MARKVAR: {
    Expr *r1 = run_code(e->kids[1]);
    if (!r1)
      return NULL;
    if (r1->getclass() != SYM_EXPR && r1->getclass() != SYMS_EXPR) {
      r1->dec();
      return NULL;
    }
#ifndef MARKVAR_32
    if (r1->getexmark())
      r1->clearexmark();
    else
      r1->setexmark();
#else
    if(((SymExpr*)r1)->getmark( ((IntExpr*)e->kids[0])->get_num() ) )
      ((SymExpr*)r1)->clearmark( ((IntExpr*)e->kids[0])->get_num() );
    else
      ((SymExpr*)r1)->setmark( ((IntExpr*)e->kids[0])->get_num() );
#endif
    return r1;
  }
  case MATCH: {
    Expr *scrut = run_code(e->kids[0]);
    if (!scrut)
      return 0;
    vector<Expr *> args;
    Expr *hd = scrut->collect_args(args);
    Expr **cases = &e->kids[1];
    // CExpr *c;
    Expr *c_or_default;
    while ((c_or_default = *cases++)) {

      if (c_or_default->getop() != CASE){
        //std::cout << "run the default " << std::endl;
        //c_or_default->print( std::cout );
        // this is the default of the MATCH
        return run_code(c_or_default);
      }

      // this is a CASE of the MATCH
      CExpr *c = (CExpr *)c_or_default;
      Expr *p = c->kids[0];
      if (hd == p->get_head()) {
	      vector<Expr *> vars;
	      p->collect_args(vars);
	      int jend = args.size();
	      vector<Expr *> old_vals(jend);
	      for (int j = 0; j < jend; j++) {
	        SymExpr *var = (SymExpr *)vars[j];
	        old_vals[j] = var->val;
	        var->val = args[j];
	        args[j]->inc();
	      }
	      scrut->dec();
	      Expr *ret = run_code(c->kids[1] /* the body of the case */);
	      for (int j = 0; j < jend; j++) {
	        ((SymExpr *)vars[j])->val = old_vals[j];
	        args[j]->dec();
	      }
	      return ret;
      }
    }
    break;
  }
  case APP: {
    Expr *tmp = e->whr();
    if (e != tmp) {
      _e = tmp;
      goto start_run_code;
    }

    // e is in weak head normal form

    vector<Expr *> args;
    Expr *hd = e->collect_args(args);
    for (int i = 0, iend = args.size(); i < iend; i++)
      if (!(args[i] = run_code(args[i]))) {
	      for (int j = 0; j < i; j++)
	         args[j]->dec();
	      return NULL;
      }
    if (hd->getop() != PROG) {
      hd->inc();
      Expr *tmp = Expr::build_app(hd,args);
      return tmp;
    }

    assert(hd->getclass() == CEXPR);
    CExpr *prog = (CExpr *)hd;
    assert(prog->kids[1]->getclass() == CEXPR);
    Expr **cur = ((CExpr *)prog->kids[1])->kids;
    vector<Expr *> old_vals;
    SymExpr *var;
    int i = 0;

    if( run_scc && e->get_head( false )->getclass()==SYMS_EXPR )
    {
      //std::cout << "running " << ((SymSExpr*)e->get_head( false ))->s.c_str() << " with " << (int)args.size() << " arguments" << std::endl;
//#ifndef USE_FLAT_APP
//      for( int a=0; a<(int)args.size(); a++ )
//      {
//        args[a] = CExpr::convert_to_flat_app( args[a] );
//      }
//#endif
      Expr *ret = run_compiled_scc( e->get_head( false ), args );
      for (int i = 0, iend = args.size(); i < iend; i++) {
        args[i]->dec();
      }
//#ifndef USE_FLAT_APP
//      ret = CExpr::convert_to_tree_app( ret );
//#endif
      //ret->inc();
      return ret;
    }
    else
    {
      while((var = (SymExpr *)*cur++)) {
        // Check whether not enough arguments were supplied
        if (i >= args.size()) {
          for (size_t i = 0; i < args.size(); i++) {
             args[i]->dec();
          }
          return NULL;
        }

        old_vals.push_back(var->val);
        var->val = args[i++];
      }

      // Check whether too many arguments were supplied
      if (i < args.size()) {
        for (size_t i = 0; i < args.size(); i++) {
           args[i]->dec();
        }
        return NULL;
      }

      if (dbg_prog) {
        dbg_prog_indent(cout);
        cout << "[";
        e->print(cout);
        cout << "\n";
      }
      dbg_prog_indent_lvl++;

      Expr *ret = run_code(prog->kids[2]);

      dbg_prog_indent_lvl--;
      if (dbg_prog) {
        dbg_prog_indent(cout);
        cout << "= ";
        if (ret)
	        ret->print(cout);
        else
	        cout << "fail";
        cout << "]\n";
      }

      cur = ((CExpr *)prog->kids[1])->kids;
      i = 0;
      while((var = (SymExpr *)*cur++)) {
        assert(i < args.size());
        args[i]->dec();
        var->val = old_vals[i++];
      }
      return ret;
    }
  }
  } // end switch
  return NULL;
}

int read_index()
{
  int index = 1;
  string v;
  char c;
  while (isdigit(c = our_getc()))
    v.push_back(c);
  our_ungetc(c);
  if( v.length()>0 )
  {
    index = atoi( v.c_str() );
  }
  return index;
}
