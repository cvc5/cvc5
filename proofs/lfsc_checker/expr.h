#ifndef sc2__expr_h
#define sc2__expr_h

#include "gmp.h"
#include <string>
#include <vector>
#include <iostream>
#include <map>
#include "chunking_memory_management.h"

#define USE_FLAT_APP
#define MARKVAR_32
#define DEBUG_SYM_NAMES
//#define DEBUG_SYMS

// Expr class
enum { CEXPR = 0,
       INT_EXPR,
       RAT_EXPR,
       HOLE_EXPR,
       SYM_EXPR,
       SYMS_EXPR };

// operators for CExprs
enum { NOT_CEXPR = 0, // for INT_EXPR, HOLE_EXPR, SYM_EXPR, SYMS_EXPR
       APP,
       PI,
       LAM,
       TYPE,
       KIND,
       ASCRIBE,
       MPZ,
       MPQ,

       PROG,
       PROGVARS,
       MATCH,
       CASE,
       PAT,
       DO,
       ADD,
       MUL,
       DIV,
       NEG,
       IFNEG,
       IFZERO,
       LET,
       RUN,
       FAIL,
       MARKVAR,
       IFMARKED,
       COMPARE
};

class SymExpr;

class Expr {
protected:
  /* bits 0-2: Expr class
     bits 3-7: operator 
     bit 8: a flag for already cloned, free_in calculation
     bits 9-31: ref count*/
  int data;

  void destroy(bool dec_kids);

  enum { INC, DEC, CREATE };
  void debugrefcnt(int ref, int what) {
#ifdef DEBUG_REFCNT
    std::cout << "[";
    debug();
    switch(what) {
    case INC:
      std::cout << " inc to ";
      break;
    case DEC:
      std::cout << " dec to ";
      break;
    case CREATE:
      std::cout << " creating]\n";
      return;
    }
    char tmp[10];
    sprintf(tmp,"%d",ref);
    std::cout << tmp << "]\n";
#else
    (void)ref;
    (void)what;
#endif
  }

  Expr(int _class, int _op)
    : data(1 << 9 /* refcount 1, not cloned */| (_op << 3) | _class)
  { }

public:
  static int markedCount;
  inline Expr* followDefs();
  inline int getclass() const { return data & 7; }
  int getexmark() const { return data & 256; }
  void setexmark() { data |= 256; }
  void clearexmark() { data &= ~256; }
  inline int getop() const { return (data >> 3) & 31; }
  int cloned() const { return data & 256; }
  void setcloned() { data |= 256; }

  inline int getrefcnt() { return data >> 9; }
  inline void inc() {
    int ref = getrefcnt();
    //static int iCounter = 0;
    //iCounter++;
    //if( iCounter%10000==0 ){
    //   //print( std::cout );
    //   std::cout << " " << ref << std::endl;
    //}
    ref = ref<4194303 ? ref + 1 : ref;
    debugrefcnt(ref,INC);
    data = (ref << 9) | (data & 511);
  }
  static void destroy(Expr *, bool);
  inline void dec(bool dec_kids = true) {
    int ref = getrefcnt();
    ref = ref - 1;
    debugrefcnt(ref,DEC);
    if (ref == 0)
      destroy(this,dec_kids);
    else
      data = (ref << 9) | (data & 511);
  }

  //must pass statType (the expr representing "type") to this function
  bool isType( Expr* statType );

  inline bool isDatatype() {
    return getclass() == SYMS_EXPR || getop() == MPZ || getop() == MPQ;
  }
  inline bool isArithTerm() {
    return getop() == ADD || getop() == NEG;
  }

  static Expr *build_app(Expr *hd, const std::vector<Expr *> &args, 
			 int start = 0);

  static Expr *make_app(Expr* e1, Expr* e2 );

  /* if this is an APP, return the head, and store the args in args.
     If follow_defs is true, we proceed through defined heads;
     otherwise not. */
  Expr *collect_args(std::vector<Expr *> &args, bool follow_defs = true);

  Expr *get_head(bool follow_defs = true);

  Expr *get_body(int op = PI, bool follow_defs = true);

  std::string toString();

  void print(std::ostream &);
  void debug();

  /* check whether or not this expr is alpha equivalent to e.  If this
     expr contains unfilled holes, fill them as we go. We do not fill
     holes in e.  We do not take responsibility for the reference to
     this nor the reference to e. */
  bool defeq(Expr *e);

  /* return a clone of this expr.  All abstractions are really duplicated
     in memory.  Other expressions may not actually be duplicated in
     memory, but their refcounts will be incremented. */
  Expr *clone(); 

  // x can be a SymExpr or a HoleExpr.
  bool free_in(Expr *x);
  bool get_free_in() { return data & 256; }
  void calc_free_in();

  static int cargCount;
  static int fiCounter;
};

class CExpr : public Expr {
public:
  C_MACROS__ADD_CHUNKING_MEMORY_MANAGEMENT_H(CExpr,kids);

  Expr **kids;
  ~CExpr() {
    delete[] kids;
  }
  CExpr(int _op) : Expr(CEXPR, _op), kids() {
    kids = new Expr *[1];
    kids[0] = 0;
    debugrefcnt(1,CREATE);
  }
  CExpr(int _op, Expr *e1) : Expr(CEXPR, _op), kids() {
    kids = new Expr *[2];
    kids[0] = e1;
    kids[1] = 0;
    debugrefcnt(1,CREATE);
  }
  CExpr(int _op, Expr *e1, Expr *e2)
    : Expr(CEXPR, _op), kids() {
    kids = new Expr *[3];
    kids[0] = e1;
    kids[1] = e2;
    kids[2] = 0;
    debugrefcnt(1,CREATE);
  }
  CExpr(int _op, Expr *e1, Expr *e2, Expr *e3)
    : Expr(CEXPR, _op), kids() {
    kids = new Expr *[4];
    kids[0] = e1;
    kids[1] = e2;
    kids[2] = e3;
    kids[3] = 0;
    debugrefcnt(1,CREATE);
  }
  CExpr(int _op, Expr *e1, Expr *e2, Expr *e3, Expr *e4)
    : Expr(CEXPR, _op), kids() {
    kids = new Expr *[5];
    kids[0] = e1;
    kids[1] = e2;
    kids[2] = e3;
    kids[3] = e4;
    kids[4] = 0;
    debugrefcnt(1,CREATE);
  }
  CExpr(int _op, const std::vector<Expr *> &_kids) 
    : Expr(CEXPR, _op), kids() {
    int i, iend = _kids.size();
    kids = new Expr *[iend + 1];
    for (i = 0; i < iend; i++)
      kids[i] = _kids[i];
    kids[i] = 0;
    debugrefcnt(1,CREATE);
  }

  // _kids must be null-terminated.
  CExpr(int _op, bool dummy, Expr **_kids) : Expr(CEXPR, _op), kids(_kids) {
    (void)dummy;
    debugrefcnt(1,CREATE);
  }

  Expr *whr();

  static Expr* convert_to_tree_app( Expr* ce );
  static Expr* convert_to_flat_app( Expr* ce );
};

class IntExpr : public Expr {
 public:
  mpz_t n;
  ~IntExpr() {
    mpz_clear(n);
  }
  IntExpr(mpz_t _n) : Expr(INT_EXPR, 0), n() {
    mpz_init_set(n,_n);
    debugrefcnt(1,CREATE);
  }
  IntExpr(signed long int _n ) : Expr(INT_EXPR, 0), n() {
    mpz_init_set_si( n, _n );
  }

  unsigned long int get_num() { return mpz_get_ui( n ); }
};

class RatExpr : public Expr {
 public:
  mpq_t n;
  ~RatExpr() {
    mpq_clear(n);
  }
  RatExpr(mpq_t _n) : Expr(RAT_EXPR, 0), n() {
    mpq_init( n );
    mpq_set(n,_n);
    debugrefcnt(1,CREATE);
    mpq_canonicalize( n );
  }
  RatExpr(signed long int _n1, unsigned long int _n2 ) : Expr(RAT_EXPR, 0), n() {
    mpq_init( n );
    mpq_set_si( n, _n1, _n2 );
    mpq_canonicalize( n );
  }
};

class SymExpr : public Expr {
 public:
  Expr *val; // may be set by beta-reduction and clone().
  static int symmCount;

  SymExpr(std::string _s, int theclass = SYM_EXPR) 
    : Expr(theclass, 0), val(0)
  {   
    (void)_s;
    if (theclass == SYM_EXPR)
      debugrefcnt(1,CREATE);
  }
  SymExpr(const SymExpr &e, int theclass = SYM_EXPR) 
    : Expr(theclass, 0), val(0)
  {
    (void)e;
    if (theclass == SYM_EXPR)
      debugrefcnt(1,CREATE);
  }
#ifdef MARKVAR_32
private:
  int mark();
  void smark( int m );
public:
  int getmark( int i = 0 ) { return (mark() >> i)&1; }
  void setmark( int i = 0 ) { smark( mark() | (1 << i) ); }
  void clearmark( int i = 0 ) { smark( mark() & ~(1 << i) ); }
#endif
};

class SymSExpr : public SymExpr {
 public:
  std::string s;
  SymSExpr(std::string _s, int theclass = SYMS_EXPR) 
    : SymExpr(_s, theclass), s(_s)
  {
    debugrefcnt(1,CREATE);
  }
  SymSExpr(const SymSExpr &e, int theclass = SYMS_EXPR) 
    : SymExpr(e, theclass), s(e.s)
  { 
    debugrefcnt(1,CREATE);
  }
};

class HoleExpr : public Expr {
  static int next_id;
public:
#ifdef DEBUG_HOLE_NAMES
  int id;
#endif
  HoleExpr() 
    : Expr(HOLE_EXPR, 0), val(0) 
  {
#ifdef DEBUG_HOLE_NAMES
    id = next_id++;
#endif
    debugrefcnt(1,CREATE);
  }
  Expr *val; // may be set during subst(), defeq(), and clone().
};

inline Expr * Expr::followDefs() {
  switch(getclass()) {
  case HOLE_EXPR: {
    HoleExpr *h = (HoleExpr *)this;
    if (h->val)
      return h->val->followDefs();
    break;
  }
  case SYMS_EXPR: 
  case SYM_EXPR: {
    SymExpr *h = (SymExpr *)this;
    if (h->val)
      return h->val->followDefs();
    break;
  }
  }

  return this;
}

#endif

