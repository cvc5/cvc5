#ifndef SC2_CHECK_H
#define SC2_CHECK_H

#include "expr.h"
#include "trie.h"

#ifdef _MSC_VER
#include <hash_map>
#include <stdio.h>
#else
#include <ext/hash_map>
#endif

#include <stack>
#include <string>
#include <map>

// see the help message in main.cpp for explanation
typedef struct args {
  std::vector<std::string> files;
  bool show_runs; 
  bool no_tail_calls; 
  bool compile_scc;
  bool compile_scc_debug;
  bool run_scc;
  bool use_nested_app;
  bool compile_lib;
} args;

extern int check_time;

class sccwriter;
class libwriter;

void init();

void check_file(const char *_filename, args a, sccwriter* scw = NULL, libwriter* lw = NULL);

void cleanup();

extern char our_getc_c;

void report_error(const std::string &);

extern int linenum;
extern int colnum;
extern const char *filename;
extern FILE *curfile;

inline void our_ungetc(char c) {
  if (our_getc_c != 0)
    report_error("Internal error: our_ungetc buffer full");
  our_getc_c = c;
  if (c == '\n') {
    linenum--;
    colnum=-1;
  }
  else
    colnum--;
}

inline char our_getc() {
  char c;
  if (our_getc_c > 0) {
    c = our_getc_c;
    our_getc_c = 0;
  }
  else{
#ifndef __linux__
	c = fgetc(curfile);
#else
    c = fgetc_unlocked(curfile);
#endif
  }
  switch(c) {
  case '\n':
    linenum++;
#ifdef DEBUG_LINES
    std::cout << "line " << linenum << "." << std::endl;
#endif
    colnum = 1;
    break;
  case char(EOF):
    break;
  default:
    colnum++;
  }

  return c;
}

// return the next character that is not whitespace
inline char non_ws() {
  char c;
  while(isspace(c = our_getc()));
  if (c == ';') {
    // comment to end of line
    while((c = our_getc()) != '\n' && c != char(EOF));
    return non_ws();
  }
  return c;
}
  
inline void eat_char(char expected) {
  if (non_ws() != expected) {
    char tmp[80];
    sprintf(tmp,"Expecting a \'%c\'",expected);
    report_error(tmp);
  }
}

extern int IDBUF_LEN;
extern char idbuf[];

inline const char *prefix_id() {
  int i = 0;
  char c = idbuf[i++] = non_ws();
  while (!isspace(c) && c != '(' && c != ')' && c != char(EOF)) {
    if (i == IDBUF_LEN)
      report_error("Identifier is too long");
    
    idbuf[i++] = c = our_getc();
  }
  our_ungetc(c);
  idbuf[i-1] = 0;
  return idbuf;
}

#ifdef _MSC_VER
typedef std::hash_map<std::string, Expr *> symmap;
typedef std::hash_map<std::string, SymExpr *> symmap2;
#else
typedef __gnu_cxx::hash_map<std::string, Expr *> symmap;
typedef __gnu_cxx::hash_map<std::string, SymExpr *> symmap2;
#endif
extern symmap2 progs;
extern std::vector< Expr* > ascHoles;

#ifdef USE_HASH_MAPS
extern symmap symbols;
extern symmap symbol_types;
#else
extern Trie<std::pair<Expr *, Expr *> > *symbols;
#endif

extern std::map<SymExpr*, int > mark_map;

extern std::vector< std::pair< std::string, std::pair<Expr *, Expr *> > > local_sym_names;

#ifndef _MSC_VER
namespace __gnu_cxx
{
  template<> struct hash< std::string >
  {
    size_t operator()( const std::string& x ) const
    {
      return hash< const char* >()( x.c_str() );
    }
  };
}
#endif

extern Expr *statMpz;
extern Expr *statMpq;
extern Expr *statType;

#endif
