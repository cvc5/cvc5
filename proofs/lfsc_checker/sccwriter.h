#ifndef SCC_WRITER_H
#define SCC_WRITER_H

#include "expr.h"
#include <vector>
#include "check.h"

enum
{
  opt_write_case_body = 0x00000001,
  opt_write_check_sym_expr = 0x00000002,
  opt_write_add_args = 0x000000004,
  opt_write_no_inc = 0x00000008,

  opt_write_call_debug = 0x00000010,
  opt_write_nested_app = 0x00000020,
};

class sccwriter
{
private:
  //options
   int options;
  //programs to write to file
  symmap progs;
  //list of indicies in progs
  std::vector< Expr* > progPtrs;
  std::vector< std::string > progNames;
  int currProgram;
  //current variables in the scope
  std::vector< std::string > vars;
  //global variables stored for lookups
  std::vector< std::string > globalSyms;
  //symbols that must be dec'ed
  std::vector< std::string > decSyms;
  //get program
  CExpr* get_prog( int n ) { return (CExpr*)progs[ progNames[n] ]; }
  //get index for string
  int get_prog_index_by_expr( Expr* e );
  int get_prog_index( const std::string& str );
  //is variable in current scope
  bool is_var( const std::string& str );
  //add global sym
  void add_global_sym( const std::string& str );
  //expression count
  static int exprCount;
  //string count
  static int strCount;
  //args count
  static int argsCount;
  //num count
  static int rnumCount;
  //indent
  static void indent( std::ostream& os, int ind );
  //write function header
  void write_function_header( std::ostream& os, int index, int opts = 0 );
  void write_code( Expr* code, std::ostream& os, int ind, const char* retModStr, int opts = 0 );
  //write all children starting at child counter to stream, store in Expr* e_...e_;
  void write_args( CExpr* code, std::ostream& os, int ind, int childCounter, std::vector< std::string >& args, int opts = 0 );
  //write expression - store result of code into e_ for some Expr* e_;
  void write_expr( Expr* code, std::ostream& os, int ind, std::string& expr, int opts = 0 );
  //write variable
  void write_variable( const std::string& n, std::ostream& os );
  //get function name
  void get_function_name( const std::string& pname, std::string& fname );
  //get the variable name
  void get_var_name( const std::string& n, std::string& nn );
  //write dec
  void write_dec( const std::string& expr, std::ostream& os, int ind );
public:
  sccwriter( int opts = 0 ) : options( opts ){}
  virtual ~sccwriter(){}

  void add_scc( const std::string& pname, Expr* exp ) { 
    //progs.push_back( std::pair< std::string, CExpr* >( pname, exp ) ); 
    progs[pname] = exp;
    progPtrs.push_back( exp );
    progNames.push_back( pname );
  }

  void write_file();
  //write code
  static void debug_write_code( Expr* code, std::ostream& os, int ind );
};

#endif
