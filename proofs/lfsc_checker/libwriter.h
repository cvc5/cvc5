#ifndef LIB_WRITER_H
#define LIB_WRITER_H

#include <vector>
#include <string>

class Expr;

class libwriter
{
private:
  std::vector< Expr* > syms;
  std::vector< Expr* > defs;

  std::vector< Expr* > judgements;
  //get the variable name
  void get_var_name( const std::string& n, std::string& nn );
public:
  libwriter(){}
  virtual ~libwriter(){}

  void add_symbol( Expr* s, Expr* t ) { 
    syms.push_back( s );
    defs.push_back( t ); 
  }

  void write_file();
};

#endif
