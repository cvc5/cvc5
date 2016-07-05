#include "sccwriter.h"

#include <fstream>
#include <sstream>

int sccwriter::exprCount = 0;
int sccwriter::strCount = 0;
int sccwriter::argsCount = 0;
int sccwriter::rnumCount = 0;

int sccwriter::get_prog_index( const std::string& str )
{
  for( int a=0; a<(int)progNames.size(); a++ ){
    if( progNames[a]==str ){
      return a;
    }
  }
  return -1;
}

int sccwriter::get_prog_index_by_expr( Expr* e )
{
  for( int a=0; a<(int)progPtrs.size(); a++ ){
    if( progPtrs[a]==e ){
      return a;
    }
  }
  return -1;
}

bool sccwriter::is_var( const std::string& str )
{
  for( int a=0; a<(int)vars.size(); a++ ){
    if( vars[a]==str ){
      return true;
    }
  }
  return false;
}

void sccwriter::add_global_sym( const std::string& str )
{
  for( int a=0; a<(int)globalSyms.size(); a++ ){
    if( globalSyms[a]==str ){
      return;
    }
  }
  globalSyms.push_back( str );
}

void sccwriter::indent( std::ostream& os, int ind )
{
   for( int a=0; a<ind; a++ )
   {
      os << "   ";
   }
}

void sccwriter::write_function_header( std::ostream& os, int index, int opts )
{
  //write the function header
  std::string fname;
  get_function_name( progNames[index], fname );
  os << "Expr* " << fname.c_str() << "( ";
  CExpr* progvars = (CExpr*)get_prog( index )->kids[1];
  int counter = 0;
  //write each argument
  while( progvars->kids[counter] )
  {
    if( counter!=0 )
    {
      os << ", ";
    }
    os << "Expr* ";
    write_variable( ((SymSExpr*)progvars->kids[counter])->s, os );
    //add to vars if options are set to do so
    if( opts&opt_write_add_args )
    {
      vars.push_back( ((SymSExpr*)progvars->kids[counter])->s );
    }
    counter++;
  }
  os << " )";
  if( opts&opt_write_call_debug )
  {
     os << "{" << std::endl;
     indent( os, 1 );
     os << "std::cout << \"Call function " << fname.c_str() << " with arguments \";" << std::endl;
     counter = 0; 
     while( progvars->kids[counter] )
     {
        if( counter!=0 )
        {
           indent( os, 1 );
           os << "std::cout << \", \";" << std::endl;
        }
        indent( os, 1 );
        write_variable( ((SymSExpr*)progvars->kids[counter])->s, os );
        os << "->print( std::cout );" << std::endl;
        counter++;
     }
     indent( os, 1 );
     os << "std::cout << std::endl;" << std::endl;
  }
}

void sccwriter::get_function_name( const std::string& pname, std::string& fname )
{
  fname = std::string( "f_" );
  fname.append( pname );
}

void sccwriter::write_variable( const std::string& n, std::ostream& os )
{
  std::string nn;
  get_var_name( n, nn );
  os << nn.c_str();
}

void sccwriter::get_var_name( const std::string& n, std::string& nn ) {
  nn = std::string( n.c_str() );
  for( int i = 0; i <(int)n.length(); i++ ){
    char c = n[i];
    if (c <= 47)
        c += 65;
    else if (c >= 58 && c <= 64)
        c += 97-58;
    if ((c >= 91 && c <= 94) || c == 96)
        c += 104-91;
    else if (c >= 123)
        c -= 4;
    nn[i] = c;
  }  
}

void sccwriter::write_file()
{
  static std::string filename( "scccode" );

  //writer the h file
  std::fstream fsh;
  std::string fnameh( filename );
  fnameh.append(".h");
  fsh.open( fnameh.c_str(), std::ios::out );
  //write the header in h
  fsh << "#ifndef SCC_CODE_H" << std::endl;
  fsh << "#define SCC_CODE_H" << std::endl << std::endl;
  //include necessary files in h file
  fsh << "#include \"check.h\"" << std::endl << std::endl;
  //write the init function
  fsh << "void init_compiled_scc();" << std::endl << std::endl;
  //write the entry function
  fsh << "Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args );" << std::endl << std::endl;
  //write the side condition code functions
  for( int n=0; n<(int)progs.size(); n++ )
  {
    //write the header in the h file
    fsh << "inline ";
    write_function_header( fsh, n );
    fsh << ";" << std::endl << std::endl;
  }
  fsh << "#endif" << std::endl << std::endl;
  fsh.close();


  //writer the cpp code
  std::fstream fsc;
  std::string fnamec( filename );
  fnamec.append(".cpp");
  fsc.open( fnamec.c_str(), std::ios::out );
  //include the h file in the cpp
  fsc << "#include \"scccode.h\"" << std::endl << std::endl;
  std::ostringstream fsc_funcs;
  //write the side condition code functions
  for( currProgram=0; currProgram<(int)progs.size(); currProgram++ )
  {
    //reset naming counters
    vars.clear();
    exprCount = 0;
    strCount = 0;
    argsCount = 0;
    rnumCount = 0;

    //for debugging
    std::cout << "program #" << currProgram << " " << progNames[currProgram].c_str() << std::endl;

    //write the function header
    write_function_header( fsc_funcs, currProgram, opt_write_add_args|options );
    if( (options&opt_write_call_debug)==0 )
    {
       fsc_funcs << "{" << std::endl;
    }
    //write the code
    //std::vector< std::string > cleanVec;
    //write_code( get_prog( n )->kids[2], fsc, 1, "return ", cleanVec );
    //debug_write_code( progs[n].second->kids[2], fsc, 1 );
    std::string expr;
    write_expr( get_prog( currProgram )->kids[2], fsc_funcs, 1, expr );
    indent( fsc_funcs, 1 );
    fsc_funcs << "return " << expr.c_str() << ";" << std::endl;
    fsc_funcs << "}" << std::endl << std::endl;
  }
  //write the predefined symbols necessary - symbols and progs
  for( int a=0; a<(int)globalSyms.size(); a++ )
  {
    fsc << "Expr* e_" << globalSyms[a].c_str() << ";" << std::endl;
  }
  for( int a=0; a<(int)progs.size(); a++ )
  {
    fsc << "Expr* e_" << progNames[a].c_str() << ";" << std::endl;
  }
  fsc << std::endl;
  //write the init function - initialize symbols and progs
  fsc << "void init_compiled_scc(){" << std::endl;
  for( int a=0; a<(int)globalSyms.size(); a++ )
  {
    indent( fsc, 1 );
    fsc << "e_" << globalSyms[a].c_str() << " = symbols->get(\"" << globalSyms[a].c_str() << "\").first;" << std::endl;
  }
  for( int a=0; a<(int)progs.size(); a++ )
  {
    indent( fsc, 1 );
    fsc << "e_" << progNames[a].c_str() << " = progs[\"" << progNames[a].c_str() << "\"];" << std::endl;
  }
  fsc << "}" << std::endl << std::endl;
  fsc << "Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args ){" << std::endl;
  //for( int n=0; n<(int)progs.size(); n++ ){
  //  indent( fsc, 1 );
  //  fsc << "static std::string s_" << progNames[n].c_str() << " = std::string( \"" << progNames[n].c_str() << "\" );" << std::endl;
  //}
  for( int n=0; n<(int)progs.size(); n++ ){
    indent( fsc, 1 );
    if( n!=0 ){
      fsc << "}else ";
    }
    //for each function, test to see if the string matches the name of the function
    fsc << "if( p==e_" << progNames[n].c_str() << " ){" << std::endl;
    indent( fsc, 2 );
    std::string fname;
    get_function_name( progNames[n], fname );
    //map the function to the proper function
    fsc << "return " << fname.c_str() << "( ";
    //write the arguments to the function from args
    CExpr* progvars = (CExpr*)get_prog( n )->kids[1];
    int counter = 0;
    bool firstTime = true;
    while( progvars->kids[counter] )
    {
      if( !firstTime )
      {
        fsc << ", ";
      }
      fsc << "args[" << counter << "]";
      firstTime = false;
      counter++;
    }
    fsc << " );" << std::endl;
  }
  indent( fsc, 1 );
  fsc << "}else{" << std::endl;
  indent( fsc, 2 );
  //return null in the case the function could not be found
  fsc << "return NULL;" << std::endl;
  indent( fsc, 1 );
  fsc << "}" << std::endl;
  fsc << "}" << std::endl << std::endl;
  fsc << fsc_funcs.str().c_str();

  fsc.close();
}

void sccwriter::write_code( Expr* code, std::ostream& os, int ind, const char* retModStr, int opts )
{
  std::string retModString;
  std::string incString;
  if ( retModStr )
  {
    retModString = std::string( retModStr );
    retModString.append( " = " );
    incString = std::string( retModStr );
    incString.append( "->inc();" );
  }
  switch( code->getclass() )
  {
  case INT_EXPR:
    {
      indent( os, ind );
      os << retModString.c_str();
      os << "new IntExpr( (signed long int)" << mpz_get_si( ((IntExpr*)code)->n ) << " );" << std::endl;
      indent( os, ind );
      os << incString.c_str() << std::endl;
    }
    break;
  case RAT_EXPR:
    {
      mpz_t num, den;
      mpz_init(num);
      mpz_init(den);
      mpq_get_num( num, ((RatExpr*)code)->n );
      mpq_get_den( den, ((RatExpr*)code)->n );
      indent( os, ind );
      os << retModString.c_str();
      os << "new RatExpr( " << mpz_get_si( num ) << ", " << mpz_get_si( den ) << " );" << std::endl;
      indent( os, ind );
      os << incString.c_str() << std::endl;
    }
    break;
  case SYMS_EXPR:
    {
      //if it is a variable, simply write it to buffer
      if( is_var( ((SymSExpr*)code)->s ) )
      {
        indent( os, ind );
        os << retModString.c_str();
        write_variable( ((SymSExpr*)code)->s.c_str(), os );
        os << ";" << std::endl;  
      }
      else  //else must look at symbol lookup table
      {
        std::string var;
        get_var_name( ((SymSExpr*)code)->s, var );
        indent( os, ind );
        os << retModString.c_str() << "e_" << var.c_str() << ";" << std::endl;
        add_global_sym( var ); 
      }
      indent( os, ind );
      os << incString.c_str() << std::endl;
    }
    break;
  default:
    switch( code->getop() )
    {
    case APP:
      {
        //collect the arguments
        std::vector< Expr* > argVector;
        code->collect_args( argVector );
        //write the arguments
        std::vector< std::string > args;
        for( int a=0; a<(int)argVector.size(); a++ )
        {
          std::string expr;
          write_expr( argVector[a], os, ind, expr );
          args.push_back( expr );
        }
        //write_args( (CExpr*)code, os, ind, 1, args );
        Expr* hd = code->get_head();
        //map to a program in the case that it is a program
        if( hd->getop()==PROG && get_prog_index_by_expr( hd )!=-1 )
        {
          indent( os, ind );
          os << retModString << "f_" << progNames[ get_prog_index_by_expr( hd ) ].c_str() << "( ";
          for( int a=0; a<(int)args.size(); a++ )
          {
            os << args[a].c_str();
            if( a!=(int)( args.size()-1 ) ){
              os << ", ";
            }
          }
          os << " );" << std::endl;
          for( int a=0; a<(int)args.size(); a++ )
          {
            write_dec( args[a], os, ind );
          }
        }
        else
        {
#ifdef USE_FLAT_APP
          std::string expr;
          write_expr( hd, os, ind, expr );
          indent( os, ind );
          os << retModString << "new CExpr( APP, ";
          os << expr.c_str() << ", ";
          for( int a=0; a<(int)args.size(); a++ )
          {
            os << args[a].c_str();
            if( a!=(int)( args.size()-1 ) ){
              os << ", ";
            }
          }
          os << " );" << std::endl;
#else
          std::string expr;
          write_expr( hd, os, ind, expr );
          indent( os, ind );
          os << retModString;
          for( int a=0; a<(int)args.size(); a++ )
          {
            os << "new CExpr( APP, ";
          }
          os << expr.c_str() << ", ";
          for( int a=0; a<(int)args.size(); a++ )
          {
            os << args[a].c_str();
            os << " )";
            if( a!=(int)( args.size()-1 ) ){
              os << ", ";
            }
          }
          os << ";" << std::endl;
#endif
          //indent( os, ind );
          //os << expr.c_str() << "->dec();" << std::endl;
        }
      }
      break;
    case MATCH:
      {
        //calculate the value for the expression
        std::string expr;
        write_expr( ((CExpr*)code)->kids[0], os, ind, expr );
        //get the head
        std::ostringstream sshd;
        sshd << "e" << exprCount;
        exprCount++;
        indent( os, ind );
        os << "Expr* " << sshd.str().c_str() << " = " << expr.c_str() << "->followDefs()->get_head();" << std::endl;
        //write the arguments
        std::vector< std::string > args;
        write_args( (CExpr*)code, os, ind, 1, args );
        bool encounterDefault = false;
        //now make an if statement corresponding to the match 
        int a = 0;
        while( ((CExpr*)code)->kids[a+1] )
        {
          indent( os, ind );
          if( a!=0 ){
            os << "}else";
          }
          if( ((CExpr*)code)->kids[a+1]->getop()!=CASE ){
            encounterDefault = true;
            os << "{" << std::endl;
            //write the body of the case
            write_code( ((CExpr*)code)->kids[a+1], os, ind+1, retModStr ); 
            indent( os, ind );
            os << "}" << std::endl;
          }else{
            if( a!=0 )
              os << " ";
            os << "if( " << sshd.str().c_str() << "==" << args[a].c_str() << " ){" << std::endl;
            //collect args from the variable in the code
            std::ostringstream ssargs;
            ssargs << "args" << argsCount;
            argsCount++;
#ifndef USE_FLAT_APP
            indent( os, ind+1 );
            os << "std::vector< Expr* > " << ssargs.str().c_str() << ";" << std::endl;
            indent( os, ind+1 );
            os << expr.c_str() << "->followDefs()->collect_args( " << ssargs.str().c_str() << " );" << std::endl;
#endif
            //set the variables defined in the pattern equal to the arguments
            std::vector< Expr* > caseArgs;
            ((CExpr*)((CExpr*)code)->kids[a+1])->kids[0]->collect_args( caseArgs );
            for( int b=0; b<(int)caseArgs.size(); b++ )
            {
              indent( os, ind+1 );
              os << "Expr* ";
              write_variable( ((SymSExpr*)caseArgs[b])->s.c_str(), os );
#ifdef USE_FLAT_APP
              os << " = ((CExpr*)" << expr.c_str() << "->followDefs())->kids[" << b+1 << "];" << std::endl;
#else
              os << " = " << ssargs.str().c_str() << "[" << b << "];" << std::endl;
#endif
              vars.push_back( ((SymSExpr*)caseArgs[b])->s );
            }
            //write the body of the case
            write_code( ((CExpr*)code)->kids[a+1], os, ind+1, retModStr, opt_write_case_body ); 
          }
          a++;
        }
        if( !encounterDefault )
        {
          indent( os, ind );
          os << "}else{" << std::endl;
          indent( os, ind + 1 );
          os << "std::cout << \"Could not find match for expression in function f_";
          os << progNames[currProgram].c_str() << " \";" << std::endl;
          indent( os, ind + 1 );
          os << sshd.str().c_str() << "->print( std::cout );" << std::endl;
          indent( os, ind + 1 );
          os << "std::cout << std::endl;" << std::endl;
          indent( os, ind + 1 );
          os << "exit( 1 );" << std::endl;
          indent( os, ind );
          os << "}" << std::endl;
        }
        write_dec( expr, os, ind );
        for( int a=0; a<(int)args.size(); a++ )
        {
          write_dec( args[a], os, ind );
        }
      }
      break;
    case CASE:
      if( opts&opt_write_case_body )
      {
        write_code( ((CExpr*)code)->kids[1], os, ind, retModStr );
      }
      else
      {
        write_code( ((CExpr*)code)->kids[0]->get_head(), os, ind, retModStr );
      }
      break;
    case DO:
      {
        //write each of the children in sequence
        int counter = 0;
        while( ((CExpr*)code)->kids[counter] )
        {
          if( ((CExpr*)code)->kids[counter+1]==NULL )
          {
            write_code( ((CExpr*)code)->kids[counter], os, ind, retModStr );
          }
          else
          {
            std::string expr;
            write_expr( ((CExpr*)code)->kids[counter], os, ind, expr );
            //clean up memory
            write_dec( expr, os, ind );
          }
          counter++;
        }
      }
      break;
    case LET:
      {
        indent( os, ind );
        os << "Expr* ";
        write_variable( ((SymSExpr*)((CExpr*)code)->kids[0])->s, os );
        os << " = NULL;" << std::endl;
        std::ostringstream ss;
        write_variable( ((SymSExpr*)((CExpr*)code)->kids[0])->s, ss );
        write_code( ((CExpr*)code)->kids[1], os, ind, ss.str().c_str() );
        //add it to the variables
        vars.push_back( ((SymSExpr*)((CExpr*)code)->kids[0])->s );
        write_code( ((CExpr*)code)->kids[2], os, ind, retModStr );
        //clean up memory
        indent( os, ind );
        write_variable( ((SymSExpr*)((CExpr*)code)->kids[0])->s, os );
        os << "->dec();" << std::endl;
      }
      break;
    case FAIL:
      {
        indent( os, ind );
        os << retModString.c_str() << "NULL;" << std::endl;
      }
      break;
#ifndef MARKVAR_32
    case MARKVAR:
      {
        //calculate the value for the expression
        std::string expr;
        write_expr( ((CExpr*)code)->kids[0], os, ind, expr, opt_write_check_sym_expr );
        //set the mark on the expression
        indent( os, ind );
        os << "if (" << expr.c_str() << "->followDefs()->getmark())" << std::endl;
        indent( os, ind+1 );
        os << expr.c_str() << "->followDefs()->clearmark();" << std::endl;
        indent( os, ind );
        os << "else" << std::endl;
        indent( os, ind+1 );
        os << expr.c_str() << "->followDefs()->setmark();" << std::endl;
        //write the return if necessary
        if( retModStr!=NULL ){
          indent( os, ind );
          os << retModString.c_str() << expr.c_str() << ";" << std::endl;
          indent( os, ind );
          os << incString.c_str() << std::endl;
        }
        write_dec( expr, os, ind );
      }
      break;
    case IFMARKED:
      {
        //calculate the value for the expression
        std::string expr;
        write_expr( ((CExpr*)code)->kids[0], os, ind, expr, opt_write_check_sym_expr );
        //if mark is set, write code for kids[1]
        indent( os, ind );
        os << "if (" << expr.c_str() << "->followDefs()->getmark()){" << std::endl;
        write_code( ((CExpr*)code)->kids[1], os, ind+1, retModStr );
        //else write code for kids[2]
        indent( os, ind );
        os << "}else{" << std::endl;
        write_code( ((CExpr*)code)->kids[2], os, ind+1, retModStr );
        indent( os, ind );
        os << "}" << std::endl;
        //clean up memory
        write_dec( expr, os, ind );
      }
      break;
#else
    case MARKVAR:
      {
        //calculate the value for the expression
        std::string expr;
        write_expr( ((CExpr*)code)->kids[1], os, ind, expr, opt_write_check_sym_expr );
        //set the mark on the expression
        indent( os, ind );
        os << "if ( ((SymExpr*)" << expr.c_str() << "->followDefs())->getmark(";
        os << ((IntExpr*)((CExpr*)code)->kids[0])->get_num() << "))" << std::endl;
        indent( os, ind+1 );
        os << "((SymExpr*)" << expr.c_str() << "->followDefs())->clearmark(";
        os << ((IntExpr*)((CExpr*)code)->kids[0])->get_num() << ");" << std::endl;
        indent( os, ind );
        os << "else" << std::endl;
        indent( os, ind+1 );
        os << "((SymExpr*)" << expr.c_str() << "->followDefs())->setmark(";
        os << ((IntExpr*)((CExpr*)code)->kids[0])->get_num() << ");" << std::endl;
        //write the return if necessary
        if( retModStr!=NULL ){
          indent( os, ind );
          os << retModString.c_str() << expr.c_str() << ";" << std::endl;
          indent( os, ind );
          os << incString.c_str() << std::endl;
        }
        write_dec( expr, os, ind );
      }
      break;
    case COMPARE:
      {
        std::string expr1, expr2;
        write_expr( ((CExpr*)code)->kids[0], os, ind, expr1, opt_write_check_sym_expr );
        write_expr( ((CExpr*)code)->kids[1], os, ind, expr2, opt_write_check_sym_expr );
        indent( os, ind );
        os << "if( ((SymExpr*)" << expr1.c_str() << ")->followDefs() < ((SymExpr*)" << expr2.c_str() << ")->followDefs() ){" << std::endl;
        write_code( ((CExpr*)code)->kids[2], os, ind+1, retModStr );
        indent( os, ind );
        os << "}else{" << std::endl;
        write_code( ((CExpr*)code)->kids[3], os, ind+1, retModStr );
        indent( os, ind );
        os << "}" << std::endl;
        //clean up memory
        write_dec( expr1, os, ind );
        write_dec( expr2, os, ind );
      }
      break;
    case IFMARKED:
      {
        //calculate the value for the expression
        std::string expr;
        write_expr( ((CExpr*)code)->kids[1], os, ind, expr, opt_write_check_sym_expr );
        //if mark is set, write code for kids[1]
        indent( os, ind );
        os << "if ( ((SymExpr*)" << expr.c_str() << "->followDefs())->getmark(";
        os << ((IntExpr*)((CExpr*)code)->kids[0])->get_num() << ")){" << std::endl;
        write_code( ((CExpr*)code)->kids[2], os, ind+1, retModStr );
        //else write code for kids[2]
        indent( os, ind );
        os << "}else{" << std::endl;
        write_code( ((CExpr*)code)->kids[3], os, ind+1, retModStr );
        indent( os, ind );
        os << "}" << std::endl;
        //clean up memory
        write_dec( expr, os, ind );
      }
      break;
#endif
    case ADD:
    case MUL:
    case DIV:
      {
        //calculate the value for the first expression
        std::string expr1;
        write_expr( ((CExpr*)code)->kids[0], os, ind, expr1 );
        //calculate the value for the second expression
        std::string expr2;
        write_expr( ((CExpr*)code)->kids[1], os, ind, expr2 );
        std::ostringstream ss;
        ss << "rnum" << rnumCount;
        rnumCount++;
        indent( os, ind );
        os << "if( " << expr1.c_str() << "->followDefs()->getclass()==INT_EXPR ){" << std::endl;
        indent( os, ind+1 );
        os << "mpz_t " << ss.str().c_str() << ";" << std::endl;
        indent( os, ind+1 );
        os << "mpz_init(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind+1 );
        os << "mpz_";
        if( code->getop()==ADD )
          os << "add";
        else
          os << "mul";
        os << "( " << ss.str().c_str() << ", ((IntExpr*)" << expr1.c_str() << "->followDefs())->n, ((IntExpr*)" << expr2.c_str() << "->followDefs())->n);" << std::endl;
        indent( os, ind+1 );
        os << retModString.c_str() << "new IntExpr(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind );
        os << "}else if( " << expr1.c_str() << "->followDefs()->getclass()==RAT_EXPR ){" << std::endl;
        indent( os, ind+1 );
        os << "mpq_t " << ss.str().c_str() << ";" << std::endl;
        indent( os, ind+1 );
        os << "mpq_init(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind+1 );
        os << "mpq_";
        if( code->getop()==ADD )
          os << "add";
        else if( code->getop()==MUL )
          os << "mul";
        else
          os << "div";
        os << "( " << ss.str().c_str() << ", ((RatExpr*)" << expr1.c_str() << "->followDefs())->n, ((RatExpr*)" << expr2.c_str() << "->followDefs())->n);" << std::endl;
        indent( os, ind+1 );
        os << retModString.c_str() << "new RatExpr(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind );
        os << "}" << std::endl;
        //clean up memory
        write_dec( expr1, os, ind );
        write_dec( expr2, os, ind );
      }
      break;
    case NEG:
      {
        //calculate the value for the first expression
        std::string expr1;
        write_expr( ((CExpr*)code)->kids[0], os, ind, expr1 );
        std::ostringstream ss;
        ss << "rnum" << rnumCount;
        rnumCount++;
        indent( os, ind );
        os << "if( " << expr1.c_str() << "->followDefs()->getclass()==INT_EXPR ){" << std::endl;
        indent( os, ind+1 );
        os << "mpz_t " << ss.str().c_str() << ";" << std::endl;
        indent( os, ind+1 );
        os << "mpz_init(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind+1 );
        os << "mpz_neg( " << ss.str().c_str() << ", ((IntExpr*)" << expr1.c_str() << "->followDefs())->n );" << std::endl;
        indent( os, ind+1 );
        os << retModString.c_str() << "new IntExpr(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind );
        os << "}else if( " << expr1.c_str() << "->followDefs()->getclass()==RAT_EXPR ){" << std::endl;
        indent( os, ind+1 );
        os << "mpq_t " << ss.str().c_str() << ";" << std::endl;
        indent( os, ind+1 );
        os << "mpq_init(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind+1 );
        os << "mpq_neg( " << ss.str().c_str() << ", ((RatExpr*)" << expr1.c_str() << "->followDefs())->n );" << std::endl;
        indent( os, ind+1 );
        os << retModString.c_str() << "new RatExpr(" << ss.str().c_str() << ");" << std::endl;
        indent( os, ind );
        os << "}" << std::endl;
        //clean up memory
        write_dec( expr1, os, ind );
      }
      break;
    case IFNEG:
    case IFZERO:
      {
        std::string expr1;
        write_expr( ((CExpr*)code)->kids[0], os, ind, expr1 );
        indent( os, ind );
        os << "if( " << expr1.c_str() << "->followDefs()->getclass()==INT_EXPR ){" << std::endl;
        indent( os, ind+1 );
        os << "if( mpz_sgn( ((IntExpr *)" << expr1.c_str() << "->followDefs())->n ) ";
        if( code->getop()==IFNEG )
          os << "<";
        else
          os << "==";
        os << " 0 ){" << std::endl;
        write_code( ((CExpr*)code)->kids[1], os, ind+2, retModStr );
        indent( os, ind+1 );
        os << "}else{" << std::endl;
        write_code( ((CExpr*)code)->kids[2], os, ind+2, retModStr );
        indent( os, ind+1 );
        os << "}" << std::endl;
        indent( os, ind );
        os << "}else if( " << expr1.c_str() << "->followDefs()->getclass()==RAT_EXPR ){" << std::endl;
        indent( os, ind+1 );
        os << "if( mpq_sgn( ((RatExpr *)" << expr1.c_str() << "->followDefs())->n ) ";
        if( code->getop()==IFNEG )
          os << "<";
        else
          os << "==";
        os << " 0 ){" << std::endl;
        write_code( ((CExpr*)code)->kids[1], os, ind+2, retModStr );
        indent( os, ind+1 );
        os << "}else{" << std::endl;
        write_code( ((CExpr*)code)->kids[2], os, ind+2, retModStr );
        indent( os, ind+1 );
        os << "}" << std::endl;
        indent( os, ind );
        os << "}" << std::endl;
        //clean up memory
        write_dec( expr1, os, ind );
      }
      break;
    case RUN:/*?*/break;
    case PI:/*?*/break;
    case LAM:/*?*/break;
    case TYPE:/*?*/break;
    case KIND:/*?*/break;
    case ASCRIBE:/*?*/break;
    case MPZ:/*?*/break;
    case PROG:/*?*/break;
    case PROGVARS:/*?*/break;
    case PAT:/*?*/break;
    }
    break;
  }
}

void sccwriter::write_args( CExpr* code, std::ostream& os, int ind, int childCounter, 
                            std::vector< std::string >& args, int opts )
{
  bool encounterCase = false;
  while( code->kids[childCounter] &&
         (!encounterCase || code->kids[childCounter]->getop()==CASE ) )
  {
    encounterCase = encounterCase || code->kids[childCounter]->getop()==CASE;
    if( code->kids[childCounter]->getclass()==SYMS_EXPR )
    {
      args.push_back( ((SymSExpr*)code->kids[childCounter])->s );
    }
    else
    {
      //calculate the value for the argument
      std::string expr;
      write_expr( code->kids[childCounter], os, ind, expr, opts );
      args.push_back( expr );
    }
    childCounter++;
  }
}

void sccwriter::write_expr( Expr* code, std::ostream& os, int ind, std::string& expr, int opts )
{
  if( code->getclass()==SYMS_EXPR && is_var( ((SymSExpr*)code)->s ) )
  {
    get_var_name( ((SymSExpr*)code)->s, expr );
    indent( os, ind );
    os << expr.c_str() << "->inc();" << std::endl;
  }
  else
  {
    std::ostringstream ss;
    ss << "e" << exprCount;
    exprCount++;
    //declare the expression
    indent( os, ind );
    if( code->getclass()==SYMS_EXPR && !is_var( ((SymSExpr*)code)->s ) )
    {
      os << "static ";
    }
    os << "Expr* " << ss.str().c_str() << " = NULL;" << std::endl;
    //write the expression
    std::ostringstream ss2;
    ss2 << ss.str().c_str();
    write_code( code, os, ind, ss2.str().c_str(), opts );

    //if is not a sym expression, then decrement the expression and return null
    if( opts&opt_write_check_sym_expr )
    {
      indent( os, ind );
      os << "if (" << expr.c_str() << "->getclass() != SYM_EXPR) {" << std::endl;
      indent( os, ind+1 );
      os << "exit( 1 );" << std::endl;
      indent( os, ind );
      os << "}" << std::endl;
    }

    expr = std::string( ss.str().c_str() );
    vars.push_back( expr );
  }
  //increment the counter for memory management
  //indent( os, ind );
  //os << expr.c_str() << "->inc();" << std::endl;
}

void sccwriter::write_dec( const std::string& expr, std::ostream& os, int ind )
{
  bool wd = true;
  if( wd )
  {
    indent( os, ind );
    os << expr.c_str() << "->dec();" << std::endl;
  }
}

void sccwriter::debug_write_code( Expr* code, std::ostream& os, int ind )
{
  indent( os, ind );
  switch( code->getclass() )
  {
  case INT_EXPR:
    os << "int_expr";
    break;
  case HOLE_EXPR:
    os << "hole_expr";
    break;
  case SYM_EXPR:
    os << "sym_expr";
    break;
  case SYMS_EXPR:
    os << "syms_expr: " << ((SymSExpr*)code)->s.c_str();
    break;
  default:
    switch( code->getop() )
    {
    case APP:
      os << "app";
      break;
    case PI:
      os << "pi";
      break;
    case LAM:
      os << "lam";
      break;
    case TYPE:
      os << "type";
      break;
    case KIND:
      os << "kind";
      break;
    case ASCRIBE:
      os << "ascribe";
      break;
    case MPZ:
      os << "mpz";
      break;
    case PROG:
      os << "prog";
      break;
    case PROGVARS:
      os << "progvars";
      break;
    case MATCH:
      os << "match";
      break;
    case CASE:
      os << "case";
      break;
    case PAT:
      os << "pat";
      break;
    case DO:
      os << "do";
      break;
    case ADD:
      os << "add";
      break;
    case NEG:
      os << "neg";
      break;
    case LET:
      os << "let";
      break;
    case RUN:
      os << "run";
      break;
    case FAIL:
      os << "fail";
      break;
    case MARKVAR:
      os << "markvar";
      break;
    case IFMARKED:
      os << "ifmarked";
      break;
    case COMPARE:
      os << "compare";
      break;
    default:
      os << "???";
      break;
    }
  }
  os << std::endl;
  if( code->getop()!=0 )
  {
    CExpr* ce = (CExpr*)code;
    int counter = 0;
    while( ce->kids[counter] ){
      debug_write_code( ce->kids[counter], os, ind+1 );
      counter++;
    }
  }
}
