#include "libwriter.h"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>

#include "expr.h"

void libwriter::get_var_name( const std::string& n, std::string& nn ) {
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

void libwriter::write_file()
{
  //std::cout << "write lib" << std::endl;
  std::ostringstream os_enum;
  std::ostringstream os_print;
  std::ostringstream os_constructor_h;
  std::ostringstream os_constructor_c;

  for ( int a=0; a<(int)syms.size(); a++ ) {
    //std::cout << "sym #" << (a+1) << ": ";
    //std::cout << ((SymSExpr*)syms[a])->s.c_str() << std::endl;
    //defs[a]->print( std::cout );
    //std::cout << std::endl;
    
    if( defs[a]->getclass()==CEXPR ){
      //calculate which arguments are required for input
      std::vector< Expr* > args;
      std::vector< bool > argsNeed;
      std::vector< Expr* > argTypes;
      CExpr* c = ((CExpr*)defs[a]);
      while( c->getop()==PI ){
        //std::cout << c->kids[0] << std::endl;
        if( ((CExpr*)c->kids[1])->getop()!=RUN ){
          args.push_back( c->kids[0] );
          argsNeed.push_back( true );
          argTypes.push_back( c->kids[1] );
        }
        for( int b=0; b<(int)args.size(); b++ ){
          if( argsNeed[b] ){
            if( ((CExpr*)c->kids[1])->getop()==RUN ){
              if( ((CExpr*)c->kids[1])->kids[1]->free_in( args[b] ) ){
                argsNeed[b] = false;
              }
            }else{
              if( c->kids[1]->free_in( args[b] ) ){
                argsNeed[b] = false;
              }
            }
          }
        }
        c = (CExpr*)(c->kids[2]);
      }

      //record if this declares a judgement
      if( ((CExpr*)defs[a])->getop()==PI && c->getop()==TYPE ){
        //std::cout << "This is a judgement" << std::endl;
        judgements.push_back( syms[a] );
      //record if this declares a proof rule
      }else if( c->getclass()==CEXPR && std::find( judgements.begin(), judgements.end(), c->kids[0] )!=judgements.end() ){
        std::cout << "Handle rule: " << ((SymSExpr*)syms[a])->s.c_str() << std::endl;
        //std::cout << "These are required to input:" << std::endl;
        //for( int b=0; b<(int)args.size(); b++ ){
        //  if( argsNeed[b] ){
        //    std::cout << ((SymSExpr*)args[b])->s.c_str() << std::endl;
        //  }
        //}
        os_enum << "    rule_" << ((SymSExpr*)syms[a])->s.c_str() << "," << std::endl;

        os_print << "  case rule_" << ((SymSExpr*)syms[a])->s.c_str() << ": os << \"";
        os_print << ((SymSExpr*)syms[a])->s.c_str() << "\";break;" << std::endl;

        std::ostringstream os_args;
        os_args << "(";
        bool firstTime = true;
        for( int b=0; b<(int)args.size(); b++ ){
          if( argsNeed[b] ){
            if( !firstTime )
              os_args << ",";
            std::string str;
            get_var_name( ((SymSExpr*)args[b])->s, str );
            os_args << " LFSCProof* " << str.c_str();
            firstTime = false;
          }
        }
        if( !firstTime ){
          os_args << " ";
        }
        os_args << ")";

        os_constructor_h << "  static LFSCProof* make_" << ((SymSExpr*)syms[a])->s.c_str();
        os_constructor_h << os_args.str().c_str() << ";" << std::endl;

        os_constructor_c << "LFSCProof* LFSCProof::make_" << ((SymSExpr*)syms[a])->s.c_str();
        os_constructor_c << os_args.str().c_str() << "{" << std::endl;
        os_constructor_c << "  LFSCProof **kids = new LFSCProof *[" << (int)args.size()+1 << "];" << std::endl;
        for( int b=0; b<(int)args.size(); b++ ){
          os_constructor_c << "  kids[" << b << "] = ";
          if( argsNeed[b] ){
            std::string str;
            get_var_name( ((SymSExpr*)args[b])->s, str );
            os_constructor_c << str.c_str();
          }else{
            os_constructor_c << "hole";
          }
          os_constructor_c << ";" << std::endl;
        }
        os_constructor_c << "  kids[" << (int)args.size() << "] = 0;" << std::endl;
        os_constructor_c << "  return new LFSCProofC( rule_" << ((SymSExpr*)syms[a])->s.c_str() << ", kids );" << std::endl;
        os_constructor_c << "}" << std::endl << std::endl;
      }
    }

    //write the header
    static std::string filename( "lfsc_proof" );
    std::fstream fsh;
    std::string fnameh( filename );
    fnameh.append(".h");
    fsh.open( fnameh.c_str(), std::ios::out );

    fsh << "#ifndef LFSC_PROOF_LIB_H" << std::endl;
    fsh << "#define LFSC_PROOF_LIB_H" << std::endl;
    fsh << std::endl;
    fsh << "#include <string>" << std::endl;
    fsh << std::endl;
    fsh << "class LFSCProof{" << std::endl;
    fsh << "protected:" << std::endl;
    fsh << "  enum{" << std::endl;
    fsh << os_enum.str().c_str();
    fsh << "  };" << std::endl;
    fsh << "  static LFSCProof* hole;" << std::endl;
    fsh << "  LFSCProof(){}" << std::endl;
    fsh << "public:" << std::endl;
    fsh << "  virtual ~LFSCProof(){}" << std::endl;
    fsh << "  static void init();" << std::endl;
    fsh << std::endl;
    fsh << "  //functions to build LFSC proofs" << std::endl;
    fsh << os_constructor_h.str().c_str();
    fsh << std::endl;
    fsh << "  virtual void set_child( int i, LFSCProof* e ) {}" << std::endl;
    fsh << "  virtual void print( std::ostream& os ){}" << std::endl;
    fsh << "};" << std::endl;
    fsh << std::endl;
    fsh << "class LFSCProofC : public LFSCProof{" << std::endl;
    fsh << "  short id;" << std::endl;
    fsh << "  LFSCProof **kids;" << std::endl;
    fsh << "public:" << std::endl;
    fsh << "  LFSCProofC( short d_id, LFSCProof **d_kids ) : id( d_id ), kids( d_kids ){}" << std::endl;
    fsh << "  void set_child( int i, LFSCProof* e ) { kids[i] = e; }" << std::endl;
    fsh << "  void print( std::ostream& os );" << std::endl;
    fsh << "};" << std::endl;
    fsh << std::endl;
    fsh << "class LFSCProofSym : public LFSCProof{" << std::endl;
    fsh << "private:" << std::endl;
    fsh << "  std::string s;" << std::endl;
    fsh << "  LFSCProofSym( std::string ss ) : s( ss ){}" << std::endl;
    fsh << "public:" << std::endl;
    fsh << "  static LFSCProofSym* make( std::string ss ) { return new LFSCProofSym( ss ); }" << std::endl;
    fsh << "  static LFSCProofSym* make( const char* ss ) { return new LFSCProofSym( std::string( ss ) ); }" << std::endl;
    fsh << "  ~LFSCProofSym(){}" << std::endl;
    fsh << "  void print( std::ostream& os ) { os << s.c_str(); }" << std::endl;
    fsh << "};" << std::endl;
    fsh << std::endl;
    fsh << "class LFSCProofLam : public LFSCProof{" << std::endl;
    fsh << "  LFSCProofSym* var;" << std::endl;
    fsh << "  LFSCProof* body;" << std::endl;
    fsh << "  LFSCProof* typ;" << std::endl;
    fsh << "  LFSCProofLam( LFSCProofSym* d_var, LFSCProof* d_body, LFSCProof* d_typ ) : var( d_var ), body( d_body ), typ( d_typ ){}" << std::endl;
    fsh << "public:" << std::endl;
    fsh << "  static LFSCProof* make( LFSCProofSym* d_var, LFSCProof* d_body, LFSCProof* d_typ = NULL ) {" << std::endl;
    fsh << "    return new LFSCProofLam( d_var, d_body, d_typ );" << std::endl;
    fsh << "  }" << std::endl;
    fsh << "  ~LFSCProofLam(){}" << std::endl;
    fsh << std::endl;
    fsh << "  void print( std::ostream& os );" << std::endl;
    fsh << "};" << std::endl;
    fsh << std::endl;
    fsh << "#endif" << std::endl;

    //write the cpp
    std::fstream fsc;
    std::string fnamec( filename );
    fnamec.append(".cpp");
    fsc.open( fnamec.c_str(), std::ios::out );

    fsc << "#include \"lfsc_proof.h\"" << std::endl;
    fsc << std::endl;
    fsc << "LFSCProof* LFSCProof::hole = NULL;" << std::endl;
    fsc << std::endl;
    fsc << "void LFSCProof::init(){" << std::endl;
    fsc << "  hole = LFSCProofSym::make( \"_\" );" << std::endl;
    fsc << "}" << std::endl;
    fsc << std::endl;
    fsc << "void LFSCProofC::print( std::ostream& os ){" << std::endl;
    fsc << "  os << \"(\";" << std::endl;
    fsc << "  switch( id ){" << std::endl;
    fsc << os_print.str().c_str();
    fsc << "  }" << std::endl;
    fsc << "  int counter = 0;" << std::endl;
    fsc << "  while( kids[counter] ){" << std::endl;
    fsc << "    os << \" \";" << std::endl;
    fsc << "    kids[counter]->print( os );" << std::endl;
    fsc << "    counter++;" << std::endl;
    fsc << "  }" << std::endl;
    fsc << "  os << \")\";" << std::endl;
    fsc << "}" << std::endl;
    fsc << std::endl;
    fsc << "void LFSCProofLam::print( std::ostream& os ){" << std::endl;
    fsc << "  os << \"(\";" << std::endl;
    fsc << "  if( typ ){" << std::endl;
    fsc << "    os << \"% \";" << std::endl;
    fsc << "  }else{" << std::endl;
    fsc << "    os << \"\\\\ \";" << std::endl;
    fsc << "  }" << std::endl;
    fsc << "  var->print( os );" << std::endl;
    fsc << "  if( typ ){" << std::endl;
    fsc << "    os << \" \";" << std::endl;
    fsc << "    typ->print( os );" << std::endl;
    fsc << "  }" << std::endl;
    fsc << "  os << std::endl;" << std::endl;
    fsc << "  body->print( os );" << std::endl;
    fsc << "  os << \")\";" << std::endl;
    fsc << "}" << std::endl;
    fsc << std::endl;
    fsc << os_constructor_c.str().c_str();
    fsc << std::endl;
  }
}
