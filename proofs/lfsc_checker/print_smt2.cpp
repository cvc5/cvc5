#include "print_smt2.h"

#include <iostream>
#include <string>
#include <vector>

#include "expr.h"

#ifdef PRINT_SMT2

void print_smt2( Expr* p, std::ostream& s, short mode )
{
  switch( p->getclass() )
  {
  case CEXPR:
    {
      switch( p->getop() )
      {
      case APP:
        {
          std::vector<Expr *> args;
          Expr *head = p->collect_args(args, false);
          short newMode = get_mode( head );
          if( is_smt2_poly_formula( head ) )
          {
            s << "(";
            head->print( s );
            s << " ";
            print_smt2( args[1], s, newMode );
            s << " ";
            print_smt2( args[2], s, newMode );
            s << ")";
          }
          else if( ( mode==2 || mode==3 ) && mode==newMode )
          {
            print_smt2( args[0], s, newMode );
            s << " ";
            print_smt2( args[1], s, newMode );
          }
          else if( newMode==1 )
          {
            if( mode!=1 || newMode!=mode ){
              s << "(";
            }
            print_smt2( args[2], s, newMode );
            s << " ";
            print_smt2( args[3], s, 0 );
            if( mode!=1 || newMode!=mode ){
              s << ")";
            }
          }
          else
          {
            s << "(";
            switch( newMode )
            {
            case 4: s << "=>";break;
            default: head->print( s );break;
            }
            s << " ";
            for( int a=0; a<(int)args.size(); a++ ){
              print_smt2( args[a], s, newMode );
              if( a!=(int)args.size()-1 )
                s << " ";
            }
            s << ")";
          }
        }
        break;
      default:
        std::cout << "Unhandled op " << p->getop() << std::endl;
        break;
      }
    }
    break;
  case HOLE_EXPR:
    {
      HoleExpr *e = (HoleExpr *)p;
      if( e->val ){
        print_smt2( e->val, s, mode );
      }else{
        s << "_";
      }
    }
    break;
  case SYMS_EXPR:
  case SYM_EXPR:
    if( ((SymExpr*)p)->val )
      print_smt2( ((SymExpr*)p)->val, s, mode );
    else
      p->print( s );
    break;
  default:
    std::cout << "Unhandled class " << p->getclass() << std::endl;
    break;
  }
}

bool is_smt2_poly_formula( Expr* e )
{
  if( e->getclass()==SYMS_EXPR )
  {
    SymSExpr* s = (SymSExpr*)e;
    static std::string eq("=");
    static std::string distinct("distinct");
    return s->s==eq || s->s==distinct;
  }else{
    return false;
  }
}

short get_mode( Expr* e )
{
  if( e->getclass()==SYMS_EXPR ){
    SymSExpr* s = (SymSExpr*)e;
    static std::string applys("apply");
    if ( s->s==applys ) return 1;
    static std::string ands("and");
    if ( s->s==ands ) return 2;
    static std::string ors("or");
    if ( s->s==ors ) return 3;
    static std::string impls("impl");
    if ( s->s==impls ) return 4;
  }
  return 0;
}

#endif
