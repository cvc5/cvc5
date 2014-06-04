#include "scccode.h"

Expr* e_pos;
Expr* e_neg;
Expr* e_tt;
Expr* e_ff;
Expr* e_cln;
Expr* e_clc;
Expr* e_concat;
Expr* e_clr;
Expr* e_litvar;
Expr* e_litpol;
Expr* e_notb;
Expr* e_iffb;
Expr* e_clear_mark;
Expr* e_append;
Expr* e_simplify_clause_h;
Expr* e_simplify_clause;

void init_compiled_scc(){
   e_pos = symbols->get("pos").first;
   e_neg = symbols->get("neg").first;
   e_tt = symbols->get("tt").first;
   e_ff = symbols->get("ff").first;
   e_cln = symbols->get("cln").first;
   e_clc = symbols->get("clc").first;
   e_concat = symbols->get("concat").first;
   e_clr = symbols->get("clr").first;
   e_litvar = progs["litvar"];
   e_litpol = progs["litpol"];
   e_notb = progs["notb"];
   e_iffb = progs["iffb"];
   e_clear_mark = progs["clear_mark"];
   e_append = progs["append"];
   e_simplify_clause_h = progs["simplify_clause_h"];
   e_simplify_clause = progs["simplify_clause"];
}

Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args ){
   if( p==e_litvar ){
      return f_litvar( args[0] );
   }else if( p==e_litpol ){
      return f_litpol( args[0] );
   }else if( p==e_notb ){
      return f_notb( args[0] );
   }else if( p==e_iffb ){
      return f_iffb( args[0], args[1] );
   }else if( p==e_clear_mark ){
      return f_clear_mark( args[0] );
   }else if( p==e_append ){
      return f_append( args[0], args[1] );
   }else if( p==e_simplify_clause_h ){
      return f_simplify_clause_h( args[0], args[1] );
   }else if( p==e_simplify_clause ){
      return f_simplify_clause( args[0] );
   }else{
      return NULL;
   }
}

Expr* f_litvar( Expr* l ){
   Expr* e0;
   l->inc();
   Expr* e1 = l->followDefs()->get_head();
   Expr* e2;
   e2 = e_pos;
   e2->inc();
   Expr* e3;
   e3 = e_neg;
   e3->inc();
   if( e1==e2 ){
      Expr* x = ((CExpr*)l->followDefs())->kids[1];
      e0 = x;
      e0->inc();
   }else if( e1==e3 ){
      Expr* x = ((CExpr*)l->followDefs())->kids[1];
      e0 = x;
      e0->inc();
   }else{
      std::cout << "Could not find match for expression in function f_litvar ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   l->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_litpol( Expr* l ){
   Expr* e0;
   l->inc();
   Expr* e1 = l->followDefs()->get_head();
   Expr* e2;
   e2 = e_pos;
   e2->inc();
   Expr* e3;
   e3 = e_neg;
   e3->inc();
   if( e1==e2 ){
      // Expr* x = ((CExpr*)l->followDefs())->kids[1];
      e0 = e_tt;
      e0->inc();
   }else if( e1==e3 ){
      // Expr* x = ((CExpr*)l->followDefs())->kids[1];
      e0 = e_ff;
      e0->inc();
   }else{
      std::cout << "Could not find match for expression in function f_litpol ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   l->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_notb( Expr* b ){
   Expr* e0;
   b->inc();
   Expr* e1 = b->followDefs()->get_head();
   Expr* e2;
   e2 = e_ff;
   e2->inc();
   Expr* e3;
   e3 = e_tt;
   e3->inc();
   if( e1==e2 ){
      e0 = e_tt;
      e0->inc();
   }else if( e1==e3 ){
      e0 = e_ff;
      e0->inc();
   }else{
      std::cout << "Could not find match for expression in function f_notb ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   b->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_iffb( Expr* b1, Expr* b2 ){
   Expr* e0;
   b1->inc();
   Expr* e1 = b1->followDefs()->get_head();
   Expr* e2;
   e2 = e_tt;
   e2->inc();
   Expr* e3;
   e3 = e_ff;
   e3->inc();
   if( e1==e2 ){
      e0 = b2;
      e0->inc();
   }else if( e1==e3 ){
      b2->inc();
      e0 = f_notb( b2 );
      b2->dec();
   }else{
      std::cout << "Could not find match for expression in function f_iffb ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   b1->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_clear_mark( Expr* v ){
   Expr* e0;
   v->inc();
   if ( ((SymExpr*)v->followDefs())->getmark(0)){
      v->inc();
      if ( ((SymExpr*)v->followDefs())->getmark(0))
         ((SymExpr*)v->followDefs())->clearmark(0);
      else
         ((SymExpr*)v->followDefs())->setmark(0);
      e0 = v;
      e0->inc();
      v->dec();
   }else{
      e0 = v;
      e0->inc();
   }
   v->dec();
   return e0;
}

Expr* f_append( Expr* c1, Expr* c2 ){
   Expr* e0;
   c1->inc();
   Expr* e1 = c1->followDefs()->get_head();
   Expr* e2;
   e2 = e_cln;
   e2->inc();
   Expr* e3;
   e3 = e_clc;
   e3->inc();
   if( e1==e2 ){
      e0 = c2;
      e0->inc();
   }else if( e1==e3 ){
      Expr* l = ((CExpr*)c1->followDefs())->kids[1];
      Expr* c1h = ((CExpr*)c1->followDefs())->kids[2];
      l->inc();
      Expr* e4;
      c1h->inc();
      c2->inc();
      e4 = f_append( c1h, c2 );
      c1h->dec();
      c2->dec();
      static Expr* e5;
      e5 = e_clc;
      e5->inc();
      e0 = new CExpr( APP, e5, l, e4 );
   }else{
      std::cout << "Could not find match for expression in function f_append ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   c1->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_simplify_clause_h( Expr* pol, Expr* c ){
   Expr* e0;
   c->inc();
   Expr* e1 = c->followDefs()->get_head();
   Expr* e2;
   e2 = e_cln;
   e2->inc();
   Expr* e3;
   e3 = e_clc;
   e3->inc();
   Expr* e4;
   e4 = e_concat;
   e4->inc();
   Expr* e5;
   e5 = e_clr;
   e5->inc();
   if( e1==e2 ){
      e0 = e_cln;
      e0->inc();
   }else if( e1==e3 ){
      Expr* l = ((CExpr*)c->followDefs())->kids[1];
      Expr* c1 = ((CExpr*)c->followDefs())->kids[2];
      Expr* v;
      l->inc();
      v = f_litvar( l );
      l->dec();
      Expr* e6;
      Expr* e7;
      l->inc();
      e7 = f_litpol( l );
      l->dec();
      pol->inc();
      e6 = f_iffb( e7, pol );
      e7->dec();
      pol->dec();
      Expr* e8 = e6->followDefs()->get_head();
      Expr* e9;
      e9 = e_tt;
      e9->inc();
      Expr* e10;
      e10 = e_ff;
      e10->inc();
      if( e8==e9 ){
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(0)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e11;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e11 = v;
            e11->inc();
            v->dec();
            e11->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* ch;
         pol->inc();
         c1->inc();
         ch = f_simplify_clause_h( pol, c1 );
         pol->dec();
         c1->dec();
         m->inc();
         Expr* e12 = m->followDefs()->get_head();
         Expr* e13;
         e13 = e_tt;
         e13->inc();
         Expr* e14;
         e14 = e_ff;
         e14->inc();
         if( e12==e13 ){
            Expr* e15;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1)){
               e15 = v;
               e15->inc();
            }else{
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(1))
                  ((SymExpr*)v->followDefs())->clearmark(1);
               else
                  ((SymExpr*)v->followDefs())->setmark(1);
               e15 = v;
               e15->inc();
               v->dec();
            }
            v->dec();
            e15->dec();
            e0 = ch;
            e0->inc();
         }else if( e12==e14 ){
            Expr* e16;
            Expr* e17;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1)){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(1))
                  ((SymExpr*)v->followDefs())->clearmark(1);
               else
                  ((SymExpr*)v->followDefs())->setmark(1);
               e17 = v;
               e17->inc();
               v->dec();
            }else{
               e17 = v;
               e17->inc();
            }
            v->dec();
            e17->dec();
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e16 = v;
            e16->inc();
            v->dec();
            e16->dec();
            l->inc();
            ch->inc();
            static Expr* e18;
            e18 = e_clc;
            e18->inc();
            e0 = new CExpr( APP, e18, l, ch );
         }else{
            std::cout << "Could not find match for expression in function f_simplify_clause_h ";
            e12->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         m->dec();
         e13->dec();
         e14->dec();
         ch->dec();
         m->dec();
      }else if( e8==e10 ){
         l->inc();
         Expr* e19;
         pol->inc();
         c1->inc();
         e19 = f_simplify_clause_h( pol, c1 );
         pol->dec();
         c1->dec();
         static Expr* e20;
         e20 = e_clc;
         e20->inc();
         e0 = new CExpr( APP, e20, l, e19 );
      }else{
         std::cout << "Could not find match for expression in function f_simplify_clause_h ";
         e8->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      e6->dec();
      e9->dec();
      e10->dec();
      v->dec();
   }else if( e1==e4 ){
      Expr* c1 = ((CExpr*)c->followDefs())->kids[1];
      Expr* c2 = ((CExpr*)c->followDefs())->kids[2];
      pol->inc();
      Expr* e21 = pol->followDefs()->get_head();
      Expr* e22;
      e22 = e_ff;
      e22->inc();
      Expr* e23;
      e23 = e_tt;
      e23->inc();
      if( e21==e22 ){
         Expr* e24;
         pol->inc();
         c1->inc();
         e24 = f_simplify_clause_h( pol, c1 );
         pol->dec();
         c1->dec();
         Expr* e25;
         pol->inc();
         c2->inc();
         e25 = f_simplify_clause_h( pol, c2 );
         pol->dec();
         c2->dec();
         static Expr* e26;
         e26 = e_concat;
         e26->inc();
         e0 = new CExpr( APP, e26, e24, e25 );
      }else if( e21==e23 ){
         Expr* e27;
         pol->inc();
         c1->inc();
         e27 = f_simplify_clause_h( pol, c1 );
         pol->dec();
         c1->dec();
         Expr* e28;
         pol->inc();
         c2->inc();
         e28 = f_simplify_clause_h( pol, c2 );
         pol->dec();
         c2->dec();
         e0 = f_append( e27, e28 );
         e27->dec();
         e28->dec();
      }else{
         std::cout << "Could not find match for expression in function f_simplify_clause_h ";
         e21->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      pol->dec();
      e22->dec();
      e23->dec();
   }else if( e1==e5 ){
      Expr* l = ((CExpr*)c->followDefs())->kids[1];
      Expr* c1 = ((CExpr*)c->followDefs())->kids[2];
      Expr* e29;
      Expr* e30;
      l->inc();
      e30 = f_litpol( l );
      l->dec();
      pol->inc();
      e29 = f_iffb( e30, pol );
      e30->dec();
      pol->dec();
      Expr* e31 = e29->followDefs()->get_head();
      Expr* e32;
      e32 = e_ff;
      e32->inc();
      Expr* e33;
      e33 = e_tt;
      e33->inc();
      if( e31==e32 ){
         l->inc();
         Expr* e34;
         pol->inc();
         c1->inc();
         e34 = f_simplify_clause_h( pol, c1 );
         pol->dec();
         c1->dec();
         static Expr* e35;
         e35 = e_clr;
         e35->inc();
         e0 = new CExpr( APP, e35, l, e34 );
      }else if( e31==e33 ){
         Expr* v;
         l->inc();
         v = f_litvar( l );
         l->dec();
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(0)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e36;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e36 = v;
            e36->inc();
            v->dec();
            e36->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* ch;
         pol->inc();
         c1->inc();
         ch = f_simplify_clause_h( pol, c1 );
         pol->dec();
         c1->dec();
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(1)){
            m->inc();
            Expr* e37 = m->followDefs()->get_head();
            Expr* e38;
            e38 = e_tt;
            e38->inc();
            Expr* e39;
            e39 = e_ff;
            e39->inc();
            if( e37==e38 ){
               e0 = ch;
               e0->inc();
            }else if( e37==e39 ){
               Expr* e40;
               Expr* e41;
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(1))
                  ((SymExpr*)v->followDefs())->clearmark(1);
               else
                  ((SymExpr*)v->followDefs())->setmark(1);
               e41 = v;
               e41->inc();
               v->dec();
               e41->dec();
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(0))
                  ((SymExpr*)v->followDefs())->clearmark(0);
               else
                  ((SymExpr*)v->followDefs())->setmark(0);
               e40 = v;
               e40->inc();
               v->dec();
               e40->dec();
               e0 = ch;
               e0->inc();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause_h ";
               e37->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m->dec();
            e38->dec();
            e39->dec();
         }else{
            e0 = NULL;
         }
         v->dec();
         ch->dec();
         m->dec();
         v->dec();
      }else{
         std::cout << "Could not find match for expression in function f_simplify_clause_h ";
         e31->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      e29->dec();
      e32->dec();
      e33->dec();
   }else{
      std::cout << "Could not find match for expression in function f_simplify_clause_h ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   c->dec();
   e2->dec();
   e3->dec();
   e4->dec();
   e5->dec();
   return e0;
}

Expr* f_simplify_clause( Expr* c ){
   Expr* e0;
   static Expr* e1;
   e1 = e_tt;
   e1->inc();
   Expr* e2;
   static Expr* e3;
   e3 = e_ff;
   e3->inc();
   c->inc();
   e2 = f_simplify_clause_h( e3, c );
   e3->dec();
   c->dec();
   e0 = f_simplify_clause_h( e1, e2 );
   e1->dec();
   e2->dec();
   return e0;
}

