#include "scccode.h"

Expr* e_cln;
Expr* e_clc;
Expr* e_concat_cl;
Expr* e_clr;
Expr* e_pos;
Expr* e_neg;
Expr* e_tt;
Expr* e_ff;
Expr* e_false;
Expr* e_true;
Expr* e_bbltn;
Expr* e_bbltc;
Expr* e_bvn;
Expr* e_bvc;
Expr* e_b0;
Expr* e_b1;
Expr* e_bitof;
Expr* e_and;
Expr* e_not;
Expr* e_or;
Expr* e_xor;
Expr* e_iff;
Expr* e_append;
Expr* e_simplify_clause;
Expr* e_mpz_sub;
Expr* e_mp_ispos;
Expr* e_mpz_eq;
Expr* e_mpz_lt;
Expr* e_mpz_lte;
Expr* e_mpz_;
Expr* e_bblt_len;
Expr* e_bblast_const;
Expr* e_bblast_var;
Expr* e_bblast_concat;
Expr* e_bblast_extract_rec;
Expr* e_bblast_extract;
Expr* e_extend_rec;
Expr* e_bblast_zextend;
Expr* e_bblast_sextend;
Expr* e_bblast_bvand;
Expr* e_bblast_bvnot;
Expr* e_bblast_bvor;
Expr* e_bblast_bvxor;
Expr* e_bblast_bvadd_carry;
Expr* e_bblast_bvadd;
Expr* e_bblast_zero;
Expr* e_bblast_bvneg;
Expr* e_reverse_help;
Expr* e_reverseb;
Expr* e_top_k_bits;
Expr* e_bottom_k_bits;
Expr* e_k_bit;
Expr* e_and_with_bit;
Expr* e_mult_step_k_h;
Expr* e_mult_step;
Expr* e_bblast_bvmul;
Expr* e_bblast_eq_rec;
Expr* e_bblast_eq;
Expr* e_bblast_bvult;
Expr* e_bblast_bvslt;
Expr* e_mk_ones;
Expr* e_mk_zero;

void init_compiled_scc(){
   e_cln = symbols->get("cln").first;
   e_clc = symbols->get("clc").first;
   e_concat_cl = symbols->get("concat_cl").first;
   e_clr = symbols->get("clr").first;
   e_pos = symbols->get("pos").first;
   e_neg = symbols->get("neg").first;
   e_tt = symbols->get("tt").first;
   e_ff = symbols->get("ff").first;
   e_false = symbols->get("false").first;
   e_true = symbols->get("true").first;
   e_bbltn = symbols->get("bbltn").first;
   e_bbltc = symbols->get("bbltc").first;
   e_bvn = symbols->get("bvn").first;
   e_bvc = symbols->get("bvc").first;
   e_b0 = symbols->get("b0").first;
   e_b1 = symbols->get("b1").first;
   e_bitof = symbols->get("bitof").first;
   e_and = symbols->get("and").first;
   e_not = symbols->get("not").first;
   e_or = symbols->get("or").first;
   e_xor = symbols->get("xor").first;
   e_iff = symbols->get("iff").first;
   e_append = progs["append"];
   e_simplify_clause = progs["simplify_clause"];
   e_mpz_sub = progs["mpz_sub"];
   e_mp_ispos = progs["mp_ispos"];
   e_mpz_eq = progs["mpz_eq"];
   e_mpz_lt = progs["mpz_lt"];
   e_mpz_lte = progs["mpz_lte"];
   e_mpz_ = progs["mpz_"];
   e_bblt_len = progs["bblt_len"];
   e_bblast_const = progs["bblast_const"];
   e_bblast_var = progs["bblast_var"];
   e_bblast_concat = progs["bblast_concat"];
   e_bblast_extract_rec = progs["bblast_extract_rec"];
   e_bblast_extract = progs["bblast_extract"];
   e_extend_rec = progs["extend_rec"];
   e_bblast_zextend = progs["bblast_zextend"];
   e_bblast_sextend = progs["bblast_sextend"];
   e_bblast_bvand = progs["bblast_bvand"];
   e_bblast_bvnot = progs["bblast_bvnot"];
   e_bblast_bvor = progs["bblast_bvor"];
   e_bblast_bvxor = progs["bblast_bvxor"];
   e_bblast_bvadd_carry = progs["bblast_bvadd_carry"];
   e_bblast_bvadd = progs["bblast_bvadd"];
   e_bblast_zero = progs["bblast_zero"];
   e_bblast_bvneg = progs["bblast_bvneg"];
   e_reverse_help = progs["reverse_help"];
   e_reverseb = progs["reverseb"];
   e_top_k_bits = progs["top_k_bits"];
   e_bottom_k_bits = progs["bottom_k_bits"];
   e_k_bit = progs["k_bit"];
   e_and_with_bit = progs["and_with_bit"];
   e_mult_step_k_h = progs["mult_step_k_h"];
   e_mult_step = progs["mult_step"];
   e_bblast_bvmul = progs["bblast_bvmul"];
   e_bblast_eq_rec = progs["bblast_eq_rec"];
   e_bblast_eq = progs["bblast_eq"];
   e_bblast_bvult = progs["bblast_bvult"];
   e_bblast_bvslt = progs["bblast_bvslt"];
   e_mk_ones = progs["mk_ones"];
   e_mk_zero = progs["mk_zero"];
}

Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args ){
   if( p==e_append ){
      return f_append( args[0], args[1] );
   }else if( p==e_simplify_clause ){
      return f_simplify_clause( args[0] );
   }else if( p==e_mpz_sub ){
      return f_mpz_sub( args[0], args[1] );
   }else if( p==e_mp_ispos ){
      return f_mp_ispos( args[0] );
   }else if( p==e_mpz_eq ){
      return f_mpz_eq( args[0], args[1] );
   }else if( p==e_mpz_lt ){
      return f_mpz_lt( args[0], args[1] );
   }else if( p==e_mpz_lte ){
      return f_mpz_lte( args[0], args[1] );
   }else if( p==e_mpz_ ){
      return f_mpz_( args[0], args[1] );
   }else if( p==e_bblt_len ){
      return f_bblt_len( args[0] );
   }else if( p==e_bblast_const ){
      return f_bblast_const( args[0], args[1] );
   }else if( p==e_bblast_var ){
      return f_bblast_var( args[0], args[1] );
   }else if( p==e_bblast_concat ){
      return f_bblast_concat( args[0], args[1] );
   }else if( p==e_bblast_extract_rec ){
      return f_bblast_extract_rec( args[0], args[1], args[2], args[3] );
   }else if( p==e_bblast_extract ){
      return f_bblast_extract( args[0], args[1], args[2], args[3] );
   }else if( p==e_extend_rec ){
      return f_extend_rec( args[0], args[1], args[2] );
   }else if( p==e_bblast_zextend ){
      return f_bblast_zextend( args[0], args[1] );
   }else if( p==e_bblast_sextend ){
      return f_bblast_sextend( args[0], args[1] );
   }else if( p==e_bblast_bvand ){
      return f_bblast_bvand( args[0], args[1] );
   }else if( p==e_bblast_bvnot ){
      return f_bblast_bvnot( args[0] );
   }else if( p==e_bblast_bvor ){
      return f_bblast_bvor( args[0], args[1] );
   }else if( p==e_bblast_bvxor ){
      return f_bblast_bvxor( args[0], args[1] );
   }else if( p==e_bblast_bvadd_carry ){
      return f_bblast_bvadd_carry( args[0], args[1], args[2] );
   }else if( p==e_bblast_bvadd ){
      return f_bblast_bvadd( args[0], args[1], args[2] );
   }else if( p==e_bblast_zero ){
      return f_bblast_zero( args[0] );
   }else if( p==e_bblast_bvneg ){
      return f_bblast_bvneg( args[0], args[1] );
   }else if( p==e_reverse_help ){
      return f_reverse_help( args[0], args[1] );
   }else if( p==e_reverseb ){
      return f_reverseb( args[0] );
   }else if( p==e_top_k_bits ){
      return f_top_k_bits( args[0], args[1] );
   }else if( p==e_bottom_k_bits ){
      return f_bottom_k_bits( args[0], args[1] );
   }else if( p==e_k_bit ){
      return f_k_bit( args[0], args[1] );
   }else if( p==e_and_with_bit ){
      return f_and_with_bit( args[0], args[1] );
   }else if( p==e_mult_step_k_h ){
      return f_mult_step_k_h( args[0], args[1], args[2], args[3], args[4] );
   }else if( p==e_mult_step ){
      return f_mult_step( args[0], args[1], args[2], args[3], args[4] );
   }else if( p==e_bblast_bvmul ){
      return f_bblast_bvmul( args[0], args[1], args[2] );
   }else if( p==e_bblast_eq_rec ){
      return f_bblast_eq_rec( args[0], args[1], args[2] );
   }else if( p==e_bblast_eq ){
      return f_bblast_eq( args[0], args[1] );
   }else if( p==e_bblast_bvult ){
      return f_bblast_bvult( args[0], args[1], args[2] );
   }else if( p==e_bblast_bvslt ){
      return f_bblast_bvslt( args[0], args[1], args[2] );
   }else if( p==e_mk_ones ){
      return f_mk_ones( args[0] );
   }else if( p==e_mk_zero ){
      return f_mk_zero( args[0] );
   }else{
      return NULL;
   }
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

Expr* f_simplify_clause( Expr* c ){
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
   e4 = e_concat_cl;
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
      l->inc();
      Expr* e6 = l->followDefs()->get_head();
      Expr* e7;
      e7 = e_pos;
      e7->inc();
      Expr* e8;
      e8 = e_neg;
      e8->inc();
      if( e6==e7 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(0)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e9;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e9 = v;
            e9->inc();
            v->dec();
            e9->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         m->inc();
         Expr* e10 = m->followDefs()->get_head();
         Expr* e11;
         e11 = e_tt;
         e11->inc();
         Expr* e12;
         e12 = e_ff;
         e12->inc();
         if( e10==e11 ){
            Expr* e13;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(2)){
               e13 = v;
               e13->inc();
            }else{
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(2))
                  ((SymExpr*)v->followDefs())->clearmark(2);
               else
                  ((SymExpr*)v->followDefs())->setmark(2);
               e13 = v;
               e13->inc();
               v->dec();
            }
            v->dec();
            e13->dec();
            e0 = ch;
            e0->inc();
         }else if( e10==e12 ){
            Expr* e14;
            Expr* e15;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(2)){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(2))
                  ((SymExpr*)v->followDefs())->clearmark(2);
               else
                  ((SymExpr*)v->followDefs())->setmark(2);
               e15 = v;
               e15->inc();
               v->dec();
            }else{
               e15 = v;
               e15->inc();
            }
            v->dec();
            e15->dec();
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e14 = v;
            e14->inc();
            v->dec();
            e14->dec();
            l->inc();
            ch->inc();
            static Expr* e16;
            e16 = e_clc;
            e16->inc();
            e0 = new CExpr( APP, e16, l, ch );
         }else{
            std::cout << "Could not find match for expression in function f_simplify_clause ";
            e10->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         m->dec();
         e11->dec();
         e12->dec();
         ch->dec();
         m->dec();
      }else if( e6==e8 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(1)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e17;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1))
               ((SymExpr*)v->followDefs())->clearmark(1);
            else
               ((SymExpr*)v->followDefs())->setmark(1);
            e17 = v;
            e17->inc();
            v->dec();
            e17->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         m->inc();
         Expr* e18 = m->followDefs()->get_head();
         Expr* e19;
         e19 = e_tt;
         e19->inc();
         Expr* e20;
         e20 = e_ff;
         e20->inc();
         if( e18==e19 ){
            Expr* e21;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(3)){
               e21 = v;
               e21->inc();
            }else{
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(3))
                  ((SymExpr*)v->followDefs())->clearmark(3);
               else
                  ((SymExpr*)v->followDefs())->setmark(3);
               e21 = v;
               e21->inc();
               v->dec();
            }
            v->dec();
            e21->dec();
            e0 = ch;
            e0->inc();
         }else if( e18==e20 ){
            Expr* e22;
            Expr* e23;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(3)){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(3))
                  ((SymExpr*)v->followDefs())->clearmark(3);
               else
                  ((SymExpr*)v->followDefs())->setmark(3);
               e23 = v;
               e23->inc();
               v->dec();
            }else{
               e23 = v;
               e23->inc();
            }
            v->dec();
            e23->dec();
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1))
               ((SymExpr*)v->followDefs())->clearmark(1);
            else
               ((SymExpr*)v->followDefs())->setmark(1);
            e22 = v;
            e22->inc();
            v->dec();
            e22->dec();
            l->inc();
            ch->inc();
            static Expr* e24;
            e24 = e_clc;
            e24->inc();
            e0 = new CExpr( APP, e24, l, ch );
         }else{
            std::cout << "Could not find match for expression in function f_simplify_clause ";
            e18->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         m->dec();
         e19->dec();
         e20->dec();
         ch->dec();
         m->dec();
      }else{
         std::cout << "Could not find match for expression in function f_simplify_clause ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      l->dec();
      e7->dec();
      e8->dec();
   }else if( e1==e4 ){
      Expr* c1 = ((CExpr*)c->followDefs())->kids[1];
      Expr* c2 = ((CExpr*)c->followDefs())->kids[2];
      Expr* e25;
      c1->inc();
      e25 = f_simplify_clause( c1 );
      c1->dec();
      Expr* e26;
      c2->inc();
      e26 = f_simplify_clause( c2 );
      c2->dec();
      e0 = f_append( e25, e26 );
      e25->dec();
      e26->dec();
   }else if( e1==e5 ){
      Expr* l = ((CExpr*)c->followDefs())->kids[1];
      Expr* c1 = ((CExpr*)c->followDefs())->kids[2];
      l->inc();
      Expr* e27 = l->followDefs()->get_head();
      Expr* e28;
      e28 = e_pos;
      e28->inc();
      Expr* e29;
      e29 = e_neg;
      e29->inc();
      if( e27==e28 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(0)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e30;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e30 = v;
            e30->inc();
            v->dec();
            e30->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* m3;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(2)){
            Expr* e31;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(2))
               ((SymExpr*)v->followDefs())->clearmark(2);
            else
               ((SymExpr*)v->followDefs())->setmark(2);
            e31 = v;
            e31->inc();
            v->dec();
            e31->dec();
            m3 = e_tt;
            m3->inc();
         }else{
            m3 = e_ff;
            m3->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(2)){
            Expr* e32;
            Expr* e33;
            m3->inc();
            Expr* e34 = m3->followDefs()->get_head();
            Expr* e35;
            e35 = e_tt;
            e35->inc();
            Expr* e36;
            e36 = e_ff;
            e36->inc();
            if( e34==e35 ){
               e33 = v;
               e33->inc();
            }else if( e34==e36 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(2))
                  ((SymExpr*)v->followDefs())->clearmark(2);
               else
                  ((SymExpr*)v->followDefs())->setmark(2);
               e33 = v;
               e33->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e34->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m3->dec();
            e35->dec();
            e36->dec();
            e33->dec();
            m->inc();
            Expr* e37 = m->followDefs()->get_head();
            Expr* e38;
            e38 = e_tt;
            e38->inc();
            Expr* e39;
            e39 = e_ff;
            e39->inc();
            if( e37==e38 ){
               e32 = v;
               e32->inc();
            }else if( e37==e39 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(0))
                  ((SymExpr*)v->followDefs())->clearmark(0);
               else
                  ((SymExpr*)v->followDefs())->setmark(0);
               e32 = v;
               e32->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e37->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m->dec();
            e38->dec();
            e39->dec();
            e32->dec();
            e0 = ch;
            e0->inc();
         }else{
            e0 = NULL;
         }
         v->dec();
         ch->dec();
         m3->dec();
         m->dec();
      }else if( e27==e29 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m2;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(1)){
            m2 = e_tt;
            m2->inc();
         }else{
            Expr* e40;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1))
               ((SymExpr*)v->followDefs())->clearmark(1);
            else
               ((SymExpr*)v->followDefs())->setmark(1);
            e40 = v;
            e40->inc();
            v->dec();
            e40->dec();
            m2 = e_ff;
            m2->inc();
         }
         v->dec();
         Expr* m4;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(3)){
            Expr* e41;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(3))
               ((SymExpr*)v->followDefs())->clearmark(3);
            else
               ((SymExpr*)v->followDefs())->setmark(3);
            e41 = v;
            e41->inc();
            v->dec();
            e41->dec();
            m4 = e_tt;
            m4->inc();
         }else{
            m4 = e_ff;
            m4->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(3)){
            Expr* e42;
            Expr* e43;
            m4->inc();
            Expr* e44 = m4->followDefs()->get_head();
            Expr* e45;
            e45 = e_tt;
            e45->inc();
            Expr* e46;
            e46 = e_ff;
            e46->inc();
            if( e44==e45 ){
               e43 = v;
               e43->inc();
            }else if( e44==e46 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(3))
                  ((SymExpr*)v->followDefs())->clearmark(3);
               else
                  ((SymExpr*)v->followDefs())->setmark(3);
               e43 = v;
               e43->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e44->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m4->dec();
            e45->dec();
            e46->dec();
            e43->dec();
            m2->inc();
            Expr* e47 = m2->followDefs()->get_head();
            Expr* e48;
            e48 = e_tt;
            e48->inc();
            Expr* e49;
            e49 = e_ff;
            e49->inc();
            if( e47==e48 ){
               e42 = v;
               e42->inc();
            }else if( e47==e49 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(1))
                  ((SymExpr*)v->followDefs())->clearmark(1);
               else
                  ((SymExpr*)v->followDefs())->setmark(1);
               e42 = v;
               e42->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e47->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m2->dec();
            e48->dec();
            e49->dec();
            e42->dec();
            e0 = ch;
            e0->inc();
         }else{
            e0 = NULL;
         }
         v->dec();
         ch->dec();
         m4->dec();
         m2->dec();
      }else{
         std::cout << "Could not find match for expression in function f_simplify_clause ";
         e27->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      l->dec();
      e28->dec();
      e29->dec();
   }else{
      std::cout << "Could not find match for expression in function f_simplify_clause ";
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

Expr* f_mpz_sub( Expr* x, Expr* y ){
   Expr* e0;
   x->inc();
   Expr* e1;
   Expr* e2;
   e2 = new IntExpr( -1 );
   e2->inc();
   y->inc();
   if( e2->followDefs()->getclass()==INT_EXPR ){
      mpz_t rnum0;
      mpz_init(rnum0);
      mpz_mul( rnum0, ((IntExpr*)e2->followDefs())->n, ((IntExpr*)y->followDefs())->n);
      e1 = new IntExpr(rnum0);
   }else if( e2->followDefs()->getclass()==RAT_EXPR ){
      mpq_t rnum0;
      mpq_init(rnum0);
      mpq_mul( rnum0, ((RatExpr*)e2->followDefs())->n, ((RatExpr*)y->followDefs())->n);
      e1 = new RatExpr(rnum0);
   }
   e2->dec();
   y->dec();
   if( x->followDefs()->getclass()==INT_EXPR ){
      mpz_t rnum1;
      mpz_init(rnum1);
      mpz_add( rnum1, ((IntExpr*)x->followDefs())->n, ((IntExpr*)e1->followDefs())->n);
      e0 = new IntExpr(rnum1);
   }else if( x->followDefs()->getclass()==RAT_EXPR ){
      mpq_t rnum1;
      mpq_init(rnum1);
      mpq_add( rnum1, ((RatExpr*)x->followDefs())->n, ((RatExpr*)e1->followDefs())->n);
      e0 = new RatExpr(rnum1);
   }
   x->dec();
   e1->dec();
   return e0;
}

Expr* f_mp_ispos( Expr* x ){
   Expr* e0;
   x->inc();
   if( x->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)x->followDefs())->n ) < 0 ){
         e0 = e_false;
         e0->inc();
      }else{
         e0 = e_true;
         e0->inc();
      }
   }else if( x->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)x->followDefs())->n ) < 0 ){
         e0 = e_false;
         e0->inc();
      }else{
         e0 = e_true;
         e0->inc();
      }
   }
   x->dec();
   return e0;
}

Expr* f_mpz_eq( Expr* x, Expr* y ){
   Expr* e0;
   Expr* e1;
   x->inc();
   y->inc();
   e1 = f_mpz_sub( x, y );
   x->dec();
   y->dec();
   if( e1->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)e1->followDefs())->n ) == 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         e0 = e_false;
         e0->inc();
      }
   }else if( e1->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)e1->followDefs())->n ) == 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         e0 = e_false;
         e0->inc();
      }
   }
   e1->dec();
   return e0;
}

Expr* f_mpz_lt( Expr* x, Expr* y ){
   Expr* e0;
   Expr* e1;
   x->inc();
   y->inc();
   e1 = f_mpz_sub( x, y );
   x->dec();
   y->dec();
   if( e1->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)e1->followDefs())->n ) < 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         e0 = e_false;
         e0->inc();
      }
   }else if( e1->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)e1->followDefs())->n ) < 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         e0 = e_false;
         e0->inc();
      }
   }
   e1->dec();
   return e0;
}

Expr* f_mpz_lte( Expr* x, Expr* y ){
   Expr* e0;
   Expr* e1;
   x->inc();
   y->inc();
   e1 = f_mpz_sub( x, y );
   x->dec();
   y->dec();
   if( e1->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)e1->followDefs())->n ) < 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         x->inc();
         y->inc();
         e0 = f_mpz_eq( x, y );
         x->dec();
         y->dec();
      }
   }else if( e1->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)e1->followDefs())->n ) < 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         x->inc();
         y->inc();
         e0 = f_mpz_eq( x, y );
         x->dec();
         y->dec();
      }
   }
   e1->dec();
   return e0;
}

Expr* f_mpz_( Expr* x, Expr* y ){
   Expr* e0;
   Expr* e1;
   x->inc();
   y->inc();
   e1 = f_mpz_sub( x, y );
   x->dec();
   y->dec();
   if( e1->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)e1->followDefs())->n ) == 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         e0 = e_false;
         e0->inc();
      }
   }else if( e1->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)e1->followDefs())->n ) == 0 ){
         e0 = e_true;
         e0->inc();
      }else{
         e0 = e_false;
         e0->inc();
      }
   }
   e1->dec();
   return e0;
}

Expr* f_bblt_len( Expr* v ){
   Expr* e0;
   v->inc();
   Expr* e1 = v->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
     e0 = new IntExpr( (long int)0 );
      e0->inc();
   }else if( e1==e3 ){
      Expr* b = ((CExpr*)v->followDefs())->kids[1];
      Expr* vh = ((CExpr*)v->followDefs())->kids[2];
      Expr* e4;
      vh->inc();
      e4 = f_bblt_len( vh );
      vh->dec();
      Expr* e5;
      e5 = new IntExpr( 1 );
      e5->inc();
      if( e4->followDefs()->getclass()==INT_EXPR ){
         mpz_t rnum0;
         mpz_init(rnum0);
         mpz_add( rnum0, ((IntExpr*)e4->followDefs())->n, ((IntExpr*)e5->followDefs())->n);
         e0 = new IntExpr(rnum0);
      }else if( e4->followDefs()->getclass()==RAT_EXPR ){
         mpq_t rnum0;
         mpq_init(rnum0);
         mpq_add( rnum0, ((RatExpr*)e4->followDefs())->n, ((RatExpr*)e5->followDefs())->n);
         e0 = new RatExpr(rnum0);
      }
      e4->dec();
      e5->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblt_len ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   v->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_const( Expr* v, Expr* n ){
   Expr* e0;
   n->inc();
   if( n->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)n->followDefs())->n ) < 0 ){
         v->inc();
         Expr* e1 = v->followDefs()->get_head();
         Expr* e2;
         e2 = e_bvn;
         e2->inc();
         if( e1==e2 ){
            e0 = e_bbltn;
            e0->inc();
         }else{
            e0 = NULL;
         }
         v->dec();
         e2->dec();
      }else{
         v->inc();
         Expr* e3 = v->followDefs()->get_head();
         Expr* e4;
         e4 = e_bvc;
         e4->inc();
         if( e3==e4 ){
            Expr* b = ((CExpr*)v->followDefs())->kids[1];
            Expr* vh = ((CExpr*)v->followDefs())->kids[2];
            Expr* e5;
            b->inc();
            Expr* e6 = b->followDefs()->get_head();
            Expr* e7;
            e7 = e_b0;
            e7->inc();
            Expr* e8;
            e8 = e_b1;
            e8->inc();
            if( e6==e7 ){
               e5 = e_false;
               e5->inc();
            }else if( e6==e8 ){
               e5 = e_true;
               e5->inc();
            }else{
               std::cout << "Could not find match for expression in function f_bblast_const ";
               e6->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            b->dec();
            e7->dec();
            e8->dec();
            Expr* e9;
            vh->inc();
            Expr* e10;
            n->inc();
            Expr* e11;
            e11 = new IntExpr( -1 );
            e11->inc();
            if( n->followDefs()->getclass()==INT_EXPR ){
               mpz_t rnum0;
               mpz_init(rnum0);
               mpz_add( rnum0, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e11->followDefs())->n);
               e10 = new IntExpr(rnum0);
            }else if( n->followDefs()->getclass()==RAT_EXPR ){
               mpq_t rnum0;
               mpq_init(rnum0);
               mpq_add( rnum0, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e11->followDefs())->n);
               e10 = new RatExpr(rnum0);
            }
            n->dec();
            e11->dec();
            e9 = f_bblast_const( vh, e10 );
            vh->dec();
            e10->dec();
            static Expr* e12;
            e12 = e_bbltc;
            e12->inc();
            e0 = new CExpr( APP, e12, e5, e9 );
         }else{
            e0 = NULL;
         }
         v->dec();
         e4->dec();
      }
   }else if( n->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)n->followDefs())->n ) < 0 ){
         v->inc();
         Expr* e13 = v->followDefs()->get_head();
         Expr* e14;
         e14 = e_bvn;
         e14->inc();
         if( e13==e14 ){
            e0 = e_bbltn;
            e0->inc();
         }else{
            e0 = NULL;
         }
         v->dec();
         e14->dec();
      }else{
         v->inc();
         Expr* e15 = v->followDefs()->get_head();
         Expr* e16;
         e16 = e_bvc;
         e16->inc();
         if( e15==e16 ){
            Expr* b = ((CExpr*)v->followDefs())->kids[1];
            Expr* vh = ((CExpr*)v->followDefs())->kids[2];
            Expr* e17;
            b->inc();
            Expr* e18 = b->followDefs()->get_head();
            Expr* e19;
            e19 = e_b0;
            e19->inc();
            Expr* e20;
            e20 = e_b1;
            e20->inc();
            if( e18==e19 ){
               e17 = e_false;
               e17->inc();
            }else if( e18==e20 ){
               e17 = e_true;
               e17->inc();
            }else{
               std::cout << "Could not find match for expression in function f_bblast_const ";
               e18->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            b->dec();
            e19->dec();
            e20->dec();
            Expr* e21;
            vh->inc();
            Expr* e22;
            n->inc();
            Expr* e23;
            e23 = new IntExpr( -1 );
            e23->inc();
            if( n->followDefs()->getclass()==INT_EXPR ){
               mpz_t rnum1;
               mpz_init(rnum1);
               mpz_add( rnum1, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e23->followDefs())->n);
               e22 = new IntExpr(rnum1);
            }else if( n->followDefs()->getclass()==RAT_EXPR ){
               mpq_t rnum1;
               mpq_init(rnum1);
               mpq_add( rnum1, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e23->followDefs())->n);
               e22 = new RatExpr(rnum1);
            }
            n->dec();
            e23->dec();
            e21 = f_bblast_const( vh, e22 );
            vh->dec();
            e22->dec();
            static Expr* e24;
            e24 = e_bbltc;
            e24->inc();
            e0 = new CExpr( APP, e24, e17, e21 );
         }else{
            e0 = NULL;
         }
         v->dec();
         e16->dec();
      }
   }
   n->dec();
   return e0;
}

Expr* f_bblast_var( Expr* x, Expr* n ){
   Expr* e0;
   n->inc();
   if( n->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)n->followDefs())->n ) < 0 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         Expr* e1;
         x->inc();
         n->inc();
         static Expr* e2;
         e2 = e_bitof;
         e2->inc();
         e1 = new CExpr( APP, e2, x, n );
         Expr* e3;
         x->inc();
         Expr* e4;
         n->inc();
         Expr* e5;
         e5 = new IntExpr( -1 );
         e5->inc();
         if( n->followDefs()->getclass()==INT_EXPR ){
            mpz_t rnum0;
            mpz_init(rnum0);
            mpz_add( rnum0, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e5->followDefs())->n);
            e4 = new IntExpr(rnum0);
         }else if( n->followDefs()->getclass()==RAT_EXPR ){
            mpq_t rnum0;
            mpq_init(rnum0);
            mpq_add( rnum0, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e5->followDefs())->n);
            e4 = new RatExpr(rnum0);
         }
         n->dec();
         e5->dec();
         e3 = f_bblast_var( x, e4 );
         x->dec();
         e4->dec();
         static Expr* e6;
         e6 = e_bbltc;
         e6->inc();
         e0 = new CExpr( APP, e6, e1, e3 );
      }
   }else if( n->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)n->followDefs())->n ) < 0 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         Expr* e7;
         x->inc();
         n->inc();
         static Expr* e8;
         e8 = e_bitof;
         e8->inc();
         e7 = new CExpr( APP, e8, x, n );
         Expr* e9;
         x->inc();
         Expr* e10;
         n->inc();
         Expr* e11;
         e11 = new IntExpr( -1 );
         e11->inc();
         if( n->followDefs()->getclass()==INT_EXPR ){
            mpz_t rnum1;
            mpz_init(rnum1);
            mpz_add( rnum1, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e11->followDefs())->n);
            e10 = new IntExpr(rnum1);
         }else if( n->followDefs()->getclass()==RAT_EXPR ){
            mpq_t rnum1;
            mpq_init(rnum1);
            mpq_add( rnum1, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e11->followDefs())->n);
            e10 = new RatExpr(rnum1);
         }
         n->dec();
         e11->dec();
         e9 = f_bblast_var( x, e10 );
         x->dec();
         e10->dec();
         static Expr* e12;
         e12 = e_bbltc;
         e12->inc();
         e0 = new CExpr( APP, e12, e7, e9 );
      }
   }
   n->dec();
   return e0;
}

Expr* f_bblast_concat( Expr* x, Expr* y ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      y->inc();
      Expr* e4 = y->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltc;
      e5->inc();
      Expr* e6;
      e6 = e_bbltn;
      e6->inc();
      if( e4==e5 ){
         Expr* by = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         by->inc();
         Expr* e7;
         x->inc();
         yh->inc();
         e7 = f_bblast_concat( x, yh );
         x->dec();
         yh->dec();
         static Expr* e8;
         e8 = e_bbltc;
         e8->inc();
         e0 = new CExpr( APP, e8, by, e7 );
      }else if( e4==e6 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         std::cout << "Could not find match for expression in function f_bblast_concat ";
         e4->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      y->dec();
      e5->dec();
      e6->dec();
   }else if( e1==e3 ){
      Expr* bx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      bx->inc();
      Expr* e9;
      xh->inc();
      y->inc();
      e9 = f_bblast_concat( xh, y );
      xh->dec();
      y->dec();
      static Expr* e10;
      e10 = e_bbltc;
      e10->inc();
      e0 = new CExpr( APP, e10, bx, e9 );
   }else{
      std::cout << "Could not find match for expression in function f_bblast_concat ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_extract_rec( Expr* x, Expr* i, Expr* j, Expr* n ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltc;
   e2->inc();
   Expr* e3;
   e3 = e_bbltn;
   e3->inc();
   if( e1==e2 ){
      Expr* bx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      Expr* e4;
      Expr* e5;
      j->inc();
      n->inc();
      e5 = f_mpz_sub( j, n );
      j->dec();
      n->dec();
      Expr* e6;
      e6 = new IntExpr( 1 );
      e6->inc();
      e4 = f_mpz_sub( e5, e6 );
      e5->dec();
      e6->dec();
      if( e4->followDefs()->getclass()==INT_EXPR ){
         if( mpz_sgn( ((IntExpr *)e4->followDefs())->n ) < 0 ){
            Expr* e7;
            Expr* e8;
            n->inc();
            i->inc();
            e8 = f_mpz_sub( n, i );
            n->dec();
            i->dec();
            Expr* e9;
            e9 = new IntExpr( 1 );
            e9->inc();
            e7 = f_mpz_sub( e8, e9 );
            e8->dec();
            e9->dec();
            if( e7->followDefs()->getclass()==INT_EXPR ){
               if( mpz_sgn( ((IntExpr *)e7->followDefs())->n ) < 0 ){
                  bx->inc();
                  Expr* e10;
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e11;
                  n->inc();
                  Expr* e12;
                  e12 = new IntExpr( 1 );
                  e12->inc();
                  e11 = f_mpz_sub( n, e12 );
                  n->dec();
                  e12->dec();
                  e10 = f_bblast_extract_rec( xh, i, j, e11 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e11->dec();
                  static Expr* e13;
                  e13 = e_bbltc;
                  e13->inc();
                  e0 = new CExpr( APP, e13, bx, e10 );
               }else{
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e14;
                  n->inc();
                  Expr* e15;
                  e15 = new IntExpr( 1 );
                  e15->inc();
                  e14 = f_mpz_sub( n, e15 );
                  n->dec();
                  e15->dec();
                  e0 = f_bblast_extract_rec( xh, i, j, e14 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e14->dec();
               }
            }else if( e7->followDefs()->getclass()==RAT_EXPR ){
               if( mpq_sgn( ((RatExpr *)e7->followDefs())->n ) < 0 ){
                  bx->inc();
                  Expr* e16;
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e17;
                  n->inc();
                  Expr* e18;
                  e18 = new IntExpr( 1 );
                  e18->inc();
                  e17 = f_mpz_sub( n, e18 );
                  n->dec();
                  e18->dec();
                  e16 = f_bblast_extract_rec( xh, i, j, e17 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e17->dec();
                  static Expr* e19;
                  e19 = e_bbltc;
                  e19->inc();
                  e0 = new CExpr( APP, e19, bx, e16 );
               }else{
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e20;
                  n->inc();
                  Expr* e21;
                  e21 = new IntExpr( 1 );
                  e21->inc();
                  e20 = f_mpz_sub( n, e21 );
                  n->dec();
                  e21->dec();
                  e0 = f_bblast_extract_rec( xh, i, j, e20 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e20->dec();
               }
            }
            e7->dec();
         }else{
            e0 = e_bbltn;
            e0->inc();
         }
      }else if( e4->followDefs()->getclass()==RAT_EXPR ){
         if( mpq_sgn( ((RatExpr *)e4->followDefs())->n ) < 0 ){
            Expr* e22;
            Expr* e23;
            n->inc();
            i->inc();
            e23 = f_mpz_sub( n, i );
            n->dec();
            i->dec();
            Expr* e24;
            e24 = new IntExpr( 1 );
            e24->inc();
            e22 = f_mpz_sub( e23, e24 );
            e23->dec();
            e24->dec();
            if( e22->followDefs()->getclass()==INT_EXPR ){
               if( mpz_sgn( ((IntExpr *)e22->followDefs())->n ) < 0 ){
                  bx->inc();
                  Expr* e25;
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e26;
                  n->inc();
                  Expr* e27;
                  e27 = new IntExpr( 1 );
                  e27->inc();
                  e26 = f_mpz_sub( n, e27 );
                  n->dec();
                  e27->dec();
                  e25 = f_bblast_extract_rec( xh, i, j, e26 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e26->dec();
                  static Expr* e28;
                  e28 = e_bbltc;
                  e28->inc();
                  e0 = new CExpr( APP, e28, bx, e25 );
               }else{
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e29;
                  n->inc();
                  Expr* e30;
                  e30 = new IntExpr( 1 );
                  e30->inc();
                  e29 = f_mpz_sub( n, e30 );
                  n->dec();
                  e30->dec();
                  e0 = f_bblast_extract_rec( xh, i, j, e29 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e29->dec();
               }
            }else if( e22->followDefs()->getclass()==RAT_EXPR ){
               if( mpq_sgn( ((RatExpr *)e22->followDefs())->n ) < 0 ){
                  bx->inc();
                  Expr* e31;
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e32;
                  n->inc();
                  Expr* e33;
                  e33 = new IntExpr( 1 );
                  e33->inc();
                  e32 = f_mpz_sub( n, e33 );
                  n->dec();
                  e33->dec();
                  e31 = f_bblast_extract_rec( xh, i, j, e32 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e32->dec();
                  static Expr* e34;
                  e34 = e_bbltc;
                  e34->inc();
                  e0 = new CExpr( APP, e34, bx, e31 );
               }else{
                  xh->inc();
                  i->inc();
                  j->inc();
                  Expr* e35;
                  n->inc();
                  Expr* e36;
                  e36 = new IntExpr( 1 );
                  e36->inc();
                  e35 = f_mpz_sub( n, e36 );
                  n->dec();
                  e36->dec();
                  e0 = f_bblast_extract_rec( xh, i, j, e35 );
                  xh->dec();
                  i->dec();
                  j->dec();
                  e35->dec();
               }
            }
            e22->dec();
         }else{
            e0 = e_bbltn;
            e0->inc();
         }
      }
      e4->dec();
   }else if( e1==e3 ){
      e0 = e_bbltn;
      e0->inc();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_extract_rec ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_extract( Expr* x, Expr* i, Expr* j, Expr* n ){
   Expr* e0;
   x->inc();
   i->inc();
   j->inc();
   Expr* e1;
   n->inc();
   Expr* e2;
   e2 = new IntExpr( 1 );
   e2->inc();
   e1 = f_mpz_sub( n, e2 );
   n->dec();
   e2->dec();
   e0 = f_bblast_extract_rec( x, i, j, e1 );
   x->dec();
   i->dec();
   j->dec();
   e1->dec();
   return e0;
}

Expr* f_extend_rec( Expr* x, Expr* i, Expr* b ){
   Expr* e0;
   i->inc();
   if( i->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)i->followDefs())->n ) < 0 ){
         e0 = x;
         e0->inc();
      }else{
         b->inc();
         Expr* e1;
         x->inc();
         Expr* e2;
         i->inc();
         Expr* e3;
         e3 = new IntExpr( 1 );
         e3->inc();
         e2 = f_mpz_sub( i, e3 );
         i->dec();
         e3->dec();
         b->inc();
         e1 = f_extend_rec( x, e2, b );
         x->dec();
         e2->dec();
         b->dec();
         static Expr* e4;
         e4 = e_bbltc;
         e4->inc();
         e0 = new CExpr( APP, e4, b, e1 );
      }
   }else if( i->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)i->followDefs())->n ) < 0 ){
         e0 = x;
         e0->inc();
      }else{
         b->inc();
         Expr* e5;
         x->inc();
         Expr* e6;
         i->inc();
         Expr* e7;
         e7 = new IntExpr( 1 );
         e7->inc();
         e6 = f_mpz_sub( i, e7 );
         i->dec();
         e7->dec();
         b->inc();
         e5 = f_extend_rec( x, e6, b );
         x->dec();
         e6->dec();
         b->dec();
         static Expr* e8;
         e8 = e_bbltc;
         e8->inc();
         e0 = new CExpr( APP, e8, b, e5 );
      }
   }
   i->dec();
   return e0;
}

Expr* f_bblast_zextend( Expr* x, Expr* i ){
   Expr* e0;
   x->inc();
   Expr* e1;
   i->inc();
   Expr* e2;
   e2 = new IntExpr( 1 );
   e2->inc();
   e1 = f_mpz_sub( i, e2 );
   i->dec();
   e2->dec();
   static Expr* e3;
   e3 = e_false;
   e3->inc();
   e0 = f_extend_rec( x, e1, e3 );
   x->dec();
   e1->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_sextend( Expr* x, Expr* i ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      e0 = NULL;
   }else if( e1==e3 ){
      Expr* xb = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      x->inc();
      Expr* e4;
      i->inc();
      Expr* e5;
      e5 = new IntExpr( 1 );
      e5->inc();
      e4 = f_mpz_sub( i, e5 );
      i->dec();
      e5->dec();
      xb->inc();
      e0 = f_extend_rec( x, e4, xb );
      x->dec();
      e4->dec();
      xb->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_sextend ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_bvand( Expr* x, Expr* y ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      y->inc();
      Expr* e4 = y->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      if( e4==e5 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         e0 = NULL;
      }
      y->dec();
      e5->dec();
   }else if( e1==e3 ){
      Expr* bx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      y->inc();
      Expr* e6 = y->followDefs()->get_head();
      Expr* e7;
      e7 = e_bbltn;
      e7->inc();
      Expr* e8;
      e8 = e_bbltc;
      e8->inc();
      if( e6==e7 ){
         e0 = NULL;
      }else if( e6==e8 ){
         Expr* by = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         Expr* e9;
         bx->inc();
         by->inc();
         static Expr* e10;
         e10 = e_and;
         e10->inc();
         e9 = new CExpr( APP, e10, bx, by );
         Expr* e11;
         xh->inc();
         yh->inc();
         e11 = f_bblast_bvand( xh, yh );
         xh->dec();
         yh->dec();
         static Expr* e12;
         e12 = e_bbltc;
         e12->inc();
         e0 = new CExpr( APP, e12, e9, e11 );
      }else{
         std::cout << "Could not find match for expression in function f_bblast_bvand ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      y->dec();
      e7->dec();
      e8->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvand ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_bvnot( Expr* x ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      e0 = e_bbltn;
      e0->inc();
   }else if( e1==e3 ){
      Expr* bx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      Expr* e4;
      bx->inc();
      static Expr* e5;
      e5 = e_not;
      e5->inc();
      e4 = new CExpr( APP, e5, bx );
      Expr* e6;
      xh->inc();
      e6 = f_bblast_bvnot( xh );
      xh->dec();
      static Expr* e7;
      e7 = e_bbltc;
      e7->inc();
      e0 = new CExpr( APP, e7, e4, e6 );
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvnot ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_bvor( Expr* x, Expr* y ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      y->inc();
      Expr* e4 = y->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      if( e4==e5 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         e0 = NULL;
      }
      y->dec();
      e5->dec();
   }else if( e1==e3 ){
      Expr* bx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      y->inc();
      Expr* e6 = y->followDefs()->get_head();
      Expr* e7;
      e7 = e_bbltn;
      e7->inc();
      Expr* e8;
      e8 = e_bbltc;
      e8->inc();
      if( e6==e7 ){
         e0 = NULL;
      }else if( e6==e8 ){
         Expr* by = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         Expr* e9;
         bx->inc();
         by->inc();
         static Expr* e10;
         e10 = e_or;
         e10->inc();
         e9 = new CExpr( APP, e10, bx, by );
         Expr* e11;
         xh->inc();
         yh->inc();
         e11 = f_bblast_bvor( xh, yh );
         xh->dec();
         yh->dec();
         static Expr* e12;
         e12 = e_bbltc;
         e12->inc();
         e0 = new CExpr( APP, e12, e9, e11 );
      }else{
         std::cout << "Could not find match for expression in function f_bblast_bvor ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      y->dec();
      e7->dec();
      e8->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvor ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_bvxor( Expr* x, Expr* y ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      y->inc();
      Expr* e4 = y->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      if( e4==e5 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         e0 = NULL;
      }
      y->dec();
      e5->dec();
   }else if( e1==e3 ){
      Expr* bx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      y->inc();
      Expr* e6 = y->followDefs()->get_head();
      Expr* e7;
      e7 = e_bbltn;
      e7->inc();
      Expr* e8;
      e8 = e_bbltc;
      e8->inc();
      if( e6==e7 ){
         e0 = NULL;
      }else if( e6==e8 ){
         Expr* by = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         Expr* e9;
         bx->inc();
         by->inc();
         static Expr* e10;
         e10 = e_xor;
         e10->inc();
         e9 = new CExpr( APP, e10, bx, by );
         Expr* e11;
         xh->inc();
         yh->inc();
         e11 = f_bblast_bvxor( xh, yh );
         xh->dec();
         yh->dec();
         static Expr* e12;
         e12 = e_bbltc;
         e12->inc();
         e0 = new CExpr( APP, e12, e9, e11 );
      }else{
         std::cout << "Could not find match for expression in function f_bblast_bvxor ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      y->dec();
      e7->dec();
      e8->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvxor ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_bvadd_carry( Expr* a, Expr* b, Expr* carry ){
   Expr* e0;
   a->inc();
   Expr* e1 = a->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      b->inc();
      Expr* e4 = b->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      if( e4==e5 ){
         e0 = carry;
         e0->inc();
      }else{
         e0 = NULL;
      }
      b->dec();
      e5->dec();
   }else if( e1==e3 ){
      Expr* ai = ((CExpr*)a->followDefs())->kids[1];
      Expr* ah = ((CExpr*)a->followDefs())->kids[2];
      b->inc();
      Expr* e6 = b->followDefs()->get_head();
      Expr* e7;
      e7 = e_bbltn;
      e7->inc();
      Expr* e8;
      e8 = e_bbltc;
      e8->inc();
      if( e6==e7 ){
         e0 = NULL;
      }else if( e6==e8 ){
         Expr* bi = ((CExpr*)b->followDefs())->kids[1];
         Expr* bh = ((CExpr*)b->followDefs())->kids[2];
         Expr* e9;
         ai->inc();
         bi->inc();
         static Expr* e10;
         e10 = e_and;
         e10->inc();
         e9 = new CExpr( APP, e10, ai, bi );
         Expr* e11;
         Expr* e12;
         ai->inc();
         bi->inc();
         static Expr* e13;
         e13 = e_xor;
         e13->inc();
         e12 = new CExpr( APP, e13, ai, bi );
         Expr* e14;
         ah->inc();
         bh->inc();
         carry->inc();
         e14 = f_bblast_bvadd_carry( ah, bh, carry );
         ah->dec();
         bh->dec();
         carry->dec();
         static Expr* e15;
         e15 = e_and;
         e15->inc();
         e11 = new CExpr( APP, e15, e12, e14 );
         static Expr* e16;
         e16 = e_or;
         e16->inc();
         e0 = new CExpr( APP, e16, e9, e11 );
      }else{
         std::cout << "Could not find match for expression in function f_bblast_bvadd_carry ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      b->dec();
      e7->dec();
      e8->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvadd_carry ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   a->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_bvadd( Expr* a, Expr* b, Expr* carry ){
   Expr* e0;
   a->inc();
   Expr* e1 = a->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      b->inc();
      Expr* e4 = b->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      if( e4==e5 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         e0 = NULL;
      }
      b->dec();
      e5->dec();
   }else if( e1==e3 ){
      Expr* ai = ((CExpr*)a->followDefs())->kids[1];
      Expr* ah = ((CExpr*)a->followDefs())->kids[2];
      b->inc();
      Expr* e6 = b->followDefs()->get_head();
      Expr* e7;
      e7 = e_bbltn;
      e7->inc();
      Expr* e8;
      e8 = e_bbltc;
      e8->inc();
      if( e6==e7 ){
         e0 = NULL;
      }else if( e6==e8 ){
         Expr* bi = ((CExpr*)b->followDefs())->kids[1];
         Expr* bh = ((CExpr*)b->followDefs())->kids[2];
         Expr* e9;
         Expr* e10;
         ai->inc();
         bi->inc();
         static Expr* e11;
         e11 = e_xor;
         e11->inc();
         e10 = new CExpr( APP, e11, ai, bi );
         Expr* e12;
         ah->inc();
         bh->inc();
         carry->inc();
         e12 = f_bblast_bvadd_carry( ah, bh, carry );
         ah->dec();
         bh->dec();
         carry->dec();
         static Expr* e13;
         e13 = e_xor;
         e13->inc();
         e9 = new CExpr( APP, e13, e10, e12 );
         Expr* e14;
         ah->inc();
         bh->inc();
         carry->inc();
         e14 = f_bblast_bvadd( ah, bh, carry );
         ah->dec();
         bh->dec();
         carry->dec();
         static Expr* e15;
         e15 = e_bbltc;
         e15->inc();
         e0 = new CExpr( APP, e15, e9, e14 );
      }else{
         std::cout << "Could not find match for expression in function f_bblast_bvadd ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      b->dec();
      e7->dec();
      e8->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvadd ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   a->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_zero( Expr* n ){
   Expr* e0;
   n->inc();
   if( n->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)n->followDefs())->n ) == 0 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         static Expr* e1;
         e1 = e_false;
         e1->inc();
         Expr* e2;
         Expr* e3;
         n->inc();
         Expr* e4;
         e4 = new IntExpr( -1 );
         e4->inc();
         if( n->followDefs()->getclass()==INT_EXPR ){
            mpz_t rnum0;
            mpz_init(rnum0);
            mpz_add( rnum0, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e4->followDefs())->n);
            e3 = new IntExpr(rnum0);
         }else if( n->followDefs()->getclass()==RAT_EXPR ){
            mpq_t rnum0;
            mpq_init(rnum0);
            mpq_add( rnum0, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e4->followDefs())->n);
            e3 = new RatExpr(rnum0);
         }
         n->dec();
         e4->dec();
         e2 = f_bblast_zero( e3 );
         e3->dec();
         static Expr* e5;
         e5 = e_bbltc;
         e5->inc();
         e0 = new CExpr( APP, e5, e1, e2 );
      }
   }else if( n->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)n->followDefs())->n ) == 0 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         static Expr* e6;
         e6 = e_false;
         e6->inc();
         Expr* e7;
         Expr* e8;
         n->inc();
         Expr* e9;
         e9 = new IntExpr( -1 );
         e9->inc();
         if( n->followDefs()->getclass()==INT_EXPR ){
            mpz_t rnum1;
            mpz_init(rnum1);
            mpz_add( rnum1, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e9->followDefs())->n);
            e8 = new IntExpr(rnum1);
         }else if( n->followDefs()->getclass()==RAT_EXPR ){
            mpq_t rnum1;
            mpq_init(rnum1);
            mpq_add( rnum1, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e9->followDefs())->n);
            e8 = new RatExpr(rnum1);
         }
         n->dec();
         e9->dec();
         e7 = f_bblast_zero( e8 );
         e8->dec();
         static Expr* e10;
         e10 = e_bbltc;
         e10->inc();
         e0 = new CExpr( APP, e10, e6, e7 );
      }
   }
   n->dec();
   return e0;
}

Expr* f_bblast_bvneg( Expr* x, Expr* n ){
   Expr* e0;
   Expr* e1;
   x->inc();
   e1 = f_bblast_bvnot( x );
   x->dec();
   Expr* e2;
   n->inc();
   e2 = f_bblast_zero( n );
   n->dec();
   static Expr* e3;
   e3 = e_true;
   e3->inc();
   e0 = f_bblast_bvadd( e1, e2, e3 );
   e1->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_reverse_help( Expr* x, Expr* acc ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      e0 = acc;
      e0->inc();
   }else if( e1==e3 ){
      Expr* xi = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      xh->inc();
      Expr* e4;
      xi->inc();
      acc->inc();
      static Expr* e5;
      e5 = e_bbltc;
      e5->inc();
      e4 = new CExpr( APP, e5, xi, acc );
      e0 = f_reverse_help( xh, e4 );
      xh->dec();
      e4->dec();
   }else{
      std::cout << "Could not find match for expression in function f_reverse_help ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_reverseb( Expr* x ){
   Expr* e0;
   x->inc();
   static Expr* e1;
   e1 = e_bbltn;
   e1->inc();
   e0 = f_reverse_help( x, e1 );
   x->dec();
   e1->dec();
   return e0;
}

Expr* f_top_k_bits( Expr* a, Expr* k ){
   Expr* e0;
   k->inc();
   if( k->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         a->inc();
         Expr* e1 = a->followDefs()->get_head();
         Expr* e2;
         e2 = e_bbltn;
         e2->inc();
         Expr* e3;
         e3 = e_bbltc;
         e3->inc();
         if( e1==e2 ){
            e0 = NULL;
         }else if( e1==e3 ){
            Expr* ai = ((CExpr*)a->followDefs())->kids[1];
            Expr* ah = ((CExpr*)a->followDefs())->kids[2];
            ai->inc();
            Expr* e4;
            ah->inc();
            Expr* e5;
            k->inc();
            Expr* e6;
            e6 = new IntExpr( 1 );
            e6->inc();
            e5 = f_mpz_sub( k, e6 );
            k->dec();
            e6->dec();
            e4 = f_top_k_bits( ah, e5 );
            ah->dec();
            e5->dec();
            static Expr* e7;
            e7 = e_bbltc;
            e7->inc();
            e0 = new CExpr( APP, e7, ai, e4 );
         }else{
            std::cout << "Could not find match for expression in function f_top_k_bits ";
            e1->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         a->dec();
         e2->dec();
         e3->dec();
      }
   }else if( k->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
         e0 = e_bbltn;
         e0->inc();
      }else{
         a->inc();
         Expr* e8 = a->followDefs()->get_head();
         Expr* e9;
         e9 = e_bbltn;
         e9->inc();
         Expr* e10;
         e10 = e_bbltc;
         e10->inc();
         if( e8==e9 ){
            e0 = NULL;
         }else if( e8==e10 ){
            Expr* ai = ((CExpr*)a->followDefs())->kids[1];
            Expr* ah = ((CExpr*)a->followDefs())->kids[2];
            ai->inc();
            Expr* e11;
            ah->inc();
            Expr* e12;
            k->inc();
            Expr* e13;
            e13 = new IntExpr( 1 );
            e13->inc();
            e12 = f_mpz_sub( k, e13 );
            k->dec();
            e13->dec();
            e11 = f_top_k_bits( ah, e12 );
            ah->dec();
            e12->dec();
            static Expr* e14;
            e14 = e_bbltc;
            e14->inc();
            e0 = new CExpr( APP, e14, ai, e11 );
         }else{
            std::cout << "Could not find match for expression in function f_top_k_bits ";
            e8->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         a->dec();
         e9->dec();
         e10->dec();
      }
   }
   k->dec();
   return e0;
}

Expr* f_bottom_k_bits( Expr* a, Expr* k ){
   Expr* e0;
   Expr* e1;
   Expr* e2;
   a->inc();
   e2 = f_reverseb( a );
   a->dec();
   k->inc();
   e1 = f_top_k_bits( e2, k );
   e2->dec();
   k->dec();
   e0 = f_reverseb( e1 );
   e1->dec();
   return e0;
}

Expr* f_k_bit( Expr* a, Expr* k ){
   Expr* e0;
   k->inc();
   if( k->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         a->inc();
         Expr* e1 = a->followDefs()->get_head();
         Expr* e2;
         e2 = e_bbltn;
         e2->inc();
         Expr* e3;
         e3 = e_bbltc;
         e3->inc();
         if( e1==e2 ){
            e0 = NULL;
         }else if( e1==e3 ){
            Expr* ai = ((CExpr*)a->followDefs())->kids[1];
            Expr* ah = ((CExpr*)a->followDefs())->kids[2];
            k->inc();
            if( k->followDefs()->getclass()==INT_EXPR ){
               if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
                  e0 = ai;
                  e0->inc();
               }else{
                  ah->inc();
                  Expr* e4;
                  k->inc();
                  Expr* e5;
                  e5 = new IntExpr( 1 );
                  e5->inc();
                  e4 = f_mpz_sub( k, e5 );
                  k->dec();
                  e5->dec();
                  e0 = f_k_bit( ah, e4 );
                  ah->dec();
                  e4->dec();
               }
            }else if( k->followDefs()->getclass()==RAT_EXPR ){
               if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
                  e0 = ai;
                  e0->inc();
               }else{
                  ah->inc();
                  Expr* e6;
                  k->inc();
                  Expr* e7;
                  e7 = new IntExpr( 1 );
                  e7->inc();
                  e6 = f_mpz_sub( k, e7 );
                  k->dec();
                  e7->dec();
                  e0 = f_k_bit( ah, e6 );
                  ah->dec();
                  e6->dec();
               }
            }
            k->dec();
         }else{
            std::cout << "Could not find match for expression in function f_k_bit ";
            e1->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         a->dec();
         e2->dec();
         e3->dec();
      }
   }else if( k->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         a->inc();
         Expr* e8 = a->followDefs()->get_head();
         Expr* e9;
         e9 = e_bbltn;
         e9->inc();
         Expr* e10;
         e10 = e_bbltc;
         e10->inc();
         if( e8==e9 ){
            e0 = NULL;
         }else if( e8==e10 ){
            Expr* ai = ((CExpr*)a->followDefs())->kids[1];
            Expr* ah = ((CExpr*)a->followDefs())->kids[2];
            k->inc();
            if( k->followDefs()->getclass()==INT_EXPR ){
               if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
                  e0 = ai;
                  e0->inc();
               }else{
                  ah->inc();
                  Expr* e11;
                  k->inc();
                  Expr* e12;
                  e12 = new IntExpr( 1 );
                  e12->inc();
                  e11 = f_mpz_sub( k, e12 );
                  k->dec();
                  e12->dec();
                  e0 = f_k_bit( ah, e11 );
                  ah->dec();
                  e11->dec();
               }
            }else if( k->followDefs()->getclass()==RAT_EXPR ){
               if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
                  e0 = ai;
                  e0->inc();
               }else{
                  ah->inc();
                  Expr* e13;
                  k->inc();
                  Expr* e14;
                  e14 = new IntExpr( 1 );
                  e14->inc();
                  e13 = f_mpz_sub( k, e14 );
                  k->dec();
                  e14->dec();
                  e0 = f_k_bit( ah, e13 );
                  ah->dec();
                  e13->dec();
               }
            }
            k->dec();
         }else{
            std::cout << "Could not find match for expression in function f_k_bit ";
            e8->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         a->dec();
         e9->dec();
         e10->dec();
      }
   }
   k->dec();
   return e0;
}

Expr* f_and_with_bit( Expr* a, Expr* bt ){
   Expr* e0;
   a->inc();
   Expr* e1 = a->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      e0 = e_bbltn;
      e0->inc();
   }else if( e1==e3 ){
      Expr* ai = ((CExpr*)a->followDefs())->kids[1];
      Expr* ah = ((CExpr*)a->followDefs())->kids[2];
      Expr* e4;
      bt->inc();
      ai->inc();
      static Expr* e5;
      e5 = e_and;
      e5->inc();
      e4 = new CExpr( APP, e5, bt, ai );
      Expr* e6;
      ah->inc();
      bt->inc();
      e6 = f_and_with_bit( ah, bt );
      ah->dec();
      bt->dec();
      static Expr* e7;
      e7 = e_bbltc;
      e7->inc();
      e0 = new CExpr( APP, e7, e4, e6 );
   }else{
      std::cout << "Could not find match for expression in function f_and_with_bit ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   a->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_mult_step_k_h( Expr* a, Expr* b, Expr* res, Expr* carry, Expr* k ){
   Expr* e0;
   a->inc();
   Expr* e1 = a->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      b->inc();
      Expr* e4 = b->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      if( e4==e5 ){
         e0 = res;
         e0->inc();
      }else{
         e0 = NULL;
      }
      b->dec();
      e5->dec();
   }else if( e1==e3 ){
      Expr* ai = ((CExpr*)a->followDefs())->kids[1];
      Expr* ah = ((CExpr*)a->followDefs())->kids[2];
      b->inc();
      Expr* e6 = b->followDefs()->get_head();
      Expr* e7;
      e7 = e_bbltn;
      e7->inc();
      Expr* e8;
      e8 = e_bbltc;
      e8->inc();
      if( e6==e7 ){
         e0 = NULL;
      }else if( e6==e8 ){
         Expr* bi = ((CExpr*)b->followDefs())->kids[1];
         Expr* bh = ((CExpr*)b->followDefs())->kids[2];
         Expr* e9;
         k->inc();
         Expr* e10;
         e10 = new IntExpr( 1 );
         e10->inc();
         e9 = f_mpz_sub( k, e10 );
         k->dec();
         e10->dec();
         if( e9->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)e9->followDefs())->n ) < 0 ){
               Expr* carry_out;
               Expr* e11;
               ai->inc();
               bi->inc();
               static Expr* e12;
               e12 = e_and;
               e12->inc();
               e11 = new CExpr( APP, e12, ai, bi );
               Expr* e13;
               Expr* e14;
               ai->inc();
               bi->inc();
               static Expr* e15;
               e15 = e_xor;
               e15->inc();
               e14 = new CExpr( APP, e15, ai, bi );
               carry->inc();
               static Expr* e16;
               e16 = e_and;
               e16->inc();
               e13 = new CExpr( APP, e16, e14, carry );
               static Expr* e17;
               e17 = e_or;
               e17->inc();
               carry_out = new CExpr( APP, e17, e11, e13 );
               Expr* curr;
               Expr* e18;
               ai->inc();
               bi->inc();
               static Expr* e19;
               e19 = e_xor;
               e19->inc();
               e18 = new CExpr( APP, e19, ai, bi );
               carry->inc();
               static Expr* e20;
               e20 = e_xor;
               e20->inc();
               curr = new CExpr( APP, e20, e18, carry );
               ah->inc();
               bh->inc();
               Expr* e21;
               curr->inc();
               res->inc();
               static Expr* e22;
               e22 = e_bbltc;
               e22->inc();
               e21 = new CExpr( APP, e22, curr, res );
               carry_out->inc();
               Expr* e23;
               k->inc();
               Expr* e24;
               e24 = new IntExpr( 1 );
               e24->inc();
               e23 = f_mpz_sub( k, e24 );
               k->dec();
               e24->dec();
               e0 = f_mult_step_k_h( ah, bh, e21, carry_out, e23 );
               ah->dec();
               bh->dec();
               e21->dec();
               carry_out->dec();
               e23->dec();
               curr->dec();
               carry_out->dec();
            }else{
               ah->inc();
               b->inc();
               Expr* e25;
               ai->inc();
               res->inc();
               static Expr* e26;
               e26 = e_bbltc;
               e26->inc();
               e25 = new CExpr( APP, e26, ai, res );
               carry->inc();
               Expr* e27;
               k->inc();
               Expr* e28;
               e28 = new IntExpr( 1 );
               e28->inc();
               e27 = f_mpz_sub( k, e28 );
               k->dec();
               e28->dec();
               e0 = f_mult_step_k_h( ah, b, e25, carry, e27 );
               ah->dec();
               b->dec();
               e25->dec();
               carry->dec();
               e27->dec();
            }
         }else if( e9->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)e9->followDefs())->n ) < 0 ){
               Expr* carry_out;
               Expr* e29;
               ai->inc();
               bi->inc();
               static Expr* e30;
               e30 = e_and;
               e30->inc();
               e29 = new CExpr( APP, e30, ai, bi );
               Expr* e31;
               Expr* e32;
               ai->inc();
               bi->inc();
               static Expr* e33;
               e33 = e_xor;
               e33->inc();
               e32 = new CExpr( APP, e33, ai, bi );
               carry->inc();
               static Expr* e34;
               e34 = e_and;
               e34->inc();
               e31 = new CExpr( APP, e34, e32, carry );
               static Expr* e35;
               e35 = e_or;
               e35->inc();
               carry_out = new CExpr( APP, e35, e29, e31 );
               Expr* curr;
               Expr* e36;
               ai->inc();
               bi->inc();
               static Expr* e37;
               e37 = e_xor;
               e37->inc();
               e36 = new CExpr( APP, e37, ai, bi );
               carry->inc();
               static Expr* e38;
               e38 = e_xor;
               e38->inc();
               curr = new CExpr( APP, e38, e36, carry );
               ah->inc();
               bh->inc();
               Expr* e39;
               curr->inc();
               res->inc();
               static Expr* e40;
               e40 = e_bbltc;
               e40->inc();
               e39 = new CExpr( APP, e40, curr, res );
               carry_out->inc();
               Expr* e41;
               k->inc();
               Expr* e42;
               e42 = new IntExpr( 1 );
               e42->inc();
               e41 = f_mpz_sub( k, e42 );
               k->dec();
               e42->dec();
               e0 = f_mult_step_k_h( ah, bh, e39, carry_out, e41 );
               ah->dec();
               bh->dec();
               e39->dec();
               carry_out->dec();
               e41->dec();
               curr->dec();
               carry_out->dec();
            }else{
               ah->inc();
               b->inc();
               Expr* e43;
               ai->inc();
               res->inc();
               static Expr* e44;
               e44 = e_bbltc;
               e44->inc();
               e43 = new CExpr( APP, e44, ai, res );
               carry->inc();
               Expr* e45;
               k->inc();
               Expr* e46;
               e46 = new IntExpr( 1 );
               e46->inc();
               e45 = f_mpz_sub( k, e46 );
               k->dec();
               e46->dec();
               e0 = f_mult_step_k_h( ah, b, e43, carry, e45 );
               ah->dec();
               b->dec();
               e43->dec();
               carry->dec();
               e45->dec();
            }
         }
         e9->dec();
      }else{
         std::cout << "Could not find match for expression in function f_mult_step_k_h ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      b->dec();
      e7->dec();
      e8->dec();
   }else{
      std::cout << "Could not find match for expression in function f_mult_step_k_h ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   a->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_mult_step( Expr* a, Expr* b, Expr* res, Expr* n, Expr* k ){
   Expr* e0;
   Expr* kh;
   n->inc();
   k->inc();
   kh = f_mpz_sub( n, k );
   n->dec();
   k->dec();
   Expr* ak;
   a->inc();
   kh->inc();
   ak = f_top_k_bits( a, kh );
   a->dec();
   kh->dec();
   Expr* bh;
   ak->inc();
   Expr* e1;
   b->inc();
   k->inc();
   e1 = f_k_bit( b, k );
   b->dec();
   k->dec();
   bh = f_and_with_bit( ak, e1 );
   ak->dec();
   e1->dec();
   Expr* e2;
   kh->inc();
   Expr* e3;
   e3 = new IntExpr( 1 );
   e3->inc();
   e2 = f_mpz_sub( kh, e3 );
   kh->dec();
   e3->dec();
   if( e2->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)e2->followDefs())->n ) == 0 ){
         res->inc();
         bh->inc();
         static Expr* e4;
         e4 = e_bbltn;
         e4->inc();
         static Expr* e5;
         e5 = e_false;
         e5->inc();
         k->inc();
         e0 = f_mult_step_k_h( res, bh, e4, e5, k );
         res->dec();
         bh->dec();
         e4->dec();
         e5->dec();
         k->dec();
      }else{
         Expr* resh;
         res->inc();
         bh->inc();
         static Expr* e6;
         e6 = e_bbltn;
         e6->inc();
         static Expr* e7;
         e7 = e_false;
         e7->inc();
         k->inc();
         resh = f_mult_step_k_h( res, bh, e6, e7, k );
         res->dec();
         bh->dec();
         e6->dec();
         e7->dec();
         k->dec();
         a->inc();
         b->inc();
         Expr* e8;
         resh->inc();
         e8 = f_reverseb( resh );
         resh->dec();
         n->inc();
         Expr* e9;
         k->inc();
         Expr* e10;
         e10 = new IntExpr( 1 );
         e10->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            mpz_t rnum0;
            mpz_init(rnum0);
            mpz_add( rnum0, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e10->followDefs())->n);
            e9 = new IntExpr(rnum0);
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            mpq_t rnum0;
            mpq_init(rnum0);
            mpq_add( rnum0, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e10->followDefs())->n);
            e9 = new RatExpr(rnum0);
         }
         k->dec();
         e10->dec();
         e0 = f_mult_step( a, b, e8, n, e9 );
         a->dec();
         b->dec();
         e8->dec();
         n->dec();
         e9->dec();
         resh->dec();
      }
   }else if( e2->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)e2->followDefs())->n ) == 0 ){
         res->inc();
         bh->inc();
         static Expr* e11;
         e11 = e_bbltn;
         e11->inc();
         static Expr* e12;
         e12 = e_false;
         e12->inc();
         k->inc();
         e0 = f_mult_step_k_h( res, bh, e11, e12, k );
         res->dec();
         bh->dec();
         e11->dec();
         e12->dec();
         k->dec();
      }else{
         Expr* resh;
         res->inc();
         bh->inc();
         static Expr* e13;
         e13 = e_bbltn;
         e13->inc();
         static Expr* e14;
         e14 = e_false;
         e14->inc();
         k->inc();
         resh = f_mult_step_k_h( res, bh, e13, e14, k );
         res->dec();
         bh->dec();
         e13->dec();
         e14->dec();
         k->dec();
         a->inc();
         b->inc();
         Expr* e15;
         resh->inc();
         e15 = f_reverseb( resh );
         resh->dec();
         n->inc();
         Expr* e16;
         k->inc();
         Expr* e17;
         e17 = new IntExpr( 1 );
         e17->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            mpz_t rnum1;
            mpz_init(rnum1);
            mpz_add( rnum1, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e17->followDefs())->n);
            e16 = new IntExpr(rnum1);
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            mpq_t rnum1;
            mpq_init(rnum1);
            mpq_add( rnum1, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e17->followDefs())->n);
            e16 = new RatExpr(rnum1);
         }
         k->dec();
         e17->dec();
         e0 = f_mult_step( a, b, e15, n, e16 );
         a->dec();
         b->dec();
         e15->dec();
         n->dec();
         e16->dec();
         resh->dec();
      }
   }
   e2->dec();
   bh->dec();
   ak->dec();
   kh->dec();
   return e0;
}

Expr* f_bblast_bvmul( Expr* a, Expr* b, Expr* n ){
   Expr* e0;
   Expr* ar;
   a->inc();
   ar = f_reverseb( a );
   a->dec();
   Expr* br;
   b->inc();
   br = f_reverseb( b );
   b->dec();
   Expr* res;
   ar->inc();
   Expr* e1;
   br->inc();
   Expr* e2;
   e2 = new IntExpr((long int) 0 );
   e2->inc();
   e1 = f_k_bit( br, e2 );
   br->dec();
   e2->dec();
   res = f_and_with_bit( ar, e1 );
   ar->dec();
   e1->dec();
   ar->inc();
   br->inc();
   res->inc();
   n->inc();
   Expr* e3;
   e3 = new IntExpr( 1 );
   e3->inc();
   e0 = f_mult_step( ar, br, res, n, e3 );
   ar->dec();
   br->dec();
   res->dec();
   n->dec();
   e3->dec();
   res->dec();
   br->dec();
   ar->dec();
   return e0;
}

Expr* f_bblast_eq_rec( Expr* x, Expr* y, Expr* f ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      y->inc();
      Expr* e4 = y->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      if( e4==e5 ){
         e0 = f;
         e0->inc();
      }else{
         e0 = NULL;
      }
      y->dec();
      e5->dec();
   }else if( e1==e3 ){
      Expr* fx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      y->inc();
      Expr* e6 = y->followDefs()->get_head();
      Expr* e7;
      e7 = e_bbltn;
      e7->inc();
      Expr* e8;
      e8 = e_bbltc;
      e8->inc();
      if( e6==e7 ){
         e0 = NULL;
      }else if( e6==e8 ){
         Expr* fy = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         xh->inc();
         yh->inc();
         Expr* e9;
         Expr* e10;
         fx->inc();
         fy->inc();
         static Expr* e11;
         e11 = e_iff;
         e11->inc();
         e10 = new CExpr( APP, e11, fx, fy );
         f->inc();
         static Expr* e12;
         e12 = e_and;
         e12->inc();
         e9 = new CExpr( APP, e12, e10, f );
         e0 = f_bblast_eq_rec( xh, yh, e9 );
         xh->dec();
         yh->dec();
         e9->dec();
      }else{
         std::cout << "Could not find match for expression in function f_bblast_eq_rec ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      y->dec();
      e7->dec();
      e8->dec();
   }else{
      e0 = NULL;
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_eq( Expr* x, Expr* y ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltc;
   e2->inc();
   if( e1==e2 ){
      Expr* bx = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      y->inc();
      Expr* e3 = y->followDefs()->get_head();
      Expr* e4;
      e4 = e_bbltc;
      e4->inc();
      if( e3==e4 ){
         Expr* by = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         xh->inc();
         yh->inc();
         Expr* e5;
         bx->inc();
         by->inc();
         static Expr* e6;
         e6 = e_iff;
         e6->inc();
         e5 = new CExpr( APP, e6, bx, by );
         e0 = f_bblast_eq_rec( xh, yh, e5 );
         xh->dec();
         yh->dec();
         e5->dec();
      }else{
         e0 = NULL;
      }
      y->dec();
      e4->dec();
   }else{
      e0 = NULL;
   }
   x->dec();
   e2->dec();
   return e0;
}

Expr* f_bblast_bvult( Expr* x, Expr* y, Expr* n ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      e0 = NULL;
   }else if( e1==e3 ){
      Expr* xi = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      y->inc();
      Expr* e4 = y->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      Expr* e6;
      e6 = e_bbltc;
      e6->inc();
      if( e4==e5 ){
         e0 = NULL;
      }else if( e4==e6 ){
         Expr* yi = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         n->inc();
         if( n->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)n->followDefs())->n ) == 0 ){
               Expr* e7;
               xi->inc();
               static Expr* e8;
               e8 = e_not;
               e8->inc();
               e7 = new CExpr( APP, e8, xi );
               yi->inc();
               static Expr* e9;
               e9 = e_and;
               e9->inc();
               e0 = new CExpr( APP, e9, e7, yi );
            }else{
               Expr* e10;
               Expr* e11;
               xi->inc();
               yi->inc();
               static Expr* e12;
               e12 = e_iff;
               e12->inc();
               e11 = new CExpr( APP, e12, xi, yi );
               Expr* e13;
               xh->inc();
               yh->inc();
               Expr* e14;
               n->inc();
               Expr* e15;
               e15 = new IntExpr( -1 );
               e15->inc();
               if( n->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum0;
                  mpz_init(rnum0);
                  mpz_add( rnum0, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e15->followDefs())->n);
                  e14 = new IntExpr(rnum0);
               }else if( n->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum0;
                  mpq_init(rnum0);
                  mpq_add( rnum0, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e15->followDefs())->n);
                  e14 = new RatExpr(rnum0);
               }
               n->dec();
               e15->dec();
               e13 = f_bblast_bvult( xh, yh, e14 );
               xh->dec();
               yh->dec();
               e14->dec();
               static Expr* e16;
               e16 = e_and;
               e16->inc();
               e10 = new CExpr( APP, e16, e11, e13 );
               Expr* e17;
               Expr* e18;
               xi->inc();
               static Expr* e19;
               e19 = e_not;
               e19->inc();
               e18 = new CExpr( APP, e19, xi );
               yi->inc();
               static Expr* e20;
               e20 = e_and;
               e20->inc();
               e17 = new CExpr( APP, e20, e18, yi );
               static Expr* e21;
               e21 = e_or;
               e21->inc();
               e0 = new CExpr( APP, e21, e10, e17 );
            }
         }else if( n->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)n->followDefs())->n ) == 0 ){
               Expr* e22;
               xi->inc();
               static Expr* e23;
               e23 = e_not;
               e23->inc();
               e22 = new CExpr( APP, e23, xi );
               yi->inc();
               static Expr* e24;
               e24 = e_and;
               e24->inc();
               e0 = new CExpr( APP, e24, e22, yi );
            }else{
               Expr* e25;
               Expr* e26;
               xi->inc();
               yi->inc();
               static Expr* e27;
               e27 = e_iff;
               e27->inc();
               e26 = new CExpr( APP, e27, xi, yi );
               Expr* e28;
               xh->inc();
               yh->inc();
               Expr* e29;
               n->inc();
               Expr* e30;
               e30 = new IntExpr( -1 );
               e30->inc();
               if( n->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum1;
                  mpz_init(rnum1);
                  mpz_add( rnum1, ((IntExpr*)n->followDefs())->n, ((IntExpr*)e30->followDefs())->n);
                  e29 = new IntExpr(rnum1);
               }else if( n->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum1;
                  mpq_init(rnum1);
                  mpq_add( rnum1, ((RatExpr*)n->followDefs())->n, ((RatExpr*)e30->followDefs())->n);
                  e29 = new RatExpr(rnum1);
               }
               n->dec();
               e30->dec();
               e28 = f_bblast_bvult( xh, yh, e29 );
               xh->dec();
               yh->dec();
               e29->dec();
               static Expr* e31;
               e31 = e_and;
               e31->inc();
               e25 = new CExpr( APP, e31, e26, e28 );
               Expr* e32;
               Expr* e33;
               xi->inc();
               static Expr* e34;
               e34 = e_not;
               e34->inc();
               e33 = new CExpr( APP, e34, xi );
               yi->inc();
               static Expr* e35;
               e35 = e_and;
               e35->inc();
               e32 = new CExpr( APP, e35, e33, yi );
               static Expr* e36;
               e36 = e_or;
               e36->inc();
               e0 = new CExpr( APP, e36, e25, e32 );
            }
         }
         n->dec();
      }else{
         std::cout << "Could not find match for expression in function f_bblast_bvult ";
         e4->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      y->dec();
      e5->dec();
      e6->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvult ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_bblast_bvslt( Expr* x, Expr* y, Expr* n ){
   Expr* e0;
   x->inc();
   Expr* e1 = x->followDefs()->get_head();
   Expr* e2;
   e2 = e_bbltn;
   e2->inc();
   Expr* e3;
   e3 = e_bbltc;
   e3->inc();
   if( e1==e2 ){
      e0 = NULL;
   }else if( e1==e3 ){
      Expr* xi = ((CExpr*)x->followDefs())->kids[1];
      Expr* xh = ((CExpr*)x->followDefs())->kids[2];
      y->inc();
      Expr* e4 = y->followDefs()->get_head();
      Expr* e5;
      e5 = e_bbltn;
      e5->inc();
      Expr* e6;
      e6 = e_bbltc;
      e6->inc();
      if( e4==e5 ){
         e0 = NULL;
      }else if( e4==e6 ){
         Expr* yi = ((CExpr*)y->followDefs())->kids[1];
         Expr* yh = ((CExpr*)y->followDefs())->kids[2];
         Expr* e7;
         n->inc();
         Expr* e8;
         e8 = new IntExpr( 1 );
         e8->inc();
         e7 = f_mpz_sub( n, e8 );
         n->dec();
         e8->dec();
         if( e7->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)e7->followDefs())->n ) == 0 ){
               xi->inc();
               Expr* e9;
               yi->inc();
               static Expr* e10;
               e10 = e_not;
               e10->inc();
               e9 = new CExpr( APP, e10, yi );
               static Expr* e11;
               e11 = e_and;
               e11->inc();
               e0 = new CExpr( APP, e11, xi, e9 );
            }else{
               Expr* e12;
               Expr* e13;
               xi->inc();
               yi->inc();
               static Expr* e14;
               e14 = e_iff;
               e14->inc();
               e13 = new CExpr( APP, e14, xi, yi );
               Expr* e15;
               xh->inc();
               yh->inc();
               Expr* e16;
               n->inc();
               Expr* e17;
               e17 = new IntExpr( 2 );
               e17->inc();
               e16 = f_mpz_sub( n, e17 );
               n->dec();
               e17->dec();
               e15 = f_bblast_bvult( xh, yh, e16 );
               xh->dec();
               yh->dec();
               e16->dec();
               static Expr* e18;
               e18 = e_and;
               e18->inc();
               e12 = new CExpr( APP, e18, e13, e15 );
               Expr* e19;
               xi->inc();
               Expr* e20;
               yi->inc();
               static Expr* e21;
               e21 = e_not;
               e21->inc();
               e20 = new CExpr( APP, e21, yi );
               static Expr* e22;
               e22 = e_and;
               e22->inc();
               e19 = new CExpr( APP, e22, xi, e20 );
               static Expr* e23;
               e23 = e_or;
               e23->inc();
               e0 = new CExpr( APP, e23, e12, e19 );
            }
         }else if( e7->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)e7->followDefs())->n ) == 0 ){
               xi->inc();
               Expr* e24;
               yi->inc();
               static Expr* e25;
               e25 = e_not;
               e25->inc();
               e24 = new CExpr( APP, e25, yi );
               static Expr* e26;
               e26 = e_and;
               e26->inc();
               e0 = new CExpr( APP, e26, xi, e24 );
            }else{
               Expr* e27;
               Expr* e28;
               xi->inc();
               yi->inc();
               static Expr* e29;
               e29 = e_iff;
               e29->inc();
               e28 = new CExpr( APP, e29, xi, yi );
               Expr* e30;
               xh->inc();
               yh->inc();
               Expr* e31;
               n->inc();
               Expr* e32;
               e32 = new IntExpr( 2 );
               e32->inc();
               e31 = f_mpz_sub( n, e32 );
               n->dec();
               e32->dec();
               e30 = f_bblast_bvult( xh, yh, e31 );
               xh->dec();
               yh->dec();
               e31->dec();
               static Expr* e33;
               e33 = e_and;
               e33->inc();
               e27 = new CExpr( APP, e33, e28, e30 );
               Expr* e34;
               xi->inc();
               Expr* e35;
               yi->inc();
               static Expr* e36;
               e36 = e_not;
               e36->inc();
               e35 = new CExpr( APP, e36, yi );
               static Expr* e37;
               e37 = e_and;
               e37->inc();
               e34 = new CExpr( APP, e37, xi, e35 );
               static Expr* e38;
               e38 = e_or;
               e38->inc();
               e0 = new CExpr( APP, e38, e27, e34 );
            }
         }
         e7->dec();
      }else{
         std::cout << "Could not find match for expression in function f_bblast_bvslt ";
         e4->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      y->dec();
      e5->dec();
      e6->dec();
   }else{
      std::cout << "Could not find match for expression in function f_bblast_bvslt ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   x->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_mk_ones( Expr* n ){
   Expr* e0;
   n->inc();
   if( n->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)n->followDefs())->n ) == 0 ){
         e0 = e_bvn;
         e0->inc();
      }else{
         static Expr* e1;
         e1 = e_b1;
         e1->inc();
         Expr* e2;
         Expr* e3;
         n->inc();
         Expr* e4;
         e4 = new IntExpr( 1 );
         e4->inc();
         e3 = f_mpz_sub( n, e4 );
         n->dec();
         e4->dec();
         e2 = f_mk_ones( e3 );
         e3->dec();
         static Expr* e5;
         e5 = e_bvc;
         e5->inc();
         e0 = new CExpr( APP, e5, e1, e2 );
      }
   }else if( n->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)n->followDefs())->n ) == 0 ){
         e0 = e_bvn;
         e0->inc();
      }else{
         static Expr* e6;
         e6 = e_b1;
         e6->inc();
         Expr* e7;
         Expr* e8;
         n->inc();
         Expr* e9;
         e9 = new IntExpr( 1 );
         e9->inc();
         e8 = f_mpz_sub( n, e9 );
         n->dec();
         e9->dec();
         e7 = f_mk_ones( e8 );
         e8->dec();
         static Expr* e10;
         e10 = e_bvc;
         e10->inc();
         e0 = new CExpr( APP, e10, e6, e7 );
      }
   }
   n->dec();
   return e0;
}

Expr* f_mk_zero( Expr* n ){
   Expr* e0;
   n->inc();
   if( n->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)n->followDefs())->n ) == 0 ){
         e0 = e_bvn;
         e0->inc();
      }else{
         static Expr* e1;
         e1 = e_b0;
         e1->inc();
         Expr* e2;
         Expr* e3;
         n->inc();
         Expr* e4;
         e4 = new IntExpr( 1 );
         e4->inc();
         e3 = f_mpz_sub( n, e4 );
         n->dec();
         e4->dec();
         e2 = f_mk_ones( e3 );
         e3->dec();
         static Expr* e5;
         e5 = e_bvc;
         e5->inc();
         e0 = new CExpr( APP, e5, e1, e2 );
      }
   }else if( n->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)n->followDefs())->n ) == 0 ){
         e0 = e_bvn;
         e0->inc();
      }else{
         static Expr* e6;
         e6 = e_b0;
         e6->inc();
         Expr* e7;
         Expr* e8;
         n->inc();
         Expr* e9;
         e9 = new IntExpr( 1 );
         e9->inc();
         e8 = f_mpz_sub( n, e9 );
         n->dec();
         e9->dec();
         e7 = f_mk_ones( e8 );
         e8->dec();
         static Expr* e10;
         e10 = e_bvc;
         e10->inc();
         e0 = new CExpr( APP, e10, e6, e7 );
      }
   }
   n->dec();
   return e0;
}

