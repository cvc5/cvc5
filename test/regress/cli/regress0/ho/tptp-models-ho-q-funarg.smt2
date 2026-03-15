; COMMAND-LINE: --tptp-models --force-logic=HO_ALL --mbqi
; SCRUBBER: sed -E 's/Bound_variable_[0-9]+/Bound_variable/g'
; EXPECT: sat
; EXPECT: %--------------------------------------------------------
; EXPECT: thf(u_type,type,
; EXPECT:     u: $tType ).
; EXPECT:
; EXPECT: thf(a_decl,type,
; EXPECT:     a: u ).
; EXPECT:
; EXPECT: thf(b_decl,type,
; EXPECT:     b: u ).
; EXPECT:
; EXPECT: thf(g_decl,type,
; EXPECT:     g: u > u ).
; EXPECT:
; EXPECT: thf(h_decl,type,
; EXPECT:     h: u > u ).
; EXPECT:
; EXPECT: thf(q_decl,type,
; EXPECT:     q: ( u > u ) > u ).
; EXPECT:
; EXPECT: %----Types of the domains
; EXPECT: thf(d_u_type,type,
; EXPECT:     d_u: $tType ).
; EXPECT:
; EXPECT: %----Types of the promotion functions
; EXPECT: thf(d2u_decl,type,
; EXPECT:     d2u: d_u > u ).
; EXPECT:
; EXPECT: %----Types of the domain elements
; EXPECT: thf(d_a_decl,type,
; EXPECT:     d_a: d_u ).
; EXPECT:
; EXPECT: thf(d_b_decl,type,
; EXPECT:     d_b: d_u ).
; EXPECT:
; EXPECT: thf(tptp_models_ho_q_funarg_smt2,interpretation,
; EXPECT:     ( ! [U: u] :
; EXPECT:       ? [DU: d_u] :
; EXPECT:         ( U = ( d2u @ DU ) )
; EXPECT:     & ! [DU: d_u] :
; EXPECT:         ( ( DU = d_a )
; EXPECT:         | ( DU = d_b ) )
; EXPECT:     & ( d_a != d_b )
; EXPECT:     & ! [DU1: d_u,DU2: d_u] :
; EXPECT:         ( ( ( d2u @ DU1 ) = ( d2u @ DU2 ) )
; EXPECT:        => ( DU1 = DU2 ) )
; EXPECT:     & ( a = ( d2u @ d_a ) )
; EXPECT:     & ( b = ( d2u @ d_b ) )
; EXPECT:     & ( ( g @ ( d2u @ d_a ) ) = ( d2u @ d_a ) )
; EXPECT:     & ( ( g @ ( d2u @ d_b ) ) = ( d2u @ d_b ) )
; EXPECT:     & ( ( h @ ( d2u @ d_a ) ) = ( d2u @ d_a ) )
; EXPECT:     & ( ( h @ ( d2u @ d_b ) ) = ( d2u @ d_b ) )
; EXPECT:     & ( q
; EXPECT:       = ( ^ [Bound_variable: u > u] :
; EXPECT:             $ite(
; EXPECT:               ( ( ^ [Bound_variable: u] :
; EXPECT:                           $ite(
; EXPECT:                             ( Bound_variable = ( d2u @ d_a ) ),
; EXPECT:                             d2u @ d_a,
; EXPECT:                             d2u @ d_b) )
; EXPECT:                           = Bound_variable ),
; EXPECT:               d2u @ d_a,
; EXPECT:               d2u @ d_b) ) ) ) ).
; EXPECT: %--------------------------------------------------------
(set-logic HO_ALL)
(set-option :produce-models true)
(declare-sort U 0)
(declare-fun A () U)
(declare-fun B () U)
(assert (distinct A B))
(assert (forall ((x U)) (or (= x A) (= x B))))
(declare-fun g () (-> U U))
(declare-fun h () (-> U U))
(assert (= g h))
(declare-fun q ((-> U U)) U)
(assert (= (q g) A))
(assert (= (q (lambda ((x U)) B)) B))
(check-sat)
(get-model)
