; COMMAND-LINE: --output-language=smt2-tptp
; EXPECT: sat
; EXPECT: %--------------------------------------------------------
; EXPECT: tff(unsorted_type,type,
; EXPECT:     unsorted: $tType ).
; EXPECT:
; EXPECT: tff(a_decl,type,
; EXPECT:     a: $i ).
; EXPECT:
; EXPECT: tff(b_decl,type,
; EXPECT:     b: $i ).
; EXPECT:
; EXPECT: %----Types of the domains
; EXPECT: tff(d_unsorted_type,type,
; EXPECT:     d_unsorted: $tType ).
; EXPECT:
; EXPECT: %----Types of the promotion functions
; EXPECT: tff(d2unsorted_decl,type,
; EXPECT:     d2unsorted: d_unsorted > $i ).
; EXPECT:
; EXPECT: %----Types of the domain elements
; EXPECT: tff(d_a_decl,type,
; EXPECT:     d_a: d_unsorted ).
; EXPECT:
; EXPECT: tff(d_b_decl,type,
; EXPECT:     d_b: d_unsorted ).
; EXPECT:
; EXPECT: tff(tptpmodels_unsorted_i_smt2,interpretation,
; EXPECT:     ( ! [U: $i] :
; EXPECT:       ? [DU: d_unsorted] :
; EXPECT:         ( U = d2unsorted(DU) )
; EXPECT:     & ! [DU: d_unsorted] :
; EXPECT:         ( ( DU = d_a )
; EXPECT:         | ( DU = d_b ) )
; EXPECT:     & ( d_a != d_b )
; EXPECT:     & ! [DU1: d_unsorted,DU2: d_unsorted] :
; EXPECT:         ( ( d2unsorted(DU1) = d2unsorted(DU2) )
; EXPECT:        => ( DU1 = DU2 ) )
; EXPECT:     & ( a = d2unsorted(d_a) )
; EXPECT:     & ( b = d2unsorted(d_b) ) ) ).
; EXPECT: %--------------------------------------------------------
(set-logic ALL)
(set-option :produce-models true)
(declare-sort unsorted 0)
(declare-fun a () unsorted)
(declare-fun b () unsorted)
(assert (distinct a b))
(check-sat)
(get-model)
