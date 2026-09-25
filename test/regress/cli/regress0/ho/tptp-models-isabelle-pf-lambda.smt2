; COMMAND-LINE: --tptp-models --force-logic=HO_ALL --mbqi
; SCRUBBER: sed -E 's/Bound_variable_[0-9]+/Bound_variable/g'
; EXPECT: sat
; EXPECT: %--------------------------------------------------------
; EXPECT: thf(a_type,type,
; EXPECT:     a: $tType ).
; EXPECT:
; EXPECT: thf(p_decl,type,
; EXPECT:     p: ( a > a ) > $o ).
; EXPECT:
; EXPECT: thf(f_decl,type,
; EXPECT:     f: a > a ).
; EXPECT:
; EXPECT: %----Types of the domains
; EXPECT: thf(d_a_type,type,
; EXPECT:     d_a: $tType ).
; EXPECT:
; EXPECT: %----Types of the promotion functions
; EXPECT: thf(d2a_decl,type,
; EXPECT:     d2a: d_a > a ).
; EXPECT:
; EXPECT: %----Types of the domain elements
; EXPECT: thf(d_a_0_decl,type,
; EXPECT:     d_a_0: d_a ).
; EXPECT:
; EXPECT: thf(tptp_models_isabelle_pf_lambda_smt2,interpretation,
; EXPECT:     ( ! [A: a] :
; EXPECT:       ? [DA: d_a] :
; EXPECT:         ( A = ( d2a @ DA ) )
; EXPECT:     & ! [DA: d_a] : ( DA = d_a_0 )
; EXPECT:     & ! [DA1: d_a,DA2: d_a] :
; EXPECT:         ( ( ( d2a @ DA1 ) = ( d2a @ DA2 ) )
; EXPECT:        => ( DA1 = DA2 ) )
; EXPECT:     & ( p
; EXPECT:       = ( ^ [Bound_variable: a > a] : $false ) )
; EXPECT:     & ( ( f @ ( d2a @ d_a_0 ) ) = ( d2a @ d_a_0 ) ) ) ).
; EXPECT: %--------------------------------------------------------
(set-logic HO_ALL)
(set-option :produce-models true)
(declare-sort A 0)
(declare-fun P ((-> A A)) Bool)
(declare-fun f () (-> A A))
(assert (not (P f)))
(check-sat)
(get-model)
