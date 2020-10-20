; REQUIRES: proof
; COMMAND-LINE: --dump-instantiations --produce-unsat-cores --print-inst-full
; EXPECT: unsat
; EXPECT: (instantiations (forall ((x Int)) (or (P x) (Q x)) )
; EXPECT:   ( 2 )
; EXPECT: )
; EXPECT: (instantiations (forall ((x Int)) (or (not (S x)) (not (Q x))) )
; EXPECT:   ( 2 )
; EXPECT: )
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)
(declare-fun S (Int) Bool)
(declare-fun W (Int) Bool)
(declare-fun U (Int) Bool)
(assert (forall ((x Int)) (or (P x) (Q x))))
(assert (forall ((x Int)) (or (R x) (W x))))
(assert (forall ((x Int)) (or (S x) (U x))))
(assert (forall ((x Int)) (or (not (S x)) (not (Q x)))))
(assert (and (not (R 0)) (not (R 10)) (not (S 1)) (not (P 2))))
(assert (S 2))
; This tests that --produce-unsat-cores minimizes the instantiations
; printed out.  This regression should require only the 2
; instantiations above, but may try more.
(check-sat)
