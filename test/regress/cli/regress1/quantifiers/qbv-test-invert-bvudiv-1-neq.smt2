; COMMAND-LINE: --cegqi-bv --cegqi-bv-ineq=keep --no-cegqi-full
; EXPECT: unsat
;; introduces unsupported Skolem
; DISABLE-TESTER: alethe
(set-logic BV)
(set-info :status unsat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (distinct a b (_ bv0 8)))
(assert (forall ((x (_ BitVec 8))) (= (bvudiv a x) b)))

(check-sat)
