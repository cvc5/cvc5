; COMMAND-LINE: --unconstrained-simp
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(assert (forall ((c (_ BitVec 8)))
  (not (= (bvashr c (bvadd a b)) b))))

(assert (= (bvadd a b) (_ bv0 8)))
(check-sat)
