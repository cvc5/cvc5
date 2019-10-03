; COMMAND-LINE: --bitblast=eager --no-check-models --no-check-proofs --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_ABV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(define-sort bv () (_ BitVec 4))
(define-sort abv () (Array bv bv))

(declare-fun v0 () (_ BitVec 4))
(declare-fun v1 () (_ BitVec 4))
(declare-fun a () abv)
(declare-fun b () abv)
(declare-fun c () abv)

(assert (not (= (select a (select b (select c v0))) (select a (select b (select c v1))))))

(assert (= v0 v1))


(check-sat)
(exit)
