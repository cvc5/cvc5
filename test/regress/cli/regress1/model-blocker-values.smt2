; COMMAND-LINE: --incremental --produce-models
; EXPECT: sat
; EXPECT: sat
; if we only block models restricted to (a,b), then there are only 2 models
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert (distinct (f a) (f b)))
(assert (= c (f a)))
(assert (distinct a b))
(assert (and (>= a 0) (>= b 0) (< a 2) (< b 2)))
(check-sat)
(block-model :values)
(check-sat)
(block-model :values)
(check-sat)
