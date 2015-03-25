; COMMAND-LINE: --incremental --abstract-values
; EXPECT: sat
; EXPECT: ((a (as @1 (Array Int Int))) (b (as @2 (Array Int Int))))
(set-logic QF_AUFLIA)
(set-option :produce-models true)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (not (= a b)))
(check-sat)
(get-value (a b))
