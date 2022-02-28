; same as bug421.smt2 but adds on command line:
; this actually caused the same bug for a different reason, so
; we check them both independently in regressions
;
; COMMAND-LINE: --incremental --abstract-values
; EXPECT: sat
; EXPECT: ((a (as @a_1 (Array Int Int))) (b (as @a_2 (Array Int Int))))
(set-logic QF_AUFLIA)
(set-option :produce-models true)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (not (= a b)))
(check-sat)
(get-value (a b))
