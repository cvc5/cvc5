; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: (((f 0) 1))
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(set-logic QF_UFLIA)

(declare-fun f (Int) Int)
(assert (= (f 0) 1))
(check-sat)
(get-value ((f 0)))
; add a "push" just to double-check that incremental mode is on
(push)
