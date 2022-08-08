; SCRUBBER: grep -v -E '(\(|\)|\:proves)'
; COMMAND-LINE: --simplification=none
; EXPECT: unsat
; DISABLE-TESTER: lfsc
(set-logic QF_UFLIA)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-option :produce-proofs true)
(declare-sort U 0)
(declare-fun f1 () U)
(declare-fun f2 () U)
(declare-fun f3 () U)
(declare-fun f4 () U)
(declare-fun p (U) Bool)
(declare-fun x () Int)
(assert (and (= 0 0) (not (= f1 f2))))
(assert (and (p f1) (or (= f1 f2) (distinct f3 f4 f2)) (p f3)))
(assert (= f3 f4))
(assert (> x 0))
(check-sat)

(get-proof :raw_preprocess)

(get-proof :preprocess)

(get-proof :sat)

(get-proof :theory_lemmas)

(get-proof :full)
