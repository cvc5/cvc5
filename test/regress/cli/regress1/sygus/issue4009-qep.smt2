; EXPECT: unsat
; COMMAND-LINE: --sygus-inference --sygus-qe-preproc -q
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; DISABLE-TESTER: lfsc
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (forall ((c Real)) (and (xor (> c a) (= b 0.0)) (distinct (+ a b) 0.0))))
(check-sat)
