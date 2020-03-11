; EXPECT: unsat
; COMMAND-LINE: --sygus-inference --sygus-qe-preproc
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (forall ((c Real)) (and (xor (> c a) (= b 0)) (distinct (+ a b) 0))))
(check-sat)
