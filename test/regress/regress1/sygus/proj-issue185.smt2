; COMMAND-LINE: -q
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :sygus-inference true)
(set-info :status unsat)
(declare-codatatypes ((a 0)) (((b (c Int) (d a)))))
(declare-fun e () a)
(declare-fun f () a)
(assert (= e (b 0 (b 0 e))))
(assert (distinct f (b 0 f)))
(assert (not (distinct e f)))
(check-sat)
