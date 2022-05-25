; COMMAND-LINE: -q
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun a () String)
(assert (forall ((b Int)) (or (> (str.len a) b) (= 0 (mod b 74998)))))
(check-sat)
