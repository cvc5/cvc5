; COMMAND-LINE: --no-nl-cov
; EXPECT: unsat
; Input has mixed arithmetic
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun s () Real)
(declare-fun k () Real)
(assert (and (< s 1) (<= k 1) (< 0 s) (= 0.0 (+ 1 (* s s k (- 1))))))
(check-sat)
