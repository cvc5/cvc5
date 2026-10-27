; COMMAND-LINE: --print-cores-full --produce-unsat-cores
; EXPECT: unsat
; EXPECT: (
; EXPECT: (let ((_let_1 (> x 0))) (and _let_1 (not _let_1)))
; EXPECT: )
(set-logic ALL)
(declare-fun x () Int)
(assert (and (> x 0) (not (> x 0))))
(check-sat)
(get-unsat-core)
