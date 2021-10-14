; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(check-sat-assuming ( (not (let ((_let_1 (= a b))) (not (and _let_1 (not _let_1))))) ))
