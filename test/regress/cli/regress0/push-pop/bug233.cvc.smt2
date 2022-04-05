; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(check-sat-assuming ( (not (let ((_let_1 (and a b))) (or _let_1 (not _let_1)))) ))
(check-sat-assuming ( (not (or a b)) ))
