; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(check-sat-assuming ( (not (= (xor a b) (or (and (not a) b) (and (not b) a)))) ))
