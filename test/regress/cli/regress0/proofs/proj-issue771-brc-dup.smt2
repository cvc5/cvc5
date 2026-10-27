; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(declare-fun b () String)
(assert (= (str.at "" 0) (str.replace (str.from_int (str.len b))
(str.from_int 0) (str.from_int (str.len a)))))
(check-sat)
