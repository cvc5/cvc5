; EXPECT: unsat
(set-logic QF_S)
(declare-fun v () String)
(assert (distinct true (str.< (str.replace (str.replace_all v v "") (str.++ v "fi") (str.from_int 0)) (str.to_lower (str.replace (str.++ v "fi") "fi" (str.rev "fi"))))))
(check-sat)
